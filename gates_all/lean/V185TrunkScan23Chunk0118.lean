import V185TrunkScan23Chunk0117

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_698136 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 5]
def baseStart_698136 : Nat := 118140960795 + 698136 * 2 ^ 59
def prefixEnd_698136 : Nat := 4983230072969 + 3 ^ 40 * 698136 * 2
def baseEnd_698136 : Nat := 39831036689709530376593

theorem tailTrace_698136 : CollatzResearch.WordTrace tailWord_698136 prefixEnd_698136 39831036689709530376593 := by
  unfold tailWord_698136
  simp only [CollatzResearch.WordTrace]
  refine ⟨12731555899389989490677131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16975407865853319320902841 12731555899389989490677131)
  ·
    refine ⟨19097333849084984236015697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12731555899389989490677131 19097333849084984236015697)
    ·
      refine ⟨14323000386813738177011773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19097333849084984236015697 14323000386813738177011773)
      ·
        refine ⟨5371125145055151816379415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14323000386813738177011773 5371125145055151816379415)
        ·
          refine ⟨8056687717582727724569123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371125145055151816379415 8056687717582727724569123)
          ·
            refine ⟨12085031576374091586853685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8056687717582727724569123 12085031576374091586853685)
            ·
              refine ⟨1132971710285071086267533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12085031576374091586853685 1132971710285071086267533)
              ·
                refine ⟨424864391356901657350325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1132971710285071086267533 424864391356901657350325)
                ·
                  refine ⟨39831036689709530376593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 424864391356901657350325 39831036689709530376593)
                  ·
                    rfl

theorem cell23_698136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 5].length) (baseStart_698136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698136 prefixEnd_698136 := by exact prefixLift 698136
  have htrace : WordTrace (prefixWord ++ tailWord_698136) baseStart_698136 baseEnd_698136 := by
    simpa [prefixWord, tailWord_698136, baseEnd_698136] using wordTrace_append hprefix tailTrace_698136
  have hstable : (prefixWord ++ tailWord_698136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698136).length < 2 ^ (prefixWord ++ tailWord_698136).sum := by decide
  have hdescent : baseEnd_698136 < baseStart_698136 := by decide
  rcases family_descends (prefixWord ++ tailWord_698136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698149 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_698149 : Nat := 118140960795 + 698149 * 2 ^ 59
def prefixEnd_698149 : Nat := 4983230072969 + 3 ^ 40 * 698149 * 2
def baseEnd_698149 : Nat := 119495335151964740842259

theorem tailTrace_698149 : CollatzResearch.WordTrace tailWord_698149 prefixEnd_698149 119495335151964740842259 := by
  unfold tailWord_698149
  simp only [CollatzResearch.WordTrace]
  refine ⟨25463585947732882201577501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16975723965155254801051667 25463585947732882201577501)
  ·
    refine ⟨9548844730399830825591563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25463585947732882201577501 9548844730399830825591563)
    ·
      refine ⟨14323267095599746238387345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9548844730399830825591563 14323267095599746238387345)
      ·
        refine ⟨10742450321699809678790509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14323267095599746238387345 10742450321699809678790509)
        ·
          refine ⟨4028418870637428629546441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10742450321699809678790509 4028418870637428629546441)
          ·
            refine ⟨3021314152978071472159831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028418870637428629546441 3021314152978071472159831)
            ·
              refine ⟨4531971229467107208239747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021314152978071472159831 4531971229467107208239747)
              ·
                refine ⟨6797956844200660812359621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531971229467107208239747 6797956844200660812359621)
                ·
                  refine ⟨1274616908287623902317429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6797956844200660812359621 1274616908287623902317429)
                  ·
                    refine ⟨119495335151964740842259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1274616908287623902317429 119495335151964740842259)
                    ·
                      rfl

theorem cell23_698149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_698149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698149 prefixEnd_698149 := by exact prefixLift 698149
  have htrace : WordTrace (prefixWord ++ tailWord_698149) baseStart_698149 baseEnd_698149 := by
    simpa [prefixWord, tailWord_698149, baseEnd_698149] using wordTrace_append hprefix tailTrace_698149
  have hstable : (prefixWord ++ tailWord_698149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698149).length < 2 ^ (prefixWord ++ tailWord_698149).sum := by decide
  have hdescent : baseEnd_698149 < baseStart_698149 := by decide
  rcases family_descends (prefixWord ++ tailWord_698149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698164 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_698164 : Nat := 118140960795 + 698164 * 2 ^ 59
def prefixEnd_698164 : Nat := 4983230072969 + 3 ^ 40 * 698164 * 2
def baseEnd_698164 : Nat := 358493707665711663839209

theorem tailTrace_698164 : CollatzResearch.WordTrace tailWord_698164 prefixEnd_698164 358493707665711663839209 := by
  unfold tailWord_698164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12732066521339269881686773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16976088695119026508915697 12732066521339269881686773)
  ·
    refine ⟨1193631236375556551408135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12732066521339269881686773 1193631236375556551408135)
    ·
      refine ⟨1790446854563334827112203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1193631236375556551408135 1790446854563334827112203)
      ·
        refine ⟨2685670281845002240668305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790446854563334827112203 2685670281845002240668305)
        ·
          refine ⟨2014252711383751680501229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685670281845002240668305 2014252711383751680501229)
          ·
            refine ⟨755344766768906880187961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2014252711383751680501229 755344766768906880187961)
            ·
              refine ⟨566508575076680160140971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755344766768906880187961 566508575076680160140971)
              ·
                refine ⟨849762862615020240211457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566508575076680160140971 849762862615020240211457)
                ·
                  refine ⟨637322146961265180158593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849762862615020240211457 637322146961265180158593)
                  ·
                    refine ⟨477991610220948885118945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637322146961265180158593 477991610220948885118945)
                    ·
                      refine ⟨358493707665711663839209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 477991610220948885118945 358493707665711663839209)
                      ·
                        rfl

theorem cell23_698164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_698164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698164 prefixEnd_698164 := by exact prefixLift 698164
  have htrace : WordTrace (prefixWord ++ tailWord_698164) baseStart_698164 baseEnd_698164 := by
    simpa [prefixWord, tailWord_698164, baseEnd_698164] using wordTrace_append hprefix tailTrace_698164
  have hstable : (prefixWord ++ tailWord_698164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698164).length < 2 ^ (prefixWord ++ tailWord_698164).sum := by decide
  have hdescent : baseEnd_698164 < baseStart_698164 := by decide
  rcases family_descends (prefixWord ++ tailWord_698164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698186 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_698186 : Nat := 118140960795 + 698186 * 2 ^ 59
def prefixEnd_698186 : Nat := 4983230072969 + 3 ^ 40 * 698186 * 2
def baseEnd_698186 : Nat := 358505004240110577764107

theorem tailTrace_698186 : CollatzResearch.WordTrace tailWord_698186 prefixEnd_698186 358505004240110577764107 := by
  unfold tailWord_698186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366233862149709380168603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16976623632399225013782941 6366233862149709380168603)
  ·
    refine ⟨9549350793224564070252905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6366233862149709380168603 9549350793224564070252905)
    ·
      refine ⟨7162013094918423052689679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9549350793224564070252905 7162013094918423052689679)
      ·
        refine ⟨10743019642377634579034519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7162013094918423052689679 10743019642377634579034519)
        ·
          refine ⟨16114529463566451868551779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10743019642377634579034519 16114529463566451868551779)
          ·
            refine ⟨24171794195349677802827669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16114529463566451868551779 24171794195349677802827669)
            ·
              refine ⟨1133052852907016147007547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24171794195349677802827669 1133052852907016147007547)
              ·
                refine ⟨1699579279360524220511321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133052852907016147007547 1699579279360524220511321)
                ·
                  refine ⟨1274684459520393165383491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1699579279360524220511321 1274684459520393165383491)
                  ·
                    refine ⟨1912026689280589748075237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274684459520393165383491 1912026689280589748075237)
                    ·
                      refine ⟨358505004240110577764107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1912026689280589748075237 358505004240110577764107)
                      ·
                        rfl

theorem cell23_698186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_698186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698186 prefixEnd_698186 := by exact prefixLift 698186
  have htrace : WordTrace (prefixWord ++ tailWord_698186) baseStart_698186 baseEnd_698186 := by
    simpa [prefixWord, tailWord_698186, baseEnd_698186] using wordTrace_append hprefix tailTrace_698186
  have hstable : (prefixWord ++ tailWord_698186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698186).length < 2 ^ (prefixWord ++ tailWord_698186).sum := by decide
  have hdescent : baseEnd_698186 < baseStart_698186 := by decide
  rcases family_descends (prefixWord ++ tailWord_698186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698219 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 3]
def baseStart_698219 : Nat := 118140960795 + 698219 * 2 ^ 59
def prefixEnd_698219 : Nat := 4983230072969 + 3 ^ 40 * 698219 * 2
def baseEnd_698219 : Nat := 358521949101708948651455

theorem tailTrace_698219 : CollatzResearch.WordTrace tailWord_698219 prefixEnd_698219 358521949101708948651455 := by
  unfold tailWord_698219
  simp only [CollatzResearch.WordTrace]
  refine ⟨25466139057479284156625711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16977426038319522771083807 25466139057479284156625711)
  ·
    refine ⟨38199208586218926234938567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25466139057479284156625711 38199208586218926234938567)
    ·
      refine ⟨57298812879328389352407851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38199208586218926234938567 57298812879328389352407851)
      ·
        refine ⟨85948219318992584028611777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57298812879328389352407851 85948219318992584028611777)
        ·
          refine ⟨64461164489244438021458833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85948219318992584028611777 64461164489244438021458833)
          ·
            refine ⟨48345873366933328516094125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64461164489244438021458833 48345873366933328516094125)
            ·
              refine ⟨18129702512599998193535297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48345873366933328516094125 18129702512599998193535297)
              ·
                refine ⟨13597276884449998645151473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18129702512599998193535297 13597276884449998645151473)
                ·
                  refine ⟨10197957663337498983863605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13597276884449998645151473 10197957663337498983863605)
                  ·
                    refine ⟨956058530937890529737213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10197957663337498983863605 956058530937890529737213)
                    ·
                      refine ⟨358521949101708948651455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 956058530937890529737213 358521949101708948651455)
                      ·
                        rfl

theorem cell23_698219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 3].length) (baseStart_698219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698219 prefixEnd_698219 := by exact prefixLift 698219
  have htrace : WordTrace (prefixWord ++ tailWord_698219) baseStart_698219 baseEnd_698219 := by
    simpa [prefixWord, tailWord_698219, baseEnd_698219] using wordTrace_append hprefix tailTrace_698219
  have hstable : (prefixWord ++ tailWord_698219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698219).length < 2 ^ (prefixWord ++ tailWord_698219).sum := by decide
  have hdescent : baseEnd_698219 < baseStart_698219 := by decide
  rcases family_descends (prefixWord ++ tailWord_698219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698230 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_698230 : Nat := 118140960795 + 698230 * 2 ^ 59
def prefixEnd_698230 : Nat := 4983230072969 + 3 ^ 40 * 698230 * 2
def baseEnd_698230 : Nat := 119509199129636135204635

theorem tailTrace_698230 : CollatzResearch.WordTrace tailWord_698230 prefixEnd_698230 119509199129636135204635 := by
  unfold tailWord_698230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591658766277464564704759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16977693506959622023517429 1591658766277464564704759)
  ·
    refine ⟨2387488149416196847057139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1591658766277464564704759 2387488149416196847057139)
    ·
      refine ⟨3581232224124295270585709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387488149416196847057139 3581232224124295270585709)
      ·
        refine ⟨1342962084046610726469641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3581232224124295270585709 1342962084046610726469641)
        ·
          refine ⟨1007221563034958044852231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342962084046610726469641 1007221563034958044852231)
          ·
            refine ⟨1510832344552437067278347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007221563034958044852231 1510832344552437067278347)
            ·
              refine ⟨2266248516828655600917521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510832344552437067278347 2266248516828655600917521)
              ·
                refine ⟨1699686387621491700688141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266248516828655600917521 1699686387621491700688141)
                ·
                  refine ⟨637382395358059387758053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1699686387621491700688141 637382395358059387758053)
                  ·
                    refine ⟨119509199129636135204635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637382395358059387758053 119509199129636135204635)
                    ·
                      rfl

theorem cell23_698230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_698230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698230 prefixEnd_698230 := by exact prefixLift 698230
  have htrace : WordTrace (prefixWord ++ tailWord_698230) baseStart_698230 baseEnd_698230 := by
    simpa [prefixWord, tailWord_698230, baseEnd_698230] using wordTrace_append hprefix tailTrace_698230
  have hstable : (prefixWord ++ tailWord_698230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698230).length < 2 ^ (prefixWord ++ tailWord_698230).sum := by decide
  have hdescent : baseEnd_698230 < baseStart_698230 := by decide
  rcases family_descends (prefixWord ++ tailWord_698230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698293 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_698293 : Nat := 118140960795 + 698293 * 2 ^ 59
def prefixEnd_698293 : Nat := 4983230072969 + 3 ^ 40 * 698293 * 2
def baseEnd_698293 : Nat := 358559946670141659126115

theorem tailTrace_698293 : CollatzResearch.WordTrace tailWord_698293 prefixEnd_698293 358559946670141659126115 := by
  unfold tailWord_698293
  simp only [CollatzResearch.WordTrace]
  refine ⟨25468838059211194794819533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16979225372807463196546355 25468838059211194794819533)
  ·
    refine ⟨9550814272204198048057325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25468838059211194794819533 9550814272204198048057325)
    ·
      refine ⟨3581555352076574268021497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9550814272204198048057325 3581555352076574268021497)
      ·
        refine ⟨2686166514057430701016123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3581555352076574268021497 2686166514057430701016123)
        ·
          refine ⟨4029249771086146051524185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686166514057430701016123 4029249771086146051524185)
          ·
            refine ⟨3021937328314609538643139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4029249771086146051524185 3021937328314609538643139)
            ·
              refine ⟨4532905992471914307964709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021937328314609538643139 4532905992471914307964709)
              ·
                refine ⟨849919873588483932743383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4532905992471914307964709 849919873588483932743383)
                ·
                  refine ⟨1274879810382725899115075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849919873588483932743383 1274879810382725899115075)
                  ·
                    refine ⟨1912319715574088848672613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274879810382725899115075 1912319715574088848672613)
                    ·
                      refine ⟨358559946670141659126115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1912319715574088848672613 358559946670141659126115)
                      ·
                        rfl

theorem cell23_698293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_698293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698293 prefixEnd_698293 := by exact prefixLift 698293
  have htrace : WordTrace (prefixWord ++ tailWord_698293) baseStart_698293 baseEnd_698293 := by
    simpa [prefixWord, tailWord_698293, baseEnd_698293] using wordTrace_append hprefix tailTrace_698293
  have hstable : (prefixWord ++ tailWord_698293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698293).length < 2 ^ (prefixWord ++ tailWord_698293).sum := by decide
  have hdescent : baseEnd_698293 < baseStart_698293 := by decide
  rcases family_descends (prefixWord ++ tailWord_698293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698316 : List Nat := [2, 2, 1, 4, 1, 4, 9]
def baseStart_698316 : Nat := 118140960795 + 698316 * 2 ^ 59
def prefixEnd_698316 : Nat := 4983230072969 + 3 ^ 40 * 698316 * 2
def baseEnd_698316 : Nat := 4426811811422161347389

theorem tailTrace_698316 : CollatzResearch.WordTrace tailWord_698316 prefixEnd_698316 4426811811422161347389 := by
  unfold tailWord_698316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734838469063934861453401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16979784625418579815271201 12734838469063934861453401)
  ·
    refine ⟨9551128851797951146090051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12734838469063934861453401 9551128851797951146090051)
    ·
      refine ⟨14326693277696926719135077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9551128851797951146090051 14326693277696926719135077)
      ·
        refine ⟨2686254989568173759837827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14326693277696926719135077 2686254989568173759837827)
        ·
          refine ⟨4029382484352260639756741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686254989568173759837827 4029382484352260639756741)
          ·
            refine ⟨755509215816048869954389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4029382484352260639756741 755509215816048869954389)
            ·
              refine ⟨4426811811422161347389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 755509215816048869954389 4426811811422161347389)
              ·
                rfl

theorem cell23_698316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 9].length) (baseStart_698316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698316 prefixEnd_698316 := by exact prefixLift 698316
  have htrace : WordTrace (prefixWord ++ tailWord_698316) baseStart_698316 baseEnd_698316 := by
    simpa [prefixWord, tailWord_698316, baseEnd_698316] using wordTrace_append hprefix tailTrace_698316
  have hstable : (prefixWord ++ tailWord_698316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698316).length < 2 ^ (prefixWord ++ tailWord_698316).sum := by decide
  have hdescent : baseEnd_698316 < baseStart_698316 := by decide
  rcases family_descends (prefixWord ++ tailWord_698316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698333 : List Nat := [1, 4, 3, 1, 3, 1, 2, 8]
def baseStart_698333 : Nat := 118140960795 + 698333 * 2 ^ 59
def prefixEnd_698333 : Nat := 4983230072969 + 3 ^ 40 * 698333 * 2
def baseEnd_698333 : Nat := 13280758736900796393553

theorem tailTrace_698333 : CollatzResearch.WordTrace tailWord_698333 prefixEnd_698333 13280758736900796393553 := by
  unfold tailWord_698333
  simp only [CollatzResearch.WordTrace]
  refine ⟨25470296979066281626275653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16980197986044187750850435 25470296979066281626275653)
  ·
    refine ⟨4775680683574927804926685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25470296979066281626275653 4775680683574927804926685)
    ·
      refine ⟨1790880256340597926847507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4775680683574927804926685 1790880256340597926847507)
      ·
        refine ⟨2686320384510896890271261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790880256340597926847507 2686320384510896890271261)
        ·
          refine ⟨1007370144191586333851723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2686320384510896890271261 1007370144191586333851723)
          ·
            refine ⟨1511055216287379500777585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007370144191586333851723 1511055216287379500777585)
            ·
              refine ⟨1133291412215534625583189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511055216287379500777585 1133291412215534625583189)
              ·
                refine ⟨13280758736900796393553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1133291412215534625583189 13280758736900796393553)
                ·
                  rfl

theorem cell23_698333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 8].length) (baseStart_698333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698333 prefixEnd_698333 := by exact prefixLift 698333
  have htrace : WordTrace (prefixWord ++ tailWord_698333) baseStart_698333 baseEnd_698333 := by
    simpa [prefixWord, tailWord_698333, baseEnd_698333] using wordTrace_append hprefix tailTrace_698333
  have hstable : (prefixWord ++ tailWord_698333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698333).length < 2 ^ (prefixWord ++ tailWord_698333).sum := by decide
  have hdescent : baseEnd_698333 < baseStart_698333 := by decide
  rcases family_descends (prefixWord ++ tailWord_698333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698376 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_698376 : Nat := 118140960795 + 698376 * 2 ^ 59
def prefixEnd_698376 : Nat := 4983230072969 + 3 ^ 40 * 698376 * 2
def baseEnd_698376 : Nat := 119534188521488278129411

theorem tailTrace_698376 : CollatzResearch.WordTrace tailWord_698376 prefixEnd_698376 119534188521488278129411 := by
  unfold tailWord_698376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12735932658955249985045491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16981243545273666646727321 12735932658955249985045491)
  ·
    refine ⟨19103898988432874977568237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12735932658955249985045491 19103898988432874977568237)
    ·
      refine ⟨7163962120662328116588089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19103898988432874977568237 7163962120662328116588089)
      ·
        refine ⟨5372971590496746087441067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163962120662328116588089 5372971590496746087441067)
        ·
          refine ⟨8059457385745119131161601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5372971590496746087441067 8059457385745119131161601)
          ·
            refine ⟨6044593039308839348371201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8059457385745119131161601 6044593039308839348371201)
            ·
              refine ⟨4533444779481629511278401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044593039308839348371201 4533444779481629511278401)
              ·
                refine ⟨3400083584611222133458801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533444779481629511278401 3400083584611222133458801)
                ·
                  refine ⟨2550062688458416600094101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3400083584611222133458801 2550062688458416600094101)
                  ·
                    refine ⟨119534188521488278129411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2550062688458416600094101 119534188521488278129411)
                    ·
                      rfl

theorem cell23_698376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_698376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698376 prefixEnd_698376 := by exact prefixLift 698376
  have htrace : WordTrace (prefixWord ++ tailWord_698376) baseStart_698376 baseEnd_698376 := by
    simpa [prefixWord, tailWord_698376, baseEnd_698376] using wordTrace_append hprefix tailTrace_698376
  have hstable : (prefixWord ++ tailWord_698376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698376).length < 2 ^ (prefixWord ++ tailWord_698376).sum := by decide
  have hdescent : baseEnd_698376 < baseStart_698376 := by decide
  rcases family_descends (prefixWord ++ tailWord_698376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698378 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_698378 : Nat := 118140960795 + 698378 * 2 ^ 59
def prefixEnd_698378 : Nat := 4983230072969 + 3 ^ 40 * 698378 * 2
def baseEnd_698378 : Nat := 358603592525773826563225

theorem tailTrace_698378 : CollatzResearch.WordTrace tailWord_698378 prefixEnd_698378 358603592525773826563225 := by
  unfold tailWord_698378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6367984565975813577915947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16981292175935502874442525 6367984565975813577915947)
  ·
    refine ⟨9551976848963720366873921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6367984565975813577915947 9551976848963720366873921)
    ·
      refine ⟨7163982636722790275155441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9551976848963720366873921 7163982636722790275155441)
      ·
        refine ⟨5372986977542092706366581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163982636722790275155441 5372986977542092706366581)
        ·
          refine ⟨503717529144571191221867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5372986977542092706366581 503717529144571191221867)
          ·
            refine ⟨755576293716856786832801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503717529144571191221867 755576293716856786832801)
            ·
              refine ⟨566682220287642590124601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755576293716856786832801 566682220287642590124601)
              ·
                refine ⟨425011665215731942593451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566682220287642590124601 425011665215731942593451)
                ·
                  refine ⟨637517497823597913890177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425011665215731942593451 637517497823597913890177)
                  ·
                    refine ⟨478138123367698435417633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637517497823597913890177 478138123367698435417633)
                    ·
                      refine ⟨358603592525773826563225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478138123367698435417633 358603592525773826563225)
                      ·
                        rfl

theorem cell23_698378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_698378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698378 prefixEnd_698378 := by exact prefixLift 698378
  have htrace : WordTrace (prefixWord ++ tailWord_698378) baseStart_698378 baseEnd_698378 := by
    simpa [prefixWord, tailWord_698378, baseEnd_698378] using wordTrace_append hprefix tailTrace_698378
  have hstable : (prefixWord ++ tailWord_698378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698378).length < 2 ^ (prefixWord ++ tailWord_698378).sum := by decide
  have hdescent : baseEnd_698378 < baseStart_698378 := by decide
  rcases family_descends (prefixWord ++ tailWord_698378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698423 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 5]
def baseStart_698423 : Nat := 118140960795 + 698423 * 2 ^ 59
def prefixEnd_698423 : Nat := 4983230072969 + 3 ^ 40 * 698423 * 2
def baseEnd_698423 : Nat := 39847411017247350055613

theorem tailTrace_698423 : CollatzResearch.WordTrace tailWord_698423 prefixEnd_698423 39847411017247350055613 := by
  unfold tailWord_698423
  simp only [CollatzResearch.WordTrace]
  refine ⟨25473579548740226997051923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16982386365826817998034615 25473579548740226997051923)
  ·
    refine ⟨38210369323110340495577885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25473579548740226997051923 38210369323110340495577885)
    ·
      refine ⟨14328888496166377685841707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38210369323110340495577885 14328888496166377685841707)
      ·
        refine ⟨21493332744249566528762561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14328888496166377685841707 21493332744249566528762561)
        ·
          refine ⟨16119999558187174896571921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21493332744249566528762561 16119999558187174896571921)
          ·
            refine ⟨12089999668640381172428941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16119999558187174896571921 12089999668640381172428941)
            ·
              refine ⟨4533749875740142939660853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12089999668640381172428941 4533749875740142939660853)
              ·
                refine ⟨425039050850638400593205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4533749875740142939660853 425039050850638400593205)
                ·
                  refine ⟨39847411017247350055613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 425039050850638400593205 39847411017247350055613)
                  ·
                    rfl

theorem cell23_698423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 5].length) (baseStart_698423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698423 prefixEnd_698423 := by exact prefixLift 698423
  have htrace : WordTrace (prefixWord ++ tailWord_698423) baseStart_698423 baseEnd_698423 := by
    simpa [prefixWord, tailWord_698423, baseEnd_698423] using wordTrace_append hprefix tailTrace_698423
  have hstable : (prefixWord ++ tailWord_698423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698423).length < 2 ^ (prefixWord ++ tailWord_698423).sum := by decide
  have hdescent : baseEnd_698423 < baseStart_698423 := by decide
  rcases family_descends (prefixWord ++ tailWord_698423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698473 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_698473 : Nat := 118140960795 + 698473 * 2 ^ 59
def prefixEnd_698473 : Nat := 4983230072969 + 3 ^ 40 * 698473 * 2
def baseEnd_698473 : Nat := 358652373187950954875287

theorem tailTrace_698473 : CollatzResearch.WordTrace tailWord_698473 prefixEnd_698473 358652373187950954875287 := by
  unfold tailWord_698473
  simp only [CollatzResearch.WordTrace]
  refine ⟨25475403198559085536372073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16983602132372723690914715 25475403198559085536372073)
  ·
    refine ⟨19106552398919314152279055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25475403198559085536372073 19106552398919314152279055)
    ·
      refine ⟨28659828598378971228418583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19106552398919314152279055 28659828598378971228418583)
      ·
        refine ⟨42989742897568456842627875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28659828598378971228418583 42989742897568456842627875)
        ·
          refine ⟨64484614346352685263941813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42989742897568456842627875 64484614346352685263941813)
          ·
            refine ⟨6045432594970564243494545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64484614346352685263941813 6045432594970564243494545)
            ·
              refine ⟨4534074446227923182620909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6045432594970564243494545 4534074446227923182620909)
              ·
                refine ⟨1700277917335471193482841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534074446227923182620909 1700277917335471193482841)
                ·
                  refine ⟨1275208438001603395112131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700277917335471193482841 1275208438001603395112131)
                  ·
                    refine ⟨1912812657002405092668197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1275208438001603395112131 1912812657002405092668197)
                    ·
                      refine ⟨358652373187950954875287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1912812657002405092668197 358652373187950954875287)
                      ·
                        rfl

theorem cell23_698473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_698473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698473 prefixEnd_698473 := by exact prefixLift 698473
  have htrace : WordTrace (prefixWord ++ tailWord_698473) baseStart_698473 baseEnd_698473 := by
    simpa [prefixWord, tailWord_698473, baseEnd_698473] using wordTrace_append hprefix tailTrace_698473
  have hstable : (prefixWord ++ tailWord_698473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698473).length < 2 ^ (prefixWord ++ tailWord_698473).sum := by decide
  have hdescent : baseEnd_698473 < baseStart_698473 := by decide
  rcases family_descends (prefixWord ++ tailWord_698473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698474 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_698474 : Nat := 118140960795 + 698474 * 2 ^ 59
def prefixEnd_698474 : Nat := 4983230072969 + 3 ^ 40 * 698474 * 2
def baseEnd_698474 : Nat := 39850320740956161218087

theorem tailTrace_698474 : CollatzResearch.WordTrace tailWord_698474 prefixEnd_698474 39850320740956161218087 := by
  unfold tailWord_698474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368859917888865676789619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16983626447703641804772317 6368859917888865676789619)
  ·
    refine ⟨9553289876833298515184429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6368859917888865676789619 9553289876833298515184429)
    ·
      refine ⟨3582483703812486943194161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9553289876833298515184429 3582483703812486943194161)
      ·
        refine ⟨2686862777859365207395621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3582483703812486943194161 2686862777859365207395621)
        ·
          refine ⟨503786770848630976386679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2686862777859365207395621 503786770848630976386679)
          ·
            refine ⟨755680156272946464580019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503786770848630976386679 755680156272946464580019)
            ·
              refine ⟨1133520234409419696870029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755680156272946464580019 1133520234409419696870029)
              ·
                refine ⟨425070087903532386326261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133520234409419696870029 425070087903532386326261)
                ·
                  refine ⟨39850320740956161218087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 425070087903532386326261 39850320740956161218087)
                  ·
                    rfl

theorem cell23_698474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_698474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698474 prefixEnd_698474 := by exact prefixLift 698474
  have htrace : WordTrace (prefixWord ++ tailWord_698474) baseStart_698474 baseEnd_698474 := by
    simpa [prefixWord, tailWord_698474, baseEnd_698474] using wordTrace_append hprefix tailTrace_698474
  have hstable : (prefixWord ++ tailWord_698474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698474).length < 2 ^ (prefixWord ++ tailWord_698474).sum := by decide
  have hdescent : baseEnd_698474 < baseStart_698474 := by decide
  rcases family_descends (prefixWord ++ tailWord_698474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698527 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_698527 : Nat := 118140960795 + 698527 * 2 ^ 59
def prefixEnd_698527 : Nat := 4983230072969 + 3 ^ 40 * 698527 * 2
def baseEnd_698527 : Nat := 358680101143293743600039

theorem tailTrace_698527 : CollatzResearch.WordTrace tailWord_698527 prefixEnd_698527 358680101143293743600039 := by
  unfold tailWord_698527
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477372740363452758837835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16984915160242301839225223 25477372740363452758837835)
  ·
    refine ⟨38216059110545179138256753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25477372740363452758837835 38216059110545179138256753)
    ·
      refine ⟨28662044332908884353692565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38216059110545179138256753 28662044332908884353692565)
      ·
        refine ⟨1343533328105103954079339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28662044332908884353692565 1343533328105103954079339)
        ·
          refine ⟨2015299992157655931119009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343533328105103954079339 2015299992157655931119009)
          ·
            refine ⟨1511474994118241948339257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2015299992157655931119009 1511474994118241948339257)
            ·
              refine ⟨1133606245588681461254443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511474994118241948339257 1133606245588681461254443)
              ·
                refine ⟨1700409368383022191881665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133606245588681461254443 1700409368383022191881665)
                ·
                  refine ⟨1275307026287266643911249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700409368383022191881665 1275307026287266643911249)
                  ·
                    refine ⟨956480269715449982933437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1275307026287266643911249 956480269715449982933437)
                    ·
                      refine ⟨358680101143293743600039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 956480269715449982933437 358680101143293743600039)
                      ·
                        rfl

theorem cell23_698527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_698527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698527 prefixEnd_698527 := by exact prefixLift 698527
  have htrace : WordTrace (prefixWord ++ tailWord_698527) baseStart_698527 baseEnd_698527 := by
    simpa [prefixWord, tailWord_698527, baseEnd_698527] using wordTrace_append hprefix tailTrace_698527
  have hstable : (prefixWord ++ tailWord_698527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698527).length < 2 ^ (prefixWord ++ tailWord_698527).sum := by decide
  have hdescent : baseEnd_698527 < baseStart_698527 := by decide
  rcases family_descends (prefixWord ++ tailWord_698527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698584 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 2, 3, 2]
def baseStart_698584 : Nat := 118140960795 + 698584 * 2 ^ 59
def prefixEnd_698584 : Nat := 4983230072969 + 3 ^ 40 * 698584 * 2
def baseEnd_698584 : Nat := 358709369540600020587277

theorem tailTrace_698584 : CollatzResearch.WordTrace tailWord_698584 prefixEnd_698584 358709369540600020587277 := by
  unfold tailWord_698584
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739725850578475746831403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16986301134104634329108537 12739725850578475746831403)
  ·
    refine ⟨19109588775867713620247105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12739725850578475746831403 19109588775867713620247105)
    ·
      refine ⟨14332191581900785215185329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19109588775867713620247105 14332191581900785215185329)
      ·
        refine ⟨10749143686425588911388997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14332191581900785215185329 10749143686425588911388997)
        ·
          refine ⟨2015464441204797920885437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10749143686425588911388997 2015464441204797920885437)
          ·
            refine ⟨755799165451799220332039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2015464441204797920885437 755799165451799220332039)
            ·
              refine ⟨1133698748177698830498059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755799165451799220332039 1133698748177698830498059)
              ·
                refine ⟨1700548122266548245747089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133698748177698830498059 1700548122266548245747089)
                ·
                  refine ⟨1275411091699911184310317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700548122266548245747089 1275411091699911184310317)
                  ·
                    refine ⟨478279159387466694116369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275411091699911184310317 478279159387466694116369)
                    ·
                      refine ⟨358709369540600020587277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478279159387466694116369 358709369540600020587277)
                      ·
                        rfl

theorem cell23_698584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_698584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698584 prefixEnd_698584 := by exact prefixLift 698584
  have htrace : WordTrace (prefixWord ++ tailWord_698584) baseStart_698584 baseEnd_698584 := by
    simpa [prefixWord, tailWord_698584, baseEnd_698584] using wordTrace_append hprefix tailTrace_698584
  have hstable : (prefixWord ++ tailWord_698584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698584).length < 2 ^ (prefixWord ++ tailWord_698584).sum := by decide
  have hdescent : baseEnd_698584 < baseStart_698584 := by decide
  rcases family_descends (prefixWord ++ tailWord_698584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698597 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_698597 : Nat := 118140960795 + 698597 * 2 ^ 59
def prefixEnd_698597 : Nat := 4983230072969 + 3 ^ 40 * 698597 * 2
def baseEnd_698597 : Nat := 358716044789108469724717

theorem tailTrace_698597 : CollatzResearch.WordTrace tailWord_698597 prefixEnd_698597 358716044789108469724717 := by
  unfold tailWord_698597
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479925850109854713886045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16986617233406569809257363 25479925850109854713886045)
  ·
    refine ⟨9554972193791195517707267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25479925850109854713886045 9554972193791195517707267)
    ·
      refine ⟨14332458290686793276560901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9554972193791195517707267 14332458290686793276560901)
      ·
        refine ⟨2687335929503773739355169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14332458290686793276560901 2687335929503773739355169)
        ·
          refine ⟨2015501947127830304516377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2687335929503773739355169 2015501947127830304516377)
          ·
            refine ⟨1511626460345872728387283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2015501947127830304516377 1511626460345872728387283)
            ·
              refine ⟨2267439690518809092580925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511626460345872728387283 2267439690518809092580925)
              ·
                refine ⟨850289883944553409717847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2267439690518809092580925 850289883944553409717847)
                ·
                  refine ⟨1275434825916830114576771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850289883944553409717847 1275434825916830114576771)
                  ·
                    refine ⟨1913152238875245171865157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1275434825916830114576771 1913152238875245171865157)
                    ·
                      refine ⟨358716044789108469724717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1913152238875245171865157 358716044789108469724717)
                      ·
                        rfl

theorem cell23_698597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_698597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698597 prefixEnd_698597 := by exact prefixLift 698597
  have htrace : WordTrace (prefixWord ++ tailWord_698597) baseStart_698597 baseEnd_698597 := by
    simpa [prefixWord, tailWord_698597, baseEnd_698597] using wordTrace_append hprefix tailTrace_698597
  have hstable : (prefixWord ++ tailWord_698597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698597).length < 2 ^ (prefixWord ++ tailWord_698597).sum := by decide
  have hdescent : baseEnd_698597 < baseStart_698597 := by decide
  rcases family_descends (prefixWord ++ tailWord_698597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698607 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 2, 4]
def baseStart_698607 : Nat := 118140960795 + 698607 * 2 ^ 59
def prefixEnd_698607 : Nat := 4983230072969 + 3 ^ 40 * 698607 * 2
def baseEnd_698607 : Nat := 119573726531884476866557

theorem tailTrace_698607 : CollatzResearch.WordTrace tailWord_698607 prefixEnd_698607 119573726531884476866557 := by
  unfold tailWord_698607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25480290580073626421750075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16986860386715750947833383 25480290580073626421750075)
  ·
    refine ⟨38220435870110439632625113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25480290580073626421750075 38220435870110439632625113)
    ·
      refine ⟨28665326902582829724468835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38220435870110439632625113 28665326902582829724468835)
      ·
        refine ⟨42997990353874244586703253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28665326902582829724468835 42997990353874244586703253)
        ·
          refine ⟨2015530797837855215001715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42997990353874244586703253 2015530797837855215001715)
          ·
            refine ⟨3023296196756782822502573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015530797837855215001715 3023296196756782822502573)
            ·
              refine ⟨1133736073783793558438465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3023296196756782822502573 1133736073783793558438465)
              ·
                refine ⟨850302055337845168828849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133736073783793558438465 850302055337845168828849)
                ·
                  refine ⟨637726541503383876621637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850302055337845168828849 637726541503383876621637)
                  ·
                    refine ⟨119573726531884476866557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637726541503383876621637 119573726531884476866557)
                    ·
                      rfl

theorem cell23_698607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_698607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698607 prefixEnd_698607 := by exact prefixLift 698607
  have htrace : WordTrace (prefixWord ++ tailWord_698607) baseStart_698607 baseEnd_698607 := by
    simpa [prefixWord, tailWord_698607, baseEnd_698607] using wordTrace_append hprefix tailTrace_698607
  have hstable : (prefixWord ++ tailWord_698607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698607).length < 2 ^ (prefixWord ++ tailWord_698607).sum := by decide
  have hdescent : baseEnd_698607 < baseStart_698607 := by decide
  rcases family_descends (prefixWord ++ tailWord_698607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698614 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_698614 : Nat := 118140960795 + 698614 * 2 ^ 59
def prefixEnd_698614 : Nat := 4983230072969 + 3 ^ 40 * 698614 * 2
def baseEnd_698614 : Nat := 358724773960234903212139

theorem tailTrace_698614 : CollatzResearch.WordTrace tailWord_698614 prefixEnd_698614 358724773960234903212139 := by
  unfold tailWord_698614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1592534118190516663578431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16987030594032177744836597 1592534118190516663578431)
  ·
    refine ⟨2388801177285774995367647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1592534118190516663578431 2388801177285774995367647)
    ·
      refine ⟨3583201765928662493051471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388801177285774995367647 3583201765928662493051471)
      ·
        refine ⟨5374802648892993739577207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583201765928662493051471 5374802648892993739577207)
        ·
          refine ⟨8062203973339490609365811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374802648892993739577207 8062203973339490609365811)
          ·
            refine ⟨12093305960009235914048717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062203973339490609365811 12093305960009235914048717)
            ·
              refine ⟨4534989735003463467768269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12093305960009235914048717 4534989735003463467768269)
              ·
                refine ⟨1700621150626298800413101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534989735003463467768269 1700621150626298800413101)
                ·
                  refine ⟨637732931484862050154913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1700621150626298800413101 637732931484862050154913)
                  ·
                    refine ⟨478299698613646537616185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637732931484862050154913 478299698613646537616185)
                    ·
                      refine ⟨358724773960234903212139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478299698613646537616185 358724773960234903212139)
                      ·
                        rfl

theorem cell23_698614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_698614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698614 prefixEnd_698614 := by exact prefixLift 698614
  have htrace : WordTrace (prefixWord ++ tailWord_698614) baseStart_698614 baseEnd_698614 := by
    simpa [prefixWord, tailWord_698614, baseEnd_698614] using wordTrace_append hprefix tailTrace_698614
  have hstable : (prefixWord ++ tailWord_698614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698614).length < 2 ^ (prefixWord ++ tailWord_698614).sum := by decide
  have hdescent : baseEnd_698614 < baseStart_698614 := by decide
  rcases family_descends (prefixWord ++ tailWord_698614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698647 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_698647 : Nat := 118140960795 + 698647 * 2 ^ 59
def prefixEnd_698647 : Nat := 4983230072969 + 3 ^ 40 * 698647 * 2
def baseEnd_698647 : Nat := 358741718821833274099487

theorem tailTrace_698647 : CollatzResearch.WordTrace tailWord_698647 prefixEnd_698647 358741718821833274099487 := by
  unfold tailWord_698647
  simp only [CollatzResearch.WordTrace]
  refine ⟨25481749499928713253206195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16987832999952475502137463 25481749499928713253206195)
  ·
    refine ⟨38222624249893069879809293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25481749499928713253206195 38222624249893069879809293)
    ·
      refine ⟨14333484093709901204928485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38222624249893069879809293 14333484093709901204928485)
      ·
        refine ⟨2687528267570606475924091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14333484093709901204928485 2687528267570606475924091)
        ·
          refine ⟨4031292401355909713886137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687528267570606475924091 4031292401355909713886137)
          ·
            refine ⟨3023469301016932285414603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4031292401355909713886137 3023469301016932285414603)
            ·
              refine ⟨4535203951525398428121905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023469301016932285414603 4535203951525398428121905)
              ·
                refine ⟨3401402963644048821091429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4535203951525398428121905 3401402963644048821091429)
                ·
                  refine ⟨637763055683259153954643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3401402963644048821091429 637763055683259153954643)
                  ·
                    refine ⟨956644583524888730931965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 637763055683259153954643 956644583524888730931965)
                    ·
                      refine ⟨358741718821833274099487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 956644583524888730931965 358741718821833274099487)
                      ·
                        rfl

theorem cell23_698647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_698647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698647 prefixEnd_698647 := by exact prefixLift 698647
  have htrace : WordTrace (prefixWord ++ tailWord_698647) baseStart_698647 baseEnd_698647 := by
    simpa [prefixWord, tailWord_698647, baseEnd_698647] using wordTrace_append hprefix tailTrace_698647
  have hstable : (prefixWord ++ tailWord_698647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698647).length < 2 ^ (prefixWord ++ tailWord_698647).sum := by decide
  have hdescent : baseEnd_698647 < baseStart_698647 := by decide
  rcases family_descends (prefixWord ++ tailWord_698647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698681 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 2, 1, 3]
def baseStart_698681 : Nat := 118140960795 + 698681 * 2 ^ 59
def prefixEnd_698681 : Nat := 4983230072969 + 3 ^ 40 * 698681 * 2
def baseEnd_698681 : Nat := 358759177164086141074331

theorem tailTrace_698681 : CollatzResearch.WordTrace tailWord_698681 prefixEnd_698681 358759177164086141074331 := by
  unfold tailWord_698681
  simp only [CollatzResearch.WordTrace]
  refine ⟨25482989581805537059943897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16988659721203691373295931 25482989581805537059943897)
  ·
    refine ⟨19112242186354152794957923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25482989581805537059943897 19112242186354152794957923)
    ·
      refine ⟨28668363279531229192436885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19112242186354152794957923 28668363279531229192436885)
      ·
        refine ⟨1343829528728026368395479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28668363279531229192436885 1343829528728026368395479)
        ·
          refine ⟨2015744293092039552593219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343829528728026368395479 2015744293092039552593219)
          ·
            refine ⟨3023616439638059328889829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015744293092039552593219 3023616439638059328889829)
            ·
              refine ⟨566928082432136124166843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3023616439638059328889829 566928082432136124166843)
              ·
                refine ⟨850392123648204186250265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566928082432136124166843 850392123648204186250265)
                ·
                  refine ⟨637794092736153139687699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850392123648204186250265 637794092736153139687699)
                  ·
                    refine ⟨956691139104229709531549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 637794092736153139687699 956691139104229709531549)
                    ·
                      refine ⟨358759177164086141074331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 956691139104229709531549 358759177164086141074331)
                      ·
                        rfl

theorem cell23_698681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_698681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698681 prefixEnd_698681 := by exact prefixLift 698681
  have htrace : WordTrace (prefixWord ++ tailWord_698681) baseStart_698681 baseEnd_698681 := by
    simpa [prefixWord, tailWord_698681, baseEnd_698681] using wordTrace_append hprefix tailTrace_698681
  have hstable : (prefixWord ++ tailWord_698681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698681).length < 2 ^ (prefixWord ++ tailWord_698681).sum := by decide
  have hdescent : baseEnd_698681 < baseStart_698681 := by decide
  rcases family_descends (prefixWord ++ tailWord_698681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698687 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 1, 4, 2]
def baseStart_698687 : Nat := 118140960795 + 698687 * 2 ^ 59
def prefixEnd_698687 : Nat := 4983230072969 + 3 ^ 40 * 698687 * 2
def baseEnd_698687 : Nat := 358762258048013117599303

theorem tailTrace_698687 : CollatzResearch.WordTrace tailWord_698687 prefixEnd_698687 358762258048013117599303 := by
  unfold tailWord_698687
  simp only [CollatzResearch.WordTrace]
  refine ⟨25483208419783800084662315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16988805613189200056441543 25483208419783800084662315)
  ·
    refine ⟨38224812629675700126993473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25483208419783800084662315 38224812629675700126993473)
    ·
      refine ⟨28668609472256775095245105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38224812629675700126993473 28668609472256775095245105)
      ·
        refine ⟨21501457104192581321433829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28668609472256775095245105 21501457104192581321433829)
        ·
          refine ⟨4031523207036108997768843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21501457104192581321433829 4031523207036108997768843)
          ·
            refine ⟨6047284810554163496653265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031523207036108997768843 6047284810554163496653265)
            ·
              refine ⟨4535463607915622622489949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6047284810554163496653265 4535463607915622622489949)
              ·
                refine ⟨1700798852968358483433731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4535463607915622622489949 1700798852968358483433731)
                ·
                  refine ⟨2551198279452537725150597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700798852968358483433731 2551198279452537725150597)
                  ·
                    refine ⟨478349677397350823465737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551198279452537725150597 478349677397350823465737)
                    ·
                      refine ⟨358762258048013117599303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478349677397350823465737 358762258048013117599303)
                      ·
                        rfl

theorem cell23_698687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_698687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698687 prefixEnd_698687 := by exact prefixLift 698687
  have htrace : WordTrace (prefixWord ++ tailWord_698687) baseStart_698687 baseEnd_698687 := by
    simpa [prefixWord, tailWord_698687, baseEnd_698687] using wordTrace_append hprefix tailTrace_698687
  have hstable : (prefixWord ++ tailWord_698687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698687).length < 2 ^ (prefixWord ++ tailWord_698687).sum := by decide
  have hdescent : baseEnd_698687 < baseStart_698687 := by decide
  rcases family_descends (prefixWord ++ tailWord_698687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698703 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_698703 : Nat := 118140960795 + 698703 * 2 ^ 59
def prefixEnd_698703 : Nat := 4983230072969 + 3 ^ 40 * 698703 * 2
def baseEnd_698703 : Nat := 358770473738485054999229

theorem tailTrace_698703 : CollatzResearch.WordTrace tailWord_698703 prefixEnd_698703 358770473738485054999229 := by
  unfold tailWord_698703
  simp only [CollatzResearch.WordTrace]
  refine ⟨25483791987725834817244763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16989194658483889878163175 25483791987725834817244763)
  ·
    refine ⟨38225687981588752225867145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25483791987725834817244763 38225687981588752225867145)
    ·
      refine ⟨28669265986191564169400359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38225687981588752225867145 28669265986191564169400359)
      ·
        refine ⟨43003898979287346254100539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28669265986191564169400359 43003898979287346254100539)
        ·
          refine ⟨64505848468931019381150809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43003898979287346254100539 64505848468931019381150809)
          ·
            refine ⟨48379386351698264535863107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64505848468931019381150809 48379386351698264535863107)
            ·
              refine ⟨72569079527547396803794661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48379386351698264535863107 72569079527547396803794661)
              ·
                refine ⟨13606702411415136900711499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72569079527547396803794661 13606702411415136900711499)
                ·
                  refine ⟨20410053617122705351067249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13606702411415136900711499 20410053617122705351067249)
                  ·
                    refine ⟨15307540212842029013300437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20410053617122705351067249 15307540212842029013300437)
                    ·
                      refine ⟨358770473738485054999229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15307540212842029013300437 358770473738485054999229)
                      ·
                        rfl

theorem cell23_698703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_698703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698703 prefixEnd_698703 := by exact prefixLift 698703
  have htrace : WordTrace (prefixWord ++ tailWord_698703) baseStart_698703 baseEnd_698703 := by
    simpa [prefixWord, tailWord_698703, baseEnd_698703] using wordTrace_append hprefix tailTrace_698703
  have hstable : (prefixWord ++ tailWord_698703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698703).length < 2 ^ (prefixWord ++ tailWord_698703).sum := by decide
  have hdescent : baseEnd_698703 < baseStart_698703 := by decide
  rcases family_descends (prefixWord ++ tailWord_698703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698777 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 4, 4, 2]
def baseStart_698777 : Nat := 118140960795 + 698777 * 2 ^ 59
def prefixEnd_698777 : Nat := 4983230072969 + 3 ^ 40 * 698777 * 2
def baseEnd_698777 : Nat := 358808471306917765473889

theorem tailTrace_698777 : CollatzResearch.WordTrace tailWord_698777 prefixEnd_698777 358808471306917765473889 := by
  unfold tailWord_698777
  simp only [CollatzResearch.WordTrace]
  refine ⟨25486490989457745455438585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16990993992971830303625723 25486490989457745455438585)
  ·
    refine ⟨19114868242093309091578939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25486490989457745455438585 19114868242093309091578939)
    ·
      refine ⟨28672302363139963637368409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19114868242093309091578939 28672302363139963637368409)
      ·
        refine ⟨21504226772354972728026307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28672302363139963637368409 21504226772354972728026307)
        ·
          refine ⟨32256340158532459092039461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21504226772354972728026307 32256340158532459092039461)
          ·
            refine ⟨6048063779724836079757399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32256340158532459092039461 6048063779724836079757399)
            ·
              refine ⟨9072095669587254119636099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048063779724836079757399 9072095669587254119636099)
              ·
                refine ⟨13608143504380881179454149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9072095669587254119636099 13608143504380881179454149)
                ·
                  refine ⟨2551526907071415221147653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13608143504380881179454149 2551526907071415221147653)
                  ·
                    refine ⟨478411295075890353965185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551526907071415221147653 478411295075890353965185)
                    ·
                      refine ⟨358808471306917765473889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478411295075890353965185 358808471306917765473889)
                      ·
                        rfl

theorem cell23_698777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_698777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698777 prefixEnd_698777 := by exact prefixLift 698777
  have htrace : WordTrace (prefixWord ++ tailWord_698777) baseStart_698777 baseEnd_698777 := by
    simpa [prefixWord, tailWord_698777, baseEnd_698777] using wordTrace_append hprefix tailTrace_698777
  have hstable : (prefixWord ++ tailWord_698777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698777).length < 2 ^ (prefixWord ++ tailWord_698777).sum := by decide
  have hdescent : baseEnd_698777 < baseStart_698777 := by decide
  rcases family_descends (prefixWord ++ tailWord_698777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698787 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 3, 4]
def baseStart_698787 : Nat := 118140960795 + 698787 * 2 ^ 59
def prefixEnd_698787 : Nat := 4983230072969 + 3 ^ 40 * 698787 * 2
def baseEnd_698787 : Nat := 119604535371154242116281

theorem tailTrace_698787 : CollatzResearch.WordTrace tailWord_698787 prefixEnd_698787 119604535371154242116281 := by
  unfold tailWord_698787
  simp only [CollatzResearch.WordTrace]
  refine ⟨25486855719421517163302615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16991237146281011442201743 25486855719421517163302615)
  ·
    refine ⟨38230283579132275744953923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25486855719421517163302615 38230283579132275744953923)
    ·
      refine ⟨57345425368698413617430885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38230283579132275744953923 57345425368698413617430885)
      ·
        refine ⟨10752267256630952553268291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57345425368698413617430885 10752267256630952553268291)
        ·
          refine ⟨16128400884946428829902437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10752267256630952553268291 16128400884946428829902437)
          ·
            refine ⟨3024075165927455405606707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16128400884946428829902437 3024075165927455405606707)
            ·
              refine ⟨4536112748891183108410061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024075165927455405606707 4536112748891183108410061)
              ·
                refine ⟨1701042280834193665653773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4536112748891183108410061 1701042280834193665653773)
                ·
                  refine ⟨637890855312822624620165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1701042280834193665653773 637890855312822624620165)
                  ·
                    refine ⟨119604535371154242116281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637890855312822624620165 119604535371154242116281)
                    ·
                      rfl

theorem cell23_698787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 4].length) (baseStart_698787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698787 prefixEnd_698787 := by exact prefixLift 698787
  have htrace : WordTrace (prefixWord ++ tailWord_698787) baseStart_698787 baseEnd_698787 := by
    simpa [prefixWord, tailWord_698787, baseEnd_698787] using wordTrace_append hprefix tailTrace_698787
  have hstable : (prefixWord ++ tailWord_698787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698787).length < 2 ^ (prefixWord ++ tailWord_698787).sum := by decide
  have hdescent : baseEnd_698787 < baseStart_698787 := by decide
  rcases family_descends (prefixWord ++ tailWord_698787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698840 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_698840 : Nat := 118140960795 + 698840 * 2 ^ 59
def prefixEnd_698840 : Nat := 4983230072969 + 3 ^ 40 * 698840 * 2
def baseEnd_698840 : Nat := 358840820588151018986099

theorem tailTrace_698840 : CollatzResearch.WordTrace tailWord_698840 prefixEnd_698840 358840820588151018986099 := by
  unfold tailWord_698840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12744394394114753607490987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16992525858819671476654649 12744394394114753607490987)
  ·
    refine ⟨19116591591172130411236481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12744394394114753607490987 19116591591172130411236481)
    ·
      refine ⟨14337443693379097808427361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19116591591172130411236481 14337443693379097808427361)
      ·
        refine ⟨10753082770034323356320521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14337443693379097808427361 10753082770034323356320521)
        ·
          refine ⟨8064812077525742517240391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10753082770034323356320521 8064812077525742517240391)
          ·
            refine ⟨12097218116288613775860587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064812077525742517240391 12097218116288613775860587)
            ·
              refine ⟨18145827174432920663790881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12097218116288613775860587 18145827174432920663790881)
              ·
                refine ⟨13609370380824690497843161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18145827174432920663790881 13609370380824690497843161)
                ·
                  refine ⟨10207027785618517873382371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13609370380824690497843161 10207027785618517873382371)
                  ·
                    refine ⟨15310541678427776810073557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10207027785618517873382371 15310541678427776810073557)
                    ·
                      refine ⟨358840820588151018986099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15310541678427776810073557 358840820588151018986099)
                      ·
                        rfl

theorem cell23_698840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_698840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698840 prefixEnd_698840 := by exact prefixLift 698840
  have htrace : WordTrace (prefixWord ++ tailWord_698840) baseStart_698840 baseEnd_698840 := by
    simpa [prefixWord, tailWord_698840, baseEnd_698840] using wordTrace_append hprefix tailTrace_698840
  have hstable : (prefixWord ++ tailWord_698840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698840).length < 2 ^ (prefixWord ++ tailWord_698840).sum := by decide
  have hdescent : baseEnd_698840 < baseStart_698840 := by decide
  rcases family_descends (prefixWord ++ tailWord_698840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698851 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 6]
def baseStart_698851 : Nat := 118140960795 + 698851 * 2 ^ 59
def prefixEnd_698851 : Nat := 4983230072969 + 3 ^ 40 * 698851 * 2
def baseEnd_698851 : Nat := 39871829875038941772061

theorem tailTrace_698851 : CollatzResearch.WordTrace tailWord_698851 prefixEnd_698851 39871829875038941772061 := by
  unfold tailWord_698851
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489189991189656093632407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16992793327459770729088271 25489189991189656093632407)
  ·
    refine ⟨38233784986784484140448611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25489189991189656093632407 38233784986784484140448611)
    ·
      refine ⟨57350677480176726210672917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38233784986784484140448611 57350677480176726210672917)
      ·
        refine ⟨2688313006883284041125293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57350677480176726210672917 2688313006883284041125293)
        ·
          refine ⟨1008117377581231515421985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2688313006883284041125293 1008117377581231515421985)
          ·
            refine ⟨756088033185923636566489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1008117377581231515421985 756088033185923636566489)
            ·
              refine ⟨567066024889442727424867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756088033185923636566489 567066024889442727424867)
              ·
                refine ⟨850599037334164091137301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567066024889442727424867 850599037334164091137301)
                ·
                  refine ⟨39871829875038941772061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 850599037334164091137301 39871829875038941772061)
                  ·
                    rfl

theorem cell23_698851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 6].length) (baseStart_698851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698851 prefixEnd_698851 := by exact prefixLift 698851
  have htrace : WordTrace (prefixWord ++ tailWord_698851) baseStart_698851 baseEnd_698851 := by
    simpa [prefixWord, tailWord_698851, baseEnd_698851] using wordTrace_append hprefix tailTrace_698851
  have hstable : (prefixWord ++ tailWord_698851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698851).length < 2 ^ (prefixWord ++ tailWord_698851).sum := by decide
  have hdescent : baseEnd_698851 < baseStart_698851 := by decide
  rcases family_descends (prefixWord ++ tailWord_698851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698867 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 4]
def baseStart_698867 : Nat := 118140960795 + 698867 * 2 ^ 59
def prefixEnd_698867 : Nat := 4983230072969 + 3 ^ 40 * 698867 * 2
def baseEnd_698867 : Nat := 358854684565822413348475

theorem tailTrace_698867 : CollatzResearch.WordTrace tailWord_698867 prefixEnd_698867 358854684565822413348475 := by
  unfold tailWord_698867
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489773559131690826214855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16993182372754460550809903 25489773559131690826214855)
  ·
    refine ⟨38234660338697536239322283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25489773559131690826214855 38234660338697536239322283)
    ·
      refine ⟨57351990508046304358983425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38234660338697536239322283 57351990508046304358983425)
      ·
        refine ⟨43013992881034728269237569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57351990508046304358983425 43013992881034728269237569)
        ·
          refine ⟨32260494660776046201928177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43013992881034728269237569 32260494660776046201928177)
          ·
            refine ⟨24195370995582034651446133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32260494660776046201928177 24195370995582034651446133)
            ·
              refine ⟨2268316030835815748573075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24195370995582034651446133 2268316030835815748573075)
              ·
                refine ⟨3402474046253723622859613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268316030835815748573075 3402474046253723622859613)
                ·
                  refine ⟨1275927767345146358572355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3402474046253723622859613 1275927767345146358572355)
                  ·
                    refine ⟨1913891651017719537858533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1275927767345146358572355 1913891651017719537858533)
                    ·
                      refine ⟨358854684565822413348475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1913891651017719537858533 358854684565822413348475)
                      ·
                        rfl

theorem cell23_698867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_698867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698867 prefixEnd_698867 := by exact prefixLift 698867
  have htrace : WordTrace (prefixWord ++ tailWord_698867) baseStart_698867 baseEnd_698867 := by
    simpa [prefixWord, tailWord_698867, baseEnd_698867] using wordTrace_append hprefix tailTrace_698867
  have hstable : (prefixWord ++ tailWord_698867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698867).length < 2 ^ (prefixWord ++ tailWord_698867).sum := by decide
  have hdescent : baseEnd_698867 < baseStart_698867 := by decide
  rcases family_descends (prefixWord ++ tailWord_698867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698877 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_698877 : Nat := 118140960795 + 698877 * 2 ^ 59
def prefixEnd_698877 : Nat := 4983230072969 + 3 ^ 40 * 698877 * 2
def baseEnd_698877 : Nat := 119619939790789124741143

theorem tailTrace_698877 : CollatzResearch.WordTrace tailWord_698877 prefixEnd_698877 119619939790789124741143 := by
  unfold tailWord_698877
  simp only [CollatzResearch.WordTrace]
  refine ⟨25490138289095462534078885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16993425526063641689385923 25490138289095462534078885)
  ·
    refine ⟨4779400929205399225139791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25490138289095462534078885 4779400929205399225139791)
    ·
      refine ⟨7169101393808098837709687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779400929205399225139791 7169101393808098837709687)
      ·
        refine ⟨10753652090712148256564531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169101393808098837709687 10753652090712148256564531)
        ·
          refine ⟨16130478136068222384846797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10753652090712148256564531 16130478136068222384846797)
          ·
            refine ⟨6048929301025583394317549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16130478136068222384846797 6048929301025583394317549)
            ·
              refine ⟨2268348487884593772869081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6048929301025583394317549 2268348487884593772869081)
              ·
                refine ⟨1701261365913445329651811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268348487884593772869081 1701261365913445329651811)
                ·
                  refine ⟨2551892048870167994477717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701261365913445329651811 2551892048870167994477717)
                  ·
                    refine ⟨119619939790789124741143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2551892048870167994477717 119619939790789124741143)
                    ·
                      rfl

theorem cell23_698877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_698877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698877 prefixEnd_698877 := by exact prefixLift 698877
  have htrace : WordTrace (prefixWord ++ tailWord_698877) baseStart_698877 baseEnd_698877 := by
    simpa [prefixWord, tailWord_698877, baseEnd_698877] using wordTrace_append hprefix tailTrace_698877
  have hstable : (prefixWord ++ tailWord_698877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698877).length < 2 ^ (prefixWord ++ tailWord_698877).sum := by decide
  have hdescent : baseEnd_698877 < baseStart_698877 := by decide
  rcases family_descends (prefixWord ++ tailWord_698877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698880 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_698880 : Nat := 118140960795 + 698880 * 2 ^ 59
def prefixEnd_698880 : Nat := 4983230072969 + 3 ^ 40 * 698880 * 2
def baseEnd_698880 : Nat := 358861359814330862485915

theorem tailTrace_698880 : CollatzResearch.WordTrace tailWord_698880 prefixEnd_698880 358861359814330862485915 := by
  unfold tailWord_698880
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745123854042297023219047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16993498472056396030958729 12745123854042297023219047)
  ·
    refine ⟨19117685781063445534828571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12745123854042297023219047 19117685781063445534828571)
    ·
      refine ⟨28676528671595168302242857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19117685781063445534828571 28676528671595168302242857)
      ·
        refine ⟨21507396503696376226682143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28676528671595168302242857 21507396503696376226682143)
        ·
          refine ⟨32261094755544564340023215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21507396503696376226682143 32261094755544564340023215)
          ·
            refine ⟨48391642133316846510034823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32261094755544564340023215 48391642133316846510034823)
            ·
              refine ⟨72587463199975269765052235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48391642133316846510034823 72587463199975269765052235)
              ·
                refine ⟨108881194799962904647578353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72587463199975269765052235 108881194799962904647578353)
                ·
                  refine ⟨81660896099972178485683765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108881194799962904647578353 81660896099972178485683765)
                  ·
                    refine ⟨7655709009372391733032853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81660896099972178485683765 7655709009372391733032853)
                    ·
                      refine ⟨358861359814330862485915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7655709009372391733032853 358861359814330862485915)
                      ·
                        rfl

theorem cell23_698880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_698880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698880 prefixEnd_698880 := by exact prefixLift 698880
  have htrace : WordTrace (prefixWord ++ tailWord_698880) baseStart_698880 baseEnd_698880 := by
    simpa [prefixWord, tailWord_698880, baseEnd_698880] using wordTrace_append hprefix tailTrace_698880
  have hstable : (prefixWord ++ tailWord_698880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698880).length < 2 ^ (prefixWord ++ tailWord_698880).sum := by decide
  have hdescent : baseEnd_698880 < baseStart_698880 := by decide
  rcases family_descends (prefixWord ++ tailWord_698880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698881 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 1, 5]
def baseStart_698881 : Nat := 118140960795 + 698881 * 2 ^ 59
def prefixEnd_698881 : Nat := 4983230072969 + 3 ^ 40 * 698881 * 2
def baseEnd_698881 : Nat := 119620624431661786191137

theorem tailTrace_698881 : CollatzResearch.WordTrace tailWord_698881 prefixEnd_698881 119620624431661786191137 := by
  unfold tailWord_698881
  simp only [CollatzResearch.WordTrace]
  refine ⟨25490284181080971217224497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16993522787387314144816331 25490284181080971217224497)
  ·
    refine ⟨19117713135810728412918373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25490284181080971217224497 19117713135810728412918373)
    ·
      refine ⟨3584571212964511577422195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19117713135810728412918373 3584571212964511577422195)
      ·
        refine ⟨5376856819446767366133293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584571212964511577422195 5376856819446767366133293)
        ·
          refine ⟨2016321307292537762299985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5376856819446767366133293 2016321307292537762299985)
          ·
            refine ⟨1512240980469403321724989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016321307292537762299985 1512240980469403321724989)
            ·
              refine ⟨567090367676026245646871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1512240980469403321724989 567090367676026245646871)
              ·
                refine ⟨850635551514039368470307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567090367676026245646871 850635551514039368470307)
                ·
                  refine ⟨1275953327271059052705461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850635551514039368470307 1275953327271059052705461)
                  ·
                    refine ⟨119620624431661786191137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1275953327271059052705461 119620624431661786191137)
                    ·
                      rfl

theorem cell23_698881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_698881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698881 prefixEnd_698881 := by exact prefixLift 698881
  have htrace : WordTrace (prefixWord ++ tailWord_698881) baseStart_698881 baseEnd_698881 := by
    simpa [prefixWord, tailWord_698881, baseEnd_698881] using wordTrace_append hprefix tailTrace_698881
  have hstable : (prefixWord ++ tailWord_698881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698881).length < 2 ^ (prefixWord ++ tailWord_698881).sum := by decide
  have hdescent : baseEnd_698881 < baseStart_698881 := by decide
  rcases family_descends (prefixWord ++ tailWord_698881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698901 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_698901 : Nat := 118140960795 + 698901 * 2 ^ 59
def prefixEnd_698901 : Nat := 4983230072969 + 3 ^ 40 * 698901 * 2
def baseEnd_698901 : Nat := 358872142908075280323319

theorem tailTrace_698901 : CollatzResearch.WordTrace tailWord_698901 prefixEnd_698901 358872142908075280323319 := by
  unfold tailWord_698901
  simp only [CollatzResearch.WordTrace]
  refine ⟨25491013641008514632952557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16994009094005676421968371 25491013641008514632952557)
  ·
    refine ⟨9559130115378192987357209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25491013641008514632952557 9559130115378192987357209)
    ·
      refine ⟨7169347586533644740517907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9559130115378192987357209 7169347586533644740517907)
      ·
        refine ⟨10754021379800467110776861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169347586533644740517907 10754021379800467110776861)
        ·
          refine ⟨4032758017425175166541323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10754021379800467110776861 4032758017425175166541323)
          ·
            refine ⟨6049137026137762749811985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032758017425175166541323 6049137026137762749811985)
            ·
              refine ⟨4536852769603322062358989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6049137026137762749811985 4536852769603322062358989)
              ·
                refine ⟨1701319788601245773384621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4536852769603322062358989 1701319788601245773384621)
                ·
                  refine ⟨637994920725467165019233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1701319788601245773384621 637994920725467165019233)
                  ·
                    refine ⟨478496190544100373764425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637994920725467165019233 478496190544100373764425)
                    ·
                      refine ⟨358872142908075280323319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478496190544100373764425 358872142908075280323319)
                      ·
                        rfl

theorem cell23_698901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_698901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698901 prefixEnd_698901 := by exact prefixLift 698901
  have htrace : WordTrace (prefixWord ++ tailWord_698901) baseStart_698901 baseEnd_698901 := by
    simpa [prefixWord, tailWord_698901, baseEnd_698901] using wordTrace_append hprefix tailTrace_698901
  have hstable : (prefixWord ++ tailWord_698901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698901).length < 2 ^ (prefixWord ++ tailWord_698901).sum := by decide
  have hdescent : baseEnd_698901 < baseStart_698901 := by decide
  rcases family_descends (prefixWord ++ tailWord_698901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698904 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_698904 : Nat := 118140960795 + 698904 * 2 ^ 59
def prefixEnd_698904 : Nat := 4983230072969 + 3 ^ 40 * 698904 * 2
def baseEnd_698904 : Nat := 358873683350038768585805

theorem tailTrace_698904 : CollatzResearch.WordTrace tailWord_698904 prefixEnd_698904 358873683350038768585805 := by
  unfold tailWord_698904
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745561529998823072655883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16994082039998430763541177 12745561529998823072655883)
  ·
    refine ⟨19118342294998234608983825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12745561529998823072655883 19118342294998234608983825)
    ·
      refine ⟨14338756721248675956737869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19118342294998234608983825 14338756721248675956737869)
      ·
        refine ⟨5377033770468253483776701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14338756721248675956737869 5377033770468253483776701)
        ·
          refine ⟨2016387663925595056416263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5377033770468253483776701 2016387663925595056416263)
          ·
            refine ⟨3024581495888392584624395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016387663925595056416263 3024581495888392584624395)
            ·
              refine ⟨4536872243832588876936593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024581495888392584624395 4536872243832588876936593)
              ·
                refine ⟨3402654182874441657702445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4536872243832588876936593 3402654182874441657702445)
                ·
                  refine ⟨1275995318577915621638417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3402654182874441657702445 1275995318577915621638417)
                  ·
                    refine ⟨956996488933436716228813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1275995318577915621638417 956996488933436716228813)
                    ·
                      refine ⟨358873683350038768585805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 956996488933436716228813 358873683350038768585805)
                      ·
                        rfl

theorem cell23_698904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_698904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698904 prefixEnd_698904 := by exact prefixLift 698904
  have htrace : WordTrace (prefixWord ++ tailWord_698904) baseStart_698904 baseEnd_698904 := by
    simpa [prefixWord, tailWord_698904, baseEnd_698904] using wordTrace_append hprefix tailTrace_698904
  have hstable : (prefixWord ++ tailWord_698904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698904).length < 2 ^ (prefixWord ++ tailWord_698904).sum := by decide
  have hdescent : baseEnd_698904 < baseStart_698904 := by decide
  rcases family_descends (prefixWord ++ tailWord_698904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698932 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_698932 : Nat := 118140960795 + 698932 * 2 ^ 59
def prefixEnd_698932 : Nat := 4983230072969 + 3 ^ 40 * 698932 * 2
def baseEnd_698932 : Nat := 119629353602788219678559

theorem tailTrace_698932 : CollatzResearch.WordTrace tailWord_698932 prefixEnd_698932 119629353602788219678559 := by
  unfold tailWord_698932
  simp only [CollatzResearch.WordTrace]
  refine ⟨12746072151948103463665525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16994762869264137951554033 12746072151948103463665525)
  ·
    refine ⟨1194944264245134699718643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12746072151948103463665525 1194944264245134699718643)
    ·
      refine ⟨1792416396367702049577965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194944264245134699718643 1792416396367702049577965)
      ·
        refine ⟨672156148637888268591737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1792416396367702049577965 672156148637888268591737)
        ·
          refine ⟨504117111478416201443803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672156148637888268591737 504117111478416201443803)
          ·
            refine ⟨756175667217624302165705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504117111478416201443803 756175667217624302165705)
            ·
              refine ⟨567131750413218226624279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756175667217624302165705 567131750413218226624279)
              ·
                refine ⟨850697625619827339936419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567131750413218226624279 850697625619827339936419)
                ·
                  refine ⟨1276046438429741009904629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850697625619827339936419 1276046438429741009904629)
                  ·
                    refine ⟨119629353602788219678559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1276046438429741009904629 119629353602788219678559)
                    ·
                      rfl

theorem cell23_698932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_698932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698932 prefixEnd_698932 := by exact prefixLift 698932
  have htrace : WordTrace (prefixWord ++ tailWord_698932) baseStart_698932 baseEnd_698932 := by
    simpa [prefixWord, tailWord_698932, baseEnd_698932] using wordTrace_append hprefix tailTrace_698932
  have hstable : (prefixWord ++ tailWord_698932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698932).length < 2 ^ (prefixWord ++ tailWord_698932).sum := by decide
  have hdescent : baseEnd_698932 < baseStart_698932 := by decide
  rcases family_descends (prefixWord ++ tailWord_698932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698938 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3]
def baseStart_698938 : Nat := 118140960795 + 698938 * 2 ^ 59
def prefixEnd_698938 : Nat := 4983230072969 + 3 ^ 40 * 698938 * 2
def baseEnd_698938 : Nat := 358891141692291635560649

theorem tailTrace_698938 : CollatzResearch.WordTrace tailWord_698938 prefixEnd_698938 358891141692291635560649 := by
  unfold tailWord_698938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373090785468617488012367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16994908761249646634699645 6373090785468617488012367)
  ·
    refine ⟨9559636178202926232018551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373090785468617488012367 9559636178202926232018551)
    ·
      refine ⟨14339454267304389348027827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9559636178202926232018551 14339454267304389348027827)
      ·
        refine ⟨21509181400956584022041741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14339454267304389348027827 21509181400956584022041741)
        ·
          refine ⟨8065943025358719008265653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21509181400956584022041741 8065943025358719008265653)
          ·
            refine ⟨756182158627379907024905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8065943025358719008265653 756182158627379907024905)
            ·
              refine ⟨567136618970534930268679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756182158627379907024905 567136618970534930268679)
              ·
                refine ⟨850704928455802395403019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567136618970534930268679 850704928455802395403019)
                ·
                  refine ⟨1276057392683703593104529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850704928455802395403019 1276057392683703593104529)
                  ·
                    refine ⟨957043044512777694828397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1276057392683703593104529 957043044512777694828397)
                    ·
                      refine ⟨358891141692291635560649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957043044512777694828397 358891141692291635560649)
                      ·
                        rfl

theorem cell23_698938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_698938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698938 prefixEnd_698938 := by exact prefixLift 698938
  have htrace : WordTrace (prefixWord ++ tailWord_698938) baseStart_698938 baseEnd_698938 := by
    simpa [prefixWord, tailWord_698938, baseEnd_698938] using wordTrace_append hprefix tailTrace_698938
  have hstable : (prefixWord ++ tailWord_698938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698938).length < 2 ^ (prefixWord ++ tailWord_698938).sum := by decide
  have hdescent : baseEnd_698938 < baseStart_698938 := by decide
  rcases family_descends (prefixWord ++ tailWord_698938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698951 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_698951 : Nat := 118140960795 + 698951 * 2 ^ 59
def prefixEnd_698951 : Nat := 4983230072969 + 3 ^ 40 * 698951 * 2
def baseEnd_698951 : Nat := 358897816940800084698089

theorem tailTrace_698951 : CollatzResearch.WordTrace tailWord_698951 prefixEnd_698951 358897816940800084698089 := by
  unfold tailWord_698951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25492837290827373172272707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16995224860551582114848471 25492837290827373172272707)
  ·
    refine ⟨38239255936241059758409061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25492837290827373172272707 38239255936241059758409061)
    ·
      refine ⟨7169860488045198704701699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38239255936241059758409061 7169860488045198704701699)
      ·
        refine ⟨10754790732067798057052549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169860488045198704701699 10754790732067798057052549)
        ·
          refine ⟨2016523262262712135697353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10754790732067798057052549 2016523262262712135697353)
          ·
            refine ⟨1512392446697034101773015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016523262262712135697353 1512392446697034101773015)
            ·
              refine ⟨2268588670045551152659523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512392446697034101773015 2268588670045551152659523)
              ·
                refine ⟨3402883005068326728989285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268588670045551152659523 3402883005068326728989285)
                ·
                  refine ⟨638040563450311261685491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3402883005068326728989285 638040563450311261685491)
                  ·
                    refine ⟨957060845175466892528237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638040563450311261685491 957060845175466892528237)
                    ·
                      refine ⟨358897816940800084698089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957060845175466892528237 358897816940800084698089)
                      ·
                        rfl

theorem cell23_698951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_698951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698951 prefixEnd_698951 := by exact prefixLift 698951
  have htrace : WordTrace (prefixWord ++ tailWord_698951) baseStart_698951 baseEnd_698951 := by
    simpa [prefixWord, tailWord_698951, baseEnd_698951] using wordTrace_append hprefix tailTrace_698951
  have hstable : (prefixWord ++ tailWord_698951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698951).length < 2 ^ (prefixWord ++ tailWord_698951).sum := by decide
  have hdescent : baseEnd_698951 < baseStart_698951 := by decide
  rcases family_descends (prefixWord ++ tailWord_698951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698967 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 2, 6]
def baseStart_698967 : Nat := 118140960795 + 698967 * 2 ^ 59
def prefixEnd_698967 : Nat := 4983230072969 + 3 ^ 40 * 698967 * 2
def baseEnd_698967 : Nat := 119635344210424007366005

theorem tailTrace_698967 : CollatzResearch.WordTrace tailWord_698967 prefixEnd_698967 119635344210424007366005 := by
  unfold tailWord_698967
  simp only [CollatzResearch.WordTrace]
  refine ⟨25493420858769407904855155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16995613905846271936570103 25493420858769407904855155)
  ·
    refine ⟨38240131288154111857282733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25493420858769407904855155 38240131288154111857282733)
    ·
      refine ⟨14340049233057791946481025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38240131288154111857282733 14340049233057791946481025)
      ·
        refine ⟨10755036924793343959860769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14340049233057791946481025 10755036924793343959860769)
        ·
          refine ⟨8066277693595007969895577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10755036924793343959860769 8066277693595007969895577)
          ·
            refine ⟨6049708270196255977421683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8066277693595007969895577 6049708270196255977421683)
            ·
              refine ⟨9074562405294383966132525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049708270196255977421683 9074562405294383966132525)
              ·
                refine ⟨3402960901985393987299697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9074562405294383966132525 3402960901985393987299697)
                ·
                  refine ⟨2552220676489045490474773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402960901985393987299697 2552220676489045490474773)
                  ·
                    refine ⟨119635344210424007366005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2552220676489045490474773 119635344210424007366005)
                    ·
                      rfl

theorem cell23_698967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_698967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698967 prefixEnd_698967 := by exact prefixLift 698967
  have htrace : WordTrace (prefixWord ++ tailWord_698967) baseStart_698967 baseEnd_698967 := by
    simpa [prefixWord, tailWord_698967, baseEnd_698967] using wordTrace_append hprefix tailTrace_698967
  have hstable : (prefixWord ++ tailWord_698967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698967).length < 2 ^ (prefixWord ++ tailWord_698967).sum := by decide
  have hdescent : baseEnd_698967 < baseStart_698967 := by decide
  rcases family_descends (prefixWord ++ tailWord_698967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698987 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4]
def baseStart_698987 : Nat := 118140960795 + 698987 * 2 ^ 59
def prefixEnd_698987 : Nat := 4983230072969 + 3 ^ 40 * 698987 * 2
def baseEnd_698987 : Nat := 358916302244361943847923

theorem tailTrace_698987 : CollatzResearch.WordTrace tailWord_698987 prefixEnd_698987 358916302244361943847923 := by
  unfold tailWord_698987
  simp only [CollatzResearch.WordTrace]
  refine ⟨25494150318696951320583215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16996100212464634213722143 25494150318696951320583215)
  ·
    refine ⟨38241225478045426980874823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25494150318696951320583215 38241225478045426980874823)
    ·
      refine ⟨57361838217068140471312235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38241225478045426980874823 57361838217068140471312235)
      ·
        refine ⟨86042757325602210706968353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57361838217068140471312235 86042757325602210706968353)
        ·
          refine ⟨64532067994201658030226265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86042757325602210706968353 64532067994201658030226265)
          ·
            refine ⟨48399050995651243522669699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64532067994201658030226265 48399050995651243522669699)
            ·
              refine ⟨72598576493476865284004549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48399050995651243522669699 72598576493476865284004549)
              ·
                refine ⟨13612233092526912240750853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72598576493476865284004549 13612233092526912240750853)
                ·
                  refine ⟨2552293704848796045140785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13612233092526912240750853 2552293704848796045140785)
                  ·
                    refine ⟨1914220278636597033855589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552293704848796045140785 1914220278636597033855589)
                    ·
                      refine ⟨358916302244361943847923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1914220278636597033855589 358916302244361943847923)
                      ·
                        rfl

theorem cell23_698987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_698987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698987 prefixEnd_698987 := by exact prefixLift 698987
  have htrace : WordTrace (prefixWord ++ tailWord_698987) baseStart_698987 baseEnd_698987 := by
    simpa [prefixWord, tailWord_698987, baseEnd_698987] using wordTrace_append hprefix tailTrace_698987
  have hstable : (prefixWord ++ tailWord_698987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698987).length < 2 ^ (prefixWord ++ tailWord_698987).sum := by decide
  have hdescent : baseEnd_698987 < baseStart_698987 := by decide
  rcases family_descends (prefixWord ++ tailWord_698987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698991 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 4, 2, 2]
def baseStart_698991 : Nat := 118140960795 + 698991 * 2 ^ 59
def prefixEnd_698991 : Nat := 4983230072969 + 3 ^ 40 * 698991 * 2
def baseEnd_698991 : Nat := 358918356166979928197905

theorem tailTrace_698991 : CollatzResearch.WordTrace tailWord_698991 prefixEnd_698991 358918356166979928197905 := by
  unfold tailWord_698991
  simp only [CollatzResearch.WordTrace]
  refine ⟨25494296210682460003728827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16996197473788306669152551 25494296210682460003728827)
  ·
    refine ⟨38241444316023690005593241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25494296210682460003728827 38241444316023690005593241)
    ·
      refine ⟨28681083237017767504194931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38241444316023690005593241 28681083237017767504194931)
      ·
        refine ⟨43021624855526651256292397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28681083237017767504194931 43021624855526651256292397)
        ·
          refine ⟨16133109320822494221109649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43021624855526651256292397 16133109320822494221109649)
          ·
            refine ⟨12099831990616870665832237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16133109320822494221109649 12099831990616870665832237)
            ·
              refine ⟨4537436996481326499687089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12099831990616870665832237 4537436996481326499687089)
              ·
                refine ⟨3403077747360994874765317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537436996481326499687089 3403077747360994874765317)
                ·
                  refine ⟨638077077630186539018497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3403077747360994874765317 638077077630186539018497)
                  ·
                    refine ⟨478557808222639904263873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 638077077630186539018497 478557808222639904263873)
                    ·
                      refine ⟨358918356166979928197905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478557808222639904263873 358918356166979928197905)
                      ·
                        rfl

theorem cell23_698991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 2, 2].length) (baseStart_698991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_698991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_698991 prefixEnd_698991 := by exact prefixLift 698991
  have htrace : WordTrace (prefixWord ++ tailWord_698991) baseStart_698991 baseEnd_698991 := by
    simpa [prefixWord, tailWord_698991, baseEnd_698991] using wordTrace_append hprefix tailTrace_698991
  have hstable : (prefixWord ++ tailWord_698991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698991).length < 2 ^ (prefixWord ++ tailWord_698991).sum := by decide
  have hdescent : baseEnd_698991 < baseStart_698991 := by decide
  rcases family_descends (prefixWord ++ tailWord_698991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699061 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_699061 : Nat := 118140960795 + 699061 * 2 ^ 59
def prefixEnd_699061 : Nat := 4983230072969 + 3 ^ 40 * 699061 * 2
def baseEnd_699061 : Nat := 119651433270931551440861

theorem tailTrace_699061 : CollatzResearch.WordTrace tailWord_699061 prefixEnd_699061 119651433270931551440861 := by
  unfold tailWord_699061
  simp only [CollatzResearch.WordTrace]
  refine ⟨25496849320428861958777037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16997899546952574639184691 25496849320428861958777037)
  ·
    refine ⟨9561318495160823234541389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25496849320428861958777037 9561318495160823234541389)
    ·
      refine ⟨3585494435685308712953021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9561318495160823234541389 3585494435685308712953021)
      ·
        refine ⟨1344560413381990767357383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3585494435685308712953021 1344560413381990767357383)
        ·
          refine ⟨2016840620072986151036075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344560413381990767357383 2016840620072986151036075)
          ·
            refine ⟨3025260930109479226554113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016840620072986151036075 3025260930109479226554113)
            ·
              refine ⟨2268945697582109419915585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025260930109479226554113 2268945697582109419915585)
              ·
                refine ⟨1701709273186582064936689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268945697582109419915585 1701709273186582064936689)
                ·
                  refine ⟨1276281954889936548702517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1701709273186582064936689 1276281954889936548702517)
                  ·
                    refine ⟨119651433270931551440861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1276281954889936548702517 119651433270931551440861)
                    ·
                      rfl

theorem cell23_699061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_699061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699061 prefixEnd_699061 := by exact prefixLift 699061
  have htrace : WordTrace (prefixWord ++ tailWord_699061) baseStart_699061 baseEnd_699061 := by
    simpa [prefixWord, tailWord_699061, baseEnd_699061] using wordTrace_append hprefix tailTrace_699061
  have hstable : (prefixWord ++ tailWord_699061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699061).length < 2 ^ (prefixWord ++ tailWord_699061).sum := by decide
  have hdescent : baseEnd_699061 < baseStart_699061 := by decide
  rcases family_descends (prefixWord ++ tailWord_699061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699087 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 12]
def baseStart_699087 : Nat := 118140960795 + 699087 * 2 ^ 59
def prefixEnd_699087 : Nat := 4983230072969 + 3 ^ 40 * 699087 * 2
def baseEnd_699087 : Nat := 39885294478867950288607

theorem tailTrace_699087 : CollatzResearch.WordTrace tailWord_699087 prefixEnd_699087 39885294478867950288607 := by
  unfold tailWord_699087
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497797618334668399223515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16998531745556445599482343 25497797618334668399223515)
  ·
    refine ⟨38246696427502002598835273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25497797618334668399223515 38246696427502002598835273)
    ·
      refine ⟨28685022320626501949126455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38246696427502002598835273 28685022320626501949126455)
      ·
        refine ⟨43027533480939752923689683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28685022320626501949126455 43027533480939752923689683)
        ·
          refine ⟨64541300221409629385534525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43027533480939752923689683 64541300221409629385534525)
          ·
            refine ⟨24202987583028611019575447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64541300221409629385534525 24202987583028611019575447)
            ·
              refine ⟨36304481374542916529363171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24202987583028611019575447 36304481374542916529363171)
              ·
                refine ⟨54456722061814374794044757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36304481374542916529363171 54456722061814374794044757)
                ·
                  refine ⟨39885294478867950288607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 54456722061814374794044757 39885294478867950288607)
                  ·
                    rfl

theorem cell23_699087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 12].length) (baseStart_699087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699087 prefixEnd_699087 := by exact prefixLift 699087
  have htrace : WordTrace (prefixWord ++ tailWord_699087) baseStart_699087 baseEnd_699087 := by
    simpa [prefixWord, tailWord_699087, baseEnd_699087] using wordTrace_append hprefix tailTrace_699087
  have hstable : (prefixWord ++ tailWord_699087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699087).length < 2 ^ (prefixWord ++ tailWord_699087).sum := by decide
  have hdescent : baseEnd_699087 < baseStart_699087 := by decide
  rcases family_descends (prefixWord ++ tailWord_699087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699108 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_699108 : Nat := 118140960795 + 699108 * 2 ^ 59
def prefixEnd_699108 : Nat := 4983230072969 + 3 ^ 40 * 699108 * 2
def baseEnd_699108 : Nat := 119659477801185323478289

theorem tailTrace_699108 : CollatzResearch.WordTrace tailWord_699108 prefixEnd_699108 119659477801185323478289 := by
  unfold tailWord_699108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12749281775629294492868989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16999042367505725990491985 12749281775629294492868989)
  ·
    refine ⟨4780980665860985434825871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12749281775629294492868989 4780980665860985434825871)
    ·
      refine ⟨7171470998791478152238807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4780980665860985434825871 7171470998791478152238807)
      ·
        refine ⟨10757206498187217228358211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7171470998791478152238807 10757206498187217228358211)
        ·
          refine ⟨16135809747280825842537317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10757206498187217228358211 16135809747280825842537317)
          ·
            refine ⟨3025464327615154845475747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16135809747280825842537317 3025464327615154845475747)
            ·
              refine ⟨4538196491422732268213621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025464327615154845475747 4538196491422732268213621)
              ·
                refine ⟨425455921070881150145027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4538196491422732268213621 425455921070881150145027)
                ·
                  refine ⟨638183881606321725217541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425455921070881150145027 638183881606321725217541)
                  ·
                    refine ⟨119659477801185323478289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638183881606321725217541 119659477801185323478289)
                    ·
                      rfl

theorem cell23_699108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_699108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699108 prefixEnd_699108 := by exact prefixLift 699108
  have htrace : WordTrace (prefixWord ++ tailWord_699108) baseStart_699108 baseEnd_699108 := by
    simpa [prefixWord, tailWord_699108, baseEnd_699108] using wordTrace_append hprefix tailTrace_699108
  have hstable : (prefixWord ++ tailWord_699108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699108).length < 2 ^ (prefixWord ++ tailWord_699108).sum := by decide
  have hdescent : baseEnd_699108 < baseStart_699108 := by decide
  rcases family_descends (prefixWord ++ tailWord_699108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699151 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 1, 5]
def baseStart_699151 : Nat := 118140960795 + 699151 * 2 ^ 59
def prefixEnd_699151 : Nat := 4983230072969 + 3 ^ 40 * 699151 * 2
def baseEnd_699151 : Nat := 119666837690566434065723

theorem tailTrace_699151 : CollatzResearch.WordTrace tailWord_699151 prefixEnd_699151 119666837690566434065723 := by
  unfold tailWord_699151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25500131890102807329553307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17000087926735204886368871 25500131890102807329553307)
  ·
    refine ⟨38250197835154210994329961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25500131890102807329553307 38250197835154210994329961)
    ·
      refine ⟨28687648376365658245747471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38250197835154210994329961 28687648376365658245747471)
      ·
        refine ⟨43031472564548487368621207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28687648376365658245747471 43031472564548487368621207)
        ·
          refine ⟨64547208846822731052931811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43031472564548487368621207 64547208846822731052931811)
          ·
            refine ⟨96820813270234096579397717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64547208846822731052931811 96820813270234096579397717)
            ·
              refine ⟨1134618905510555819289817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 96820813270234096579397717 1134618905510555819289817)
              ·
                refine ⟨850964179132916864467363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134618905510555819289817 850964179132916864467363)
                ·
                  refine ⟨1276446268699375296701045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850964179132916864467363 1276446268699375296701045)
                  ·
                    refine ⟨119666837690566434065723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1276446268699375296701045 119666837690566434065723)
                    ·
                      rfl

theorem cell23_699151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_699151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699151 prefixEnd_699151 := by exact prefixLift 699151
  have htrace : WordTrace (prefixWord ++ tailWord_699151) baseStart_699151 baseEnd_699151 := by
    simpa [prefixWord, tailWord_699151, baseEnd_699151] using wordTrace_append hprefix tailTrace_699151
  have hstable : (prefixWord ++ tailWord_699151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699151).length < 2 ^ (prefixWord ++ tailWord_699151).sum := by decide
  have hdescent : baseEnd_699151 < baseStart_699151 := by decide
  rcases family_descends (prefixWord ++ tailWord_699151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699182 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_699182 : Nat := 118140960795 + 699182 * 2 ^ 59
def prefixEnd_699182 : Nat := 4983230072969 + 3 ^ 40 * 699182 * 2
def baseEnd_699182 : Nat := 359016430971988680909527

theorem tailTrace_699182 : CollatzResearch.WordTrace tailWord_699182 prefixEnd_699182 359016430971988680909527 := by
  unfold tailWord_699182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187657819123812452991475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17000841701993666415954533 3187657819123812452991475)
  ·
    refine ⟨4781486728685718679487213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3187657819123812452991475 4781486728685718679487213)
    ·
      refine ⟨1793057523257144504807705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4781486728685718679487213 1793057523257144504807705)
      ·
        refine ⟨1344793142442858378605779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1793057523257144504807705 1344793142442858378605779)
        ·
          refine ⟨2017189713664287567908669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344793142442858378605779 2017189713664287567908669)
          ·
            refine ⟨756446142624107837965751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2017189713664287567908669 756446142624107837965751)
            ·
              refine ⟨1134669213936161756948627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756446142624107837965751 1134669213936161756948627)
              ·
                refine ⟨1702003820904242635422941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134669213936161756948627 1702003820904242635422941)
                ·
                  refine ⟨638251432839090988283603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1702003820904242635422941 638251432839090988283603)
                  ·
                    refine ⟨957377149258636482425405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638251432839090988283603 957377149258636482425405)
                    ·
                      refine ⟨359016430971988680909527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957377149258636482425405 359016430971988680909527)
                      ·
                        rfl

theorem cell23_699182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_699182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699182 prefixEnd_699182 := by exact prefixLift 699182
  have htrace : WordTrace (prefixWord ++ tailWord_699182) baseStart_699182 baseEnd_699182 := by
    simpa [prefixWord, tailWord_699182, baseEnd_699182] using wordTrace_append hprefix tailTrace_699182
  have hstable : (prefixWord ++ tailWord_699182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699182).length < 2 ^ (prefixWord ++ tailWord_699182).sum := by decide
  have hdescent : baseEnd_699182 < baseStart_699182 := by decide
  rcases family_descends (prefixWord ++ tailWord_699182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699191 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_699191 : Nat := 118140960795 + 699191 * 2 ^ 59
def prefixEnd_699191 : Nat := 4983230072969 + 3 ^ 40 * 699191 * 2
def baseEnd_699191 : Nat := 359021052297879145696985

theorem tailTrace_699191 : CollatzResearch.WordTrace tailWord_699191 prefixEnd_699191 359021052297879145696985 := by
  unfold tailWord_699191
  simp only [CollatzResearch.WordTrace]
  refine ⟨25501590809957894161009427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17001060539971929440672951 25501590809957894161009427)
  ·
    refine ⟨38252386214936841241514141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25501590809957894161009427 38252386214936841241514141)
    ·
      refine ⟨14344644830601315465567803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38252386214936841241514141 14344644830601315465567803)
      ·
        refine ⟨21516967245901973198351705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14344644830601315465567803 21516967245901973198351705)
        ·
          refine ⟨16137725434426479898763779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21516967245901973198351705 16137725434426479898763779)
          ·
            refine ⟨24206588151639719848145669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16137725434426479898763779 24206588151639719848145669)
            ·
              refine ⟨4538735278432447471527313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24206588151639719848145669 4538735278432447471527313)
              ·
                refine ⟨3404051458824335603645485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538735278432447471527313 3404051458824335603645485)
                ·
                  refine ⟨1276519297059125851367057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3404051458824335603645485 1276519297059125851367057)
                  ·
                    refine ⟨957389472794344388525293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1276519297059125851367057 957389472794344388525293)
                    ·
                      refine ⟨359021052297879145696985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957389472794344388525293 359021052297879145696985)
                      ·
                        rfl

theorem cell23_699191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_699191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699191 prefixEnd_699191 := by exact prefixLift 699191
  have htrace : WordTrace (prefixWord ++ tailWord_699191) baseStart_699191 baseEnd_699191 := by
    simpa [prefixWord, tailWord_699191, baseEnd_699191] using wordTrace_append hprefix tailTrace_699191
  have hstable : (prefixWord ++ tailWord_699191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699191).length < 2 ^ (prefixWord ++ tailWord_699191).sum := by decide
  have hdescent : baseEnd_699191 < baseStart_699191 := by decide
  rcases family_descends (prefixWord ++ tailWord_699191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699224 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_699224 : Nat := 118140960795 + 699224 * 2 ^ 59
def prefixEnd_699224 : Nat := 4983230072969 + 3 ^ 40 * 699224 * 2
def baseEnd_699224 : Nat := 119679332386492505528111

theorem tailTrace_699224 : CollatzResearch.WordTrace tailWord_699224 prefixEnd_699224 119679332386492505528111 := by
  unfold tailWord_699224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12751397209419170398480363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17001862945892227197973817 12751397209419170398480363)
  ·
    refine ⟨19127095814128755597720545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12751397209419170398480363 19127095814128755597720545)
    ·
      refine ⟨14345321860596566698290409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19127095814128755597720545 14345321860596566698290409)
      ·
        refine ⟨10758991395447425023717807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14345321860596566698290409 10758991395447425023717807)
        ·
          refine ⟨16138487093171137535576711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758991395447425023717807 16138487093171137535576711)
          ·
            refine ⟨24207730639756706303365067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16138487093171137535576711 24207730639756706303365067)
            ·
              refine ⟨36311595959635059455047601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24207730639756706303365067 36311595959635059455047601)
              ·
                refine ⟨27233696969726294591285701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36311595959635059455047601 27233696969726294591285701)
                ·
                  refine ⟨5106318181823680235866069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27233696969726294591285701 5106318181823680235866069)
                  ·
                    refine ⟨119679332386492505528111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5106318181823680235866069 119679332386492505528111)
                    ·
                      rfl

theorem cell23_699224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_699224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699224 prefixEnd_699224 := by exact prefixLift 699224
  have htrace : WordTrace (prefixWord ++ tailWord_699224) baseStart_699224 baseEnd_699224 := by
    simpa [prefixWord, tailWord_699224, baseEnd_699224] using wordTrace_append hprefix tailTrace_699224
  have hstable : (prefixWord ++ tailWord_699224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699224).length < 2 ^ (prefixWord ++ tailWord_699224).sum := by decide
  have hdescent : baseEnd_699224 < baseStart_699224 := by decide
  rcases family_descends (prefixWord ++ tailWord_699224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699225 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 1, 2, 3]
def baseStart_699225 : Nat := 118140960795 + 699225 * 2 ^ 59
def prefixEnd_699225 : Nat := 4983230072969 + 3 ^ 40 * 699225 * 2
def baseEnd_699225 : Nat := 359038510640132012671829

theorem tailTrace_699225 : CollatzResearch.WordTrace tailWord_699225 prefixEnd_699225 359038510640132012671829 := by
  unfold tailWord_699225
  simp only [CollatzResearch.WordTrace]
  refine ⟨25502830891834717967747129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17001887261223145311831419 25502830891834717967747129)
  ·
    refine ⟨19127123168876038475810347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25502830891834717967747129 19127123168876038475810347)
    ·
      refine ⟨28690684753314057713715521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19127123168876038475810347 28690684753314057713715521)
      ·
        refine ⟨21518013564985543285286641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28690684753314057713715521 21518013564985543285286641)
        ·
          refine ⟨16138510173739157463964981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21518013564985543285286641 16138510173739157463964981)
          ·
            refine ⟨1512985328788046012246717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16138510173739157463964981 1512985328788046012246717)
            ·
              refine ⟨567369498295517254592519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1512985328788046012246717 567369498295517254592519)
              ·
                refine ⟨851054247443275881888779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567369498295517254592519 851054247443275881888779)
                ·
                  refine ⟨1276581371164913822833169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851054247443275881888779 1276581371164913822833169)
                  ·
                    refine ⟨957436028373685367124877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1276581371164913822833169 957436028373685367124877)
                    ·
                      refine ⟨359038510640132012671829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957436028373685367124877 359038510640132012671829)
                      ·
                        rfl

theorem cell23_699225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_699225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699225 prefixEnd_699225 := by exact prefixLift 699225
  have htrace : WordTrace (prefixWord ++ tailWord_699225) baseStart_699225 baseEnd_699225 := by
    simpa [prefixWord, tailWord_699225, baseEnd_699225] using wordTrace_append hprefix tailTrace_699225
  have hstable : (prefixWord ++ tailWord_699225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699225).length < 2 ^ (prefixWord ++ tailWord_699225).sum := by decide
  have hdescent : baseEnd_699225 < baseStart_699225 := by decide
  rcases family_descends (prefixWord ++ tailWord_699225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699239 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_699239 : Nat := 118140960795 + 699239 * 2 ^ 59
def prefixEnd_699239 : Nat := 4983230072969 + 3 ^ 40 * 699239 * 2
def baseEnd_699239 : Nat := 359045699369294957896765

theorem tailTrace_699239 : CollatzResearch.WordTrace tailWord_699239 prefixEnd_699239 359045699369294957896765 := by
  unfold tailWord_699239
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503341513783998358756771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17002227675855998905837847 25503341513783998358756771)
  ·
    refine ⟨38255012270675997538135157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25503341513783998358756771 38255012270675997538135157)
    ·
      refine ⟨3586407400375874769200171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38255012270675997538135157 3586407400375874769200171)
      ·
        refine ⟨5379611100563812153800257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586407400375874769200171 5379611100563812153800257)
        ·
          refine ⟨4034708325422859115350193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5379611100563812153800257 4034708325422859115350193)
          ·
            refine ⟨3026031244067144336512645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4034708325422859115350193 3026031244067144336512645)
            ·
              refine ⟨567380858262589563096121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3026031244067144336512645 567380858262589563096121)
              ·
                refine ⟨425535643696942172322091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567380858262589563096121 425535643696942172322091)
                ·
                  refine ⟨638303465545413258483137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425535643696942172322091 638303465545413258483137)
                  ·
                    refine ⟨478727599159059943862353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 638303465545413258483137 478727599159059943862353)
                    ·
                      refine ⟨359045699369294957896765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478727599159059943862353 359045699369294957896765)
                      ·
                        rfl

theorem cell23_699239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_699239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699239 prefixEnd_699239 := by exact prefixLift 699239
  have htrace : WordTrace (prefixWord ++ tailWord_699239) baseStart_699239 baseEnd_699239 := by
    simpa [prefixWord, tailWord_699239, baseEnd_699239] using wordTrace_append hprefix tailTrace_699239
  have hstable : (prefixWord ++ tailWord_699239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699239).length < 2 ^ (prefixWord ++ tailWord_699239).sum := by decide
  have hdescent : baseEnd_699239 < baseStart_699239 := by decide
  rcases family_descends (prefixWord ++ tailWord_699239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699248 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 3, 3, 2]
def baseStart_699248 : Nat := 118140960795 + 699248 * 2 ^ 59
def prefixEnd_699248 : Nat := 4983230072969 + 3 ^ 40 * 699248 * 2
def baseEnd_699248 : Nat := 359050320695185422684223

theorem tailTrace_699248 : CollatzResearch.WordTrace tailWord_699248 prefixEnd_699248 359050320695185422684223 := by
  unfold tailWord_699248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12751834885375696447917199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17002446513834261930556265 12751834885375696447917199)
  ·
    refine ⟨19127752328063544671875799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12751834885375696447917199 19127752328063544671875799)
    ·
      refine ⟨28691628492095317007813699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19127752328063544671875799 28691628492095317007813699)
      ·
        refine ⟨43037442738142975511720549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28691628492095317007813699 43037442738142975511720549)
        ·
          refine ⟨8069520513401807908447603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43037442738142975511720549 8069520513401807908447603)
          ·
            refine ⟨12104280770102711862671405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8069520513401807908447603 12104280770102711862671405)
            ·
              refine ⟨4539105288788516948501777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12104280770102711862671405 4539105288788516948501777)
              ·
                refine ⟨3404328966591387711376333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539105288788516948501777 3404328966591387711376333)
                ·
                  refine ⟨1276623362471770391766125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3404328966591387711376333 1276623362471770391766125)
                  ·
                    refine ⟨478733760926913896912297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276623362471770391766125 478733760926913896912297)
                    ·
                      refine ⟨359050320695185422684223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478733760926913896912297 359050320695185422684223)
                      ·
                        rfl

theorem cell23_699248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 3, 2].length) (baseStart_699248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699248 prefixEnd_699248 := by exact prefixLift 699248
  have htrace : WordTrace (prefixWord ++ tailWord_699248) baseStart_699248 baseEnd_699248 := by
    simpa [prefixWord, tailWord_699248, baseEnd_699248] using wordTrace_append hprefix tailTrace_699248
  have hstable : (prefixWord ++ tailWord_699248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699248).length < 2 ^ (prefixWord ++ tailWord_699248).sum := by decide
  have hdescent : baseEnd_699248 < baseStart_699248 := by decide
  rcases family_descends (prefixWord ++ tailWord_699248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699311 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_699311 : Nat := 118140960795 + 699311 * 2 ^ 59
def prefixEnd_699311 : Nat := 4983230072969 + 3 ^ 40 * 699311 * 2
def baseEnd_699311 : Nat := 359082669976418676196433

theorem tailTrace_699311 : CollatzResearch.WordTrace tailWord_699311 prefixEnd_699311 359082669976418676196433 := by
  unfold tailWord_699311
  simp only [CollatzResearch.WordTrace]
  refine ⟨25505967569523154655377787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17003978379682103103585191 25505967569523154655377787)
  ·
    refine ⟨38258951354284731983066681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25505967569523154655377787 38258951354284731983066681)
    ·
      refine ⟨28694213515713548987300011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38258951354284731983066681 28694213515713548987300011)
      ·
        refine ⟨43041320273570323480950017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28694213515713548987300011 43041320273570323480950017)
        ·
          refine ⟨32280990205177742610712513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43041320273570323480950017 32280990205177742610712513)
          ·
            refine ⟨24210742653883306958034385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32280990205177742610712513 24210742653883306958034385)
            ·
              refine ⟨18158056990412480218525789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24210742653883306958034385 18158056990412480218525789)
              ·
                refine ⟨6809271371404680081947171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18158056990412480218525789 6809271371404680081947171)
                ·
                  refine ⟨10213907057107020122920757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6809271371404680081947171 10213907057107020122920757)
                  ·
                    refine ⟨957553786603783136523821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10213907057107020122920757 957553786603783136523821)
                    ·
                      refine ⟨359082669976418676196433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957553786603783136523821 359082669976418676196433)
                      ·
                        rfl

theorem cell23_699311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_699311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699311 prefixEnd_699311 := by exact prefixLift 699311
  have htrace : WordTrace (prefixWord ++ tailWord_699311) baseStart_699311 baseEnd_699311 := by
    simpa [prefixWord, tailWord_699311, baseEnd_699311] using wordTrace_append hprefix tailTrace_699311
  have hstable : (prefixWord ++ tailWord_699311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699311).length < 2 ^ (prefixWord ++ tailWord_699311).sum := by decide
  have hdescent : baseEnd_699311 < baseStart_699311 := by decide
  rcases family_descends (prefixWord ++ tailWord_699311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699338 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_699338 : Nat := 118140960795 + 699338 * 2 ^ 59
def prefixEnd_699338 : Nat := 4983230072969 + 3 ^ 40 * 699338 * 2
def baseEnd_699338 : Nat := 359096533954090070558809

theorem tailTrace_699338 : CollatzResearch.WordTrace tailWord_699338 prefixEnd_699338 359096533954090070558809 := by
  unfold tailWord_699338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376738085106334566652667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17004634893616892177740445 6376738085106334566652667)
  ·
    refine ⟨9565107127659501849979001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6376738085106334566652667 9565107127659501849979001)
    ·
      refine ⟨7173830345744626387484251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9565107127659501849979001 7173830345744626387484251)
      ·
        refine ⟨10760745518616939581226377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7173830345744626387484251 10760745518616939581226377)
        ·
          refine ⟨8070559138962704685919783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10760745518616939581226377 8070559138962704685919783)
          ·
            refine ⟨12105838708444057028879675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070559138962704685919783 12105838708444057028879675)
            ·
              refine ⟨18158758062666085543319513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12105838708444057028879675 18158758062666085543319513)
              ·
                refine ⟨13619068546999564157489635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18158758062666085543319513 13619068546999564157489635)
                ·
                  refine ⟨20428602820499346236234453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13619068546999564157489635 20428602820499346236234453)
                  ·
                    refine ⟨478795378605453427411745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20428602820499346236234453 478795378605453427411745)
                    ·
                      refine ⟨359096533954090070558809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478795378605453427411745 359096533954090070558809)
                      ·
                        rfl

theorem cell23_699338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_699338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699338 prefixEnd_699338 := by exact prefixLift 699338
  have htrace : WordTrace (prefixWord ++ tailWord_699338) baseStart_699338 baseEnd_699338 := by
    simpa [prefixWord, tailWord_699338, baseEnd_699338] using wordTrace_append hprefix tailTrace_699338
  have hstable : (prefixWord ++ tailWord_699338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699338).length < 2 ^ (prefixWord ++ tailWord_699338).sum := by decide
  have hdescent : baseEnd_699338 < baseStart_699338 := by decide
  rcases family_descends (prefixWord ++ tailWord_699338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699348 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_699348 : Nat := 118140960795 + 699348 * 2 ^ 59
def prefixEnd_699348 : Nat := 4983230072969 + 3 ^ 40 * 699348 * 2
def baseEnd_699348 : Nat := 119700556253545010477921

theorem tailTrace_699348 : CollatzResearch.WordTrace tailWord_699348 prefixEnd_699348 119700556253545010477921 := by
  unfold tailWord_699348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753658535194554987237349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17004878046926073316316465 12753658535194554987237349)
  ·
    refine ⟨2391310975348979060107003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12753658535194554987237349 2391310975348979060107003)
    ·
      refine ⟨3586966463023468590160505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391310975348979060107003 3586966463023468590160505)
      ·
        refine ⟨2690224847267601442620379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3586966463023468590160505 2690224847267601442620379)
        ·
          refine ⟨4035337270901402163930569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690224847267601442620379 4035337270901402163930569)
          ·
            refine ⟨3026502953176051622947927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4035337270901402163930569 3026502953176051622947927)
            ·
              refine ⟨4539754429764077434421891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026502953176051622947927 4539754429764077434421891)
              ·
                refine ⟨6809631644646116151632837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4539754429764077434421891 6809631644646116151632837)
                ·
                  refine ⟨1276805933371146778431157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6809631644646116151632837 1276805933371146778431157)
                  ·
                    refine ⟨119700556253545010477921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1276805933371146778431157 119700556253545010477921)
                    ·
                      rfl

theorem cell23_699348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_699348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699348 prefixEnd_699348 := by exact prefixLift 699348
  have htrace : WordTrace (prefixWord ++ tailWord_699348) baseStart_699348 baseEnd_699348 := by
    simpa [prefixWord, tailWord_699348, baseEnd_699348] using wordTrace_append hprefix tailTrace_699348
  have hstable : (prefixWord ++ tailWord_699348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699348).length < 2 ^ (prefixWord ++ tailWord_699348).sum := by decide
  have hdescent : baseEnd_699348 < baseStart_699348 := by decide
  rcases family_descends (prefixWord ++ tailWord_699348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699351 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_699351 : Nat := 118140960795 + 699351 * 2 ^ 59
def prefixEnd_699351 : Nat := 4983230072969 + 3 ^ 40 * 699351 * 2
def baseEnd_699351 : Nat := 359103209202598519696249

theorem tailTrace_699351 : CollatzResearch.WordTrace tailWord_699351 prefixEnd_699351 359103209202598519696249 := by
  unfold tailWord_699351
  simp only [CollatzResearch.WordTrace]
  refine ⟨25507426489378241486833907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17004950992918827657889271 25507426489378241486833907)
  ·
    refine ⟨38261139734067362230250861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25507426489378241486833907 38261139734067362230250861)
    ·
      refine ⟨14347927400275260836344073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38261139734067362230250861 14347927400275260836344073)
      ·
        refine ⟨10760945550206445627258055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14347927400275260836344073 10760945550206445627258055)
        ·
          refine ⟨16141418325309668440887083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760945550206445627258055 16141418325309668440887083)
          ·
            refine ⟨24212127487964502661330625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16141418325309668440887083 24212127487964502661330625)
            ·
              refine ⟨18159095615973376995997969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24212127487964502661330625 18159095615973376995997969)
              ·
                refine ⟨13619321711980032746998477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18159095615973376995997969 13619321711980032746998477)
                ·
                  refine ⟨5107245641992512280124429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13619321711980032746998477 5107245641992512280124429)
                  ·
                    refine ⟨1915217115747192105046661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5107245641992512280124429 1915217115747192105046661)
                    ·
                      refine ⟨359103209202598519696249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1915217115747192105046661 359103209202598519696249)
                      ·
                        rfl

theorem cell23_699351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_699351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699351 prefixEnd_699351 := by exact prefixLift 699351
  have htrace : WordTrace (prefixWord ++ tailWord_699351) baseStart_699351 baseEnd_699351 := by
    simpa [prefixWord, tailWord_699351, baseEnd_699351] using wordTrace_append hprefix tailTrace_699351
  have hstable : (prefixWord ++ tailWord_699351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699351).length < 2 ^ (prefixWord ++ tailWord_699351).sum := by decide
  have hdescent : baseEnd_699351 < baseStart_699351 := by decide
  rcases family_descends (prefixWord ++ tailWord_699351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699411 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_699411 : Nat := 118140960795 + 699411 * 2 ^ 59
def prefixEnd_699411 : Nat := 4983230072969 + 3 ^ 40 * 699411 * 2
def baseEnd_699411 : Nat := 359134018041868284945973

theorem tailTrace_699411 : CollatzResearch.WordTrace tailWord_699411 prefixEnd_699411 359134018041868284945973 := by
  unfold tailWord_699411
  simp only [CollatzResearch.WordTrace]
  refine ⟨25509614869160871734018087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17006409912773914489345391 25509614869160871734018087)
  ·
    refine ⟨38264422303741307601027131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25509614869160871734018087 38264422303741307601027131)
    ·
      refine ⟨57396633455611961401540697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38264422303741307601027131 57396633455611961401540697)
      ·
        refine ⟨43047475091708971051155523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57396633455611961401540697 43047475091708971051155523)
        ·
          refine ⟨64571212637563456576733285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43047475091708971051155523 64571212637563456576733285)
          ·
            refine ⟨12107102369543148108137491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64571212637563456576733285 12107102369543148108137491)
            ·
              refine ⟨18160653554314722162206237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12107102369543148108137491 18160653554314722162206237)
              ·
                refine ⟨6810245082868020810827339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18160653554314722162206237 6810245082868020810827339)
                ·
                  refine ⟨10215367624302031216241009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810245082868020810827339 10215367624302031216241009)
                  ·
                    refine ⟨7661525718226523412180757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10215367624302031216241009 7661525718226523412180757)
                    ·
                      refine ⟨359134018041868284945973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7661525718226523412180757 359134018041868284945973)
                      ·
                        rfl

theorem cell23_699411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_699411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699411 prefixEnd_699411 := by exact prefixLift 699411
  have htrace : WordTrace (prefixWord ++ tailWord_699411) baseStart_699411 baseEnd_699411 := by
    simpa [prefixWord, tailWord_699411, baseEnd_699411] using wordTrace_append hprefix tailTrace_699411
  have hstable : (prefixWord ++ tailWord_699411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699411).length < 2 ^ (prefixWord ++ tailWord_699411).sum := by decide
  have hdescent : baseEnd_699411 < baseStart_699411 := by decide
  rcases family_descends (prefixWord ++ tailWord_699411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699435 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 3]
def baseStart_699435 : Nat := 118140960795 + 699435 * 2 ^ 59
def prefixEnd_699435 : Nat := 4983230072969 + 3 ^ 40 * 699435 * 2
def baseEnd_699435 : Nat := 359146341577576191045863

theorem tailTrace_699435 : CollatzResearch.WordTrace tailWord_699435 prefixEnd_699435 359146341577576191045863 := by
  unfold tailWord_699435
  simp only [CollatzResearch.WordTrace]
  refine ⟨25510490221073923832891759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17006993480715949221927839 25510490221073923832891759)
  ·
    refine ⟨38265735331610885749337639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25510490221073923832891759 38265735331610885749337639)
    ·
      refine ⟨57398602997416328624006459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38265735331610885749337639 57398602997416328624006459)
      ·
        refine ⟨86097904496124492936009689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57398602997416328624006459 86097904496124492936009689)
        ·
          refine ⟨64573428372093369702007267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86097904496124492936009689 64573428372093369702007267)
          ·
            refine ⟨96860142558140054553010901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64573428372093369702007267 96860142558140054553010901)
            ·
              refine ⟨2270159591206407528586193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96860142558140054553010901 2270159591206407528586193)
              ·
                refine ⟨1702619693404805646439645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270159591206407528586193 1702619693404805646439645)
                ·
                  refine ⟨638482385026802117414867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1702619693404805646439645 638482385026802117414867)
                  ·
                    refine ⟨957723577540203176122301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638482385026802117414867 957723577540203176122301)
                    ·
                      refine ⟨359146341577576191045863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957723577540203176122301 359146341577576191045863)
                      ·
                        rfl

theorem cell23_699435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 3].length) (baseStart_699435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699435 prefixEnd_699435 := by exact prefixLift 699435
  have htrace : WordTrace (prefixWord ++ tailWord_699435) baseStart_699435 baseEnd_699435 := by
    simpa [prefixWord, tailWord_699435, baseEnd_699435] using wordTrace_append hprefix tailTrace_699435
  have hstable : (prefixWord ++ tailWord_699435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699435).length < 2 ^ (prefixWord ++ tailWord_699435).sum := by decide
  have hdescent : baseEnd_699435 < baseStart_699435 := by decide
  rcases family_descends (prefixWord ++ tailWord_699435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699469 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_699469 : Nat := 118140960795 + 699469 * 2 ^ 59
def prefixEnd_699469 : Nat := 4983230072969 + 3 ^ 40 * 699469 * 2
def baseEnd_699469 : Nat := 359163799919829058020707

theorem tailTrace_699469 : CollatzResearch.WordTrace tailWord_699469 prefixEnd_699469 359163799919829058020707 := by
  unfold tailWord_699469
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511730302950747639629461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17007820201967165093086307 25511730302950747639629461)
  ·
    refine ⟨1195862357950816295607631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25511730302950747639629461 1195862357950816295607631)
    ·
      refine ⟨1793793536926224443411447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195862357950816295607631 1793793536926224443411447)
      ·
        refine ⟨2690690305389336665117171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793793536926224443411447 2690690305389336665117171)
        ·
          refine ⟨4036035458084004997675757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690690305389336665117171 4036035458084004997675757)
          ·
            refine ⟨1513513296781501874128409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4036035458084004997675757 1513513296781501874128409)
            ·
              refine ⟨1135134972586126405596307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513513296781501874128409 1135134972586126405596307)
              ·
                refine ⟨1702702458879189608394461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135134972586126405596307 1702702458879189608394461)
                ·
                  refine ⟨638513422079696103147923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1702702458879189608394461 638513422079696103147923)
                  ·
                    refine ⟨957770133119544154721885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638513422079696103147923 957770133119544154721885)
                    ·
                      refine ⟨359163799919829058020707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957770133119544154721885 359163799919829058020707)
                      ·
                        rfl

theorem cell23_699469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_699469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699469 prefixEnd_699469 := by exact prefixLift 699469
  have htrace : WordTrace (prefixWord ++ tailWord_699469) baseStart_699469 baseEnd_699469 := by
    simpa [prefixWord, tailWord_699469, baseEnd_699469] using wordTrace_append hprefix tailTrace_699469
  have hstable : (prefixWord ++ tailWord_699469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699469).length < 2 ^ (prefixWord ++ tailWord_699469).sum := by decide
  have hdescent : baseEnd_699469 < baseStart_699469 := by decide
  rcases family_descends (prefixWord ++ tailWord_699469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699486 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_699486 : Nat := 118140960795 + 699486 * 2 ^ 59
def prefixEnd_699486 : Nat := 4983230072969 + 3 ^ 40 * 699486 * 2
def baseEnd_699486 : Nat := 359172529090955491508129

theorem tailTrace_699486 : CollatzResearch.WordTrace tailWord_699486 prefixEnd_699486 359172529090955491508129 := by
  unfold tailWord_699486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189043792986144942874789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17008233562592773028665541 3189043792986144942874789)
  ·
    refine ⟨597945711184902176789023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3189043792986144942874789 597945711184902176789023)
    ·
      refine ⟨896918566777353265183535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597945711184902176789023 896918566777353265183535)
      ·
        refine ⟨1345377850166029897775303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896918566777353265183535 1345377850166029897775303)
        ·
          refine ⟨2018066775249044846662955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345377850166029897775303 2018066775249044846662955)
          ·
            refine ⟨3027100162873567269994433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018066775249044846662955 3027100162873567269994433)
            ·
              refine ⟨2270325122155175452495825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3027100162873567269994433 2270325122155175452495825)
              ·
                refine ⟨1702743841616381589371869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270325122155175452495825 1702743841616381589371869)
                ·
                  refine ⟨638528940606143096014451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1702743841616381589371869 638528940606143096014451)
                  ·
                    refine ⟨957793410909214644021677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638528940606143096014451 957793410909214644021677)
                    ·
                      refine ⟨359172529090955491508129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 957793410909214644021677 359172529090955491508129)
                      ·
                        rfl

theorem cell23_699486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_699486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699486 prefixEnd_699486 := by exact prefixLift 699486
  have htrace : WordTrace (prefixWord ++ tailWord_699486) baseStart_699486 baseEnd_699486 := by
    simpa [prefixWord, tailWord_699486, baseEnd_699486] using wordTrace_append hprefix tailTrace_699486
  have hstable : (prefixWord ++ tailWord_699486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699486).length < 2 ^ (prefixWord ++ tailWord_699486).sum := by decide
  have hdescent : baseEnd_699486 < baseStart_699486 := by decide
  rcases family_descends (prefixWord ++ tailWord_699486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699488 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_699488 : Nat := 118140960795 + 699488 * 2 ^ 59
def prefixEnd_699488 : Nat := 4983230072969 + 3 ^ 40 * 699488 * 2
def baseEnd_699488 : Nat := 359173556052264483683119

theorem tailTrace_699488 : CollatzResearch.WordTrace tailWord_699488 prefixEnd_699488 359173556052264483683119 := by
  unfold tailWord_699488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12756211644940956942285559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17008282193254609256380745 12756211644940956942285559)
  ·
    refine ⟨19134317467411435413428339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12756211644940956942285559 19134317467411435413428339)
    ·
      refine ⟨28701476201117153120142509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19134317467411435413428339 28701476201117153120142509)
      ·
        refine ⟨10763053575418932420053441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28701476201117153120142509 10763053575418932420053441)
        ·
          refine ⟨8072290181564199315040081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10763053575418932420053441 8072290181564199315040081)
          ·
            refine ⟨6054217636173149486280061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8072290181564199315040081 6054217636173149486280061)
            ·
              refine ⟨2270331613564931057355023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6054217636173149486280061 2270331613564931057355023)
              ·
                refine ⟨3405497420347396586032535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270331613564931057355023 3405497420347396586032535)
                ·
                  refine ⟨5108246130521094879048803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405497420347396586032535 5108246130521094879048803)
                  ·
                    refine ⟨7662369195781642318573205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5108246130521094879048803 7662369195781642318573205)
                    ·
                      refine ⟨359173556052264483683119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7662369195781642318573205 359173556052264483683119)
                      ·
                        rfl

theorem cell23_699488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_699488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699488 prefixEnd_699488 := by exact prefixLift 699488
  have htrace : WordTrace (prefixWord ++ tailWord_699488) baseStart_699488 baseEnd_699488 := by
    simpa [prefixWord, tailWord_699488, baseEnd_699488] using wordTrace_append hprefix tailTrace_699488
  have hstable : (prefixWord ++ tailWord_699488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699488).length < 2 ^ (prefixWord ++ tailWord_699488).sum := by decide
  have hdescent : baseEnd_699488 < baseStart_699488 := by decide
  rcases family_descends (prefixWord ++ tailWord_699488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699552 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 3, 3, 2]
def baseStart_699552 : Nat := 118140960795 + 699552 * 2 ^ 59
def prefixEnd_699552 : Nat := 4983230072969 + 3 ^ 40 * 699552 * 2
def baseEnd_699552 : Nat := 359206418814152233282825

theorem tailTrace_699552 : CollatzResearch.WordTrace tailWord_699552 prefixEnd_699552 359206418814152233282825 := by
  unfold tailWord_699552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757378780825026407450455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17009838374433368543267273 12757378780825026407450455)
  ·
    refine ⟨19136068171237539611175683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12757378780825026407450455 19136068171237539611175683)
    ·
      refine ⟨28704102256856309416763525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19136068171237539611175683 28704102256856309416763525)
      ·
        refine ⟨5382019173160558015643161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28704102256856309416763525 5382019173160558015643161)
        ·
          refine ⟨4036514379870418511732371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382019173160558015643161 4036514379870418511732371)
          ·
            refine ⟨6054771569805627767598557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036514379870418511732371 6054771569805627767598557)
            ·
              refine ⟨2270539338677110412849459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6054771569805627767598557 2270539338677110412849459)
              ·
                refine ⟨3405809008015665619274189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270539338677110412849459 3405809008015665619274189)
                ·
                  refine ⟨1277178378005874607227821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3405809008015665619274189 1277178378005874607227821)
                  ·
                    refine ⟨478941891752202977710433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277178378005874607227821 478941891752202977710433)
                    ·
                      refine ⟨359206418814152233282825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 478941891752202977710433 359206418814152233282825)
                      ·
                        rfl

theorem cell23_699552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_699552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699552 prefixEnd_699552 := by exact prefixLift 699552
  have htrace : WordTrace (prefixWord ++ tailWord_699552) baseStart_699552 baseEnd_699552 := by
    simpa [prefixWord, tailWord_699552, baseEnd_699552] using wordTrace_append hprefix tailTrace_699552
  have hstable : (prefixWord ++ tailWord_699552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699552).length < 2 ^ (prefixWord ++ tailWord_699552).sum := by decide
  have hdescent : baseEnd_699552 < baseStart_699552 := by decide
  rcases family_descends (prefixWord ++ tailWord_699552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699578 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_699578 : Nat := 118140960795 + 699578 * 2 ^ 59
def prefixEnd_699578 : Nat := 4983230072969 + 3 ^ 40 * 699578 * 2
def baseEnd_699578 : Nat := 359219769311169131557705

theorem tailTrace_699578 : CollatzResearch.WordTrace tailWord_699578 prefixEnd_699578 359219769311169131557705 := by
  unfold tailWord_699578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6378926464888964813836847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17010470573037239503564925 6378926464888964813836847)
  ·
    refine ⟨9568389697333447220755271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6378926464888964813836847 9568389697333447220755271)
    ·
      refine ⟨14352584546000170831132907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9568389697333447220755271 14352584546000170831132907)
      ·
        refine ⟨21528876819000256246699361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14352584546000170831132907 21528876819000256246699361)
        ·
          refine ⟨16146657614250192185024521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21528876819000256246699361 16146657614250192185024521)
          ·
            refine ⟨12109993210687644138768391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16146657614250192185024521 12109993210687644138768391)
            ·
              refine ⟨18164989816031466208152587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12109993210687644138768391 18164989816031466208152587)
              ·
                refine ⟨27247484724047199312228881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18164989816031466208152587 27247484724047199312228881)
                ·
                  refine ⟨20435613543035399484171661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27247484724047199312228881 20435613543035399484171661)
                  ·
                    refine ⟨7663355078638274806564373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20435613543035399484171661 7663355078638274806564373)
                    ·
                      refine ⟨359219769311169131557705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7663355078638274806564373 359219769311169131557705)
                      ·
                        rfl

theorem cell23_699578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_699578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699578 prefixEnd_699578 := by exact prefixLift 699578
  have htrace : WordTrace (prefixWord ++ tailWord_699578) baseStart_699578 baseEnd_699578 := by
    simpa [prefixWord, tailWord_699578, baseEnd_699578] using wordTrace_append hprefix tailTrace_699578
  have hstable : (prefixWord ++ tailWord_699578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699578).length < 2 ^ (prefixWord ++ tailWord_699578).sum := by decide
  have hdescent : baseEnd_699578 < baseStart_699578 := by decide
  rcases family_descends (prefixWord ++ tailWord_699578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699605 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 9]
def baseStart_699605 : Nat := 118140960795 + 699605 * 2 ^ 59
def prefixEnd_699605 : Nat := 4983230072969 + 3 ^ 40 * 699605 * 2
def baseEnd_699605 : Nat := 39914848143204502880009

theorem tailTrace_699605 : CollatzResearch.WordTrace tailWord_699605 prefixEnd_699605 39914848143204502880009 := by
  unfold tailWord_699605
  simp only [CollatzResearch.WordTrace]
  refine ⟨25516690630458042866580269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17011127086972028577720179 25516690630458042866580269)
  ·
    refine ⟨9568758986421766074967601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25516690630458042866580269 9568758986421766074967601)
    ·
      refine ⟨7176569239816324556225701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9568758986421766074967601 7176569239816324556225701)
      ·
        refine ⟨1345606732465560854292319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7176569239816324556225701 1345606732465560854292319)
        ·
          refine ⟨2018410098698341281438479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345606732465560854292319 2018410098698341281438479)
          ·
            refine ⟨3027615148047511922157719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018410098698341281438479 3027615148047511922157719)
            ·
              refine ⟨4541422722071267883236579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027615148047511922157719 4541422722071267883236579)
              ·
                refine ⟨6812134083106901824854869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541422722071267883236579 6812134083106901824854869)
                ·
                  refine ⟨39914848143204502880009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6812134083106901824854869 39914848143204502880009)
                  ·
                    rfl

theorem cell23_699605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_699605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699605 prefixEnd_699605 := by exact prefixLift 699605
  have htrace : WordTrace (prefixWord ++ tailWord_699605) baseStart_699605 baseEnd_699605 := by
    simpa [prefixWord, tailWord_699605, baseEnd_699605] using wordTrace_append hprefix tailTrace_699605
  have hstable : (prefixWord ++ tailWord_699605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699605).length < 2 ^ (prefixWord ++ tailWord_699605).sum := by decide
  have hdescent : baseEnd_699605 < baseStart_699605 := by decide
  rcases family_descends (prefixWord ++ tailWord_699605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699650 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_699650 : Nat := 118140960795 + 699650 * 2 ^ 59
def prefixEnd_699650 : Nat := 4983230072969 + 3 ^ 40 * 699650 * 2
def baseEnd_699650 : Nat := 359256739918292849857375

theorem tailTrace_699650 : CollatzResearch.WordTrace tailWord_699650 prefixEnd_699650 359256739918292849857375 := by
  unfold tailWord_699650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379582978823753887992101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17012221276863343701312269 6379582978823753887992101)
  ·
    refine ⟨1196171808529453853998519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6379582978823753887992101 1196171808529453853998519)
    ·
      refine ⟨1794257712794180780997779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196171808529453853998519 1794257712794180780997779)
      ·
        refine ⟨2691386569191271171496669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794257712794180780997779 2691386569191271171496669)
        ·
          refine ⟨1009269963446726689311251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2691386569191271171496669 1009269963446726689311251)
          ·
            refine ⟨1513904945170090033966877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009269963446726689311251 1513904945170090033966877)
            ·
              refine ⟨567714354438783762737579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513904945170090033966877 567714354438783762737579)
              ·
                refine ⟨851571531658175644106369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567714354438783762737579 851571531658175644106369)
                ·
                  refine ⟨638678648743631733079777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 851571531658175644106369 638678648743631733079777)
                  ·
                    refine ⟨479008986557723799809833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 638678648743631733079777 479008986557723799809833)
                    ·
                      refine ⟨359256739918292849857375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479008986557723799809833 359256739918292849857375)
                      ·
                        rfl

theorem cell23_699650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_699650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699650 prefixEnd_699650 := by exact prefixLift 699650
  have htrace : WordTrace (prefixWord ++ tailWord_699650) baseStart_699650 baseEnd_699650 := by
    simpa [prefixWord, tailWord_699650, baseEnd_699650] using wordTrace_append hprefix tailTrace_699650
  have hstable : (prefixWord ++ tailWord_699650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699650).length < 2 ^ (prefixWord ++ tailWord_699650).sum := by decide
  have hdescent : baseEnd_699650 < baseStart_699650 := by decide
  rcases family_descends (prefixWord ++ tailWord_699650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699695 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 6]
def baseStart_699695 : Nat := 118140960795 + 699695 * 2 ^ 59
def prefixEnd_699695 : Nat := 4983230072969 + 3 ^ 40 * 699695 * 2
def baseEnd_699695 : Nat := 39919982949749463754963

theorem tailTrace_699695 : CollatzResearch.WordTrace tailWord_699695 prefixEnd_699695 39919982949749463754963 := by
  unfold tailWord_699695
  simp only [CollatzResearch.WordTrace]
  refine ⟨25519973200131988237356539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17013315466754658824904359 25519973200131988237356539)
  ·
    refine ⟨38279959800197982356034809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25519973200131988237356539 38279959800197982356034809)
    ·
      refine ⟨28709969850148486767026107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38279959800197982356034809 28709969850148486767026107)
      ·
        refine ⟨43064954775222730150539161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28709969850148486767026107 43064954775222730150539161)
        ·
          refine ⟨32298716081417047612904371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43064954775222730150539161 32298716081417047612904371)
          ·
            refine ⟨48448074122125571419356557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32298716081417047612904371 48448074122125571419356557)
            ·
              refine ⟨18168027795797089282258709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48448074122125571419356557 18168027795797089282258709)
              ·
                refine ⟨851626302927988560105877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18168027795797089282258709 851626302927988560105877)
                ·
                  refine ⟨39919982949749463754963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 851626302927988560105877 39919982949749463754963)
                  ·
                    rfl

theorem cell23_699695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 6].length) (baseStart_699695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699695 prefixEnd_699695 := by exact prefixLift 699695
  have htrace : WordTrace (prefixWord ++ tailWord_699695) baseStart_699695 baseEnd_699695 := by
    simpa [prefixWord, tailWord_699695, baseEnd_699695] using wordTrace_append hprefix tailTrace_699695
  have hstable : (prefixWord ++ tailWord_699695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699695).length < 2 ^ (prefixWord ++ tailWord_699695).sum := by decide
  have hdescent : baseEnd_699695 < baseStart_699695 := by decide
  rcases family_descends (prefixWord ++ tailWord_699695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699699 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 3, 4]
def baseStart_699699 : Nat := 118140960795 + 699699 * 2 ^ 59
def prefixEnd_699699 : Nat := 4983230072969 + 3 ^ 40 * 699699 * 2
def baseEnd_699699 : Nat := 119760633490121052714883

theorem tailTrace_699699 : CollatzResearch.WordTrace tailWord_699699 prefixEnd_699699 119760633490121052714883 := by
  unfold tailWord_699699
  simp only [CollatzResearch.WordTrace]
  refine ⟨25520119092117496920502151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17013412728078331280334767 25520119092117496920502151)
  ·
    refine ⟨38280178638176245380753227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25520119092117496920502151 38280178638176245380753227)
    ·
      refine ⟨57420267957264368071129841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38280178638176245380753227 57420267957264368071129841)
      ·
        refine ⟨43065200967948276053347381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57420267957264368071129841 43065200967948276053347381)
        ·
          refine ⟨4037362590745150880001317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43065200967948276053347381 4037362590745150880001317)
          ·
            refine ⟨757005485764715790000247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4037362590745150880001317 757005485764715790000247)
            ·
              refine ⟨1135508228647073685000371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757005485764715790000247 1135508228647073685000371)
              ·
                refine ⟨1703262342970610527500557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135508228647073685000371 1703262342970610527500557)
                ·
                  refine ⟨638723378613978947812709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1703262342970610527500557 638723378613978947812709)
                  ·
                    refine ⟨119760633490121052714883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638723378613978947812709 119760633490121052714883)
                    ·
                      rfl

theorem cell23_699699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 4].length) (baseStart_699699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699699 prefixEnd_699699 := by exact prefixLift 699699
  have htrace : WordTrace (prefixWord ++ tailWord_699699) baseStart_699699 baseEnd_699699 := by
    simpa [prefixWord, tailWord_699699, baseEnd_699699] using wordTrace_append hprefix tailTrace_699699
  have hstable : (prefixWord ++ tailWord_699699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699699).length < 2 ^ (prefixWord ++ tailWord_699699).sum := by decide
  have hdescent : baseEnd_699699 < baseStart_699699 := by decide
  rcases family_descends (prefixWord ++ tailWord_699699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699749 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 2, 3, 2]
def baseStart_699749 : Nat := 118140960795 + 699749 * 2 ^ 59
def prefixEnd_699749 : Nat := 4983230072969 + 3 ^ 40 * 699749 * 2
def baseEnd_699749 : Nat := 359307574503087962519419

theorem tailTrace_699749 : CollatzResearch.WordTrace tailWord_699749 prefixEnd_699749 359307574503087962519419 := by
  unfold tailWord_699749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25521942741936355459822301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17014628494624236973214867 25521942741936355459822301)
  ·
    refine ⟨9570728528226133297433363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25521942741936355459822301 9570728528226133297433363)
    ·
      refine ⟨14356092792339199946150045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9570728528226133297433363 14356092792339199946150045)
      ·
        refine ⟨5383534797127199979806267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14356092792339199946150045 5383534797127199979806267)
        ·
          refine ⟨8075302195690799969709401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5383534797127199979806267 8075302195690799969709401)
          ·
            refine ⟨6056476646768099977282051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8075302195690799969709401 6056476646768099977282051)
            ·
              refine ⟨9084714970152149965923077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056476646768099977282051 9084714970152149965923077)
              ·
                refine ⟨1703384056903528118610577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9084714970152149965923077 1703384056903528118610577)
                ·
                  refine ⟨1277538042677646088957933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1703384056903528118610577 1277538042677646088957933)
                  ·
                    refine ⟨479076766004117283359225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277538042677646088957933 479076766004117283359225)
                    ·
                      refine ⟨359307574503087962519419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479076766004117283359225 359307574503087962519419)
                      ·
                        rfl

theorem cell23_699749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_699749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699749 prefixEnd_699749 := by exact prefixLift 699749
  have htrace : WordTrace (prefixWord ++ tailWord_699749) baseStart_699749 baseEnd_699749 := by
    simpa [prefixWord, tailWord_699749, baseEnd_699749] using wordTrace_append hprefix tailTrace_699749
  have hstable : (prefixWord ++ tailWord_699749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699749).length < 2 ^ (prefixWord ++ tailWord_699749).sum := by decide
  have hdescent : baseEnd_699749 < baseStart_699749 := by decide
  rcases family_descends (prefixWord ++ tailWord_699749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699762 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_699762 : Nat := 118140960795 + 699762 * 2 ^ 59
def prefixEnd_699762 : Nat := 4983230072969 + 3 ^ 40 * 699762 * 2
def baseEnd_699762 : Nat := 359314249751596411656859

theorem tailTrace_699762 : CollatzResearch.WordTrace tailWord_699762 prefixEnd_699762 359314249751596411656859 := by
  unfold tailWord_699762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380604222722314670011385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17014944593926172453363693 6380604222722314670011385)
  ·
    refine ⟨4785453167041736002508539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6380604222722314670011385 4785453167041736002508539)
    ·
      refine ⟨7178179750562604003762809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785453167041736002508539 7178179750562604003762809)
      ·
        refine ⟨5383634812921953002822107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7178179750562604003762809 5383634812921953002822107)
        ·
          refine ⟨8075452219382929504233161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5383634812921953002822107 8075452219382929504233161)
          ·
            refine ⟨6056589164537197128174871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8075452219382929504233161 6056589164537197128174871)
            ·
              refine ⟨9084883746805795692262307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056589164537197128174871 9084883746805795692262307)
              ·
                refine ⟨13627325620208693538393461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9084883746805795692262307 13627325620208693538393461)
                ·
                  refine ⟨1277561776894565019224387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13627325620208693538393461 1277561776894565019224387)
                  ·
                    refine ⟨1916342665341847528836581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1277561776894565019224387 1916342665341847528836581)
                    ·
                      refine ⟨359314249751596411656859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1916342665341847528836581 359314249751596411656859)
                      ·
                        rfl

theorem cell23_699762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_699762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699762 prefixEnd_699762 := by exact prefixLift 699762
  have htrace : WordTrace (prefixWord ++ tailWord_699762) baseStart_699762 baseEnd_699762 := by
    simpa [prefixWord, tailWord_699762, baseEnd_699762] using wordTrace_append hprefix tailTrace_699762
  have hstable : (prefixWord ++ tailWord_699762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699762).length < 2 ^ (prefixWord ++ tailWord_699762).sum := by decide
  have hdescent : baseEnd_699762 < baseStart_699762 := by decide
  rcases family_descends (prefixWord ++ tailWord_699762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699772 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_699772 : Nat := 118140960795 + 699772 * 2 ^ 59
def prefixEnd_699772 : Nat := 4983230072969 + 3 ^ 40 * 699772 * 2
def baseEnd_699772 : Nat := 119773128186047124177271

theorem tailTrace_699772 : CollatzResearch.WordTrace tailWord_699772 prefixEnd_699772 119773128186047124177271 := by
  unfold tailWord_699772
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761390810426515193954785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17015187747235353591939713 12761390810426515193954785)
  ·
    refine ⟨9571043107819886395466089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12761390810426515193954785 9571043107819886395466089)
    ·
      refine ⟨7178282330864914796599567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9571043107819886395466089 7178282330864914796599567)
      ·
        refine ⟨10767423496297372194899351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7178282330864914796599567 10767423496297372194899351)
        ·
          refine ⟨16151135244446058292349027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10767423496297372194899351 16151135244446058292349027)
          ·
            refine ⟨24226702866669087438523541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16151135244446058292349027 24226702866669087438523541)
            ·
              refine ⟨1135626696875113473680791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24226702866669087438523541 1135626696875113473680791)
              ·
                refine ⟨1703440045312670210521187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135626696875113473680791 1703440045312670210521187)
                ·
                  refine ⟨2555160067969005315781781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703440045312670210521187 2555160067969005315781781)
                  ·
                    refine ⟨119773128186047124177271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2555160067969005315781781 119773128186047124177271)
                    ·
                      rfl

theorem cell23_699772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_699772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699772 prefixEnd_699772 := by exact prefixLift 699772
  have htrace : WordTrace (prefixWord ++ tailWord_699772) baseStart_699772 baseEnd_699772 := by
    simpa [prefixWord, tailWord_699772, baseEnd_699772] using wordTrace_append hprefix tailTrace_699772
  have hstable : (prefixWord ++ tailWord_699772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699772).length < 2 ^ (prefixWord ++ tailWord_699772).sum := by decide
  have hdescent : baseEnd_699772 < baseStart_699772 := by decide
  rcases family_descends (prefixWord ++ tailWord_699772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699790 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_699790 : Nat := 118140960795 + 699790 * 2 ^ 59
def prefixEnd_699790 : Nat := 4983230072969 + 3 ^ 40 * 699790 * 2
def baseEnd_699790 : Nat := 359328627209922302106731

theorem tailTrace_699790 : CollatzResearch.WordTrace tailWord_699790 prefixEnd_699790 359328627209922302106731 := by
  unfold tailWord_699790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190429766848477432758103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17015625423191879641376549 3190429766848477432758103)
  ·
    refine ⟨4785644650272716149137155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190429766848477432758103 4785644650272716149137155)
    ·
      refine ⟨7178466975409074223705733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785644650272716149137155 7178466975409074223705733)
      ·
        refine ⟨1345962557889201416944825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7178466975409074223705733 1345962557889201416944825)
        ·
          refine ⟨1009471918416901062708619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345962557889201416944825 1009471918416901062708619)
          ·
            refine ⟨1514207877625351594062929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009471918416901062708619 1514207877625351594062929)
            ·
              refine ⟨1135655908219013695547197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514207877625351594062929 1135655908219013695547197)
              ·
                refine ⟨425870965582130135830199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1135655908219013695547197 425870965582130135830199)
                ·
                  refine ⟨638806448373195203745299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425870965582130135830199 638806448373195203745299)
                  ·
                    refine ⟨958209672559792805617949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638806448373195203745299 958209672559792805617949)
                    ·
                      refine ⟨359328627209922302106731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958209672559792805617949 359328627209922302106731)
                      ·
                        rfl

theorem cell23_699790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_699790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699790 prefixEnd_699790 := by exact prefixLift 699790
  have htrace : WordTrace (prefixWord ++ tailWord_699790) baseStart_699790 baseEnd_699790 := by
    simpa [prefixWord, tailWord_699790, baseEnd_699790] using wordTrace_append hprefix tailTrace_699790
  have hstable : (prefixWord ++ tailWord_699790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699790).length < 2 ^ (prefixWord ++ tailWord_699790).sum := by decide
  have hdescent : baseEnd_699790 < baseStart_699790 := by decide
  rcases family_descends (prefixWord ++ tailWord_699790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699796 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_699796 : Nat := 118140960795 + 699796 * 2 ^ 59
def prefixEnd_699796 : Nat := 4983230072969 + 3 ^ 40 * 699796 * 2
def baseEnd_699796 : Nat := 359331708093849278631703

theorem tailTrace_699796 : CollatzResearch.WordTrace tailWord_699796 prefixEnd_699796 359331708093849278631703 := by
  unfold tailWord_699796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761828486383041243391621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17015771315177388324522161 12761828486383041243391621)
  ·
    refine ⟨2392842841196820233135929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12761828486383041243391621 2392842841196820233135929)
    ·
      refine ⟨1794632130897615174851947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2392842841196820233135929 1794632130897615174851947)
      ·
        refine ⟨2691948196346422762277921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794632130897615174851947 2691948196346422762277921)
        ·
          refine ⟨2018961147259817071708441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691948196346422762277921 2018961147259817071708441)
          ·
            refine ⟨1514220860444862803781331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018961147259817071708441 1514220860444862803781331)
            ·
              refine ⟨2271331290667294205671997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514220860444862803781331 2271331290667294205671997)
              ·
                refine ⟨851749234000235327126999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2271331290667294205671997 851749234000235327126999)
                ·
                  refine ⟨1277623851000352990690499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851749234000235327126999 1277623851000352990690499)
                  ·
                    refine ⟨1916435776500529486035749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1277623851000352990690499 1916435776500529486035749)
                    ·
                      refine ⟨359331708093849278631703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1916435776500529486035749 359331708093849278631703)
                      ·
                        rfl

theorem cell23_699796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_699796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699796 prefixEnd_699796 := by exact prefixLift 699796
  have htrace : WordTrace (prefixWord ++ tailWord_699796) baseStart_699796 baseEnd_699796 := by
    simpa [prefixWord, tailWord_699796, baseEnd_699796] using wordTrace_append hprefix tailTrace_699796
  have hstable : (prefixWord ++ tailWord_699796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699796).length < 2 ^ (prefixWord ++ tailWord_699796).sum := by decide
  have hdescent : baseEnd_699796 < baseStart_699796 := by decide
  rcases family_descends (prefixWord ++ tailWord_699796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699816 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_699816 : Nat := 118140960795 + 699816 * 2 ^ 59
def prefixEnd_699816 : Nat := 4983230072969 + 3 ^ 40 * 699816 * 2
def baseEnd_699816 : Nat := 359341977706939200381611

theorem tailTrace_699816 : CollatzResearch.WordTrace tailWord_699816 prefixEnd_699816 359341977706939200381611 := by
  unfold tailWord_699816
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762193216346812951255651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17016257621795750601674201 12762193216346812951255651)
  ·
    refine ⟨19143289824520219426883477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12762193216346812951255651 19143289824520219426883477)
    ·
      refine ⟨897341710524385285635163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19143289824520219426883477 897341710524385285635163)
      ·
        refine ⟨1346012565786577928452745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897341710524385285635163 1346012565786577928452745)
        ·
          refine ⟨1009509424339933446339559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346012565786577928452745 1009509424339933446339559)
          ·
            refine ⟨1514264136509900169509339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009509424339933446339559 1514264136509900169509339)
            ·
              refine ⟨2271396204764850254264009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514264136509900169509339 2271396204764850254264009)
              ·
                refine ⟨1703547153573637690698007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271396204764850254264009 1703547153573637690698007)
                ·
                  refine ⟨2555320730360456536047011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703547153573637690698007 2555320730360456536047011)
                  ·
                    refine ⟨3832981095540684804070517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2555320730360456536047011 3832981095540684804070517)
                    ·
                      refine ⟨359341977706939200381611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3832981095540684804070517 359341977706939200381611)
                      ·
                        rfl

theorem cell23_699816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_699816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699816 prefixEnd_699816 := by exact prefixLift 699816
  have htrace : WordTrace (prefixWord ++ tailWord_699816) baseStart_699816 baseEnd_699816 := by
    simpa [prefixWord, tailWord_699816, baseEnd_699816] using wordTrace_append hprefix tailTrace_699816
  have hstable : (prefixWord ++ tailWord_699816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699816).length < 2 ^ (prefixWord ++ tailWord_699816).sum := by decide
  have hdescent : baseEnd_699816 < baseStart_699816 := by decide
  rcases family_descends (prefixWord ++ tailWord_699816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699836 : List Nat := [2, 2, 2, 4, 2, 2, 2, 7]
def baseStart_699836 : Nat := 118140960795 + 699836 * 2 ^ 59
def prefixEnd_699836 : Nat := 4983230072969 + 3 ^ 40 * 699836 * 2
def baseEnd_699836 : Nat := 13309342493334411930797

theorem tailTrace_699836 : CollatzResearch.WordTrace tailWord_699836 prefixEnd_699836 13309342493334411930797 := by
  unfold tailWord_699836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762557946310584659119681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17016743928414112878826241 12762557946310584659119681)
  ·
    refine ⟨9571918459732938494339761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12762557946310584659119681 9571918459732938494339761)
    ·
      refine ⟨7178938844799703870754821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9571918459732938494339761 7178938844799703870754821)
      ·
        refine ⟨1346051033399944475766529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7178938844799703870754821 1346051033399944475766529)
        ·
          refine ⟨1009538275049958356824897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346051033399944475766529 1009538275049958356824897)
          ·
            refine ⟨757153706287468767618673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009538275049958356824897 757153706287468767618673)
            ·
              refine ⟨567865279715601575714005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757153706287468767618673 567865279715601575714005)
              ·
                refine ⟨13309342493334411930797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 567865279715601575714005 13309342493334411930797)
                ·
                  rfl

theorem cell23_699836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 7].length) (baseStart_699836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699836 prefixEnd_699836 := by exact prefixLift 699836
  have htrace : WordTrace (prefixWord ++ tailWord_699836) baseStart_699836 baseEnd_699836 := by
    simpa [prefixWord, tailWord_699836, baseEnd_699836] using wordTrace_append hprefix tailTrace_699836
  have hstable : (prefixWord ++ tailWord_699836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699836).length < 2 ^ (prefixWord ++ tailWord_699836).sum := by decide
  have hdescent : baseEnd_699836 < baseStart_699836 := by decide
  rcases family_descends (prefixWord ++ tailWord_699836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699839 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 3, 3, 2]
def baseStart_699839 : Nat := 118140960795 + 699839 * 2 ^ 59
def prefixEnd_699839 : Nat := 4983230072969 + 3 ^ 40 * 699839 * 2
def baseEnd_699839 : Nat := 359353787761992610394005

theorem tailTrace_699839 : CollatzResearch.WordTrace tailWord_699839 prefixEnd_699839 359353787761992610394005 := by
  unfold tailWord_699839
  simp only [CollatzResearch.WordTrace]
  refine ⟨25525225311610300830598571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17016816874406867220399047 25525225311610300830598571)
  ·
    refine ⟨38287837967415451245897857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25525225311610300830598571 38287837967415451245897857)
    ·
      refine ⟨28715878475561588434423393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38287837967415451245897857 28715878475561588434423393)
      ·
        refine ⟨21536908856671191325817545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28715878475561588434423393 21536908856671191325817545)
        ·
          refine ⟨16152681642503393494363159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21536908856671191325817545 16152681642503393494363159)
          ·
            refine ⟨24229022463755090241544739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16152681642503393494363159 24229022463755090241544739)
            ·
              refine ⟨36343533695632635362317109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24229022463755090241544739 36343533695632635362317109)
              ·
                refine ⟨3407206283965559565217229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36343533695632635362317109 3407206283965559565217229)
                ·
                  refine ⟨1277702356487084836956461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3407206283965559565217229 1277702356487084836956461)
                  ·
                    refine ⟨479138383682656813858673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277702356487084836956461 479138383682656813858673)
                    ·
                      refine ⟨359353787761992610394005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479138383682656813858673 359353787761992610394005)
                      ·
                        rfl

theorem cell23_699839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_699839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699839 prefixEnd_699839 := by exact prefixLift 699839
  have htrace : WordTrace (prefixWord ++ tailWord_699839) baseStart_699839 baseEnd_699839 := by
    simpa [prefixWord, tailWord_699839, baseEnd_699839] using wordTrace_append hprefix tailTrace_699839
  have hstable : (prefixWord ++ tailWord_699839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699839).length < 2 ^ (prefixWord ++ tailWord_699839).sum := by decide
  have hdescent : baseEnd_699839 < baseStart_699839 := by decide
  rcases family_descends (prefixWord ++ tailWord_699839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699886 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_699886 : Nat := 118140960795 + 699886 * 2 ^ 59
def prefixEnd_699886 : Nat := 4983230072969 + 3 ^ 40 * 699886 * 2
def baseEnd_699886 : Nat := 359377921352753926506289

theorem tailTrace_699886 : CollatzResearch.WordTrace tailWord_699886 prefixEnd_699886 359377921352753926506289 := by
  unfold tailWord_699886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190867442805003482194939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17017959694960018571706341 3190867442805003482194939)
  ·
    refine ⟨4786301164207505223292409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190867442805003482194939 4786301164207505223292409)
    ·
      refine ⟨3589725873155628917469307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4786301164207505223292409 3589725873155628917469307)
      ·
        refine ⟨5384588809733443376203961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589725873155628917469307 5384588809733443376203961)
        ·
          refine ⟨4038441607300082532152971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5384588809733443376203961 4038441607300082532152971)
          ·
            refine ⟨6057662410950123798229457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038441607300082532152971 6057662410950123798229457)
            ·
              refine ⟨4543246808212592848672093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6057662410950123798229457 4543246808212592848672093)
              ·
                refine ⟨1703717553079722318252035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4543246808212592848672093 1703717553079722318252035)
                ·
                  refine ⟨2555576329619583477378053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703717553079722318252035 2555576329619583477378053)
                  ·
                    refine ⟨479170561803671902008385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2555576329619583477378053 479170561803671902008385)
                    ·
                      refine ⟨359377921352753926506289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479170561803671902008385 359377921352753926506289)
                      ·
                        rfl

theorem cell23_699886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_699886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699886 prefixEnd_699886 := by exact prefixLift 699886
  have htrace : WordTrace (prefixWord ++ tailWord_699886) baseStart_699886 baseEnd_699886 := by
    simpa [prefixWord, tailWord_699886, baseEnd_699886] using wordTrace_append hprefix tailTrace_699886
  have hstable : (prefixWord ++ tailWord_699886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699886).length < 2 ^ (prefixWord ++ tailWord_699886).sum := by decide
  have hdescent : baseEnd_699886 < baseStart_699886 := by decide
  rcases family_descends (prefixWord ++ tailWord_699886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699890 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_699890 : Nat := 118140960795 + 699890 * 2 ^ 59
def prefixEnd_699890 : Nat := 4983230072969 + 3 ^ 40 * 699890 * 2
def baseEnd_699890 : Nat := 359379975275371910856271

theorem tailTrace_699890 : CollatzResearch.WordTrace tailWord_699890 prefixEnd_699890 359379975275371910856271 := by
  unfold tailWord_699890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381771358606384135176281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17018056956283691027136749 6381771358606384135176281)
  ·
    refine ⟨4786328518954788101382211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6381771358606384135176281 4786328518954788101382211)
    ·
      refine ⟨7179492778432182152073317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786328518954788101382211 7179492778432182152073317)
      ·
        refine ⟨1346154895956034153513747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7179492778432182152073317 1346154895956034153513747)
        ·
          refine ⟨2019232343934051230270621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346154895956034153513747 2019232343934051230270621)
          ·
            refine ⟨757212128975269211351483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2019232343934051230270621 757212128975269211351483)
            ·
              refine ⟨1135818193462903817027225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757212128975269211351483 1135818193462903817027225)
              ·
                refine ⟨851863645097177862770419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135818193462903817027225 851863645097177862770419)
                ·
                  refine ⟨1277795467645766794155629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851863645097177862770419 1277795467645766794155629)
                  ·
                    refine ⟨479173300367162547808361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277795467645766794155629 479173300367162547808361)
                    ·
                      refine ⟨359379975275371910856271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479173300367162547808361 359379975275371910856271)
                      ·
                        rfl

theorem cell23_699890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_699890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699890 prefixEnd_699890 := by exact prefixLift 699890
  have htrace : WordTrace (prefixWord ++ tailWord_699890) baseStart_699890 baseEnd_699890 := by
    simpa [prefixWord, tailWord_699890, baseEnd_699890] using wordTrace_append hprefix tailTrace_699890
  have hstable : (prefixWord ++ tailWord_699890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699890).length < 2 ^ (prefixWord ++ tailWord_699890).sum := by decide
  have hdescent : baseEnd_699890 < baseStart_699890 := by decide
  rcases family_descends (prefixWord ++ tailWord_699890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699906 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_699906 : Nat := 118140960795 + 699906 * 2 ^ 59
def prefixEnd_699906 : Nat := 4983230072969 + 3 ^ 40 * 699906 * 2
def baseEnd_699906 : Nat := 359388190965843848256197

theorem tailTrace_699906 : CollatzResearch.WordTrace tailWord_699906 prefixEnd_699906 359388190965843848256197 := by
  unfold tailWord_699906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381917250591892818321893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17018446001578380848858381 6381917250591892818321893)
  ·
    refine ⟨1196609484485979903435355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6381917250591892818321893 1196609484485979903435355)
    ·
      refine ⟨1794914226728969855153033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196609484485979903435355 1794914226728969855153033)
      ·
        refine ⟨1346185670046727391364775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794914226728969855153033 1346185670046727391364775)
        ·
          refine ⟨2019278505070091087047163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346185670046727391364775 2019278505070091087047163)
          ·
            refine ⟨3028917757605136630570745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019278505070091087047163 3028917757605136630570745)
            ·
              refine ⟨2271688318203852472928059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3028917757605136630570745 2271688318203852472928059)
              ·
                refine ⟨3407532477305778709392089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271688318203852472928059 3407532477305778709392089)
                ·
                  refine ⟨2555649357979334032044067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3407532477305778709392089 2555649357979334032044067)
                  ·
                    refine ⟨3833474036969001048066101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2555649357979334032044067 3833474036969001048066101)
                    ·
                      refine ⟨359388190965843848256197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3833474036969001048066101 359388190965843848256197)
                      ·
                        rfl

theorem cell23_699906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_699906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699906 prefixEnd_699906 := by exact prefixLift 699906
  have htrace : WordTrace (prefixWord ++ tailWord_699906) baseStart_699906 baseEnd_699906 := by
    simpa [prefixWord, tailWord_699906, baseEnd_699906] using wordTrace_append hprefix tailTrace_699906
  have hstable : (prefixWord ++ tailWord_699906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699906).length < 2 ^ (prefixWord ++ tailWord_699906).sum := by decide
  have hdescent : baseEnd_699906 < baseStart_699906 := by decide
  rcases family_descends (prefixWord ++ tailWord_699906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699909 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 5]
def baseStart_699909 : Nat := 118140960795 + 699909 * 2 ^ 59
def prefixEnd_699909 : Nat := 4983230072969 + 3 ^ 40 * 699909 * 2
def baseEnd_699909 : Nat := 39932192378645259613187

theorem tailTrace_699909 : CollatzResearch.WordTrace tailWord_699909 prefixEnd_699909 39932192378645259613187 := by
  unfold tailWord_699909
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527778421356702785646781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17018518947571135190431187 25527778421356702785646781)
  ·
    refine ⟨9572916908008763544617543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25527778421356702785646781 9572916908008763544617543)
    ·
      refine ⟨14359375362013145316926315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9572916908008763544617543 14359375362013145316926315)
      ·
        refine ⟨21539063043019717975389473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14359375362013145316926315 21539063043019717975389473)
        ·
          refine ⟨16154297282264788481542105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21539063043019717975389473 16154297282264788481542105)
          ·
            refine ⟨12115722961698591361156579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16154297282264788481542105 12115722961698591361156579)
            ·
              refine ⟨18173584442547887041734869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12115722961698591361156579 18173584442547887041734869)
              ·
                refine ⟨425943385372216102540661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18173584442547887041734869 425943385372216102540661)
                ·
                  refine ⟨39932192378645259613187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 425943385372216102540661 39932192378645259613187)
                  ·
                    rfl

theorem cell23_699909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_699909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699909 prefixEnd_699909 := by exact prefixLift 699909
  have htrace : WordTrace (prefixWord ++ tailWord_699909) baseStart_699909 baseEnd_699909 := by
    simpa [prefixWord, tailWord_699909, baseEnd_699909] using wordTrace_append hprefix tailTrace_699909
  have hstable : (prefixWord ++ tailWord_699909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699909).length < 2 ^ (prefixWord ++ tailWord_699909).sum := by decide
  have hdescent : baseEnd_699909 < baseStart_699909 := by decide
  rcases family_descends (prefixWord ++ tailWord_699909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699936 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_699936 : Nat := 118140960795 + 699936 * 2 ^ 59
def prefixEnd_699936 : Nat := 4983230072969 + 3 ^ 40 * 699936 * 2
def baseEnd_699936 : Nat := 359403595385478730881059

theorem tailTrace_699936 : CollatzResearch.WordTrace tailWord_699936 prefixEnd_699936 359403595385478730881059 := by
  unfold tailWord_699936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12764381596129443198439831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17019175461505924264586441 12764381596129443198439831)
  ·
    refine ⟨19146572394194164797659747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12764381596129443198439831 19146572394194164797659747)
    ·
      refine ⟨28719858591291247196489621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19146572394194164797659747 28719858591291247196489621)
      ·
        refine ⟨1346243371466777212335451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28719858591291247196489621 1346243371466777212335451)
        ·
          refine ⟨2019365057200165818503177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346243371466777212335451 2019365057200165818503177)
          ·
            refine ⟨1514523792900124363877383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019365057200165818503177 1514523792900124363877383)
            ·
              refine ⟨2271785689350186545816075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514523792900124363877383 2271785689350186545816075)
              ·
                refine ⟨3407678534025279818724113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271785689350186545816075 3407678534025279818724113)
                ·
                  refine ⟨2555758900518959864043085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3407678534025279818724113 2555758900518959864043085)
                  ·
                    refine ⟨958409587694609949016157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2555758900518959864043085 958409587694609949016157)
                    ·
                      refine ⟨359403595385478730881059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958409587694609949016157 359403595385478730881059)
                      ·
                        rfl

theorem cell23_699936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_699936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699936 prefixEnd_699936 := by exact prefixLift 699936
  have htrace : WordTrace (prefixWord ++ tailWord_699936) baseStart_699936 baseEnd_699936 := by
    simpa [prefixWord, tailWord_699936, baseEnd_699936] using wordTrace_append hprefix tailTrace_699936
  have hstable : (prefixWord ++ tailWord_699936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699936).length < 2 ^ (prefixWord ++ tailWord_699936).sum := by decide
  have hdescent : baseEnd_699936 < baseStart_699936 := by decide
  rcases family_descends (prefixWord ++ tailWord_699936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699946 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_699946 : Nat := 118140960795 + 699946 * 2 ^ 59
def prefixEnd_699946 : Nat := 4983230072969 + 3 ^ 40 * 699946 * 2
def baseEnd_699946 : Nat := 359408730192023691756013

theorem tailTrace_699946 : CollatzResearch.WordTrace tailWord_699946 prefixEnd_699946 359408730192023691756013 := by
  unfold tailWord_699946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382281980555664526185923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17019418614815105403162461 6382281980555664526185923)
  ·
    refine ⟨9573422970833496789278885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6382281980555664526185923 9573422970833496789278885)
    ·
      refine ⟨1795016807031280647989791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9573422970833496789278885 1795016807031280647989791)
      ·
        refine ⟨2692525210546920971984687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795016807031280647989791 2692525210546920971984687)
        ·
          refine ⟨4038787815820381457977031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692525210546920971984687 4038787815820381457977031)
          ·
            refine ⟨6058181723730572186965547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038787815820381457977031 6058181723730572186965547)
            ·
              refine ⟨9087272585595858280448321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058181723730572186965547 9087272585595858280448321)
              ·
                refine ⟨6815454439196893710336241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9087272585595858280448321 6815454439196893710336241)
                ·
                  refine ⟨5111590829397670282752181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6815454439196893710336241 5111590829397670282752181)
                  ·
                    refine ⟨479211640256031589008017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5111590829397670282752181 479211640256031589008017)
                    ·
                      refine ⟨359408730192023691756013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479211640256031589008017 359408730192023691756013)
                      ·
                        rfl

theorem cell23_699946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_699946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699946 prefixEnd_699946 := by exact prefixLift 699946
  have htrace : WordTrace (prefixWord ++ tailWord_699946) baseStart_699946 baseEnd_699946 := by
    simpa [prefixWord, tailWord_699946, baseEnd_699946] using wordTrace_append hprefix tailTrace_699946
  have hstable : (prefixWord ++ tailWord_699946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699946).length < 2 ^ (prefixWord ++ tailWord_699946).sum := by decide
  have hdescent : baseEnd_699946 < baseStart_699946 := by decide
  rcases family_descends (prefixWord ++ tailWord_699946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699959 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_699959 : Nat := 118140960795 + 699959 * 2 ^ 59
def prefixEnd_699959 : Nat := 4983230072969 + 3 ^ 40 * 699959 * 2
def baseEnd_699959 : Nat := 359415405440532140893453

theorem tailTrace_699959 : CollatzResearch.WordTrace tailWord_699959 prefixEnd_699959 359415405440532140893453 := by
  unfold tailWord_699959
  simp only [CollatzResearch.WordTrace]
  refine ⟨25529602071175561324966931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17019734714117040883311287 25529602071175561324966931)
  ·
    refine ⟨38294403106763341987450397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25529602071175561324966931 38294403106763341987450397)
    ·
      refine ⟨14360401165036253245293899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38294403106763341987450397 14360401165036253245293899)
      ·
        refine ⟨21540601747554379867940849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14360401165036253245293899 21540601747554379867940849)
        ·
          refine ⟨16155451310665784900955637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21540601747554379867940849 16155451310665784900955637)
          ·
            refine ⟨1514573560374917334464591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16155451310665784900955637 1514573560374917334464591)
            ·
              refine ⟨2271860340562376001696887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514573560374917334464591 2271860340562376001696887)
              ·
                refine ⟨3407790510843564002545331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271860340562376001696887 3407790510843564002545331)
                ·
                  refine ⟨5111685766265346003817997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407790510843564002545331 5111685766265346003817997)
                  ·
                    refine ⟨1916882162349504751431749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5111685766265346003817997 1916882162349504751431749)
                    ·
                      refine ⟨359415405440532140893453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1916882162349504751431749 359415405440532140893453)
                      ·
                        rfl

theorem cell23_699959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_699959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699959 prefixEnd_699959 := by exact prefixLift 699959
  have htrace : WordTrace (prefixWord ++ tailWord_699959) baseStart_699959 baseEnd_699959 := by
    simpa [prefixWord, tailWord_699959, baseEnd_699959] using wordTrace_append hprefix tailTrace_699959
  have hstable : (prefixWord ++ tailWord_699959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699959).length < 2 ^ (prefixWord ++ tailWord_699959).sum := by decide
  have hdescent : baseEnd_699959 < baseStart_699959 := by decide
  rcases family_descends (prefixWord ++ tailWord_699959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699979 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 3]
def baseStart_699979 : Nat := 118140960795 + 699979 * 2 ^ 59
def prefixEnd_699979 : Nat := 4983230072969 + 3 ^ 40 * 699979 * 2
def baseEnd_699979 : Nat := 359425675053622062643361

theorem tailTrace_699979 : CollatzResearch.WordTrace tailWord_699979 prefixEnd_699979 359425675053622062643361 := by
  unfold tailWord_699979
  simp only [CollatzResearch.WordTrace]
  refine ⟨25530331531103104740694991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17020221020735403160463327 25530331531103104740694991)
  ·
    refine ⟨38295497296654657111042487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25530331531103104740694991 38295497296654657111042487)
    ·
      refine ⟨57443245944981985666563731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38295497296654657111042487 57443245944981985666563731)
      ·
        refine ⟨86164868917472978499845597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57443245944981985666563731 86164868917472978499845597)
        ·
          refine ⟨32311825844052366937442099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86164868917472978499845597 32311825844052366937442099)
          ·
            refine ⟨48467738766078550406163149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32311825844052366937442099 48467738766078550406163149)
            ·
              refine ⟨18175402037279456402311181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48467738766078550406163149 18175402037279456402311181)
              ·
                refine ⟨6815775763979796150866693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18175402037279456402311181 6815775763979796150866693)
                ·
                  refine ⟨1277957955746211778287505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6815775763979796150866693 1277957955746211778287505)
                  ·
                    refine ⟨958468466809658833715629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277957955746211778287505 958468466809658833715629)
                    ·
                      refine ⟨359425675053622062643361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958468466809658833715629 359425675053622062643361)
                      ·
                        rfl

theorem cell23_699979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 3].length) (baseStart_699979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699979 prefixEnd_699979 := by exact prefixLift 699979
  have htrace : WordTrace (prefixWord ++ tailWord_699979) baseStart_699979 baseEnd_699979 := by
    simpa [prefixWord, tailWord_699979, baseEnd_699979] using wordTrace_append hprefix tailTrace_699979
  have hstable : (prefixWord ++ tailWord_699979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699979).length < 2 ^ (prefixWord ++ tailWord_699979).sum := by decide
  have hdescent : baseEnd_699979 < baseStart_699979 := by decide
  rcases family_descends (prefixWord ++ tailWord_699979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699986 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_699986 : Nat := 118140960795 + 699986 * 2 ^ 59
def prefixEnd_699986 : Nat := 4983230072969 + 3 ^ 40 * 699986 * 2
def baseEnd_699986 : Nat := 119809756472734511751943

theorem tailTrace_699986 : CollatzResearch.WordTrace tailWord_699986 prefixEnd_699986 119809756472734511751943 := by
  unfold tailWord_699986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382646710519436234049953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17020391228051829957466541 6382646710519436234049953)
  ·
    refine ⟨4786985032889577175537465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6382646710519436234049953 4786985032889577175537465)
    ·
      refine ⟨3590238774667182881653099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4786985032889577175537465 3590238774667182881653099)
      ·
        refine ⟨5385358162000774322479649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590238774667182881653099 5385358162000774322479649)
        ·
          refine ⟨4039018621500580741859737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385358162000774322479649 4039018621500580741859737)
          ·
            refine ⟨3029263966125435556394803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4039018621500580741859737 3029263966125435556394803)
            ·
              refine ⟨4543895949188153334592205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029263966125435556394803 4543895949188153334592205)
              ·
                refine ⟨1703960980945557500472077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4543895949188153334592205 1703960980945557500472077)
                ·
                  refine ⟨638985367854584062677029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1703960980945557500472077 638985367854584062677029)
                  ·
                    refine ⟨119809756472734511751943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638985367854584062677029 119809756472734511751943)
                    ·
                      rfl

theorem cell23_699986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_699986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699986 prefixEnd_699986 := by exact prefixLift 699986
  have htrace : WordTrace (prefixWord ++ tailWord_699986) baseStart_699986 baseEnd_699986 := by
    simpa [prefixWord, tailWord_699986, baseEnd_699986] using wordTrace_append hprefix tailTrace_699986
  have hstable : (prefixWord ++ tailWord_699986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699986).length < 2 ^ (prefixWord ++ tailWord_699986).sum := by decide
  have hdescent : baseEnd_699986 < baseStart_699986 := by decide
  rcases family_descends (prefixWord ++ tailWord_699986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699996 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_699996 : Nat := 118140960795 + 699996 * 2 ^ 59
def prefixEnd_699996 : Nat := 4983230072969 + 3 ^ 40 * 699996 * 2
def baseEnd_699996 : Nat := 359434404224748496130783

theorem tailTrace_699996 : CollatzResearch.WordTrace tailWord_699996 prefixEnd_699996 359434404224748496130783 := by
  unfold tailWord_699996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765475786020758322031921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17020634381361011096042561 12765475786020758322031921)
  ·
    refine ⟨9574106839515568741523941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12765475786020758322031921 9574106839515568741523941)
    ·
      refine ⟨1795145032409169139035739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9574106839515568741523941 1795145032409169139035739)
      ·
        refine ⟨2692717548613753708553609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795145032409169139035739 2692717548613753708553609)
        ·
          refine ⟨2019538161460315281415207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2692717548613753708553609 2019538161460315281415207)
          ·
            refine ⟨3029307242190472922122811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019538161460315281415207 3029307242190472922122811)
            ·
              refine ⟨4543960863285709383184217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029307242190472922122811 4543960863285709383184217)
              ·
                refine ⟨3407970647464282037388163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543960863285709383184217 3407970647464282037388163)
                ·
                  refine ⟨5111955971196423056082245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407970647464282037388163 5111955971196423056082245)
                  ·
                    refine ⟨958491744599329323015421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111955971196423056082245 958491744599329323015421)
                    ·
                      refine ⟨359434404224748496130783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958491744599329323015421 359434404224748496130783)
                      ·
                        rfl

theorem cell23_699996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_699996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_699996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_699996 prefixEnd_699996 := by exact prefixLift 699996
  have htrace : WordTrace (prefixWord ++ tailWord_699996) baseStart_699996 baseEnd_699996 := by
    simpa [prefixWord, tailWord_699996, baseEnd_699996] using wordTrace_append hprefix tailTrace_699996
  have hstable : (prefixWord ++ tailWord_699996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699996).length < 2 ^ (prefixWord ++ tailWord_699996).sum := by decide
  have hdescent : baseEnd_699996 < baseStart_699996 := by decide
  rcases family_descends (prefixWord ++ tailWord_699996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700050 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_700050 : Nat := 118140960795 + 700050 * 2 ^ 59
def prefixEnd_700050 : Nat := 4983230072969 + 3 ^ 40 * 700050 * 2
def baseEnd_700050 : Nat := 39940236908899031650615

theorem tailTrace_700050 : CollatzResearch.WordTrace tailWord_700050 prefixEnd_700050 39940236908899031650615 := by
  unfold tailWord_700050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383230278461470966632401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17021947409230589244353069 6383230278461470966632401)
  ·
    refine ⟨4787422708846103224974301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6383230278461470966632401 4787422708846103224974301)
    ·
      refine ⟨1795283515817288709365363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4787422708846103224974301 1795283515817288709365363)
      ·
        refine ⟨2692925273725933064048045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795283515817288709365363 2692925273725933064048045)
        ·
          refine ⟨1009846977647224899018017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2692925273725933064048045 1009846977647224899018017)
          ·
            refine ⟨757385233235418674263513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009846977647224899018017 757385233235418674263513)
            ·
              refine ⟨568038924926564005697635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757385233235418674263513 568038924926564005697635)
              ·
                refine ⟨852058387389846008546453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568038924926564005697635 852058387389846008546453)
                ·
                  refine ⟨39940236908899031650615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 852058387389846008546453 39940236908899031650615)
                  ·
                    rfl

theorem cell23_700050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_700050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700050 prefixEnd_700050 := by exact prefixLift 700050
  have htrace : WordTrace (prefixWord ++ tailWord_700050) baseStart_700050 baseEnd_700050 := by
    simpa [prefixWord, tailWord_700050, baseEnd_700050] using wordTrace_append hprefix tailTrace_700050
  have hstable : (prefixWord ++ tailWord_700050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700050).length < 2 ^ (prefixWord ++ tailWord_700050).sum := by decide
  have hdescent : baseEnd_700050 < baseStart_700050 := by decide
  rcases family_descends (prefixWord ++ tailWord_700050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700063 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 3, 5]
def baseStart_700063 : Nat := 118140960795 + 700063 * 2 ^ 59
def prefixEnd_700063 : Nat := 4983230072969 + 3 ^ 40 * 700063 * 2
def baseEnd_700063 : Nat := 119822935809533244664325

theorem tailTrace_700063 : CollatzResearch.WordTrace tailWord_700063 prefixEnd_700063 119822935809533244664325 := by
  unfold tailWord_700063
  simp only [CollatzResearch.WordTrace]
  refine ⟨25533395262798787086752843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17022263508532524724501895 25533395262798787086752843)
  ·
    refine ⟨38300092894198180630129265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25533395262798787086752843 38300092894198180630129265)
    ·
      refine ⟨28725069670648635472596949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38300092894198180630129265 28725069670648635472596949)
      ·
        refine ⟨673243820405827393888991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28725069670648635472596949 673243820405827393888991)
        ·
          refine ⟨1009865730608741090833487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673243820405827393888991 1009865730608741090833487)
          ·
            refine ⟨1514798595913111636250231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009865730608741090833487 1514798595913111636250231)
            ·
              refine ⟨2272197893869667454375347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514798595913111636250231 2272197893869667454375347)
              ·
                refine ⟨3408296840804501181563021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272197893869667454375347 3408296840804501181563021)
                ·
                  refine ⟨1278111315301687943086133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3408296840804501181563021 1278111315301687943086133)
                  ·
                    refine ⟨119822935809533244664325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1278111315301687943086133 119822935809533244664325)
                    ·
                      rfl

theorem cell23_700063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_700063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700063 prefixEnd_700063 := by exact prefixLift 700063
  have htrace : WordTrace (prefixWord ++ tailWord_700063) baseStart_700063 baseEnd_700063 := by
    simpa [prefixWord, tailWord_700063, baseEnd_700063] using wordTrace_append hprefix tailTrace_700063
  have hstable : (prefixWord ++ tailWord_700063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700063).length < 2 ^ (prefixWord ++ tailWord_700063).sum := by decide
  have hdescent : baseEnd_700063 < baseStart_700063 := by decide
  rcases family_descends (prefixWord ++ tailWord_700063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700069 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_700069 : Nat := 118140960795 + 700069 * 2 ^ 59
def prefixEnd_700069 : Nat := 4983230072969 + 3 ^ 40 * 700069 * 2
def baseEnd_700069 : Nat := 359471888312526710517947

theorem tailTrace_700069 : CollatzResearch.WordTrace tailWord_700069 prefixEnd_700069 359471888312526710517947 := by
  unfold tailWord_700069
  simp only [CollatzResearch.WordTrace]
  refine ⟨25533614100777050111471261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17022409400518033407647507 25533614100777050111471261)
  ·
    refine ⟨9575105287791393791801723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25533614100777050111471261 9575105287791393791801723)
    ·
      refine ⟨14362657931687090687702585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9575105287791393791801723 14362657931687090687702585)
      ·
        refine ⟨10771993448765318015776939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14362657931687090687702585 10771993448765318015776939)
        ·
          refine ⟨16157990173147977023665409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10771993448765318015776939 16157990173147977023665409)
          ·
            refine ⟨12118492629860982767749057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16157990173147977023665409 12118492629860982767749057)
            ·
              refine ⟨9088869472395737075811793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12118492629860982767749057 9088869472395737075811793)
              ·
                refine ⟨6816652104296802806858845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9088869472395737075811793 6816652104296802806858845)
                ·
                  refine ⟨2556244539111301052572067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6816652104296802806858845 2556244539111301052572067)
                  ·
                    refine ⟨3834366808666951578858101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2556244539111301052572067 3834366808666951578858101)
                    ·
                      refine ⟨359471888312526710517947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3834366808666951578858101 359471888312526710517947)
                      ·
                        rfl

theorem cell23_700069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_700069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700069 prefixEnd_700069 := by exact prefixLift 700069
  have htrace : WordTrace (prefixWord ++ tailWord_700069) baseStart_700069 baseEnd_700069 := by
    simpa [prefixWord, tailWord_700069, baseEnd_700069] using wordTrace_append hprefix tailTrace_700069
  have hstable : (prefixWord ++ tailWord_700069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700069).length < 2 ^ (prefixWord ++ tailWord_700069).sum := by decide
  have hdescent : baseEnd_700069 < baseStart_700069 := by decide
  rcases family_descends (prefixWord ++ tailWord_700069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700083 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 1, 1, 4]
def baseStart_700083 : Nat := 118140960795 + 700083 * 2 ^ 59
def prefixEnd_700083 : Nat := 4983230072969 + 3 ^ 40 * 700083 * 2
def baseEnd_700083 : Nat := 359479077041689655742883

theorem tailTrace_700083 : CollatzResearch.WordTrace tailWord_700083 prefixEnd_700083 359479077041689655742883 := by
  unfold tailWord_700083
  simp only [CollatzResearch.WordTrace]
  refine ⟨25534124722726330502480903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17022749815150887001653935 25534124722726330502480903)
  ·
    refine ⟨38301187084089495753721355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25534124722726330502480903 38301187084089495753721355)
    ·
      refine ⟨57451780626134243630582033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38301187084089495753721355 57451780626134243630582033)
      ·
        refine ⟨43088835469600682722936525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57451780626134243630582033 43088835469600682722936525)
        ·
          refine ⟨16158313301100256021101197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43088835469600682722936525 16158313301100256021101197)
          ·
            refine ⟨6059367487912596007912949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16158313301100256021101197 6059367487912596007912949)
            ·
              refine ⟨568065701991805875741839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6059367487912596007912949 568065701991805875741839)
              ·
                refine ⟨852098552987708813612759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568065701991805875741839 852098552987708813612759)
                ·
                  refine ⟨1278147829481563220419139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852098552987708813612759 1278147829481563220419139)
                  ·
                    refine ⟨1917221744222344830628709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1278147829481563220419139 1917221744222344830628709)
                    ·
                      refine ⟨359479077041689655742883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1917221744222344830628709 359479077041689655742883)
                      ·
                        rfl

theorem cell23_700083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 1, 4].length) (baseStart_700083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700083 prefixEnd_700083 := by exact prefixLift 700083
  have htrace : WordTrace (prefixWord ++ tailWord_700083) baseStart_700083 baseEnd_700083 := by
    simpa [prefixWord, tailWord_700083, baseEnd_700083] using wordTrace_append hprefix tailTrace_700083
  have hstable : (prefixWord ++ tailWord_700083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700083).length < 2 ^ (prefixWord ++ tailWord_700083).sum := by decide
  have hdescent : baseEnd_700083 < baseStart_700083 := by decide
  rcases family_descends (prefixWord ++ tailWord_700083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700093 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_700093 : Nat := 118140960795 + 700093 * 2 ^ 59
def prefixEnd_700093 : Nat := 4983230072969 + 3 ^ 40 * 700093 * 2
def baseEnd_700093 : Nat := 119828070616078205539279

theorem tailTrace_700093 : CollatzResearch.WordTrace tailWord_700093 prefixEnd_700093 119828070616078205539279 := by
  unfold tailWord_700093
  simp only [CollatzResearch.WordTrace]
  refine ⟨25534489452690102210344933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17022992968460068140229955 25534489452690102210344933)
  ·
    refine ⟨4787716772379394164439675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25534489452690102210344933 4787716772379394164439675)
    ·
      refine ⟨7181575158569091246659513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787716772379394164439675 7181575158569091246659513)
      ·
        refine ⟨5386181368926818434994635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7181575158569091246659513 5386181368926818434994635)
        ·
          refine ⟨8079272053390227652491953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386181368926818434994635 8079272053390227652491953)
          ·
            refine ⟨6059454040042670739368965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8079272053390227652491953 6059454040042670739368965)
            ·
              refine ⟨1136147632508000763631681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6059454040042670739368965 1136147632508000763631681)
              ·
                refine ⟨852110724381000572723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136147632508000763631681 852110724381000572723761)
                ·
                  refine ⟨639083043285750429542821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 852110724381000572723761 639083043285750429542821)
                  ·
                    refine ⟨119828070616078205539279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639083043285750429542821 119828070616078205539279)
                    ·
                      rfl

theorem cell23_700093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_700093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700093 prefixEnd_700093 := by exact prefixLift 700093
  have htrace : WordTrace (prefixWord ++ tailWord_700093) baseStart_700093 baseEnd_700093 := by
    simpa [prefixWord, tailWord_700093, baseEnd_700093] using wordTrace_append hprefix tailTrace_700093
  have hstable : (prefixWord ++ tailWord_700093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700093).length < 2 ^ (prefixWord ++ tailWord_700093).sum := by decide
  have hdescent : baseEnd_700093 < baseStart_700093 := by decide
  rcases family_descends (prefixWord ++ tailWord_700093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700094 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_700094 : Nat := 118140960795 + 700094 * 2 ^ 59
def prefixEnd_700094 : Nat := 4983230072969 + 3 ^ 40 * 700094 * 2
def baseEnd_700094 : Nat := 359484725328889112705333

theorem tailTrace_700094 : CollatzResearch.WordTrace tailWord_700094 prefixEnd_700094 359484725328889112705333 := by
  unfold tailWord_700094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191815740710809922641417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17023017283790986254087557 3191815740710809922641417)
  ·
    refine ⟨2393861805533107441981063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3191815740710809922641417 2393861805533107441981063)
    ·
      refine ⟨3590792708299661162971595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393861805533107441981063 3590792708299661162971595)
      ·
        refine ⟨5386189062449491744457393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590792708299661162971595 5386189062449491744457393)
        ·
          refine ⟨4039641796837118808343045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386189062449491744457393 4039641796837118808343045)
          ·
            refine ⟨757432836906959776564321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4039641796837118808343045 757432836906959776564321)
            ·
              refine ⟨568074627680219832423241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757432836906959776564321 568074627680219832423241)
              ·
                refine ⟨426055970760164874317431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568074627680219832423241 426055970760164874317431)
                ·
                  refine ⟨639083956140247311476147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426055970760164874317431 639083956140247311476147)
                  ·
                    refine ⟨958625934210370967214221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639083956140247311476147 958625934210370967214221)
                    ·
                      refine ⟨359484725328889112705333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958625934210370967214221 359484725328889112705333)
                      ·
                        rfl

theorem cell23_700094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_700094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700094 prefixEnd_700094 := by exact prefixLift 700094
  have htrace : WordTrace (prefixWord ++ tailWord_700094) baseStart_700094 baseEnd_700094 := by
    simpa [prefixWord, tailWord_700094, baseEnd_700094] using wordTrace_append hprefix tailTrace_700094
  have hstable : (prefixWord ++ tailWord_700094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700094).length < 2 ^ (prefixWord ++ tailWord_700094).sum := by decide
  have hdescent : baseEnd_700094 < baseStart_700094 := by decide
  rcases family_descends (prefixWord ++ tailWord_700094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700100 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_700100 : Nat := 118140960795 + 700100 * 2 ^ 59
def prefixEnd_700100 : Nat := 4983230072969 + 3 ^ 40 * 700100 * 2
def baseEnd_700100 : Nat := 359487806212816089230305

theorem tailTrace_700100 : CollatzResearch.WordTrace tailWord_700100 prefixEnd_700100 359487806212816089230305 := by
  unfold tailWord_700100
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767372381832371202924877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17023163175776494937233169 12767372381832371202924877)
  ·
    refine ⟨4787764643187139201096829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12767372381832371202924877 4787764643187139201096829)
    ·
      refine ⟨1795411741195177200411311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4787764643187139201096829 1795411741195177200411311)
      ·
        refine ⟨2693117611792765800616967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795411741195177200411311 2693117611792765800616967)
        ·
          refine ⟨4039676417689148700925451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693117611792765800616967 4039676417689148700925451)
          ·
            refine ⟨6059514626533723051388177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039676417689148700925451 6059514626533723051388177)
            ·
              refine ⟨4544635969900292288541133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6059514626533723051388177 4544635969900292288541133)
              ·
                refine ⟨1704238488712609608202925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4544635969900292288541133 1704238488712609608202925)
                ·
                  refine ⟨639089433267228603076097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1704238488712609608202925 639089433267228603076097)
                  ·
                    refine ⟨479317074950421452307073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639089433267228603076097 479317074950421452307073)
                    ·
                      refine ⟨359487806212816089230305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479317074950421452307073 359487806212816089230305)
                      ·
                        rfl

theorem cell23_700100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_700100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700100 prefixEnd_700100 := by exact prefixLift 700100
  have htrace : WordTrace (prefixWord ++ tailWord_700100) baseStart_700100 baseEnd_700100 := by
    simpa [prefixWord, tailWord_700100, baseEnd_700100] using wordTrace_append hprefix tailTrace_700100
  have hstable : (prefixWord ++ tailWord_700100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700100).length < 2 ^ (prefixWord ++ tailWord_700100).sum := by decide
  have hdescent : baseEnd_700100 < baseStart_700100 := by decide
  rcases family_descends (prefixWord ++ tailWord_700100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700119 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 2, 7]
def baseStart_700119 : Nat := 118140960795 + 700119 * 2 ^ 59
def prefixEnd_700119 : Nat := 4983230072969 + 3 ^ 40 * 700119 * 2
def baseEnd_700119 : Nat := 119832520781750504964239

theorem tailTrace_700119 : CollatzResearch.WordTrace tailWord_700119 prefixEnd_700119 119832520781750504964239 := by
  unfold tailWord_700119
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535437750595908650791411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17023625167063939100527607 25535437750595908650791411)
  ·
    refine ⟨38303156625893862976187117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25535437750595908650791411 38303156625893862976187117)
    ·
      refine ⟨14363683734710198616070169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38303156625893862976187117 14363683734710198616070169)
      ·
        refine ⟨10772762801032648962052627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14363683734710198616070169 10772762801032648962052627)
        ·
          refine ⟨16159144201548973443078941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10772762801032648962052627 16159144201548973443078941)
          ·
            refine ⟨6059679075580865041154603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16159144201548973443078941 6059679075580865041154603)
            ·
              refine ⟨9089518613371297561731905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059679075580865041154603 9089518613371297561731905)
              ·
                refine ⟨6817138960028473171298929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9089518613371297561731905 6817138960028473171298929)
                ·
                  refine ⟨5112854220021354878474197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6817138960028473171298929 5112854220021354878474197)
                  ·
                    refine ⟨119832520781750504964239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5112854220021354878474197 119832520781750504964239)
                    ·
                      rfl

theorem cell23_700119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_700119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700119 prefixEnd_700119 := by exact prefixLift 700119
  have htrace : WordTrace (prefixWord ++ tailWord_700119) baseStart_700119 baseEnd_700119 := by
    simpa [prefixWord, tailWord_700119, baseEnd_700119] using wordTrace_append hprefix tailTrace_700119
  have hstable : (prefixWord ++ tailWord_700119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700119).length < 2 ^ (prefixWord ++ tailWord_700119).sum := by decide
  have hdescent : baseEnd_700119 < baseStart_700119 := by decide
  rcases family_descends (prefixWord ++ tailWord_700119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700133 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_700133 : Nat := 118140960795 + 700133 * 2 ^ 59
def prefixEnd_700133 : Nat := 4983230072969 + 3 ^ 40 * 700133 * 2
def baseEnd_700133 : Nat := 359504751074414460117653

theorem tailTrace_700133 : CollatzResearch.WordTrace tailWord_700133 prefixEnd_700133 359504751074414460117653 := by
  unfold tailWord_700133
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535948372545189041801053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17023965581696792694534035 25535948372545189041801053)
  ·
    refine ⟨9575980639704445890675395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25535948372545189041801053 9575980639704445890675395)
    ·
      refine ⟨14363970959556668836013093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9575980639704445890675395 14363970959556668836013093)
      ·
        refine ⟨2693244554916875406752455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14363970959556668836013093 2693244554916875406752455)
        ·
          refine ⟨4039866832375313110128683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693244554916875406752455 4039866832375313110128683)
          ·
            refine ⟨6059800248562969665193025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039866832375313110128683 6059800248562969665193025)
            ·
              refine ⟨4544850186422227248894769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6059800248562969665193025 4544850186422227248894769)
              ·
                refine ⟨3408637639816670436671077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544850186422227248894769 3408637639816670436671077)
                ·
                  refine ⟨639119557465625706875827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3408637639816670436671077 639119557465625706875827)
                  ·
                    refine ⟨958679336198438560313741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639119557465625706875827 958679336198438560313741)
                    ·
                      refine ⟨359504751074414460117653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958679336198438560313741 359504751074414460117653)
                      ·
                        rfl

theorem cell23_700133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_700133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700133 prefixEnd_700133 := by exact prefixLift 700133
  have htrace : WordTrace (prefixWord ++ tailWord_700133) baseStart_700133 baseEnd_700133 := by
    simpa [prefixWord, tailWord_700133, baseEnd_700133] using wordTrace_append hprefix tailTrace_700133
  have hstable : (prefixWord ++ tailWord_700133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700133).length < 2 ^ (prefixWord ++ tailWord_700133).sum := by decide
  have hdescent : baseEnd_700133 < baseStart_700133 := by decide
  rcases family_descends (prefixWord ++ tailWord_700133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700150 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_700150 : Nat := 118140960795 + 700150 * 2 ^ 59
def prefixEnd_700150 : Nat := 4983230072969 + 3 ^ 40 * 700150 * 2
def baseEnd_700150 : Nat := 359513480245540893605075

theorem tailTrace_700150 : CollatzResearch.WordTrace tailWord_700150 prefixEnd_700150 359513480245540893605075 := by
  unfold tailWord_700150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596035525842725059073119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17024378942322400630113269 1596035525842725059073119)
  ·
    refine ⟨2394053288764087588609679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1596035525842725059073119 2394053288764087588609679)
    ·
      refine ⟨3591079933146131382914519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2394053288764087588609679 3591079933146131382914519)
      ·
        refine ⟨5386619899719197074371779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591079933146131382914519 5386619899719197074371779)
        ·
          refine ⟨8079929849578795611557669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386619899719197074371779 8079929849578795611557669)
          ·
            refine ⟨1514986846796024177167063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8079929849578795611557669 1514986846796024177167063)
            ·
              refine ⟨2272480270194036265750595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514986846796024177167063 2272480270194036265750595)
              ·
                refine ⟨3408720405291054398625893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272480270194036265750595 3408720405291054398625893)
                ·
                  refine ⟨639135075992072699742355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3408720405291054398625893 639135075992072699742355)
                  ·
                    refine ⟨958702613988109049613533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639135075992072699742355 958702613988109049613533)
                    ·
                      refine ⟨359513480245540893605075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958702613988109049613533 359513480245540893605075)
                      ·
                        rfl

theorem cell23_700150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_700150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700150 prefixEnd_700150 := by exact prefixLift 700150
  have htrace : WordTrace (prefixWord ++ tailWord_700150) baseStart_700150 baseEnd_700150 := by
    simpa [prefixWord, tailWord_700150, baseEnd_700150] using wordTrace_append hprefix tailTrace_700150
  have hstable : (prefixWord ++ tailWord_700150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700150).length < 2 ^ (prefixWord ++ tailWord_700150).sum := by decide
  have hdescent : baseEnd_700150 < baseStart_700150 := by decide
  rcases family_descends (prefixWord ++ tailWord_700150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700167 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_700167 : Nat := 118140960795 + 700167 * 2 ^ 59
def prefixEnd_700167 : Nat := 4983230072969 + 3 ^ 40 * 700167 * 2
def baseEnd_700167 : Nat := 359522209416667327092497

theorem tailTrace_700167 : CollatzResearch.WordTrace tailWord_700167 prefixEnd_700167 359522209416667327092497 := by
  unfold tailWord_700167
  simp only [CollatzResearch.WordTrace]
  refine ⟨25537188454422012848538755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17024792302948008565692503 25537188454422012848538755)
  ·
    refine ⟨38305782681633019272808133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25537188454422012848538755 38305782681633019272808133)
    ·
      refine ⟨7182334252806191113651525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38305782681633019272808133 7182334252806191113651525)
      ·
        refine ⟨1346687672401160833809661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7182334252806191113651525 1346687672401160833809661)
        ·
          refine ⟨505007877150435312678623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1346687672401160833809661 505007877150435312678623)
          ·
            refine ⟨757511815725652969017935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505007877150435312678623 757511815725652969017935)
            ·
              refine ⟨1136267723588479453526903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757511815725652969017935 1136267723588479453526903)
              ·
                refine ⟨1704401585382719180290355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136267723588479453526903 1704401585382719180290355)
                ·
                  refine ⟨2556602378074078770435533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704401585382719180290355 2556602378074078770435533)
                  ·
                    refine ⟨958725891777779538913325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2556602378074078770435533 958725891777779538913325)
                    ·
                      refine ⟨359522209416667327092497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958725891777779538913325 359522209416667327092497)
                      ·
                        rfl

theorem cell23_700167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_700167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700167 prefixEnd_700167 := by exact prefixLift 700167
  have htrace : WordTrace (prefixWord ++ tailWord_700167) baseStart_700167 baseEnd_700167 := by
    simpa [prefixWord, tailWord_700167, baseEnd_700167] using wordTrace_append hprefix tailTrace_700167
  have hstable : (prefixWord ++ tailWord_700167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700167).length < 2 ^ (prefixWord ++ tailWord_700167).sum := by decide
  have hdescent : baseEnd_700167 < baseStart_700167 := by decide
  rcases family_descends (prefixWord ++ tailWord_700167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700179 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 9]
def baseStart_700179 : Nat := 118140960795 + 700179 * 2 ^ 59
def prefixEnd_700179 : Nat := 4983230072969 + 3 ^ 40 * 700179 * 2
def baseEnd_700179 : Nat := 39947596798280142238049

theorem tailTrace_700179 : CollatzResearch.WordTrace tailWord_700179 prefixEnd_700179 39947596798280142238049 := by
  unfold tailWord_700179
  simp only [CollatzResearch.WordTrace]
  refine ⟨25537626130378538897975591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17025084086919025931983727 25537626130378538897975591)
  ·
    refine ⟨38306439195567808346963387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25537626130378538897975591 38306439195567808346963387)
    ·
      refine ⟨57459658793351712520445081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38306439195567808346963387 57459658793351712520445081)
      ·
        refine ⟨43094744095013784390333811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57459658793351712520445081 43094744095013784390333811)
        ·
          refine ⟨64642116142520676585500717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43094744095013784390333811 64642116142520676585500717)
          ·
            refine ⟨24240793553445253719562769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64642116142520676585500717 24240793553445253719562769)
            ·
              refine ⟨18180595165083940289672077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24240793553445253719562769 18180595165083940289672077)
              ·
                refine ⟨6817723186906477608627029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18180595165083940289672077 6817723186906477608627029)
                ·
                  refine ⟨39947596798280142238049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6817723186906477608627029 39947596798280142238049)
                  ·
                    rfl

theorem cell23_700179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 9].length) (baseStart_700179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700179 prefixEnd_700179 := by exact prefixLift 700179
  have htrace : WordTrace (prefixWord ++ tailWord_700179) baseStart_700179 baseEnd_700179 := by
    simpa [prefixWord, tailWord_700179, baseEnd_700179] using wordTrace_append hprefix tailTrace_700179
  have hstable : (prefixWord ++ tailWord_700179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700179).length < 2 ^ (prefixWord ++ tailWord_700179).sum := by decide
  have hdescent : baseEnd_700179 < baseStart_700179 := by decide
  rcases family_descends (prefixWord ++ tailWord_700179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700263 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_700263 : Nat := 118140960795 + 700263 * 2 ^ 59
def prefixEnd_700263 : Nat := 4983230072969 + 3 ^ 40 * 700263 * 2
def baseEnd_700263 : Nat := 359571503559498951492055

theorem tailTrace_700263 : CollatzResearch.WordTrace tailWord_700263 prefixEnd_700263 359571503559498951492055 := by
  unfold tailWord_700263
  simp only [CollatzResearch.WordTrace]
  refine ⟨25540689862074221244033443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17027126574716147496022295 25540689862074221244033443)
  ·
    refine ⟨38311034793111331866050165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25540689862074221244033443 38311034793111331866050165)
    ·
      refine ⟨3591659511854187362442203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38311034793111331866050165 3591659511854187362442203)
      ·
        refine ⟨5387489267781281043663305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591659511854187362442203 5387489267781281043663305)
        ·
          refine ⟨4040616950835960782747479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5387489267781281043663305 4040616950835960782747479)
          ·
            refine ⟨6060925426253941174121219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040616950835960782747479 6060925426253941174121219)
            ·
              refine ⟨9091388139380911761181829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060925426253941174121219 9091388139380911761181829)
              ·
                refine ⟨1704635276133920955221593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9091388139380911761181829 1704635276133920955221593)
                ·
                  refine ⟨1278476457100440716416195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1704635276133920955221593 1278476457100440716416195)
                  ·
                    refine ⟨1917714685650661074624293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1278476457100440716416195 1917714685650661074624293)
                    ·
                      refine ⟨359571503559498951492055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1917714685650661074624293 359571503559498951492055)
                      ·
                        rfl

theorem cell23_700263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_700263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700263 prefixEnd_700263 := by exact prefixLift 700263
  have htrace : WordTrace (prefixWord ++ tailWord_700263) baseStart_700263 baseEnd_700263 := by
    simpa [prefixWord, tailWord_700263, baseEnd_700263] using wordTrace_append hprefix tailTrace_700263
  have hstable : (prefixWord ++ tailWord_700263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700263).length < 2 ^ (prefixWord ++ tailWord_700263).sum := by decide
  have hdescent : baseEnd_700263 < baseStart_700263 := by decide
  rcases family_descends (prefixWord ++ tailWord_700263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700273 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 3, 4]
def baseStart_700273 : Nat := 118140960795 + 700273 * 2 ^ 59
def prefixEnd_700273 : Nat := 4983230072969 + 3 ^ 40 * 700273 * 2
def baseEnd_700273 : Nat := 119858879455347970789003

theorem tailTrace_700273 : CollatzResearch.WordTrace tailWord_700273 prefixEnd_700273 119858879455347970789003 := by
  unfold tailWord_700273
  simp only [CollatzResearch.WordTrace]
  refine ⟨25541054592037992951897473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17027369728025328634598315 25541054592037992951897473)
  ·
    refine ⟨19155790944028494713923105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25541054592037992951897473 19155790944028494713923105)
    ·
      refine ⟨14366843208021371035442329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19155790944028494713923105 14366843208021371035442329)
      ·
        refine ⟨10775132406016028276581747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14366843208021371035442329 10775132406016028276581747)
        ·
          refine ⟨16162698609024042414872621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775132406016028276581747 16162698609024042414872621)
          ·
            refine ⟨6061011978384015905577233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16162698609024042414872621 6061011978384015905577233)
            ·
              refine ⟨4545758983788011929182925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6061011978384015905577233 4545758983788011929182925)
              ·
                refine ⟨1704659618920504473443597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4545758983788011929182925 1704659618920504473443597)
                ·
                  refine ⟨639247357095189177541349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1704659618920504473443597 639247357095189177541349)
                  ·
                    refine ⟨119858879455347970789003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639247357095189177541349 119858879455347970789003)
                    ·
                      rfl

theorem cell23_700273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_700273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700273 prefixEnd_700273 := by exact prefixLift 700273
  have htrace : WordTrace (prefixWord ++ tailWord_700273) baseStart_700273 baseEnd_700273 := by
    simpa [prefixWord, tailWord_700273, baseEnd_700273] using wordTrace_append hprefix tailTrace_700273
  have hstable : (prefixWord ++ tailWord_700273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700273).length < 2 ^ (prefixWord ++ tailWord_700273).sum := by decide
  have hdescent : baseEnd_700273 < baseStart_700273 := by decide
  rcases family_descends (prefixWord ++ tailWord_700273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700350 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_700350 : Nat := 118140960795 + 700350 * 2 ^ 59
def prefixEnd_700350 : Nat := 4983230072969 + 3 ^ 40 * 700350 * 2
def baseEnd_700350 : Nat := 119872058792146703701385

theorem tailTrace_700350 : CollatzResearch.WordTrace tailWord_700350 prefixEnd_700350 119872058792146703701385 := by
  unfold tailWord_700350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192982876594879387806313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17029242008506023401633669 3192982876594879387806313)
  ·
    refine ⟨2394737157446159540854735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3192982876594879387806313 2394737157446159540854735)
    ·
      refine ⟨3592105736169239311282103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2394737157446159540854735 3592105736169239311282103)
      ·
        refine ⟨5388158604253858966923155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3592105736169239311282103 5388158604253858966923155)
        ·
          refine ⟨8082237906380788450384733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5388158604253858966923155 8082237906380788450384733)
          ·
            refine ⟨3030839214892795668894275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8082237906380788450384733 3030839214892795668894275)
            ·
              refine ⟨4546258822339193503341413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030839214892795668894275 4546258822339193503341413)
              ·
                refine ⟨852423529188598781876515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4546258822339193503341413 852423529188598781876515)
                ·
                  refine ⟨1278635293782898172814773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852423529188598781876515 1278635293782898172814773)
                  ·
                    refine ⟨119872058792146703701385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1278635293782898172814773 119872058792146703701385)
                    ·
                      rfl

theorem cell23_700350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_700350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700350 prefixEnd_700350 := by exact prefixLift 700350
  have htrace : WordTrace (prefixWord ++ tailWord_700350) baseStart_700350 baseEnd_700350 := by
    simpa [prefixWord, tailWord_700350, baseEnd_700350] using wordTrace_append hprefix tailTrace_700350
  have hstable : (prefixWord ++ tailWord_700350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700350).length < 2 ^ (prefixWord ++ tailWord_700350).sum := by decide
  have hdescent : baseEnd_700350 < baseStart_700350 := by decide
  rcases family_descends (prefixWord ++ tailWord_700350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700363 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 6, 4]
def baseStart_700363 : Nat := 118140960795 + 700363 * 2 ^ 59
def prefixEnd_700363 : Nat := 4983230072969 + 3 ^ 40 * 700363 * 2
def baseEnd_700363 : Nat := 119874283874982853413865

theorem tailTrace_700363 : CollatzResearch.WordTrace tailWord_700363 prefixEnd_700363 119874283874982853413865 := by
  unfold tailWord_700363
  simp only [CollatzResearch.WordTrace]
  refine ⟨25544337161711938322673743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17029558107807958881782495 25544337161711938322673743)
  ·
    refine ⟨38316505742567907484010615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25544337161711938322673743 38316505742567907484010615)
    ·
      refine ⟨57474758613851861226015923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38316505742567907484010615 57474758613851861226015923)
      ·
        refine ⟨86212137920777791839023885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57474758613851861226015923 86212137920777791839023885)
        ·
          refine ⟨32329551720291671939633957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86212137920777791839023885 32329551720291671939633957)
          ·
            refine ⟨6061790947554688488681367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32329551720291671939633957 6061790947554688488681367)
            ·
              refine ⟨9092686421332032733022051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061790947554688488681367 9092686421332032733022051)
              ·
                refine ⟨13639029631998049099533077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9092686421332032733022051 13639029631998049099533077)
                ·
                  refine ⟨639329513999908551540613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13639029631998049099533077 639329513999908551540613)
                  ·
                    refine ⟨119874283874982853413865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639329513999908551540613 119874283874982853413865)
                    ·
                      rfl

theorem cell23_700363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 4].length) (baseStart_700363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700363 prefixEnd_700363 := by exact prefixLift 700363
  have htrace : WordTrace (prefixWord ++ tailWord_700363) baseStart_700363 baseEnd_700363 := by
    simpa [prefixWord, tailWord_700363, baseEnd_700363] using wordTrace_append hprefix tailTrace_700363
  have hstable : (prefixWord ++ tailWord_700363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700363).length < 2 ^ (prefixWord ++ tailWord_700363).sum := by decide
  have hdescent : baseEnd_700363 < baseStart_700363 := by decide
  rcases family_descends (prefixWord ++ tailWord_700363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700364 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 1, 1, 3]
def baseStart_700364 : Nat := 118140960795 + 700364 * 2 ^ 59
def prefixEnd_700364 : Nat := 4983230072969 + 3 ^ 40 * 700364 * 2
def baseEnd_700364 : Nat := 359623365105603056329091

theorem tailTrace_700364 : CollatzResearch.WordTrace tailWord_700364 prefixEnd_700364 359623365105603056329091 := by
  unfold tailWord_700364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772186817354157746730073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17029582423138876995640097 12772186817354157746730073)
  ·
    refine ⟨9579140113015618310047555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12772186817354157746730073 9579140113015618310047555)
    ·
      refine ⟨14368710169523427465071333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9579140113015618310047555 14368710169523427465071333)
      ·
        refine ⟨2694133156785642649700875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14368710169523427465071333 2694133156785642649700875)
        ·
          refine ⟨4041199735178463974551313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694133156785642649700875 4041199735178463974551313)
          ·
            refine ⟨3030899801383847980913485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041199735178463974551313 3030899801383847980913485)
            ·
              refine ⟨1136587425518942992842557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3030899801383847980913485 1136587425518942992842557)
              ·
                refine ⟨426220284569603622315959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1136587425518942992842557 426220284569603622315959)
                ·
                  refine ⟨639330426854405433473939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426220284569603622315959 639330426854405433473939)
                  ·
                    refine ⟨958995640281608150210909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639330426854405433473939 958995640281608150210909)
                    ·
                      refine ⟨359623365105603056329091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 958995640281608150210909 359623365105603056329091)
                      ·
                        rfl

theorem cell23_700364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_700364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700364 prefixEnd_700364 := by exact prefixLift 700364
  have htrace : WordTrace (prefixWord ++ tailWord_700364) baseStart_700364 baseEnd_700364 := by
    simpa [prefixWord, tailWord_700364, baseEnd_700364] using wordTrace_append hprefix tailTrace_700364
  have hstable : (prefixWord ++ tailWord_700364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700364).length < 2 ^ (prefixWord ++ tailWord_700364).sum := by decide
  have hdescent : baseEnd_700364 < baseStart_700364 := by decide
  rcases family_descends (prefixWord ++ tailWord_700364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700381 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_700381 : Nat := 118140960795 + 700381 * 2 ^ 59
def prefixEnd_700381 : Nat := 4983230072969 + 3 ^ 40 * 700381 * 2
def baseEnd_700381 : Nat := 359632094276729489816513

theorem tailTrace_700381 : CollatzResearch.WordTrace tailWord_700381 prefixEnd_700381 359632094276729489816513 := by
  unfold tailWord_700381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25544993675646727396828997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17029995783764484931219331 25544993675646727396828997)
  ·
    refine ⟨4789686314183761386905437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25544993675646727396828997 4789686314183761386905437)
    ·
      refine ⟨1796132367818910520089539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4789686314183761386905437 1796132367818910520089539)
      ·
        refine ⟨2694198551728365780134309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796132367818910520089539 2694198551728365780134309)
        ·
          refine ⟨505162228449068583775183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2694198551728365780134309 505162228449068583775183)
          ·
            refine ⟨757743342673602875662775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505162228449068583775183 757743342673602875662775)
            ·
              refine ⟨1136615014010404313494163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757743342673602875662775 1136615014010404313494163)
              ·
                refine ⟨1704922521015606470241245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136615014010404313494163 1704922521015606470241245)
                ·
                  refine ⟨639345945380852426340467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1704922521015606470241245 639345945380852426340467)
                  ·
                    refine ⟨959018918071278639510701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639345945380852426340467 959018918071278639510701)
                    ·
                      refine ⟨359632094276729489816513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959018918071278639510701 359632094276729489816513)
                      ·
                        rfl

theorem cell23_700381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_700381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700381 prefixEnd_700381 := by exact prefixLift 700381
  have htrace : WordTrace (prefixWord ++ tailWord_700381) baseStart_700381 baseEnd_700381 := by
    simpa [prefixWord, tailWord_700381, baseEnd_700381] using wordTrace_append hprefix tailTrace_700381
  have hstable : (prefixWord ++ tailWord_700381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700381).length < 2 ^ (prefixWord ++ tailWord_700381).sum := by decide
  have hdescent : baseEnd_700381 < baseStart_700381 := by decide
  rcases family_descends (prefixWord ++ tailWord_700381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700383 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_700383 : Nat := 118140960795 + 700383 * 2 ^ 59
def prefixEnd_700383 : Nat := 4983230072969 + 3 ^ 40 * 700383 * 2
def baseEnd_700383 : Nat := 359633121238038481991503

theorem tailTrace_700383 : CollatzResearch.WordTrace tailWord_700383 prefixEnd_700383 359633121238038481991503 := by
  unfold tailWord_700383
  simp only [CollatzResearch.WordTrace]
  refine ⟨25545066621639481738401803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17030044414426321158934535 25545066621639481738401803)
  ·
    refine ⟨38317599932459222607602705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25545066621639481738401803 38317599932459222607602705)
    ·
      refine ⟨28738199949344416955702029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38317599932459222607602705 28738199949344416955702029)
      ·
        refine ⟨10776824981004156358388261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28738199949344416955702029 10776824981004156358388261)
        ·
          refine ⟨2020654683938279317197799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10776824981004156358388261 2020654683938279317197799)
          ·
            refine ⟨3030982025907418975796699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020654683938279317197799 3030982025907418975796699)
            ·
              refine ⟨4546473038861128463695049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030982025907418975796699 4546473038861128463695049)
              ·
                refine ⟨3409854779145846347771287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4546473038861128463695049 3409854779145846347771287)
                ·
                  refine ⟨5114782168718769521656931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409854779145846347771287 5114782168718769521656931)
                  ·
                    refine ⟨7672173253078154282485397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114782168718769521656931 7672173253078154282485397)
                    ·
                      refine ⟨359633121238038481991503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7672173253078154282485397 359633121238038481991503)
                      ·
                        rfl

theorem cell23_700383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_700383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700383 prefixEnd_700383 := by exact prefixLift 700383
  have htrace : WordTrace (prefixWord ++ tailWord_700383) baseStart_700383 baseEnd_700383 := by
    simpa [prefixWord, tailWord_700383, baseEnd_700383] using wordTrace_append hprefix tailTrace_700383
  have hstable : (prefixWord ++ tailWord_700383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700383).length < 2 ^ (prefixWord ++ tailWord_700383).sum := by decide
  have hdescent : baseEnd_700383 < baseStart_700383 := by decide
  rcases family_descends (prefixWord ++ tailWord_700383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700403 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 3]
def baseStart_700403 : Nat := 118140960795 + 700403 * 2 ^ 59
def prefixEnd_700403 : Nat := 4983230072969 + 3 ^ 40 * 700403 * 2
def baseEnd_700403 : Nat := 359643390851128403741411

theorem tailTrace_700403 : CollatzResearch.WordTrace tailWord_700403 prefixEnd_700403 359643390851128403741411 := by
  unfold tailWord_700403
  simp only [CollatzResearch.WordTrace]
  refine ⟨25545796081567025154129863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17030530721044683436086575 25545796081567025154129863)
  ·
    refine ⟨38318694122350537731194795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25545796081567025154129863 38318694122350537731194795)
    ·
      refine ⟨57478041183525806596792193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38318694122350537731194795 57478041183525806596792193)
      ·
        refine ⟨43108530887644354947594145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57478041183525806596792193 43108530887644354947594145)
        ·
          refine ⟨32331398165733266210695609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43108530887644354947594145 32331398165733266210695609)
          ·
            refine ⟨24248548624299949658021707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32331398165733266210695609 24248548624299949658021707)
            ·
              refine ⟨36372822936449924487032561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24248548624299949658021707 36372822936449924487032561)
              ·
                refine ⟨27279617202337443365274421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36372822936449924487032561 27279617202337443365274421)
                ·
                  refine ⟨2557464112719135315494477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27279617202337443365274421 2557464112719135315494477)
                  ·
                    refine ⟨959049042269675743310429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2557464112719135315494477 959049042269675743310429)
                    ·
                      refine ⟨359643390851128403741411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959049042269675743310429 359643390851128403741411)
                      ·
                        rfl

theorem cell23_700403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_700403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700403 prefixEnd_700403 := by exact prefixLift 700403
  have htrace : WordTrace (prefixWord ++ tailWord_700403) baseStart_700403 baseEnd_700403 := by
    simpa [prefixWord, tailWord_700403, baseEnd_700403] using wordTrace_append hprefix tailTrace_700403
  have hstable : (prefixWord ++ tailWord_700403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700403).length < 2 ^ (prefixWord ++ tailWord_700403).sum := by decide
  have hdescent : baseEnd_700403 < baseStart_700403 := by decide
  rcases family_descends (prefixWord ++ tailWord_700403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700453 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_700453 : Nat := 118140960795 + 700453 * 2 ^ 59
def prefixEnd_700453 : Nat := 4983230072969 + 3 ^ 40 * 700453 * 2
def baseEnd_700453 : Nat := 119889688294617736038727

theorem tailTrace_700453 : CollatzResearch.WordTrace tailWord_700453 prefixEnd_700453 119889688294617736038727 := by
  unfold tailWord_700453
  simp only [CollatzResearch.WordTrace]
  refine ⟨25547619731385883693450013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17031746487590589128966675 25547619731385883693450013)
  ·
    refine ⟨9580357399269706385043755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25547619731385883693450013 9580357399269706385043755)
    ·
      refine ⟨14370536098904559577565633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9580357399269706385043755 14370536098904559577565633)
      ·
        refine ⟨10777902074178419683174225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14370536098904559577565633 10777902074178419683174225)
        ·
          refine ⟨8083426555633814762380669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10777902074178419683174225 8083426555633814762380669)
          ·
            refine ⟨3031284958362680535892751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8083426555633814762380669 3031284958362680535892751)
            ·
              refine ⟨4546927437544020803839127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031284958362680535892751 4546927437544020803839127)
              ·
                refine ⟨6820391156316031205758691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546927437544020803839127 6820391156316031205758691)
                ·
                  refine ⟨10230586734474046808638037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6820391156316031205758691 10230586734474046808638037)
                  ·
                    refine ⟨119889688294617736038727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10230586734474046808638037 119889688294617736038727)
                    ·
                      rfl

theorem cell23_700453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_700453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700453 prefixEnd_700453 := by exact prefixLift 700453
  have htrace : WordTrace (prefixWord ++ tailWord_700453) baseStart_700453 baseEnd_700453 := by
    simpa [prefixWord, tailWord_700453, baseEnd_700453] using wordTrace_append hprefix tailTrace_700453
  have hstable : (prefixWord ++ tailWord_700453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700453).length < 2 ^ (prefixWord ++ tailWord_700453).sum := by decide
  have hdescent : baseEnd_700453 < baseStart_700453 := by decide
  rcases family_descends (prefixWord ++ tailWord_700453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700463 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_700463 : Nat := 118140960795 + 700463 * 2 ^ 59
def prefixEnd_700463 : Nat := 4983230072969 + 3 ^ 40 * 700463 * 2
def baseEnd_700463 : Nat := 359674199690398168991135

theorem tailTrace_700463 : CollatzResearch.WordTrace tailWord_700463 prefixEnd_700463 359674199690398168991135 := by
  unfold tailWord_700463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25547984461349655401314043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17031989640899770267542695 25547984461349655401314043)
  ·
    refine ⟨38321976692024483101971065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25547984461349655401314043 38321976692024483101971065)
    ·
      refine ⟨28741482519018362326478299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38321976692024483101971065 28741482519018362326478299)
      ·
        refine ⟨43112223778527543489717449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28741482519018362326478299 43112223778527543489717449)
        ·
          refine ⟨32334167833895657617288087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43112223778527543489717449 32334167833895657617288087)
          ·
            refine ⟨48501251750843486425932131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32334167833895657617288087 48501251750843486425932131)
            ·
              refine ⟨72751877626265229638898197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48501251750843486425932131 72751877626265229638898197)
              ·
                refine ⟨3410244263731182639323353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72751877626265229638898197 3410244263731182639323353)
                ·
                  refine ⟨2557683197798386979492515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3410244263731182639323353 2557683197798386979492515)
                  ·
                    refine ⟨3836524796697580469238773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2557683197798386979492515 3836524796697580469238773)
                    ·
                      refine ⟨359674199690398168991135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3836524796697580469238773 359674199690398168991135)
                      ·
                        rfl

theorem cell23_700463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_700463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700463 prefixEnd_700463 := by exact prefixLift 700463
  have htrace : WordTrace (prefixWord ++ tailWord_700463) baseStart_700463 baseEnd_700463 := by
    simpa [prefixWord, tailWord_700463, baseEnd_700463] using wordTrace_append hprefix tailTrace_700463
  have hstable : (prefixWord ++ tailWord_700463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700463).length < 2 ^ (prefixWord ++ tailWord_700463).sum := by decide
  have hdescent : baseEnd_700463 < baseStart_700463 := by decide
  rcases family_descends (prefixWord ++ tailWord_700463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700470 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_700470 : Nat := 118140960795 + 700470 * 2 ^ 59
def prefixEnd_700470 : Nat := 4983230072969 + 3 ^ 40 * 700470 * 2
def baseEnd_700470 : Nat := 119892598018326547201201

theorem tailTrace_700470 : CollatzResearch.WordTrace tailWord_700470 prefixEnd_700470 119892598018326547201201 := by
  unfold tailWord_700470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596764985770268474801179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17032159848216197064545909 1596764985770268474801179)
  ·
    refine ⟨2395147478655402712201769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1596764985770268474801179 2395147478655402712201769)
    ·
      refine ⟨1796360608991552034151327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2395147478655402712201769 1796360608991552034151327)
      ·
        refine ⟨2694540913487328051226991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796360608991552034151327 2694540913487328051226991)
        ·
          refine ⟨4041811370230992076840487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694540913487328051226991 4041811370230992076840487)
          ·
            refine ⟨6062717055346488115260731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041811370230992076840487 6062717055346488115260731)
            ·
              refine ⟨9094075583019732172891097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6062717055346488115260731 9094075583019732172891097)
              ·
                refine ⟨6820556687264799129668323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9094075583019732172891097 6820556687264799129668323)
                ·
                  refine ⟨10230835030897198694502485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6820556687264799129668323 10230835030897198694502485)
                  ·
                    refine ⟨119892598018326547201201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10230835030897198694502485 119892598018326547201201)
                    ·
                      rfl

theorem cell23_700470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_700470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700470 prefixEnd_700470 := by exact prefixLift 700470
  have htrace : WordTrace (prefixWord ++ tailWord_700470) baseStart_700470 baseEnd_700470 := by
    simpa [prefixWord, tailWord_700470, baseEnd_700470] using wordTrace_append hprefix tailTrace_700470
  have hstable : (prefixWord ++ tailWord_700470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700470).length < 2 ^ (prefixWord ++ tailWord_700470).sum := by decide
  have hdescent : baseEnd_700470 < baseStart_700470 := by decide
  rcases family_descends (prefixWord ++ tailWord_700470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700477 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_700477 : Nat := 118140960795 + 700477 * 2 ^ 59
def prefixEnd_700477 : Nat := 4983230072969 + 3 ^ 40 * 700477 * 2
def baseEnd_700477 : Nat := 359681388419561114216071

theorem tailTrace_700477 : CollatzResearch.WordTrace tailWord_700477 prefixEnd_700477 359681388419561114216071 := by
  unfold tailWord_700477
  simp only [CollatzResearch.WordTrace]
  refine ⟨25548495083298935792323685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17032330055532623861549123 25548495083298935792323685)
  ·
    refine ⟨4790342828118550461060691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25548495083298935792323685 4790342828118550461060691)
    ·
      refine ⟨7185514242177825691591037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4790342828118550461060691 7185514242177825691591037)
      ·
        refine ⟨2694567840816684634346639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7185514242177825691591037 2694567840816684634346639)
        ·
          refine ⟨4041851761225026951519959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694567840816684634346639 4041851761225026951519959)
          ·
            refine ⟨6062777641837540427279939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041851761225026951519959 6062777641837540427279939)
            ·
              refine ⟨9094166462756310640919909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6062777641837540427279939 9094166462756310640919909)
              ·
                refine ⟨1705156211766808245172483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9094166462756310640919909 1705156211766808245172483)
                ·
                  refine ⟨2557734317650212367758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705156211766808245172483 2557734317650212367758725)
                  ·
                    refine ⟨479575184559414818954761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2557734317650212367758725 479575184559414818954761)
                    ·
                      refine ⟨359681388419561114216071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479575184559414818954761 359681388419561114216071)
                      ·
                        rfl

theorem cell23_700477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_700477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700477 prefixEnd_700477 := by exact prefixLift 700477
  have htrace : WordTrace (prefixWord ++ tailWord_700477) baseStart_700477 baseEnd_700477 := by
    simpa [prefixWord, tailWord_700477, baseEnd_700477] using wordTrace_append hprefix tailTrace_700477
  have hstable : (prefixWord ++ tailWord_700477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700477).length < 2 ^ (prefixWord ++ tailWord_700477).sum := by decide
  have hdescent : baseEnd_700477 < baseStart_700477 := by decide
  rcases family_descends (prefixWord ++ tailWord_700477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700481 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_700481 : Nat := 118140960795 + 700481 * 2 ^ 59
def prefixEnd_700481 : Nat := 4983230072969 + 3 ^ 40 * 700481 * 2
def baseEnd_700481 : Nat := 359683442342179098566053

theorem tailTrace_700481 : CollatzResearch.WordTrace tailWord_700481 prefixEnd_700481 359683442342179098566053 := by
  unfold tailWord_700481
  simp only [CollatzResearch.WordTrace]
  refine ⟨25548640975284444475469297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17032427316856296316979531 25548640975284444475469297)
  ·
    refine ⟨19161480731463333356601973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25548640975284444475469297 19161480731463333356601973)
    ·
      refine ⟨1796388818574687502181435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19161480731463333356601973 1796388818574687502181435)
      ·
        refine ⟨2694583227862031253272153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796388818574687502181435 2694583227862031253272153)
        ·
          refine ⟨2020937420896523439954115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694583227862031253272153 2020937420896523439954115)
          ·
            refine ⟨3031406131344785159931173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020937420896523439954115 3031406131344785159931173)
            ·
              refine ⟨568388649627147217487095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3031406131344785159931173 568388649627147217487095)
              ·
                refine ⟨852582974440720826230643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568388649627147217487095 852582974440720826230643)
                ·
                  refine ⟨1278874461661081239345965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852582974440720826230643 1278874461661081239345965)
                  ·
                    refine ⟨479577923122905464754737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278874461661081239345965 479577923122905464754737)
                    ·
                      refine ⟨359683442342179098566053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479577923122905464754737 359683442342179098566053)
                      ·
                        rfl

theorem cell23_700481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_700481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700481 prefixEnd_700481 := by exact prefixLift 700481
  have htrace : WordTrace (prefixWord ++ tailWord_700481) baseStart_700481 baseEnd_700481 := by
    simpa [prefixWord, tailWord_700481, baseEnd_700481] using wordTrace_append hprefix tailTrace_700481
  have hstable : (prefixWord ++ tailWord_700481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700481).length < 2 ^ (prefixWord ++ tailWord_700481).sum := by decide
  have hdescent : baseEnd_700481 < baseStart_700481 := by decide
  rcases family_descends (prefixWord ++ tailWord_700481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700494 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_700494 : Nat := 118140960795 + 700494 * 2 ^ 59
def prefixEnd_700494 : Nat := 4983230072969 + 3 ^ 40 * 700494 * 2
def baseEnd_700494 : Nat := 359690117590687547703493

theorem tailTrace_700494 : CollatzResearch.WordTrace tailWord_700494 prefixEnd_700494 359690117590687547703493 := by
  unfold tailWord_700494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193639390529668461961567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17032743416158231797128357 3193639390529668461961567)
  ·
    refine ⟨4790459085794502692942351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3193639390529668461961567 4790459085794502692942351)
    ·
      refine ⟨7185688628691754039413527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4790459085794502692942351 7185688628691754039413527)
      ·
        refine ⟨10778532943037631059120291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7185688628691754039413527 10778532943037631059120291)
        ·
          refine ⟨16167799414556446588680437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10778532943037631059120291 16167799414556446588680437)
          ·
            refine ⟨1515731195114666867688791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16167799414556446588680437 1515731195114666867688791)
            ·
              refine ⟨2273596792672000301533187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515731195114666867688791 2273596792672000301533187)
              ·
                refine ⟨3410395189008000452299781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273596792672000301533187 3410395189008000452299781)
                ·
                  refine ⟨639449097939000084806209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3410395189008000452299781 639449097939000084806209)
                  ·
                    refine ⟨479586823454250063604657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639449097939000084806209 479586823454250063604657)
                    ·
                      refine ⟨359690117590687547703493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479586823454250063604657 359690117590687547703493)
                      ·
                        rfl

theorem cell23_700494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_700494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700494 prefixEnd_700494 := by exact prefixLift 700494
  have htrace : WordTrace (prefixWord ++ tailWord_700494) baseStart_700494 baseEnd_700494 := by
    simpa [prefixWord, tailWord_700494, baseEnd_700494] using wordTrace_append hprefix tailTrace_700494
  have hstable : (prefixWord ++ tailWord_700494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700494).length < 2 ^ (prefixWord ++ tailWord_700494).sum := by decide
  have hdescent : baseEnd_700494 < baseStart_700494 := by decide
  rcases family_descends (prefixWord ++ tailWord_700494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700530 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_700530 : Nat := 118140960795 + 700530 * 2 ^ 59
def prefixEnd_700530 : Nat := 4983230072969 + 3 ^ 40 * 700530 * 2
def baseEnd_700530 : Nat := 119902867631416468951109

theorem tailTrace_700530 : CollatzResearch.WordTrace tailWord_700530 prefixEnd_700530 119902867631416468951109 := by
  unfold tailWord_700530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387607038026731461000761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17033618768071283896002029 6387607038026731461000761)
  ·
    refine ⟨4790705278520048595750571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6387607038026731461000761 4790705278520048595750571)
    ·
      refine ⟨7186057917780072893625857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4790705278520048595750571 7186057917780072893625857)
      ·
        refine ⟨5389543438335054670219393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7186057917780072893625857 5389543438335054670219393)
        ·
          refine ⟨4042157578751291002664545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5389543438335054670219393 4042157578751291002664545)
          ·
            refine ⟨3031618184063468251998409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042157578751291002664545 3031618184063468251998409)
            ·
              refine ⟨2273713638047601188998807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3031618184063468251998409 2273713638047601188998807)
              ·
                refine ⟨3410570457071401783498211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273713638047601188998807 3410570457071401783498211)
                ·
                  refine ⟨5115855685607102675247317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410570457071401783498211 5115855685607102675247317)
                  ·
                    refine ⟨119902867631416468951109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5115855685607102675247317 119902867631416468951109)
                    ·
                      rfl

theorem cell23_700530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_700530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700530 prefixEnd_700530 := by exact prefixLift 700530
  have htrace : WordTrace (prefixWord ++ tailWord_700530) baseStart_700530 baseEnd_700530 := by
    simpa [prefixWord, tailWord_700530, baseEnd_700530] using wordTrace_append hprefix tailTrace_700530
  have hstable : (prefixWord ++ tailWord_700530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700530).length < 2 ^ (prefixWord ++ tailWord_700530).sum := by decide
  have hdescent : baseEnd_700530 < baseStart_700530 := by decide
  rcases family_descends (prefixWord ++ tailWord_700530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700534 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_700534 : Nat := 118140960795 + 700534 * 2 ^ 59
def prefixEnd_700534 : Nat := 4983230072969 + 3 ^ 40 * 700534 * 2
def baseEnd_700534 : Nat := 39967850757429710133701

theorem tailTrace_700534 : CollatzResearch.WordTrace tailWord_700534 prefixEnd_700534 39967850757429710133701 := by
  unfold tailWord_700534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596910877755777157946791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17033716029394956351432437 1596910877755777157946791)
  ·
    refine ⟨2395366316633665736920187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1596910877755777157946791 2395366316633665736920187)
    ·
      refine ⟨3593049474950498605380281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395366316633665736920187 3593049474950498605380281)
      ·
        refine ⟨2694787106212873954035211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3593049474950498605380281 2694787106212873954035211)
        ·
          refine ⟨4042180659319310931052817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694787106212873954035211 4042180659319310931052817)
          ·
            refine ⟨3031635494489483198289613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042180659319310931052817 3031635494489483198289613)
            ·
              refine ⟨1136863310433556199358605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3031635494489483198289613 1136863310433556199358605)
              ·
                refine ⟨426323741412583574759477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1136863310433556199358605 426323741412583574759477)
                ·
                  refine ⟨39967850757429710133701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 426323741412583574759477 39967850757429710133701)
                  ·
                    rfl

theorem cell23_700534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_700534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700534 prefixEnd_700534 := by exact prefixLift 700534
  have htrace : WordTrace (prefixWord ++ tailWord_700534) baseStart_700534 baseEnd_700534 := by
    simpa [prefixWord, tailWord_700534, baseEnd_700534] using wordTrace_append hprefix tailTrace_700534
  have hstable : (prefixWord ++ tailWord_700534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700534).length < 2 ^ (prefixWord ++ tailWord_700534).sum := by decide
  have hdescent : baseEnd_700534 < baseStart_700534 := by decide
  rcases family_descends (prefixWord ++ tailWord_700534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700594 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_700594 : Nat := 118140960795 + 700594 * 2 ^ 59
def prefixEnd_700594 : Nat := 4983230072969 + 3 ^ 40 * 700594 * 2
def baseEnd_700594 : Nat := 119913821885379052151011

theorem tailTrace_700594 : CollatzResearch.WordTrace tailWord_700594 prefixEnd_700594 119913821885379052151011 := by
  unfold tailWord_700594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388190605968766193583209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17035174949250043182888557 6388190605968766193583209)
  ·
    refine ⟨4791142954476574645187407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6388190605968766193583209 4791142954476574645187407)
    ·
      refine ⟨7186714431714861967781111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791142954476574645187407 7186714431714861967781111)
      ·
        refine ⟨10780071647572292951671667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186714431714861967781111 10780071647572292951671667)
        ·
          refine ⟨16170107471358439427507501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10780071647572292951671667 16170107471358439427507501)
          ·
            refine ⟨6063790301759414785315313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16170107471358439427507501 6063790301759414785315313)
            ·
              refine ⟨4547842726319561088986485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6063790301759414785315313 4547842726319561088986485)
              ·
                refine ⟨426360255592458852092483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4547842726319561088986485 426360255592458852092483)
                ·
                  refine ⟨639540383388688278138725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426360255592458852092483 639540383388688278138725)
                  ·
                    refine ⟨119913821885379052151011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639540383388688278138725 119913821885379052151011)
                    ·
                      rfl

theorem cell23_700594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_700594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700594 prefixEnd_700594 := by exact prefixLift 700594
  have htrace : WordTrace (prefixWord ++ tailWord_700594) baseStart_700594 baseEnd_700594 := by
    simpa [prefixWord, tailWord_700594, baseEnd_700594] using wordTrace_append hprefix tailTrace_700594
  have hstable : (prefixWord ++ tailWord_700594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700594).length < 2 ^ (prefixWord ++ tailWord_700594).sum := by decide
  have hdescent : baseEnd_700594 < baseStart_700594 := by decide
  rcases family_descends (prefixWord ++ tailWord_700594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700651 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 1, 1, 3]
def baseStart_700651 : Nat := 118140960795 + 700651 * 2 ^ 59
def prefixEnd_700651 : Nat := 4983230072969 + 3 ^ 40 * 700651 * 2
def baseEnd_700651 : Nat := 359770734053443433440271

theorem tailTrace_700651 : CollatzResearch.WordTrace tailWord_700651 prefixEnd_700651 359770734053443433440271 := by
  unfold tailWord_700651
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554841384668563509157807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17036560923112375672771871 25554841384668563509157807)
  ·
    refine ⟨38332262077002845263736711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25554841384668563509157807 38332262077002845263736711)
    ·
      refine ⟨57498393115504267895605067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38332262077002845263736711 57498393115504267895605067)
      ·
        refine ⟨86247589673256401843407601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57498393115504267895605067 86247589673256401843407601)
        ·
          refine ⟨64685692254942301382555701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86247589673256401843407601 64685692254942301382555701)
          ·
            refine ⟨6064283648900840754614597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64685692254942301382555701 6064283648900840754614597)
            ·
              refine ⟨1137053184168907641490237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6064283648900840754614597 1137053184168907641490237)
              ·
                refine ⟨426394944063340365558839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137053184168907641490237 426394944063340365558839)
                ·
                  refine ⟨639592416095010548338259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426394944063340365558839 639592416095010548338259)
                  ·
                    refine ⟨959388624142515822507389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639592416095010548338259 959388624142515822507389)
                    ·
                      refine ⟨359770734053443433440271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959388624142515822507389 359770734053443433440271)
                      ·
                        rfl

theorem cell23_700651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 1, 3].length) (baseStart_700651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700651 prefixEnd_700651 := by exact prefixLift 700651
  have htrace : WordTrace (prefixWord ++ tailWord_700651) baseStart_700651 baseEnd_700651 := by
    simpa [prefixWord, tailWord_700651, baseEnd_700651] using wordTrace_append hprefix tailTrace_700651
  have hstable : (prefixWord ++ tailWord_700651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700651).length < 2 ^ (prefixWord ++ tailWord_700651).sum := by decide
  have hdescent : baseEnd_700651 < baseStart_700651 := by decide
  rcases family_descends (prefixWord ++ tailWord_700651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700677 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_700677 : Nat := 118140960795 + 700677 * 2 ^ 59
def prefixEnd_700677 : Nat := 4983230072969 + 3 ^ 40 * 700677 * 2
def baseEnd_700677 : Nat := 359784084550460331715151

theorem tailTrace_700677 : CollatzResearch.WordTrace tailWord_700677 prefixEnd_700677 359784084550460331715151 := by
  unfold tailWord_700677
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555789682574369949604285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17037193121716246633069523 25555789682574369949604285)
  ·
    refine ⟨9583421130965388731101607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25555789682574369949604285 9583421130965388731101607)
    ·
      refine ⟨14375131696448083096652411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583421130965388731101607 14375131696448083096652411)
      ·
        refine ⟨21562697544672124644978617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14375131696448083096652411 21562697544672124644978617)
        ·
          refine ⟨16172023158504093483733963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21562697544672124644978617 16172023158504093483733963)
          ·
            refine ⟨24258034737756140225600945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16172023158504093483733963 24258034737756140225600945)
            ·
              refine ⟨18193526053317105169200709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24258034737756140225600945 18193526053317105169200709)
              ·
                refine ⟨3411286134996957219225133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18193526053317105169200709 3411286134996957219225133)
                ·
                  refine ⟨1279232300623858957209425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3411286134996957219225133 1279232300623858957209425)
                  ·
                    refine ⟨959424225467894217907069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1279232300623858957209425 959424225467894217907069)
                    ·
                      refine ⟨359784084550460331715151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959424225467894217907069 359784084550460331715151)
                      ·
                        rfl

theorem cell23_700677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_700677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700677 prefixEnd_700677 := by exact prefixLift 700677
  have htrace : WordTrace (prefixWord ++ tailWord_700677) baseStart_700677 baseEnd_700677 := by
    simpa [prefixWord, tailWord_700677, baseEnd_700677] using wordTrace_append hprefix tailTrace_700677
  have hstable : (prefixWord ++ tailWord_700677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700677).length < 2 ^ (prefixWord ++ tailWord_700677).sum := by decide
  have hdescent : baseEnd_700677 < baseStart_700677 := by decide
  rcases family_descends (prefixWord ++ tailWord_700677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700702 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_700702 : Nat := 118140960795 + 700702 * 2 ^ 59
def prefixEnd_700702 : Nat := 4983230072969 + 3 ^ 40 * 700702 * 2
def baseEnd_700702 : Nat := 359796921566822733902537

theorem tailTrace_700702 : CollatzResearch.WordTrace tailWord_700702 prefixEnd_700702 359796921566822733902537 := by
  unfold tailWord_700702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194587688435474902408045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17037801004989199479509573 3194587688435474902408045)
  ·
    refine ⟨1197970383163303088403017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3194587688435474902408045 1197970383163303088403017)
    ·
      refine ⟨898477787372477316302263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197970383163303088403017 898477787372477316302263)
      ·
        refine ⟨1347716681058715974453395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898477787372477316302263 1347716681058715974453395)
        ·
          refine ⟨2021575021588073961680093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347716681058715974453395 2021575021588073961680093)
          ·
            refine ⟨758090633095527735630035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2021575021588073961680093 758090633095527735630035)
            ·
              refine ⟨1137135949643291603445053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758090633095527735630035 1137135949643291603445053)
              ·
                refine ⟨426425981116234351291895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137135949643291603445053 426425981116234351291895)
                ·
                  refine ⟨639638971674351526937843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426425981116234351291895 639638971674351526937843)
                  ·
                    refine ⟨959458457511527290406765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639638971674351526937843 959458457511527290406765)
                    ·
                      refine ⟨359796921566822733902537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959458457511527290406765 359796921566822733902537)
                      ·
                        rfl

theorem cell23_700702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_700702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700702 prefixEnd_700702 := by exact prefixLift 700702
  have htrace : WordTrace (prefixWord ++ tailWord_700702) baseStart_700702 baseEnd_700702 := by
    simpa [prefixWord, tailWord_700702, baseEnd_700702] using wordTrace_append hprefix tailTrace_700702
  have hstable : (prefixWord ++ tailWord_700702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700702).length < 2 ^ (prefixWord ++ tailWord_700702).sum := by decide
  have hdescent : baseEnd_700702 < baseStart_700702 := by decide
  rcases family_descends (prefixWord ++ tailWord_700702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700707 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 3]
def baseStart_700707 : Nat := 118140960795 + 700707 * 2 ^ 59
def prefixEnd_700707 : Nat := 4983230072969 + 3 ^ 40 * 700707 * 2
def baseEnd_700707 : Nat := 359799488970095214340013

theorem tailTrace_700707 : CollatzResearch.WordTrace tailWord_700707 prefixEnd_700707 359799488970095214340013 := by
  unfold tailWord_700707
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556883872465685073196375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17037922581643790048797583 25556883872465685073196375)
  ·
    refine ⟨38335325808698527609794563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25556883872465685073196375 38335325808698527609794563)
    ·
      refine ⟨57502988713047791414691845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38335325808698527609794563 57502988713047791414691845)
      ·
        refine ⟨10781810383696460890254721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57502988713047791414691845 10781810383696460890254721)
        ·
          refine ⟨8086357787772345667691041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10781810383696460890254721 8086357787772345667691041)
          ·
            refine ⟨6064768340829259250768281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086357787772345667691041 6064768340829259250768281)
            ·
              refine ⟨4548576255621944438076211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064768340829259250768281 4548576255621944438076211)
              ·
                refine ⟨6822864383432916657114317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548576255621944438076211 6822864383432916657114317)
                ·
                  refine ⟨2558574143787343746417869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6822864383432916657114317 2558574143787343746417869)
                  ·
                    refine ⟨959465303920253904906701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2558574143787343746417869 959465303920253904906701)
                    ·
                      refine ⟨359799488970095214340013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959465303920253904906701 359799488970095214340013)
                      ·
                        rfl

theorem cell23_700707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_700707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700707 prefixEnd_700707 := by exact prefixLift 700707
  have htrace : WordTrace (prefixWord ++ tailWord_700707) baseStart_700707 baseEnd_700707 := by
    simpa [prefixWord, tailWord_700707, baseEnd_700707] using wordTrace_append hprefix tailTrace_700707
  have hstable : (prefixWord ++ tailWord_700707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700707).length < 2 ^ (prefixWord ++ tailWord_700707).sum := by decide
  have hdescent : baseEnd_700707 < baseStart_700707 := by decide
  rcases family_descends (prefixWord ++ tailWord_700707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700714 : List Nat := [3, 1, 4, 2, 2, 2, 9]
def baseStart_700714 : Nat := 118140960795 + 700714 * 2 ^ 59
def prefixEnd_700714 : Nat := 4983230072969 + 3 ^ 40 * 700714 * 2
def baseEnd_700714 : Nat := 4442013374502181320401

theorem tailTrace_700714 : CollatzResearch.WordTrace tailWord_700714 prefixEnd_700714 4442013374502181320401 := by
  unfold tailWord_700714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389284795860081317175299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17038092788960216845800797 6389284795860081317175299)
  ·
    refine ⟨9583927193790121975762949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6389284795860081317175299 9583927193790121975762949)
    ·
      refine ⟨1796986348835647870455553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9583927193790121975762949 1796986348835647870455553)
      ·
        refine ⟨1347739761626735902841665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1796986348835647870455553 1347739761626735902841665)
        ·
          refine ⟨1010804821220051927131249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347739761626735902841665 1010804821220051927131249)
          ·
            refine ⟨758103615915038945348437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1010804821220051927131249 758103615915038945348437)
            ·
              refine ⟨4442013374502181320401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 758103615915038945348437 4442013374502181320401)
              ·
                rfl

theorem cell23_700714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 9].length) (baseStart_700714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700714 prefixEnd_700714 := by exact prefixLift 700714
  have htrace : WordTrace (prefixWord ++ tailWord_700714) baseStart_700714 baseEnd_700714 := by
    simpa [prefixWord, tailWord_700714, baseEnd_700714] using wordTrace_append hprefix tailTrace_700714
  have hstable : (prefixWord ++ tailWord_700714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700714).length < 2 ^ (prefixWord ++ tailWord_700714).sum := by decide
  have hdescent : baseEnd_700714 < baseStart_700714 := by decide
  rcases family_descends (prefixWord ++ tailWord_700714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700725 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_700725 : Nat := 118140960795 + 700725 * 2 ^ 59
def prefixEnd_700725 : Nat := 4983230072969 + 3 ^ 40 * 700725 * 2
def baseEnd_700725 : Nat := 359808731621876143914931

theorem tailTrace_700725 : CollatzResearch.WordTrace tailWord_700725 prefixEnd_700725 359808731621876143914931 := by
  unfold tailWord_700725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25557540386400474147351629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17038360257600316098234419 25557540386400474147351629)
  ·
    refine ⟨9584077644900177805256861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25557540386400474147351629 9584077644900177805256861)
    ·
      refine ⟨3594029116837566676971323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9584077644900177805256861 3594029116837566676971323)
      ·
        refine ⟨5391043675256350015456985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594029116837566676971323 5391043675256350015456985)
        ·
          refine ⟨4043282756442262511592739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5391043675256350015456985 4043282756442262511592739)
          ·
            refine ⟨6064924134663393767389109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043282756442262511592739 6064924134663393767389109)
            ·
              refine ⟨568586637624693165692729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6064924134663393767389109 568586637624693165692729)
              ·
                refine ⟨426439978218519874269547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568586637624693165692729 426439978218519874269547)
                ·
                  refine ⟨639659967327779811404321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426439978218519874269547 639659967327779811404321)
                  ·
                    refine ⟨479744975495834858553241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639659967327779811404321 479744975495834858553241)
                    ·
                      refine ⟨359808731621876143914931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479744975495834858553241 359808731621876143914931)
                      ·
                        rfl

theorem cell23_700725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_700725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700725 prefixEnd_700725 := by exact prefixLift 700725
  have htrace : WordTrace (prefixWord ++ tailWord_700725) baseStart_700725 baseEnd_700725 := by
    simpa [prefixWord, tailWord_700725, baseEnd_700725] using wordTrace_append hprefix tailTrace_700725
  have hstable : (prefixWord ++ tailWord_700725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700725).length < 2 ^ (prefixWord ++ tailWord_700725).sum := by decide
  have hdescent : baseEnd_700725 < baseStart_700725 := by decide
  rcases family_descends (prefixWord ++ tailWord_700725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700767 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_700767 : Nat := 118140960795 + 700767 * 2 ^ 59
def prefixEnd_700767 : Nat := 4983230072969 + 3 ^ 40 * 700767 * 2
def baseEnd_700767 : Nat := 359830297809364979589737

theorem tailTrace_700767 : CollatzResearch.WordTrace tailWord_700767 prefixEnd_700767 359830297809364979589737 := by
  unfold tailWord_700767
  simp only [CollatzResearch.WordTrace]
  refine ⟨25559072252248315320380555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17039381501498876880253703 25559072252248315320380555)
  ·
    refine ⟨38338608378372472980570833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25559072252248315320380555 38338608378372472980570833)
    ·
      refine ⟨28753956283779354735428125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38338608378372472980570833 28753956283779354735428125)
      ·
        refine ⟨10782733606417258025785547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28753956283779354735428125 10782733606417258025785547)
        ·
          refine ⟨16174100409625887038678321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10782733606417258025785547 16174100409625887038678321)
          ·
            refine ⟨12130575307219415279008741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16174100409625887038678321 12130575307219415279008741)
            ·
              refine ⟨2274482870103640364814139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12130575307219415279008741 2274482870103640364814139)
              ·
                refine ⟨3411724305155460547221209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274482870103640364814139 3411724305155460547221209)
                ·
                  refine ⟨2558793228866595410415907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411724305155460547221209 2558793228866595410415907)
                  ·
                    refine ⟨3838189843299893115623861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558793228866595410415907 3838189843299893115623861)
                    ·
                      refine ⟨359830297809364979589737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3838189843299893115623861 359830297809364979589737)
                      ·
                        rfl

theorem cell23_700767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_700767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700767 prefixEnd_700767 := by exact prefixLift 700767
  have htrace : WordTrace (prefixWord ++ tailWord_700767) baseStart_700767 baseEnd_700767 := by
    simpa [prefixWord, tailWord_700767, baseEnd_700767] using wordTrace_append hprefix tailTrace_700767
  have hstable : (prefixWord ++ tailWord_700767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700767).length < 2 ^ (prefixWord ++ tailWord_700767).sum := by decide
  have hdescent : baseEnd_700767 < baseStart_700767 := by decide
  rcases family_descends (prefixWord ++ tailWord_700767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700777 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_700777 : Nat := 118140960795 + 700777 * 2 ^ 59
def prefixEnd_700777 : Nat := 4983230072969 + 3 ^ 40 * 700777 * 2
def baseEnd_700777 : Nat := 359835432615909940464691

theorem tailTrace_700777 : CollatzResearch.WordTrace tailWord_700777 prefixEnd_700777 359835432615909940464691 := by
  unfold tailWord_700777
  simp only [CollatzResearch.WordTrace]
  refine ⟨25559436982212087028244585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17039624654808058018829723 25559436982212087028244585)
  ·
    refine ⟨19169577736659065271183439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25559436982212087028244585 19169577736659065271183439)
    ·
      refine ⟨28754366604988597906775159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19169577736659065271183439 28754366604988597906775159)
      ·
        refine ⟨43131549907482896860162739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28754366604988597906775159 43131549907482896860162739)
        ·
          refine ⟨64697324861224345290244109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43131549907482896860162739 64697324861224345290244109)
          ·
            refine ⟨24261496822959129483841541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64697324861224345290244109 24261496822959129483841541)
            ·
              refine ⟨4549030654304836778220289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24261496822959129483841541 4549030654304836778220289)
              ·
                refine ⟨3411772990728627583665217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549030654304836778220289 3411772990728627583665217)
                ·
                  refine ⟨2558829743046470687748913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411772990728627583665217 2558829743046470687748913)
                  ·
                    refine ⟨1919122307284853015811685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558829743046470687748913 1919122307284853015811685)
                    ·
                      refine ⟨359835432615909940464691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1919122307284853015811685 359835432615909940464691)
                      ·
                        rfl

theorem cell23_700777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_700777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700777 prefixEnd_700777 := by exact prefixLift 700777
  have htrace : WordTrace (prefixWord ++ tailWord_700777) baseStart_700777 baseEnd_700777 := by
    simpa [prefixWord, tailWord_700777, baseEnd_700777] using wordTrace_append hprefix tailTrace_700777
  have hstable : (prefixWord ++ tailWord_700777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700777).length < 2 ^ (prefixWord ++ tailWord_700777).sum := by decide
  have hdescent : baseEnd_700777 < baseStart_700777 := by decide
  rcases family_descends (prefixWord ++ tailWord_700777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700834 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_700834 : Nat := 118140960795 + 700834 * 2 ^ 59
def prefixEnd_700834 : Nat := 4983230072969 + 3 ^ 40 * 700834 * 2
def baseEnd_700834 : Nat := 119954900337738739150643

theorem tailTrace_700834 : CollatzResearch.WordTrace tailWord_700834 prefixEnd_700834 119954900337738739150643 := by
  unfold tailWord_700834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390378985751396440767389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17041010628670390508713037 6390378985751396440767389)
  ·
    refine ⟨2396392119656773665287771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6390378985751396440767389 2396392119656773665287771)
    ·
      refine ⟨3594588179485160497931657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2396392119656773665287771 3594588179485160497931657)
      ·
        refine ⟨2695941134613870373448743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3594588179485160497931657 2695941134613870373448743)
        ·
          refine ⟨4043911701920805560173115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695941134613870373448743 4043911701920805560173115)
          ·
            refine ⟨6065867552881208340259673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043911701920805560173115 6065867552881208340259673)
            ·
              refine ⟨4549400664660906255194755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6065867552881208340259673 4549400664660906255194755)
              ·
                refine ⟨6824100996991359382792133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4549400664660906255194755 6824100996991359382792133)
                ·
                  refine ⟨1279518936935879884273525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6824100996991359382792133 1279518936935879884273525)
                  ·
                    refine ⟨119954900337738739150643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1279518936935879884273525 119954900337738739150643)
                    ·
                      rfl

theorem cell23_700834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_700834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700834 prefixEnd_700834 := by exact prefixLift 700834
  have htrace : WordTrace (prefixWord ++ tailWord_700834) baseStart_700834 baseEnd_700834 := by
    simpa [prefixWord, tailWord_700834, baseEnd_700834] using wordTrace_append hprefix tailTrace_700834
  have hstable : (prefixWord ++ tailWord_700834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700834).length < 2 ^ (prefixWord ++ tailWord_700834).sum := by decide
  have hdescent : baseEnd_700834 < baseStart_700834 := by decide
  rcases family_descends (prefixWord ++ tailWord_700834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700867 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4]
def baseStart_700867 : Nat := 118140960795 + 700867 * 2 ^ 59
def prefixEnd_700867 : Nat := 4983230072969 + 3 ^ 40 * 700867 * 2
def baseEnd_700867 : Nat := 359881645874814588339277

theorem tailTrace_700867 : CollatzResearch.WordTrace tailWord_700867 prefixEnd_700867 359881645874814588339277 := by
  unfold tailWord_700867
  simp only [CollatzResearch.WordTrace]
  refine ⟨25562719551886032399020855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17041813034590688266013903 25562719551886032399020855)
  ·
    refine ⟨38344079327829048598531283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25562719551886032399020855 38344079327829048598531283)
    ·
      refine ⟨57516118991743572897796925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38344079327829048598531283 57516118991743572897796925)
      ·
        refine ⟨21568544621903839836673847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57516118991743572897796925 21568544621903839836673847)
        ·
          refine ⟨32352816932855759755010771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21568544621903839836673847 32352816932855759755010771)
          ·
            refine ⟨48529225399283639632516157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32352816932855759755010771 48529225399283639632516157)
            ·
              refine ⟨18198459524731364862193559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48529225399283639632516157 18198459524731364862193559)
              ·
                refine ⟨27297689287097047293290339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18198459524731364862193559 27297689287097047293290339)
                ·
                  refine ⟨40946533930645570939935509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27297689287097047293290339 40946533930645570939935509)
                  ·
                    refine ⟨1919368777999011137809477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40946533930645570939935509 1919368777999011137809477)
                    ·
                      refine ⟨359881645874814588339277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1919368777999011137809477 359881645874814588339277)
                      ·
                        rfl

theorem cell23_700867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_700867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700867 prefixEnd_700867 := by exact prefixLift 700867
  have htrace : WordTrace (prefixWord ++ tailWord_700867) baseStart_700867 baseEnd_700867 := by
    simpa [prefixWord, tailWord_700867, baseEnd_700867] using wordTrace_append hprefix tailTrace_700867
  have hstable : (prefixWord ++ tailWord_700867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700867).length < 2 ^ (prefixWord ++ tailWord_700867).sum := by decide
  have hdescent : baseEnd_700867 < baseStart_700867 := by decide
  rcases family_descends (prefixWord ++ tailWord_700867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700874 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_700874 : Nat := 118140960795 + 700874 * 2 ^ 59
def prefixEnd_700874 : Nat := 4983230072969 + 3 ^ 40 * 700874 * 2
def baseEnd_700874 : Nat := 359885240239396060951745

theorem tailTrace_700874 : CollatzResearch.WordTrace tailWord_700874 prefixEnd_700874 359885240239396060951745 := by
  unfold tailWord_700874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390743715715168148631419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17041983241907115063017117 6390743715715168148631419)
  ·
    refine ⟨9586115573572752222947129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6390743715715168148631419 9586115573572752222947129)
    ·
      refine ⟨7189586680179564167210347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9586115573572752222947129 7189586680179564167210347)
      ·
        refine ⟨10784380020269346250815521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189586680179564167210347 10784380020269346250815521)
        ·
          refine ⟨8088285015202009688111641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10784380020269346250815521 8088285015202009688111641)
          ·
            refine ⟨6066213761401507266083731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8088285015202009688111641 6066213761401507266083731)
            ·
              refine ⟨9099320642102260899125597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066213761401507266083731 9099320642102260899125597)
              ·
                refine ⟨3412245240788347837172099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9099320642102260899125597 3412245240788347837172099)
                ·
                  refine ⟨5118367861182521755758149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412245240788347837172099 5118367861182521755758149)
                  ·
                    refine ⟨959693973971722829204653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118367861182521755758149 959693973971722829204653)
                    ·
                      refine ⟨359885240239396060951745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959693973971722829204653 359885240239396060951745)
                      ·
                        rfl

theorem cell23_700874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_700874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700874 prefixEnd_700874 := by exact prefixLift 700874
  have htrace : WordTrace (prefixWord ++ tailWord_700874) baseStart_700874 baseEnd_700874 := by
    simpa [prefixWord, tailWord_700874, baseEnd_700874] using wordTrace_append hprefix tailTrace_700874
  have hstable : (prefixWord ++ tailWord_700874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700874).length < 2 ^ (prefixWord ++ tailWord_700874).sum := by decide
  have hdescent : baseEnd_700874 < baseStart_700874 := by decide
  rcases family_descends (prefixWord ++ tailWord_700874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700921 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 3]
def baseStart_700921 : Nat := 118140960795 + 700921 * 2 ^ 59
def prefixEnd_700921 : Nat := 4983230072969 + 3 ^ 40 * 700921 * 2
def baseEnd_700921 : Nat := 359909373830157377064029

theorem tailTrace_700921 : CollatzResearch.WordTrace tailWord_700921 prefixEnd_700921 359909373830157377064029 := by
  unfold tailWord_700921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25564689093690399621486617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17043126062460266414324411 25564689093690399621486617)
  ·
    refine ⟨19173516820267799716114963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25564689093690399621486617 19173516820267799716114963)
    ·
      refine ⟨28760275230401699574172445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19173516820267799716114963 28760275230401699574172445)
      ·
        refine ⟨10785103211400637340314667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28760275230401699574172445 10785103211400637340314667)
        ·
          refine ⟨16177654817100956010472001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10785103211400637340314667 16177654817100956010472001)
          ·
            refine ⟨12133241112825717007854001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16177654817100956010472001 12133241112825717007854001)
            ·
              refine ⟨9099930834619287755890501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12133241112825717007854001 9099930834619287755890501)
              ·
                refine ⟨1706237031491116454229469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9099930834619287755890501 1706237031491116454229469)
                ·
                  refine ⟨639838886809168670336051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1706237031491116454229469 639838886809168670336051)
                  ·
                    refine ⟨959758330213753005504077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639838886809168670336051 959758330213753005504077)
                    ·
                      refine ⟨359909373830157377064029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959758330213753005504077 359909373830157377064029)
                      ·
                        rfl

theorem cell23_700921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_700921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700921 prefixEnd_700921 := by exact prefixLift 700921
  have htrace : WordTrace (prefixWord ++ tailWord_700921) baseStart_700921 baseEnd_700921 := by
    simpa [prefixWord, tailWord_700921, baseEnd_700921] using wordTrace_append hprefix tailTrace_700921
  have hstable : (prefixWord ++ tailWord_700921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700921).length < 2 ^ (prefixWord ++ tailWord_700921).sum := by decide
  have hdescent : baseEnd_700921 < baseStart_700921 := by decide
  rcases family_descends (prefixWord ++ tailWord_700921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700978 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_700978 : Nat := 118140960795 + 700978 * 2 ^ 59
def prefixEnd_700978 : Nat := 4983230072969 + 3 ^ 40 * 700978 * 2
def baseEnd_700978 : Nat := 359938642227463654051267

theorem tailTrace_700978 : CollatzResearch.WordTrace tailWord_700978 prefixEnd_700978 359938642227463654051267 := by
  unfold tailWord_700978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391692013620974589077897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17044512036322598904207725 6391692013620974589077897)
  ·
    refine ⟨4793769010215730941808423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6391692013620974589077897 4793769010215730941808423)
    ·
      refine ⟨7190653515323596412712635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793769010215730941808423 7190653515323596412712635)
      ·
        refine ⟨10785980272985394619068953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190653515323596412712635 10785980272985394619068953)
        ·
          refine ⟨8089485204739045964301715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10785980272985394619068953 8089485204739045964301715)
          ·
            refine ⟨12134227807108568946452573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089485204739045964301715 12134227807108568946452573)
            ·
              refine ⟨4550335427665713354919715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12134227807108568946452573 4550335427665713354919715)
              ·
                refine ⟨6825503141498570032379573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550335427665713354919715 6825503141498570032379573)
                ·
                  refine ⟨639890919515490940535585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6825503141498570032379573 639890919515490940535585)
                  ·
                    refine ⟨479918189636618205401689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639890919515490940535585 479918189636618205401689)
                    ·
                      refine ⟨359938642227463654051267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479918189636618205401689 359938642227463654051267)
                      ·
                        rfl

theorem cell23_700978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_700978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700978 prefixEnd_700978 := by exact prefixLift 700978
  have htrace : WordTrace (prefixWord ++ tailWord_700978) baseStart_700978 baseEnd_700978 := by
    simpa [prefixWord, tailWord_700978, baseEnd_700978] using wordTrace_append hprefix tailTrace_700978
  have hstable : (prefixWord ++ tailWord_700978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700978).length < 2 ^ (prefixWord ++ tailWord_700978).sum := by decide
  have hdescent : baseEnd_700978 < baseStart_700978 := by decide
  rcases family_descends (prefixWord ++ tailWord_700978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700981 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_700981 : Nat := 118140960795 + 700981 * 2 ^ 59
def prefixEnd_700981 : Nat := 4983230072969 + 3 ^ 40 * 700981 * 2
def baseEnd_700981 : Nat := 359940182669427142313753

theorem tailTrace_700981 : CollatzResearch.WordTrace tailWord_700981 prefixEnd_700981 359940182669427142313753 := by
  unfold tailWord_700981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566877473473029868670797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17044584982315353245780531 25566877473473029868670797)
  ·
    refine ⟨9587579052552386200751549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25566877473473029868670797 9587579052552386200751549)
    ·
      refine ⟨3595342144707144825281831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9587579052552386200751549 3595342144707144825281831)
      ·
        refine ⟨5393013217060717237922747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595342144707144825281831 5393013217060717237922747)
        ·
          refine ⟨8089519825591075856884121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393013217060717237922747 8089519825591075856884121)
          ·
            refine ⟨6067139869193306892663091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8089519825591075856884121 6067139869193306892663091)
            ·
              refine ⟨9100709803789960338994637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067139869193306892663091 9100709803789960338994637)
              ·
                refine ⟨3412766176421235127122989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9100709803789960338994637 3412766176421235127122989)
                ·
                  refine ⟨1279787316157963172671121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3412766176421235127122989 1279787316157963172671121)
                  ·
                    refine ⟨959840487118472379503341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1279787316157963172671121 959840487118472379503341)
                    ·
                      refine ⟨359940182669427142313753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 959840487118472379503341 359940182669427142313753)
                      ·
                        rfl

theorem cell23_700981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_700981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700981 prefixEnd_700981 := by exact prefixLift 700981
  have htrace : WordTrace (prefixWord ++ tailWord_700981) baseStart_700981 baseEnd_700981 := by
    simpa [prefixWord, tailWord_700981, baseEnd_700981] using wordTrace_append hprefix tailTrace_700981
  have hstable : (prefixWord ++ tailWord_700981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700981).length < 2 ^ (prefixWord ++ tailWord_700981).sum := by decide
  have hdescent : baseEnd_700981 < baseStart_700981 := by decide
  rcases family_descends (prefixWord ++ tailWord_700981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700982 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_700982 : Nat := 118140960795 + 700982 * 2 ^ 59
def prefixEnd_700982 : Nat := 4983230072969 + 3 ^ 40 * 700982 * 2
def baseEnd_700982 : Nat := 359940696150081638401249

theorem tailTrace_700982 : CollatzResearch.WordTrace tailWord_700982 prefixEnd_700982 359940696150081638401249 := by
  unfold tailWord_700982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597932121654337939966075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17044609297646271359638133 1597932121654337939966075)
  ·
    refine ⟨2396898182481506909949113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1597932121654337939966075 2396898182481506909949113)
    ·
      refine ⟨1797673636861130182461835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2396898182481506909949113 1797673636861130182461835)
      ·
        refine ⟨2696510455291695273692753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797673636861130182461835 2696510455291695273692753)
        ·
          refine ⟨2022382841468771455269565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2696510455291695273692753 2022382841468771455269565)
          ·
            refine ⟨758393565550789295726087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2022382841468771455269565 758393565550789295726087)
            ·
              refine ⟨1137590348326183943589131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758393565550789295726087 1137590348326183943589131)
              ·
                refine ⟨1706385522489275915383697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137590348326183943589131 1706385522489275915383697)
                ·
                  refine ⟨1279789141866956936537773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706385522489275915383697 1279789141866956936537773)
                  ·
                    refine ⟨479920928200108851201665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279789141866956936537773 479920928200108851201665)
                    ·
                      refine ⟨359940696150081638401249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479920928200108851201665 359940696150081638401249)
                      ·
                        rfl

theorem cell23_700982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_700982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_700982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_700982 prefixEnd_700982 := by exact prefixLift 700982
  have htrace : WordTrace (prefixWord ++ tailWord_700982) baseStart_700982 baseEnd_700982 := by
    simpa [prefixWord, tailWord_700982, baseEnd_700982] using wordTrace_append hprefix tailTrace_700982
  have hstable : (prefixWord ++ tailWord_700982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700982).length < 2 ^ (prefixWord ++ tailWord_700982).sum := by decide
  have hdescent : baseEnd_700982 < baseStart_700982 := by decide
  rcases family_descends (prefixWord ++ tailWord_700982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701005 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_701005 : Nat := 118140960795 + 701005 * 2 ^ 59
def prefixEnd_701005 : Nat := 4983230072969 + 3 ^ 40 * 701005 * 2
def baseEnd_701005 : Nat := 119984168735045016137881

theorem tailTrace_701005 : CollatzResearch.WordTrace tailWord_701005 prefixEnd_701005 119984168735045016137881 := by
  unfold tailWord_701005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25567752825386081967544469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17045168550257387978362979 25567752825386081967544469)
  ·
    refine ⟨1198488413689972592228647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25567752825386081967544469 1198488413689972592228647)
    ·
      refine ⟨1797732620534958888342971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198488413689972592228647 1797732620534958888342971)
      ·
        refine ⟨2696598930802438332514457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797732620534958888342971 2696598930802438332514457)
        ·
          refine ⟨2022449198101828749385843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2696598930802438332514457 2022449198101828749385843)
          ·
            refine ⟨3033673797152743124078765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022449198101828749385843 3033673797152743124078765)
            ·
              refine ⟨1137627673932278671529537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3033673797152743124078765 1137627673932278671529537)
              ·
                refine ⟨853220755449209003647153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137627673932278671529537 853220755449209003647153)
                ·
                  refine ⟨639915566586906752735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 853220755449209003647153 639915566586906752735365)
                  ·
                    refine ⟨119984168735045016137881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639915566586906752735365 119984168735045016137881)
                    ·
                      rfl

theorem cell23_701005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_701005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701005 prefixEnd_701005 := by exact prefixLift 701005
  have htrace : WordTrace (prefixWord ++ tailWord_701005) baseStart_701005 baseEnd_701005 := by
    simpa [prefixWord, tailWord_701005, baseEnd_701005] using wordTrace_append hprefix tailTrace_701005
  have hstable : (prefixWord ++ tailWord_701005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701005).length < 2 ^ (prefixWord ++ tailWord_701005).sum := by decide
  have hdescent : baseEnd_701005 < baseStart_701005 := by decide
  rcases family_descends (prefixWord ++ tailWord_701005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701012 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_701012 : Nat := 118140960795 + 701012 * 2 ^ 59
def prefixEnd_701012 : Nat := 4983230072969 + 3 ^ 40 * 701012 * 2
def baseEnd_701012 : Nat := 359956100569716521026111

theorem tailTrace_701012 : CollatzResearch.WordTrace tailWord_701012 prefixEnd_701012 359956100569716521026111 := by
  unfold tailWord_701012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12784004068180361081524645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17045338757573814775366193 12784004068180361081524645)
  ·
    refine ⟨2397000762783817702785871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12784004068180361081524645 2397000762783817702785871)
    ·
      refine ⟨3595501144175726554178807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397000762783817702785871 3595501144175726554178807)
      ·
        refine ⟨5393251716263589831268211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595501144175726554178807 5393251716263589831268211)
        ·
          refine ⟨8089877574395384746902317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393251716263589831268211 8089877574395384746902317)
          ·
            refine ⟨3033704090398269280088369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8089877574395384746902317 3033704090398269280088369)
            ·
              refine ⟨2275278067798701960066277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3033704090398269280088369 2275278067798701960066277)
              ·
                refine ⟨426614637712256617512427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2275278067798701960066277 426614637712256617512427)
                ·
                  refine ⟨639921956568384926268641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426614637712256617512427 639921956568384926268641)
                  ·
                    refine ⟨479941467426288694701481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639921956568384926268641 479941467426288694701481)
                    ·
                      refine ⟨359956100569716521026111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479941467426288694701481 359956100569716521026111)
                      ·
                        rfl

theorem cell23_701012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_701012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701012 prefixEnd_701012 := by exact prefixLift 701012
  have htrace : WordTrace (prefixWord ++ tailWord_701012) baseStart_701012 baseEnd_701012 := by
    simpa [prefixWord, tailWord_701012, baseEnd_701012] using wordTrace_append hprefix tailTrace_701012
  have hstable : (prefixWord ++ tailWord_701012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701012).length < 2 ^ (prefixWord ++ tailWord_701012).sum := by decide
  have hdescent : baseEnd_701012 < baseStart_701012 := by decide
  rcases family_descends (prefixWord ++ tailWord_701012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701046 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_701046 : Nat := 118140960795 + 701046 * 2 ^ 59
def prefixEnd_701046 : Nat := 4983230072969 + 3 ^ 40 * 701046 * 2
def baseEnd_701046 : Nat := 359973558911969388000955

theorem tailTrace_701046 : CollatzResearch.WordTrace tailWord_701046 prefixEnd_701046 359973558911969388000955 := by
  unfold tailWord_701046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598078013639846623111687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17046165478825030646524661 1598078013639846623111687)
  ·
    refine ⟨2397117020459769934667531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598078013639846623111687 2397117020459769934667531)
    ·
      refine ⟨3595675530689654902001297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397117020459769934667531 3595675530689654902001297)
      ·
        refine ⟨2696756648017241176500973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3595675530689654902001297 2696756648017241176500973)
        ·
          refine ⟨1011283743006465441187865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2696756648017241176500973 1011283743006465441187865)
          ·
            refine ⟨758462807254849080890899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011283743006465441187865 758462807254849080890899)
            ·
              refine ⟨1137694210882273621336349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758462807254849080890899 1137694210882273621336349)
              ·
                refine ⟨426635329080852608001131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137694210882273621336349 426635329080852608001131)
                ·
                  refine ⟨639952993621278912001697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426635329080852608001131 639952993621278912001697)
                  ·
                    refine ⟨479964745215959184001273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639952993621278912001697 479964745215959184001273)
                    ·
                      refine ⟨359973558911969388000955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479964745215959184001273 359973558911969388000955)
                      ·
                        rfl

theorem cell23_701046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_701046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701046 prefixEnd_701046 := by exact prefixLift 701046
  have htrace : WordTrace (prefixWord ++ tailWord_701046) baseStart_701046 baseEnd_701046 := by
    simpa [prefixWord, tailWord_701046, baseEnd_701046] using wordTrace_append hprefix tailTrace_701046
  have hstable : (prefixWord ++ tailWord_701046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701046).length < 2 ^ (prefixWord ++ tailWord_701046).sum := by decide
  have hdescent : baseEnd_701046 < baseStart_701046 := by decide
  rcases family_descends (prefixWord ++ tailWord_701046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701089 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_701089 : Nat := 118140960795 + 701089 * 2 ^ 59
def prefixEnd_701089 : Nat := 4983230072969 + 3 ^ 40 * 701089 * 2
def baseEnd_701089 : Nat := 359995638580112719763257

theorem tailTrace_701089 : CollatzResearch.WordTrace tailWord_701089 prefixEnd_701089 359995638580112719763257 := by
  unfold tailWord_701089
  simp only [CollatzResearch.WordTrace]
  refine ⟨25570816557081764313602321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17047211038054509542401547 25570816557081764313602321)
  ·
    refine ⟨19178112417811323235201741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25570816557081764313602321 19178112417811323235201741)
    ·
      refine ⟨7191792156679246213200653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19178112417811323235201741 7191792156679246213200653)
      ·
        refine ⟨2696922058754717329950245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7191792156679246213200653 2696922058754717329950245)
        ·
          refine ⟨505672886016509499365671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2696922058754717329950245 505672886016509499365671)
          ·
            refine ⟨758509329024764249048507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505672886016509499365671 758509329024764249048507)
            ·
              refine ⟨1137763993537146373572761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758509329024764249048507 1137763993537146373572761)
              ·
                refine ⟨853322995152859780179571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137763993537146373572761 853322995152859780179571)
                ·
                  refine ⟨1279984492729289670269357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853322995152859780179571 1279984492729289670269357)
                  ·
                    refine ⟨479994184773483626351009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279984492729289670269357 479994184773483626351009)
                    ·
                      refine ⟨359995638580112719763257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 479994184773483626351009 359995638580112719763257)
                      ·
                        rfl

theorem cell23_701089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_701089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701089 prefixEnd_701089 := by exact prefixLift 701089
  have htrace : WordTrace (prefixWord ++ tailWord_701089) baseStart_701089 baseEnd_701089 := by
    simpa [prefixWord, tailWord_701089, baseEnd_701089] using wordTrace_append hprefix tailTrace_701089
  have hstable : (prefixWord ++ tailWord_701089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701089).length < 2 ^ (prefixWord ++ tailWord_701089).sum := by decide
  have hdescent : baseEnd_701089 < baseStart_701089 := by decide
  rcases family_descends (prefixWord ++ tailWord_701089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701102 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_701102 : Nat := 118140960795 + 701102 * 2 ^ 59
def prefixEnd_701102 : Nat := 4983230072969 + 3 ^ 40 * 701102 * 2
def baseEnd_701102 : Nat := 360002313828621168900697

theorem tailTrace_701102 : CollatzResearch.WordTrace tailWord_701102 prefixEnd_701102 360002313828621168900697 := by
  unfold tailWord_701102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196411338254333441728195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17047527137356445022550373 3196411338254333441728195)
  ·
    refine ⟨4794617007381500162592293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3196411338254333441728195 4794617007381500162592293)
    ·
      refine ⟨898990688884031280486055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4794617007381500162592293 898990688884031280486055)
      ·
        refine ⟨1348486033326046920729083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898990688884031280486055 1348486033326046920729083)
        ·
          refine ⟨2022729049989070381093625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348486033326046920729083 2022729049989070381093625)
          ·
            refine ⟨1517046787491802785820219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022729049989070381093625 1517046787491802785820219)
            ·
              refine ⟨2275570181237704178730329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517046787491802785820219 2275570181237704178730329)
              ·
                refine ⟨1706677635928278134047747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275570181237704178730329 1706677635928278134047747)
                ·
                  refine ⟨2560016453892417201071621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706677635928278134047747 2560016453892417201071621)
                  ·
                    refine ⟨480003085104828225200929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560016453892417201071621 480003085104828225200929)
                    ·
                      refine ⟨360002313828621168900697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480003085104828225200929 360002313828621168900697)
                      ·
                        rfl

theorem cell23_701102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_701102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701102 prefixEnd_701102 := by exact prefixLift 701102
  have htrace : WordTrace (prefixWord ++ tailWord_701102) baseStart_701102 baseEnd_701102 := by
    simpa [prefixWord, tailWord_701102, baseEnd_701102] using wordTrace_append hprefix tailTrace_701102
  have hstable : (prefixWord ++ tailWord_701102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701102).length < 2 ^ (prefixWord ++ tailWord_701102).sum := by decide
  have hdescent : baseEnd_701102 < baseStart_701102 := by decide
  rcases family_descends (prefixWord ++ tailWord_701102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701118 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_701118 : Nat := 118140960795 + 701118 * 2 ^ 59
def prefixEnd_701118 : Nat := 4983230072969 + 3 ^ 40 * 701118 * 2
def baseEnd_701118 : Nat := 360010529519093106300623

theorem tailTrace_701118 : CollatzResearch.WordTrace tailWord_701118 prefixEnd_701118 360010529519093106300623 := by
  unfold tailWord_701118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196484284247087783301001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17047916182651134844272005 3196484284247087783301001)
  ·
    refine ⟨2397363213185315837475751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3196484284247087783301001 2397363213185315837475751)
    ·
      refine ⟨3596044819777973756213627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397363213185315837475751 3596044819777973756213627)
      ·
        refine ⟨5394067229666960634320441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596044819777973756213627 5394067229666960634320441)
        ·
          refine ⟨4045550422250220475740331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5394067229666960634320441 4045550422250220475740331)
          ·
            refine ⟨6068325633375330713610497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045550422250220475740331 6068325633375330713610497)
            ·
              refine ⟨4551244225031498035207873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6068325633375330713610497 4551244225031498035207873)
              ·
                refine ⟨3413433168773623526405905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551244225031498035207873 3413433168773623526405905)
                ·
                  refine ⟨2560074876580217644804429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3413433168773623526405905 2560074876580217644804429)
                  ·
                    refine ⟨960028078717581616801661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560074876580217644804429 960028078717581616801661)
                    ·
                      refine ⟨360010529519093106300623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960028078717581616801661 360010529519093106300623)
                      ·
                        rfl

theorem cell23_701118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_701118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701118 prefixEnd_701118 := by exact prefixLift 701118
  have htrace : WordTrace (prefixWord ++ tailWord_701118) baseStart_701118 baseEnd_701118 := by
    simpa [prefixWord, tailWord_701118, baseEnd_701118] using wordTrace_append hprefix tailTrace_701118
  have hstable : (prefixWord ++ tailWord_701118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701118).length < 2 ^ (prefixWord ++ tailWord_701118).sum := by decide
  have hdescent : baseEnd_701118 < baseStart_701118 := by decide
  rcases family_descends (prefixWord ++ tailWord_701118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701128 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_701128 : Nat := 118140960795 + 701128 * 2 ^ 59
def prefixEnd_701128 : Nat := 4983230072969 + 3 ^ 40 * 701128 * 2
def baseEnd_701128 : Nat := 360015664325638067175577

theorem tailTrace_701128 : CollatzResearch.WordTrace tailWord_701128 prefixEnd_701128 360015664325638067175577 := by
  unfold tailWord_701128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12786119501970236987136019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17048159335960315982848025 12786119501970236987136019)
  ·
    refine ⟨19179179252955355480704029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12786119501970236987136019 19179179252955355480704029)
    ·
      refine ⟨7192192219858258305264011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19179179252955355480704029 7192192219858258305264011)
      ·
        refine ⟨10788288329787387457896017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192192219858258305264011 10788288329787387457896017)
        ·
          refine ⟨8091216247340540593422013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10788288329787387457896017 8091216247340540593422013)
          ·
            refine ⟨3034206092752702722533255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8091216247340540593422013 3034206092752702722533255)
            ·
              refine ⟨4551309139129054083799883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034206092752702722533255 4551309139129054083799883)
              ·
                refine ⟨6826963708693581125699825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551309139129054083799883 6826963708693581125699825)
                ·
                  refine ⟨5120222781520185844274869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6826963708693581125699825 5120222781520185844274869)
                  ·
                    refine ⟨480020885767517422900769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5120222781520185844274869 480020885767517422900769)
                    ·
                      refine ⟨360015664325638067175577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480020885767517422900769 360015664325638067175577)
                      ·
                        rfl

theorem cell23_701128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_701128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701128 prefixEnd_701128 := by exact prefixLift 701128
  have htrace : WordTrace (prefixWord ++ tailWord_701128) baseStart_701128 baseEnd_701128 := by
    simpa [prefixWord, tailWord_701128, baseEnd_701128] using wordTrace_append hprefix tailTrace_701128
  have hstable : (prefixWord ++ tailWord_701128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701128).length < 2 ^ (prefixWord ++ tailWord_701128).sum := by decide
  have hdescent : baseEnd_701128 < baseStart_701128 := by decide
  rcases family_descends (prefixWord ++ tailWord_701128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701155 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 2, 5]
def baseStart_701155 : Nat := 118140960795 + 701155 * 2 ^ 59
def prefixEnd_701155 : Nat := 4983230072969 + 3 ^ 40 * 701155 * 2
def baseEnd_701155 : Nat := 120009842767769820512651

theorem tailTrace_701155 : CollatzResearch.WordTrace tailWord_701155 prefixEnd_701155 120009842767769820512651 := by
  unfold tailWord_701155
  simp only [CollatzResearch.WordTrace]
  refine ⟨25573223774842657585504919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17048815849895105057003279 25573223774842657585504919)
  ·
    refine ⟨38359835662263986378257379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25573223774842657585504919 38359835662263986378257379)
    ·
      refine ⟨57539753493395979567386069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38359835662263986378257379 57539753493395979567386069)
      ·
        refine ⟨1348587972501468271110611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 57539753493395979567386069 1348587972501468271110611)
        ·
          refine ⟨2022881958752202406665917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348587972501468271110611 2022881958752202406665917)
          ·
            refine ⟨758580734532075902499719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2022881958752202406665917 758580734532075902499719)
            ·
              refine ⟨1137871101798113853749579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758580734532075902499719 1137871101798113853749579)
              ·
                refine ⟨1706806652697170780624369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137871101798113853749579 1706806652697170780624369)
                ·
                  refine ⟨1280104989522878085468277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706806652697170780624369 1280104989522878085468277)
                  ·
                    refine ⟨120009842767769820512651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1280104989522878085468277 120009842767769820512651)
                    ·
                      rfl

theorem cell23_701155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 5].length) (baseStart_701155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701155 prefixEnd_701155 := by exact prefixLift 701155
  have htrace : WordTrace (prefixWord ++ tailWord_701155) baseStart_701155 baseEnd_701155 := by
    simpa [prefixWord, tailWord_701155, baseEnd_701155] using wordTrace_append hprefix tailTrace_701155
  have hstable : (prefixWord ++ tailWord_701155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701155).length < 2 ^ (prefixWord ++ tailWord_701155).sum := by decide
  have hdescent : baseEnd_701155 < baseStart_701155 := by decide
  rcases family_descends (prefixWord ++ tailWord_701155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701178 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_701178 : Nat := 118140960795 + 701178 * 2 ^ 59
def prefixEnd_701178 : Nat := 4983230072969 + 3 ^ 40 * 701178 * 2
def baseEnd_701178 : Nat := 360041338358362871550347

theorem tailTrace_701178 : CollatzResearch.WordTrace tailWord_701178 prefixEnd_701178 360041338358362871550347 := by
  unfold tailWord_701178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393515663439833128398047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17049375102506221675728125 6393515663439833128398047)
  ·
    refine ⟨9590273495159749692597071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6393515663439833128398047 9590273495159749692597071)
    ·
      refine ⟨14385410242739624538895607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9590273495159749692597071 14385410242739624538895607)
      ·
        refine ⟨21578115364109436808343411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14385410242739624538895607 21578115364109436808343411)
        ·
          refine ⟨32367173046164155212515117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21578115364109436808343411 32367173046164155212515117)
          ·
            refine ⟨12137689892311558204693169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32367173046164155212515117 12137689892311558204693169)
            ·
              refine ⟨9103267419233668653519877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12137689892311558204693169 9103267419233668653519877)
              ·
                refine ⟨1706862641106312872534977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9103267419233668653519877 1706862641106312872534977)
                ·
                  refine ⟨1280146980829734654401233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706862641106312872534977 1280146980829734654401233)
                  ·
                    refine ⟨960110235622300990800925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280146980829734654401233 960110235622300990800925)
                    ·
                      refine ⟨360041338358362871550347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960110235622300990800925 360041338358362871550347)
                      ·
                        rfl

theorem cell23_701178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_701178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701178 prefixEnd_701178 := by exact prefixLift 701178
  have htrace : WordTrace (prefixWord ++ tailWord_701178) baseStart_701178 baseEnd_701178 := by
    simpa [prefixWord, tailWord_701178, baseEnd_701178] using wordTrace_append hprefix tailTrace_701178
  have hstable : (prefixWord ++ tailWord_701178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701178).length < 2 ^ (prefixWord ++ tailWord_701178).sum := by decide
  have hdescent : baseEnd_701178 < baseStart_701178 := by decide
  rcases family_descends (prefixWord ++ tailWord_701178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701181 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 8]
def baseStart_701181 : Nat := 118140960795 + 701181 * 2 ^ 59
def prefixEnd_701181 : Nat := 4983230072969 + 3 ^ 40 * 701181 * 2
def baseEnd_701181 : Nat := 40004764311147373312537

theorem tailTrace_701181 : CollatzResearch.WordTrace tailWord_701181 prefixEnd_701181 40004764311147373312537 := by
  unfold tailWord_701181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25574172072748464025951397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17049448048498976017300931 25574172072748464025951397)
  ·
    refine ⟨4795157263640337004865887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25574172072748464025951397 4795157263640337004865887)
    ·
      refine ⟨7192735895460505507298831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4795157263640337004865887 7192735895460505507298831)
      ·
        refine ⟨10789103843190758260948247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192735895460505507298831 10789103843190758260948247)
        ·
          refine ⟨16183655764786137391422371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10789103843190758260948247 16183655764786137391422371)
          ·
            refine ⟨24275483647179206087133557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16183655764786137391422371 24275483647179206087133557)
            ·
              refine ⟨2275826591923050570668771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24275483647179206087133557 2275826591923050570668771)
              ·
                refine ⟨3413739887884575856003157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275826591923050570668771 3413739887884575856003157)
                ·
                  refine ⟨40004764311147373312537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3413739887884575856003157 40004764311147373312537)
                  ·
                    rfl

theorem cell23_701181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_701181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701181 prefixEnd_701181 := by exact prefixLift 701181
  have htrace : WordTrace (prefixWord ++ tailWord_701181) baseStart_701181 baseEnd_701181 := by
    simpa [prefixWord, tailWord_701181, baseEnd_701181] using wordTrace_append hprefix tailTrace_701181
  have hstable : (prefixWord ++ tailWord_701181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701181).length < 2 ^ (prefixWord ++ tailWord_701181).sum := by decide
  have hdescent : baseEnd_701181 < baseStart_701181 := by decide
  rcases family_descends (prefixWord ++ tailWord_701181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701228 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_701228 : Nat := 118140960795 + 701228 * 2 ^ 59
def prefixEnd_701228 : Nat := 4983230072969 + 3 ^ 40 * 701228 * 2
def baseEnd_701228 : Nat := 120022337463695891975039

theorem tailTrace_701228 : CollatzResearch.WordTrace tailWord_701228 prefixEnd_701228 120022337463695891975039 := by
  unfold tailWord_701228
  simp only [CollatzResearch.WordTrace]
  refine ⟨12787943151789095526456169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17050590869052127368608225 12787943151789095526456169)
  ·
    refine ⟨9590957363841821644842127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12787943151789095526456169 9590957363841821644842127)
    ·
      refine ⟨14386436045762732467263191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9590957363841821644842127 14386436045762732467263191)
      ·
        refine ⟨21579654068644098700894787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14386436045762732467263191 21579654068644098700894787)
        ·
          refine ⟨32369481102966148051342181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21579654068644098700894787 32369481102966148051342181)
          ·
            refine ⟨6069277706806152759626659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32369481102966148051342181 6069277706806152759626659)
            ·
              refine ⟨9103916560209229139439989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069277706806152759626659 9103916560209229139439989)
              ·
                refine ⟨853492177519615231822499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9103916560209229139439989 853492177519615231822499)
                ·
                  refine ⟨1280238266279422847733749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853492177519615231822499 1280238266279422847733749)
                  ·
                    refine ⟨120022337463695891975039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1280238266279422847733749 120022337463695891975039)
                    ·
                      rfl

theorem cell23_701228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_701228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701228 prefixEnd_701228 := by exact prefixLift 701228
  have htrace : WordTrace (prefixWord ++ tailWord_701228) baseStart_701228 baseEnd_701228 := by
    simpa [prefixWord, tailWord_701228, baseEnd_701228] using wordTrace_append hprefix tailTrace_701228
  have hstable : (prefixWord ++ tailWord_701228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701228).length < 2 ^ (prefixWord ++ tailWord_701228).sum := by decide
  have hdescent : baseEnd_701228 < baseStart_701228 := by decide
  rcases family_descends (prefixWord ++ tailWord_701228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701229 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_701229 : Nat := 118140960795 + 701229 * 2 ^ 59
def prefixEnd_701229 : Nat := 4983230072969 + 3 ^ 40 * 701229 * 2
def baseEnd_701229 : Nat := 360067525871742172012613

theorem tailTrace_701229 : CollatzResearch.WordTrace tailWord_701229 prefixEnd_701229 360067525871742172012613 := by
  unfold tailWord_701229
  simp only [CollatzResearch.WordTrace]
  refine ⟨25575922776574568223698741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17050615184383045482465827 25575922776574568223698741)
  ·
    refine ⟨2397742760303865770971757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25575922776574568223698741 2397742760303865770971757)
    ·
      refine ⟨899153535113949664114409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2397742760303865770971757 899153535113949664114409)
      ·
        refine ⟨674365151335462248085807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 899153535113949664114409 674365151335462248085807)
        ·
          refine ⟨1011547727003193372128711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674365151335462248085807 1011547727003193372128711)
          ·
            refine ⟨1517321590504790058193067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011547727003193372128711 1517321590504790058193067)
            ·
              refine ⟨2275982385757185087289601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517321590504790058193067 2275982385757185087289601)
              ·
                refine ⟨1706986789317888815467201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275982385757185087289601 1706986789317888815467201)
                ·
                  refine ⟨1280240091988416611600401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706986789317888815467201 1280240091988416611600401)
                  ·
                    refine ⟨960180068991312458700301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280240091988416611600401 960180068991312458700301)
                    ·
                      refine ⟨360067525871742172012613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960180068991312458700301 360067525871742172012613)
                      ·
                        rfl

theorem cell23_701229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_701229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701229 prefixEnd_701229 := by exact prefixLift 701229
  have htrace : WordTrace (prefixWord ++ tailWord_701229) baseStart_701229 baseEnd_701229 := by
    simpa [prefixWord, tailWord_701229, baseEnd_701229] using wordTrace_append hprefix tailTrace_701229
  have hstable : (prefixWord ++ tailWord_701229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701229).length < 2 ^ (prefixWord ++ tailWord_701229).sum := by decide
  have hdescent : baseEnd_701229 < baseStart_701229 := by decide
  rcases family_descends (prefixWord ++ tailWord_701229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701235 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 4, 3, 2]
def baseStart_701235 : Nat := 118140960795 + 701235 * 2 ^ 59
def prefixEnd_701235 : Nat := 4983230072969 + 3 ^ 40 * 701235 * 2
def baseEnd_701235 : Nat := 360070606755669148537585

theorem tailTrace_701235 : CollatzResearch.WordTrace tailWord_701235 prefixEnd_701235 360070606755669148537585 := by
  unfold tailWord_701235
  simp only [CollatzResearch.WordTrace]
  refine ⟨25576141614552831248417159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17050761076368554165611439 25576141614552831248417159)
  ·
    refine ⟨38364212421829246872625739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25576141614552831248417159 38364212421829246872625739)
    ·
      refine ⟨57546318632743870308938609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38364212421829246872625739 57546318632743870308938609)
      ·
        refine ⟨43159738974557902731703957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57546318632743870308938609 43159738974557902731703957)
        ·
          refine ⟨2023112764432401690548623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43159738974557902731703957 2023112764432401690548623)
          ·
            refine ⟨3034669146648602535822935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023112764432401690548623 3034669146648602535822935)
            ·
              refine ⟨4552003719972903803734403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034669146648602535822935 4552003719972903803734403)
              ·
                refine ⟨6828005579959355705601605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552003719972903803734403 6828005579959355705601605)
                ·
                  refine ⟨1280251046242379194800301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6828005579959355705601605 1280251046242379194800301)
                  ·
                    refine ⟨480094142340892198050113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1280251046242379194800301 480094142340892198050113)
                    ·
                      refine ⟨360070606755669148537585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480094142340892198050113 360070606755669148537585)
                      ·
                        rfl

theorem cell23_701235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3, 2].length) (baseStart_701235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701235 prefixEnd_701235 := by exact prefixLift 701235
  have htrace : WordTrace (prefixWord ++ tailWord_701235) baseStart_701235 baseEnd_701235 := by
    simpa [prefixWord, tailWord_701235, baseEnd_701235] using wordTrace_append hprefix tailTrace_701235
  have hstable : (prefixWord ++ tailWord_701235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701235).length < 2 ^ (prefixWord ++ tailWord_701235).sum := by decide
  have hdescent : baseEnd_701235 < baseStart_701235 := by decide
  rcases family_descends (prefixWord ++ tailWord_701235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701236 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_701236 : Nat := 118140960795 + 701236 * 2 ^ 59
def prefixEnd_701236 : Nat := 4983230072969 + 3 ^ 40 * 701236 * 2
def baseEnd_701236 : Nat := 120023706745441214875027

theorem tailTrace_701236 : CollatzResearch.WordTrace tailWord_701236 prefixEnd_701236 120023706745441214875027 := by
  unfold tailWord_701236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12788089043774604209601781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17050785391699472279469041 12788089043774604209601781)
  ·
    refine ⟨1198883347853869144650167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12788089043774604209601781 1198883347853869144650167)
    ·
      refine ⟨1798325021780803716975251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198883347853869144650167 1798325021780803716975251)
      ·
        refine ⟨2697487532671205575462877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798325021780803716975251 2697487532671205575462877)
        ·
          refine ⟨1011557824751702090798579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2697487532671205575462877 1011557824751702090798579)
          ·
            refine ⟨1517336737127553136197869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011557824751702090798579 1517336737127553136197869)
            ·
              refine ⟨569001276422832426074201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1517336737127553136197869 569001276422832426074201)
              ·
                refine ⟨426750957317124319555651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569001276422832426074201 426750957317124319555651)
                ·
                  refine ⟨640126435975686479333477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426750957317124319555651 640126435975686479333477)
                  ·
                    refine ⟨120023706745441214875027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640126435975686479333477 120023706745441214875027)
                    ·
                      rfl

theorem cell23_701236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_701236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701236 prefixEnd_701236 := by exact prefixLift 701236
  have htrace : WordTrace (prefixWord ++ tailWord_701236) baseStart_701236 baseEnd_701236 := by
    simpa [prefixWord, tailWord_701236, baseEnd_701236] using wordTrace_append hprefix tailTrace_701236
  have hstable : (prefixWord ++ tailWord_701236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701236).length < 2 ^ (prefixWord ++ tailWord_701236).sum := by decide
  have hdescent : baseEnd_701236 < baseStart_701236 := by decide
  rcases family_descends (prefixWord ++ tailWord_701236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701249 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 6]
def baseStart_701249 : Nat := 118140960795 + 701249 * 2 ^ 59
def prefixEnd_701249 : Nat := 4983230072969 + 3 ^ 40 * 701249 * 2
def baseEnd_701249 : Nat := 40008643942759121529169

theorem tailTrace_701249 : CollatzResearch.WordTrace tailWord_701249 prefixEnd_701249 40008643942759121529169 := by
  unfold tailWord_701249
  simp only [CollatzResearch.WordTrace]
  refine ⟨25576652236502111639426801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17051101491001407759617867 25576652236502111639426801)
  ·
    refine ⟨19182489177376583729570101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25576652236502111639426801 19182489177376583729570101)
    ·
      refine ⟨1798358360379054724647197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19182489177376583729570101 1798358360379054724647197)
      ·
        refine ⟨674384385142145521742699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1798358360379054724647197 674384385142145521742699)
        ·
          refine ⟨1011576577713218282614049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674384385142145521742699 1011576577713218282614049)
          ·
            refine ⟨758682433284913711960537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011576577713218282614049 758682433284913711960537)
            ·
              refine ⟨569011824963685283970403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758682433284913711960537 569011824963685283970403)
              ·
                refine ⟨853517737445527925955605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569011824963685283970403 853517737445527925955605)
                ·
                  refine ⟨40008643942759121529169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 853517737445527925955605 40008643942759121529169)
                  ·
                    rfl

theorem cell23_701249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 6].length) (baseStart_701249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701249 prefixEnd_701249 := by exact prefixLift 701249
  have htrace : WordTrace (prefixWord ++ tailWord_701249) baseStart_701249 baseEnd_701249 := by
    simpa [prefixWord, tailWord_701249, baseEnd_701249] using wordTrace_append hprefix tailTrace_701249
  have hstable : (prefixWord ++ tailWord_701249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701249).length < 2 ^ (prefixWord ++ tailWord_701249).sum := by decide
  have hdescent : baseEnd_701249 < baseStart_701249 := by decide
  rcases family_descends (prefixWord ++ tailWord_701249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701258 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_701258 : Nat := 118140960795 + 701258 * 2 ^ 59
def prefixEnd_701258 : Nat := 4983230072969 + 3 ^ 40 * 701258 * 2
def baseEnd_701258 : Nat := 120027472270240852849993

theorem tailTrace_701258 : CollatzResearch.WordTrace tailWord_701258 prefixEnd_701258 120027472270240852849993 := by
  unfold tailWord_701258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394245123367376544126107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17051320328979670784336285 6394245123367376544126107)
  ·
    refine ⟨9591367685051064816189161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6394245123367376544126107 9591367685051064816189161)
    ·
      refine ⟨7193525763788298612141871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9591367685051064816189161 7193525763788298612141871)
      ·
        refine ⟨10790288645682447918212807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7193525763788298612141871 10790288645682447918212807)
        ·
          refine ⟨16185432968523671877319211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10790288645682447918212807 16185432968523671877319211)
          ·
            refine ⟨24278149452785507815978817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16185432968523671877319211 24278149452785507815978817)
            ·
              refine ⟨18208612089589130861984113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24278149452785507815978817 18208612089589130861984113)
              ·
                refine ⟨13656459067191848146488085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18208612089589130861984113 13656459067191848146488085)
                ·
                  refine ⟨640146518774617881866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13656459067191848146488085 640146518774617881866629)
                  ·
                    refine ⟨120027472270240852849993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640146518774617881866629 120027472270240852849993)
                    ·
                      rfl

theorem cell23_701258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_701258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701258 prefixEnd_701258 := by exact prefixLift 701258
  have htrace : WordTrace (prefixWord ++ tailWord_701258) baseStart_701258 baseEnd_701258 := by
    simpa [prefixWord, tailWord_701258, baseEnd_701258] using wordTrace_append hprefix tailTrace_701258
  have hstable : (prefixWord ++ tailWord_701258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701258).length < 2 ^ (prefixWord ++ tailWord_701258).sum := by decide
  have hdescent : baseEnd_701258 < baseStart_701258 := by decide
  rcases family_descends (prefixWord ++ tailWord_701258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701265 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_701265 : Nat := 118140960795 + 701265 * 2 ^ 59
def prefixEnd_701265 : Nat := 4983230072969 + 3 ^ 40 * 701265 * 2
def baseEnd_701265 : Nat := 360086011175304031162447

theorem tailTrace_701265 : CollatzResearch.WordTrace tailWord_701265 prefixEnd_701265 360086011175304031162447 := by
  unfold tailWord_701265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25577235804444146372009249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17051490536296097581339499 25577235804444146372009249)
  ·
    refine ⟨19182926853333109779006937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25577235804444146372009249 19182926853333109779006937)
    ·
      refine ⟨14387195139999832334255203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19182926853333109779006937 14387195139999832334255203)
      ·
        refine ⟨21580792709999748501382805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14387195139999832334255203 21580792709999748501382805)
        ·
          refine ⟨1011599658281238211002319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21580792709999748501382805 1011599658281238211002319)
          ·
            refine ⟨1517399487421857316503479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011599658281238211002319 1517399487421857316503479)
            ·
              refine ⟨2276099231132785974755219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517399487421857316503479 2276099231132785974755219)
              ·
                refine ⟨3414148846699178962132829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276099231132785974755219 3414148846699178962132829)
                ·
                  refine ⟨1280305817512192110799811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3414148846699178962132829 1280305817512192110799811)
                  ·
                    refine ⟨1920458726268288166199717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1280305817512192110799811 1920458726268288166199717)
                    ·
                      refine ⟨360086011175304031162447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1920458726268288166199717 360086011175304031162447)
                      ·
                        rfl

theorem cell23_701265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_701265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701265 prefixEnd_701265 := by exact prefixLift 701265
  have htrace : WordTrace (prefixWord ++ tailWord_701265) baseStart_701265 baseEnd_701265 := by
    simpa [prefixWord, tailWord_701265, baseEnd_701265] using wordTrace_append hprefix tailTrace_701265
  have hstable : (prefixWord ++ tailWord_701265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701265).length < 2 ^ (prefixWord ++ tailWord_701265).sum := by decide
  have hdescent : baseEnd_701265 < baseStart_701265 := by decide
  rcases family_descends (prefixWord ++ tailWord_701265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701285 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_701285 : Nat := 118140960795 + 701285 * 2 ^ 59
def prefixEnd_701285 : Nat := 4983230072969 + 3 ^ 40 * 701285 * 2
def baseEnd_701285 : Nat := 360096280788393952912355

theorem tailTrace_701285 : CollatzResearch.WordTrace tailWord_701285 prefixEnd_701285 360096280788393952912355 := by
  unfold tailWord_701285
  simp only [CollatzResearch.WordTrace]
  refine ⟨25577965264371689787737309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17051976842914459858491539 25577965264371689787737309)
  ·
    refine ⟨9591736974139383670401491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25577965264371689787737309 9591736974139383670401491)
    ·
      refine ⟨14387605461209075505602237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9591736974139383670401491 14387605461209075505602237)
      ·
        refine ⟨5395352047953403314600839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14387605461209075505602237 5395352047953403314600839)
        ·
          refine ⟨8093028071930104971901259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5395352047953403314600839 8093028071930104971901259)
          ·
            refine ⟨12139542107895157457851889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093028071930104971901259 12139542107895157457851889)
            ·
              refine ⟨9104656580921368093388917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12139542107895157457851889 9104656580921368093388917)
              ·
                refine ⟨853561554461378258755211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9104656580921368093388917 853561554461378258755211)
                ·
                  refine ⟨1280342331692067388132817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853561554461378258755211 1280342331692067388132817)
                  ·
                    refine ⟨960256748769050541099613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280342331692067388132817 960256748769050541099613)
                    ·
                      refine ⟨360096280788393952912355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960256748769050541099613 360096280788393952912355)
                      ·
                        rfl

theorem cell23_701285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_701285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701285 prefixEnd_701285 := by exact prefixLift 701285
  have htrace : WordTrace (prefixWord ++ tailWord_701285) baseStart_701285 baseEnd_701285 := by
    simpa [prefixWord, tailWord_701285, baseEnd_701285] using wordTrace_append hprefix tailTrace_701285
  have hstable : (prefixWord ++ tailWord_701285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701285).length < 2 ^ (prefixWord ++ tailWord_701285).sum := by decide
  have hdescent : baseEnd_701285 < baseStart_701285 := by decide
  rcases family_descends (prefixWord ++ tailWord_701285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701302 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_701302 : Nat := 118140960795 + 701302 * 2 ^ 59
def prefixEnd_701302 : Nat := 4983230072969 + 3 ^ 40 * 701302 * 2
def baseEnd_701302 : Nat := 360105009959520386399777

theorem tailTrace_701302 : CollatzResearch.WordTrace tailWord_701302 prefixEnd_701302 360105009959520386399777 := by
  unfold tailWord_701302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598661581581881355694135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17052390203540067794070773 1598661581581881355694135)
  ·
    refine ⟨2397992372372822033541203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598661581581881355694135 2397992372372822033541203)
    ·
      refine ⟨3596988558559233050311805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397992372372822033541203 3596988558559233050311805)
      ·
        refine ⟨1348870709459712393866927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3596988558559233050311805 1348870709459712393866927)
        ·
          refine ⟨2023306064189568590800391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348870709459712393866927 2023306064189568590800391)
          ·
            refine ⟨3034959096284352886200587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023306064189568590800391 3034959096284352886200587)
            ·
              refine ⟨4552438644426529329300881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034959096284352886200587 4552438644426529329300881)
              ·
                refine ⟨3414328983319896996975661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552438644426529329300881 3414328983319896996975661)
                ·
                  refine ⟨1280373368744961373865873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3414328983319896996975661 1280373368744961373865873)
                  ·
                    refine ⟨960280026558721030399405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280373368744961373865873 960280026558721030399405)
                    ·
                      refine ⟨360105009959520386399777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960280026558721030399405 360105009959520386399777)
                      ·
                        rfl

theorem cell23_701302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_701302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701302 prefixEnd_701302 := by exact prefixLift 701302
  have htrace : WordTrace (prefixWord ++ tailWord_701302) baseStart_701302 baseEnd_701302 := by
    simpa [prefixWord, tailWord_701302, baseEnd_701302] using wordTrace_append hprefix tailTrace_701302
  have hstable : (prefixWord ++ tailWord_701302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701302).length < 2 ^ (prefixWord ++ tailWord_701302).sum := by decide
  have hdescent : baseEnd_701302 < baseStart_701302 := by decide
  rcases family_descends (prefixWord ++ tailWord_701302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701315 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 3]
def baseStart_701315 : Nat := 118140960795 + 701315 * 2 ^ 59
def prefixEnd_701315 : Nat := 4983230072969 + 3 ^ 40 * 701315 * 2
def baseEnd_701315 : Nat := 360111685208028835537217

theorem tailTrace_701315 : CollatzResearch.WordTrace tailWord_701315 prefixEnd_701315 360111685208028835537217 := by
  unfold tailWord_701315
  simp only [CollatzResearch.WordTrace]
  refine ⟨25579059454263004911329399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17052706302842003274219599 25579059454263004911329399)
  ·
    refine ⟨38368589181394507366994099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25579059454263004911329399 38368589181394507366994099)
    ·
      refine ⟨57552883772091761050491149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38368589181394507366994099 57552883772091761050491149)
      ·
        refine ⟨21582331414534410393934181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57552883772091761050491149 21582331414534410393934181)
        ·
          refine ⟨4046687140225201948862659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21582331414534410393934181 4046687140225201948862659)
          ·
            refine ⟨6070030710337802923293989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046687140225201948862659 6070030710337802923293989)
            ·
              refine ⟨1138130758188338048117623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6070030710337802923293989 1138130758188338048117623)
              ·
                refine ⟨1707196137282507072176435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138130758188338048117623 1707196137282507072176435)
                ·
                  refine ⟨2560794205923760608264653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707196137282507072176435 2560794205923760608264653)
                  ·
                    refine ⟨960297827221410228099245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560794205923760608264653 960297827221410228099245)
                    ·
                      refine ⟨360111685208028835537217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960297827221410228099245 360111685208028835537217)
                      ·
                        rfl

theorem cell23_701315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_701315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701315 prefixEnd_701315 := by exact prefixLift 701315
  have htrace : WordTrace (prefixWord ++ tailWord_701315) baseStart_701315 baseEnd_701315 := by
    simpa [prefixWord, tailWord_701315, baseEnd_701315] using wordTrace_append hprefix tailTrace_701315
  have hstable : (prefixWord ++ tailWord_701315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701315).length < 2 ^ (prefixWord ++ tailWord_701315).sum := by decide
  have hdescent : baseEnd_701315 < baseStart_701315 := by decide
  rcases family_descends (prefixWord ++ tailWord_701315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701332 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_701332 : Nat := 118140960795 + 701332 * 2 ^ 59
def prefixEnd_701332 : Nat := 4983230072969 + 3 ^ 40 * 701332 * 2
def baseEnd_701332 : Nat := 360120414379155269024639

theorem tailTrace_701332 : CollatzResearch.WordTrace tailWord_701332 prefixEnd_701332 360120414379155269024639 := by
  unfold tailWord_701332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12789839747600708407349125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17053119663467611209798833 12789839747600708407349125)
  ·
    refine ⟨2398094952675132826377961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12789839747600708407349125 2398094952675132826377961)
    ·
      refine ⟨1798571214506349619783471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2398094952675132826377961 1798571214506349619783471)
      ·
        refine ⟨2697856821759524429675207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798571214506349619783471 2697856821759524429675207)
        ·
          refine ⟨4046785232639286644512811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697856821759524429675207 4046785232639286644512811)
          ·
            refine ⟨6070177848958929966769217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046785232639286644512811 6070177848958929966769217)
            ·
              refine ⟨4552633386719197475076913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6070177848958929966769217 4552633386719197475076913)
              ·
                refine ⟨3414475040039398106307685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552633386719197475076913 3414475040039398106307685)
                ·
                  refine ⟨640214070007387144932691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3414475040039398106307685 640214070007387144932691)
                  ·
                    refine ⟨960321105011080717399037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640214070007387144932691 960321105011080717399037)
                    ·
                      refine ⟨360120414379155269024639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960321105011080717399037 360120414379155269024639)
                      ·
                        rfl

theorem cell23_701332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_701332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701332 prefixEnd_701332 := by exact prefixLift 701332
  have htrace : WordTrace (prefixWord ++ tailWord_701332) baseStart_701332 baseEnd_701332 := by
    simpa [prefixWord, tailWord_701332, baseEnd_701332] using wordTrace_append hprefix tailTrace_701332
  have hstable : (prefixWord ++ tailWord_701332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701332).length < 2 ^ (prefixWord ++ tailWord_701332).sum := by decide
  have hdescent : baseEnd_701332 < baseStart_701332 := by decide
  rcases family_descends (prefixWord ++ tailWord_701332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701348 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_701348 : Nat := 118140960795 + 701348 * 2 ^ 59
def prefixEnd_701348 : Nat := 4983230072969 + 3 ^ 40 * 701348 * 2
def baseEnd_701348 : Nat := 120042876689875735474855

theorem tailTrace_701348 : CollatzResearch.WordTrace tailWord_701348 prefixEnd_701348 120042876689875735474855 := by
  unfold tailWord_701348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790131531571725773640349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17053508708762301031520465 12790131531571725773640349)
  ·
    refine ⟨4796299324339397165115131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12790131531571725773640349 4796299324339397165115131)
    ·
      refine ⟨7194448986509095747672697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796299324339397165115131 7194448986509095747672697)
      ·
        refine ⟨5395836739881821810754523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7194448986509095747672697 5395836739881821810754523)
        ·
          refine ⟨8093755109822732716131785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5395836739881821810754523 8093755109822732716131785)
          ·
            refine ⟨6070316332367049537098839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8093755109822732716131785 6070316332367049537098839)
            ·
              refine ⟨9105474498550574305648259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070316332367049537098839 9105474498550574305648259)
              ·
                refine ⟨13658211747825861458472389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105474498550574305648259 13658211747825861458472389)
                ·
                  refine ⟨2560914702717349023463573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13658211747825861458472389 2560914702717349023463573)
                  ·
                    refine ⟨120042876689875735474855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2560914702717349023463573 120042876689875735474855)
                    ·
                      rfl

theorem cell23_701348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_701348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701348 prefixEnd_701348 := by exact prefixLift 701348
  have htrace : WordTrace (prefixWord ++ tailWord_701348) baseStart_701348 baseEnd_701348 := by
    simpa [prefixWord, tailWord_701348, baseEnd_701348] using wordTrace_append hprefix tailTrace_701348
  have hstable : (prefixWord ++ tailWord_701348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701348).length < 2 ^ (prefixWord ++ tailWord_701348).sum := by decide
  have hdescent : baseEnd_701348 < baseStart_701348 := by decide
  rcases family_descends (prefixWord ++ tailWord_701348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701479 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_701479 : Nat := 118140960795 + 701479 * 2 ^ 59
def prefixEnd_701479 : Nat := 4983230072969 + 3 ^ 40 * 701479 * 2
def baseEnd_701479 : Nat := 360195896035366193886463

theorem tailTrace_701479 : CollatzResearch.WordTrace tailWord_701479 prefixEnd_701479 360195896035366193886463 := by
  unfold tailWord_701479
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585041025668860920299491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17056694017112573946866327 25585041025668860920299491)
  ·
    refine ⟨38377561538503291380449237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25585041025668860920299491 38377561538503291380449237)
    ·
      refine ⟨899474098558670891729279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 38377561538503291380449237 899474098558670891729279)
      ·
        refine ⟨1349211147838006337593919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899474098558670891729279 1349211147838006337593919)
        ·
          refine ⟨2023816721757009506390879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349211147838006337593919 2023816721757009506390879)
          ·
            refine ⟨3035725082635514259586319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023816721757009506390879 3035725082635514259586319)
            ·
              refine ⟨4553587623953271389379479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035725082635514259586319 4553587623953271389379479)
              ·
                refine ⟨6830381435929907084069219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553587623953271389379479 6830381435929907084069219)
                ·
                  refine ⟨10245572153894860626103829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6830381435929907084069219 10245572153894860626103829)
                  ·
                    refine ⟨480261194713821591848617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10245572153894860626103829 480261194713821591848617)
                    ·
                      refine ⟨360195896035366193886463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480261194713821591848617 360195896035366193886463)
                      ·
                        rfl

theorem cell23_701479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_701479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701479 prefixEnd_701479 := by exact prefixLift 701479
  have htrace : WordTrace (prefixWord ++ tailWord_701479) baseStart_701479 baseEnd_701479 := by
    simpa [prefixWord, tailWord_701479, baseEnd_701479] using wordTrace_append hprefix tailTrace_701479
  have hstable : (prefixWord ++ tailWord_701479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701479).length < 2 ^ (prefixWord ++ tailWord_701479).sum := by decide
  have hdescent : baseEnd_701479 < baseStart_701479 := by decide
  rcases family_descends (prefixWord ++ tailWord_701479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701512 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_701512 : Nat := 118140960795 + 701512 * 2 ^ 59
def prefixEnd_701512 : Nat := 4983230072969 + 3 ^ 40 * 701512 * 2
def baseEnd_701512 : Nat := 360212840896964564773811

theorem tailTrace_701512 : CollatzResearch.WordTrace tailWord_701512 prefixEnd_701512 360212840896964564773811 := by
  unfold tailWord_701512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793122317274653778125395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17057496423032871704167193 12793122317274653778125395)
  ·
    refine ⟨19189683475911980667188093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12793122317274653778125395 19189683475911980667188093)
    ·
      refine ⟨7196131303466992750195535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19189683475911980667188093 7196131303466992750195535)
      ·
        refine ⟨10794196955200489125293303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196131303466992750195535 10794196955200489125293303)
        ·
          refine ⟨16191295432800733687939955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10794196955200489125293303 16191295432800733687939955)
          ·
            refine ⟨24286943149201100531909933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16191295432800733687939955 24286943149201100531909933)
            ·
              refine ⟨9107603680950412699466225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24286943149201100531909933 9107603680950412699466225)
              ·
                refine ⟨6830702760712809524599669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9107603680950412699466225 6830702760712809524599669)
                ·
                  refine ⟨640378383816825892931219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6830702760712809524599669 640378383816825892931219)
                  ·
                    refine ⟨960567575725238839396829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640378383816825892931219 960567575725238839396829)
                    ·
                      refine ⟨360212840896964564773811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960567575725238839396829 360212840896964564773811)
                      ·
                        rfl

theorem cell23_701512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_701512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701512 prefixEnd_701512 := by exact prefixLift 701512
  have htrace : WordTrace (prefixWord ++ tailWord_701512) baseStart_701512 baseEnd_701512 := by
    simpa [prefixWord, tailWord_701512, baseEnd_701512] using wordTrace_append hprefix tailTrace_701512
  have hstable : (prefixWord ++ tailWord_701512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701512).length < 2 ^ (prefixWord ++ tailWord_701512).sum := by decide
  have hdescent : baseEnd_701512 < baseStart_701512 := by decide
  rcases family_descends (prefixWord ++ tailWord_701512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701549 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_701549 : Nat := 118140960795 + 701549 * 2 ^ 59
def prefixEnd_701549 : Nat := 4983230072969 + 3 ^ 40 * 701549 * 2
def baseEnd_701549 : Nat := 120077279893726973337047

theorem tailTrace_701549 : CollatzResearch.WordTrace tailWord_701549 prefixEnd_701549 120077279893726973337047 := by
  unfold tailWord_701549
  simp only [CollatzResearch.WordTrace]
  refine ⟨25587594135415262875347701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17058396090276841916898467 25587594135415262875347701)
  ·
    refine ⟨2398836950195180894563847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25587594135415262875347701 2398836950195180894563847)
    ·
      refine ⟨3598255425292771341845771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398836950195180894563847 3598255425292771341845771)
      ·
        refine ⟨5397383137939157012768657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598255425292771341845771 5397383137939157012768657)
        ·
          refine ⟨4048037353454367759576493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5397383137939157012768657 4048037353454367759576493)
          ·
            refine ⟨1518014007545387909841185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4048037353454367759576493 1518014007545387909841185)
            ·
              refine ⟨1138510505659040932380889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518014007545387909841185 1138510505659040932380889)
              ·
                refine ⟨853882879244280699285667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138510505659040932380889 853882879244280699285667)
                ·
                  refine ⟨1280824318866421048928501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853882879244280699285667 1280824318866421048928501)
                  ·
                    refine ⟨120077279893726973337047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1280824318866421048928501 120077279893726973337047)
                    ·
                      rfl

theorem cell23_701549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_701549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701549 prefixEnd_701549 := by exact prefixLift 701549
  have htrace : WordTrace (prefixWord ++ tailWord_701549) baseStart_701549 baseEnd_701549 := by
    simpa [prefixWord, tailWord_701549, baseEnd_701549] using wordTrace_append hprefix tailTrace_701549
  have hstable : (prefixWord ++ tailWord_701549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701549).length < 2 ^ (prefixWord ++ tailWord_701549).sum := by decide
  have hdescent : baseEnd_701549 < baseStart_701549 := by decide
  rcases family_descends (prefixWord ++ tailWord_701549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701552 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 6, 2]
def baseStart_701552 : Nat := 118140960795 + 701552 * 2 ^ 59
def prefixEnd_701552 : Nat := 4983230072969 + 3 ^ 40 * 701552 * 2
def baseEnd_701552 : Nat := 360233380123144408273627

theorem tailTrace_701552 : CollatzResearch.WordTrace tailWord_701552 prefixEnd_701552 360233380123144408273627 := by
  unfold tailWord_701552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793851777202197193853455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17058469036269596258471273 12793851777202197193853455)
  ·
    refine ⟨19190777665803295790780183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12793851777202197193853455 19190777665803295790780183)
    ·
      refine ⟨28786166498704943686170275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19190777665803295790780183 28786166498704943686170275)
      ·
        refine ⟨43179249748057415529255413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28786166498704943686170275 43179249748057415529255413)
        ·
          refine ⟨4048054663880382705867695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43179249748057415529255413 4048054663880382705867695)
          ·
            refine ⟨6072081995820574058801543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048054663880382705867695 6072081995820574058801543)
            ·
              refine ⟨9108122993730861088202315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072081995820574058801543 9108122993730861088202315)
              ·
                refine ⟨13662184490596291632303473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9108122993730861088202315 13662184490596291632303473)
                ·
                  refine ⟨10246638367947218724227605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13662184490596291632303473 10246638367947218724227605)
                  ·
                    refine ⟨480311173497525877698169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10246638367947218724227605 480311173497525877698169)
                    ·
                      refine ⟨360233380123144408273627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480311173497525877698169 360233380123144408273627)
                      ·
                        rfl

theorem cell23_701552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 6, 2].length) (baseStart_701552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701552 prefixEnd_701552 := by exact prefixLift 701552
  have htrace : WordTrace (prefixWord ++ tailWord_701552) baseStart_701552 baseEnd_701552 := by
    simpa [prefixWord, tailWord_701552, baseEnd_701552] using wordTrace_append hprefix tailTrace_701552
  have hstable : (prefixWord ++ tailWord_701552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701552).length < 2 ^ (prefixWord ++ tailWord_701552).sum := by decide
  have hdescent : baseEnd_701552 < baseStart_701552 := by decide
  rcases family_descends (prefixWord ++ tailWord_701552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701555 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 3]
def baseStart_701555 : Nat := 118140960795 + 701555 * 2 ^ 59
def prefixEnd_701555 : Nat := 4983230072969 + 3 ^ 40 * 701555 * 2
def baseEnd_701555 : Nat := 360234920565107896536113

theorem tailTrace_701555 : CollatzResearch.WordTrace tailWord_701555 prefixEnd_701555 360234920565107896536113 := by
  unfold tailWord_701555
  simp only [CollatzResearch.WordTrace]
  refine ⟨25587812973393525900066119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17058541982262350600044079 25587812973393525900066119)
  ·
    refine ⟨38381719460090288850099179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25587812973393525900066119 38381719460090288850099179)
    ·
      refine ⟨57572579190135433275148769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38381719460090288850099179 57572579190135433275148769)
      ·
        refine ⟨43179434392601574956361577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57572579190135433275148769 43179434392601574956361577)
        ·
          refine ⟨32384575794451181217271183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43179434392601574956361577 32384575794451181217271183)
          ·
            refine ⟨48576863691676771825906775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32384575794451181217271183 48576863691676771825906775)
            ·
              refine ⟨72865295537515157738860163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48576863691676771825906775 72865295537515157738860163)
              ·
                refine ⟨109297943306272736608290245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72865295537515157738860163 109297943306272736608290245)
                ·
                  refine ⟨20493364369926138114054421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109297943306272736608290245 20493364369926138114054421)
                  ·
                    refine ⟨960626454840287724096301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20493364369926138114054421 960626454840287724096301)
                    ·
                      refine ⟨360234920565107896536113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 960626454840287724096301 360234920565107896536113)
                      ·
                        rfl

theorem cell23_701555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_701555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701555 prefixEnd_701555 := by exact prefixLift 701555
  have htrace : WordTrace (prefixWord ++ tailWord_701555) baseStart_701555 baseEnd_701555 := by
    simpa [prefixWord, tailWord_701555, baseEnd_701555] using wordTrace_append hprefix tailTrace_701555
  have hstable : (prefixWord ++ tailWord_701555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701555).length < 2 ^ (prefixWord ++ tailWord_701555).sum := by decide
  have hdescent : baseEnd_701555 < baseStart_701555 := by decide
  rcases family_descends (prefixWord ++ tailWord_701555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701569 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_701569 : Nat := 118140960795 + 701569 * 2 ^ 59
def prefixEnd_701569 : Nat := 4983230072969 + 3 ^ 40 * 701569 * 2
def baseEnd_701569 : Nat := 360242109294270841761049

theorem tailTrace_701569 : CollatzResearch.WordTrace tailWord_701569 prefixEnd_701569 360242109294270841761049 := by
  unfold tailWord_701569
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588323595342806291075761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17058882396895204194050507 25588323595342806291075761)
  ·
    refine ⟨19191242696507104718306821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25588323595342806291075761 19191242696507104718306821)
    ·
      refine ⟨3598358005595082134682529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19191242696507104718306821 3598358005595082134682529)
      ·
        refine ⟨2698768504196311601011897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3598358005595082134682529 2698768504196311601011897)
        ·
          refine ⟨2024076378147233700758923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698768504196311601011897 2024076378147233700758923)
          ·
            refine ⟨3036114567220850551138385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024076378147233700758923 3036114567220850551138385)
            ·
              refine ⟨2277085925415637913353789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036114567220850551138385 2277085925415637913353789)
              ·
                refine ⟨853907222030864217507671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2277085925415637913353789 853907222030864217507671)
                ·
                  refine ⟨1280860833046296326261507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853907222030864217507671 1280860833046296326261507)
                  ·
                    refine ⟨1921291249569444489392261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1280860833046296326261507 1921291249569444489392261)
                    ·
                      refine ⟨360242109294270841761049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1921291249569444489392261 360242109294270841761049)
                      ·
                        rfl

theorem cell23_701569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_701569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701569 prefixEnd_701569 := by exact prefixLift 701569
  have htrace : WordTrace (prefixWord ++ tailWord_701569) baseStart_701569 baseEnd_701569 := by
    simpa [prefixWord, tailWord_701569, baseEnd_701569] using wordTrace_append hprefix tailTrace_701569
  have hstable : (prefixWord ++ tailWord_701569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701569).length < 2 ^ (prefixWord ++ tailWord_701569).sum := by decide
  have hdescent : baseEnd_701569 < baseStart_701569 := by decide
  rcases family_descends (prefixWord ++ tailWord_701569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701572 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_701572 : Nat := 118140960795 + 701572 * 2 ^ 59
def prefixEnd_701572 : Nat := 4983230072969 + 3 ^ 40 * 701572 * 2
def baseEnd_701572 : Nat := 360243649736234330023535

theorem tailTrace_701572 : CollatzResearch.WordTrace tailWord_701572 prefixEnd_701572 360243649736234330023535 := by
  unfold tailWord_701572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794216507165968901717485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17058955342887958535623313 12794216507165968901717485)
  ·
    refine ⟨4797831190187238338144057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12794216507165968901717485 4797831190187238338144057)
    ·
      refine ⟨3598373392640428753608043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4797831190187238338144057 3598373392640428753608043)
      ·
        refine ⟨5397560088960643130412065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598373392640428753608043 5397560088960643130412065)
        ·
          refine ⟨4048170066720482347809049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5397560088960643130412065 4048170066720482347809049)
          ·
            refine ⟨3036127550040361760856787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4048170066720482347809049 3036127550040361760856787)
            ·
              refine ⟨4554191325060542641285181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036127550040361760856787 4554191325060542641285181)
              ·
                refine ⟨1707821746897703490481943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4554191325060542641285181 1707821746897703490481943)
                ·
                  refine ⟨2561732620346555235722915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707821746897703490481943 2561732620346555235722915)
                  ·
                    refine ⟨3842598930519832853584373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2561732620346555235722915 3842598930519832853584373)
                    ·
                      refine ⟨360243649736234330023535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3842598930519832853584373 360243649736234330023535)
                      ·
                        rfl

theorem cell23_701572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_701572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701572 prefixEnd_701572 := by exact prefixLift 701572
  have htrace : WordTrace (prefixWord ++ tailWord_701572) baseStart_701572 baseEnd_701572 := by
    simpa [prefixWord, tailWord_701572, baseEnd_701572] using wordTrace_append hprefix tailTrace_701572
  have hstable : (prefixWord ++ tailWord_701572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701572).length < 2 ^ (prefixWord ++ tailWord_701572).sum := by decide
  have hdescent : baseEnd_701572 < baseStart_701572 := by decide
  rcases family_descends (prefixWord ++ tailWord_701572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701582 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_701582 : Nat := 118140960795 + 701582 * 2 ^ 59
def prefixEnd_701582 : Nat := 4983230072969 + 3 ^ 40 * 701582 * 2
def baseEnd_701582 : Nat := 360248784542779290898489

theorem tailTrace_701582 : CollatzResearch.WordTrace tailWord_701582 prefixEnd_701582 360248784542779290898489 := by
  unfold tailWord_701582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198599718036963688912375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17059198496197139674199333 3198599718036963688912375)
  ·
    refine ⟨4797899577055445533368563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3198599718036963688912375 4797899577055445533368563)
    ·
      refine ⟨7196849365583168300052845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797899577055445533368563 7196849365583168300052845)
      ·
        refine ⟨2698818512093688112519817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7196849365583168300052845 2698818512093688112519817)
        ·
          refine ⟨2024113884070266084389863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698818512093688112519817 2024113884070266084389863)
          ·
            refine ⟨3036170826105399126584795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024113884070266084389863 3036170826105399126584795)
            ·
              refine ⟨4554256239158098689877193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036170826105399126584795 4554256239158098689877193)
              ·
                refine ⟨3415692179368574017407895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4554256239158098689877193 3415692179368574017407895)
                ·
                  refine ⟨5123538269052861026111843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415692179368574017407895 5123538269052861026111843)
                  ·
                    refine ⟨7685307403579291539167765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5123538269052861026111843 7685307403579291539167765)
                    ·
                      refine ⟨360248784542779290898489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7685307403579291539167765 360248784542779290898489)
                      ·
                        rfl

theorem cell23_701582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_701582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701582 prefixEnd_701582 := by exact prefixLift 701582
  have htrace : WordTrace (prefixWord ++ tailWord_701582) baseStart_701582 baseEnd_701582 := by
    simpa [prefixWord, tailWord_701582, baseEnd_701582] using wordTrace_append hprefix tailTrace_701582
  have hstable : (prefixWord ++ tailWord_701582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701582).length < 2 ^ (prefixWord ++ tailWord_701582).sum := by decide
  have hdescent : baseEnd_701582 < baseStart_701582 := by decide
  rcases family_descends (prefixWord ++ tailWord_701582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701592 : List Nat := [2, 1, 2, 4, 2, 2, 2, 8]
def baseStart_701592 : Nat := 118140960795 + 701592 * 2 ^ 59
def prefixEnd_701592 : Nat := 4983230072969 + 3 ^ 40 * 701592 * 2
def baseEnd_701592 : Nat := 13342737753678675991609

theorem tailTrace_701592 : CollatzResearch.WordTrace tailWord_701592 prefixEnd_701592 13342737753678675991609 := by
  unfold tailWord_701592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794581237129740609581515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17059441649506320812775353 12794581237129740609581515)
  ·
    refine ⟨19191871855694610914372273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12794581237129740609581515 19191871855694610914372273)
    ·
      refine ⟨14393903891770958185779205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19191871855694610914372273 14393903891770958185779205)
      ·
        refine ⟨2698856979707054659833601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14393903891770958185779205 2698856979707054659833601)
        ·
          refine ⟨2024142734780290994875201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698856979707054659833601 2024142734780290994875201)
          ·
            refine ⟨1518107051085218246156401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024142734780290994875201 1518107051085218246156401)
            ·
              refine ⟨1138580288313913684617301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518107051085218246156401 1138580288313913684617301)
              ·
                refine ⟨13342737753678675991609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1138580288313913684617301 13342737753678675991609)
                ·
                  rfl

theorem cell23_701592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 8].length) (baseStart_701592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701592 prefixEnd_701592 := by exact prefixLift 701592
  have htrace : WordTrace (prefixWord ++ tailWord_701592) baseStart_701592 baseEnd_701592 := by
    simpa [prefixWord, tailWord_701592, baseEnd_701592] using wordTrace_append hprefix tailTrace_701592
  have hstable : (prefixWord ++ tailWord_701592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701592).length < 2 ^ (prefixWord ++ tailWord_701592).sum := by decide
  have hdescent : baseEnd_701592 < baseStart_701592 := by decide
  rcases family_descends (prefixWord ++ tailWord_701592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701596 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_701596 : Nat := 118140960795 + 701596 * 2 ^ 59
def prefixEnd_701596 : Nat := 4983230072969 + 3 ^ 40 * 701596 * 2
def baseEnd_701596 : Nat := 120085324423980745374475

theorem tailTrace_701596 : CollatzResearch.WordTrace tailWord_701596 prefixEnd_701596 120085324423980745374475 := by
  unfold tailWord_701596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794654183122494951154321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17059538910829993268205761 12794654183122494951154321)
  ·
    refine ⟨9595990637341871213365741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12794654183122494951154321 9595990637341871213365741)
    ·
      refine ⟨3598496489003201705012153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9595990637341871213365741 3598496489003201705012153)
      ·
        refine ⟨2698872366752401278759115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3598496489003201705012153 2698872366752401278759115)
        ·
          refine ⟨4048308550128601918138673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698872366752401278759115 4048308550128601918138673)
          ·
            refine ⟨3036231412596451438604005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4048308550128601918138673 3036231412596451438604005)
            ·
              refine ⟨569293389861834644738251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3036231412596451438604005 569293389861834644738251)
              ·
                refine ⟨853940084792751967107377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569293389861834644738251 853940084792751967107377)
                ·
                  refine ⟨640455063594563975330533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 853940084792751967107377 640455063594563975330533)
                  ·
                    refine ⟨120085324423980745374475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640455063594563975330533 120085324423980745374475)
                    ·
                      rfl

theorem cell23_701596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_701596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701596 prefixEnd_701596 := by exact prefixLift 701596
  have htrace : WordTrace (prefixWord ++ tailWord_701596) baseStart_701596 baseEnd_701596 := by
    simpa [prefixWord, tailWord_701596, baseEnd_701596] using wordTrace_append hprefix tailTrace_701596
  have hstable : (prefixWord ++ tailWord_701596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701596).length < 2 ^ (prefixWord ++ tailWord_701596).sum := by decide
  have hdescent : baseEnd_701596 < baseStart_701596 := by decide
  rcases family_descends (prefixWord ++ tailWord_701596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701615 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_701615 : Nat := 118140960795 + 701615 * 2 ^ 59
def prefixEnd_701615 : Nat := 4983230072969 + 3 ^ 40 * 701615 * 2
def baseEnd_701615 : Nat := 360265729404377661785837

theorem tailTrace_701615 : CollatzResearch.WordTrace tailWord_701615 prefixEnd_701615 360265729404377661785837 := by
  unfold tailWord_701615
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590001353176156147250299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17060000902117437431500199 25590001353176156147250299)
  ·
    refine ⟨38385002029764234220875449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25590001353176156147250299 38385002029764234220875449)
    ·
      refine ⟨28788751522323175665656587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38385002029764234220875449 28788751522323175665656587)
      ·
        refine ⟨43183127283484763498484881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28788751522323175665656587 43183127283484763498484881)
        ·
          refine ⟨32387345462613572623863661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43183127283484763498484881 32387345462613572623863661)
          ·
            refine ⟨12145254548480089733948873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32387345462613572623863661 12145254548480089733948873)
            ·
              refine ⟨9108940911360067300461655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12145254548480089733948873 9108940911360067300461655)
              ·
                refine ⟨13663411367040100950692483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9108940911360067300461655 13663411367040100950692483)
                ·
                  refine ⟨20495117050560151426038725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13663411367040100950692483 20495117050560151426038725)
                  ·
                    refine ⟨3842834446980028392382261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20495117050560151426038725 3842834446980028392382261)
                    ·
                      refine ⟨360265729404377661785837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3842834446980028392382261 360265729404377661785837)
                      ·
                        rfl

theorem cell23_701615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_701615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701615 prefixEnd_701615 := by exact prefixLift 701615
  have htrace : WordTrace (prefixWord ++ tailWord_701615) baseStart_701615 baseEnd_701615 := by
    simpa [prefixWord, tailWord_701615, baseEnd_701615] using wordTrace_append hprefix tailTrace_701615
  have hstable : (prefixWord ++ tailWord_701615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701615).length < 2 ^ (prefixWord ++ tailWord_701615).sum := by decide
  have hdescent : baseEnd_701615 < baseStart_701615 := by decide
  rcases family_descends (prefixWord ++ tailWord_701615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701642 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_701642 : Nat := 118140960795 + 701642 * 2 ^ 59
def prefixEnd_701642 : Nat := 4983230072969 + 3 ^ 40 * 701642 * 2
def baseEnd_701642 : Nat := 360279593382049056148213

theorem tailTrace_701642 : CollatzResearch.WordTrace tailWord_701642 prefixEnd_701642 360279593382049056148213 := by
  unfold tailWord_701642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6397746531019584939620795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17060657416052226505655453 6397746531019584939620795)
  ·
    refine ⟨9596619796529377409431193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6397746531019584939620795 9596619796529377409431193)
    ·
      refine ⟨7197464847397033057073395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9596619796529377409431193 7197464847397033057073395)
      ·
        refine ⟨10796197271095549585610093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197464847397033057073395 10796197271095549585610093)
        ·
          refine ⟨4048573976660831094603785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10796197271095549585610093 4048573976660831094603785)
          ·
            refine ⟨3036430482495623320952839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4048573976660831094603785 3036430482495623320952839)
            ·
              refine ⟨4554645723743434981429259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036430482495623320952839 4554645723743434981429259)
              ·
                refine ⟨6831968585615152472143889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554645723743434981429259 6831968585615152472143889)
                ·
                  refine ⟨5123976439211364354107917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6831968585615152472143889 5123976439211364354107917)
                  ·
                    refine ⟨1921491164704261632790469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5123976439211364354107917 1921491164704261632790469)
                    ·
                      refine ⟨360279593382049056148213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1921491164704261632790469 360279593382049056148213)
                      ·
                        rfl

theorem cell23_701642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_701642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701642 prefixEnd_701642 := by exact prefixLift 701642
  have htrace : WordTrace (prefixWord ++ tailWord_701642) baseStart_701642 baseEnd_701642 := by
    simpa [prefixWord, tailWord_701642, baseEnd_701642] using wordTrace_append hprefix tailTrace_701642
  have hstable : (prefixWord ++ tailWord_701642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701642).length < 2 ^ (prefixWord ++ tailWord_701642).sum := by decide
  have hdescent : baseEnd_701642 < baseStart_701642 := by decide
  rcases family_descends (prefixWord ++ tailWord_701642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701672 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_701672 : Nat := 118140960795 + 701672 * 2 ^ 59
def prefixEnd_701672 : Nat := 4983230072969 + 3 ^ 40 * 701672 * 2
def baseEnd_701672 : Nat := 360294997801683938773075

theorem tailTrace_701672 : CollatzResearch.WordTrace tailWord_701672 prefixEnd_701672 360294997801683938773075 := by
  unfold tailWord_701672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796040156984827441037635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17061386875979769921383513 12796040156984827441037635)
  ·
    refine ⟨19194060235477241161556453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12796040156984827441037635 19194060235477241161556453)
    ·
      refine ⟨3598886294151982717791835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19194060235477241161556453 3598886294151982717791835)
      ·
        refine ⟨5398329441227974076687753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598886294151982717791835 5398329441227974076687753)
        ·
          refine ⟨4048747080920980557515815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5398329441227974076687753 4048747080920980557515815)
          ·
            refine ⟨6073120621381470836273723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048747080920980557515815 6073120621381470836273723)
            ·
              refine ⟨9109680932072206254410585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073120621381470836273723 9109680932072206254410585)
              ·
                refine ⟨6832260699054154690807939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9109680932072206254410585 6832260699054154690807939)
                ·
                  refine ⟨10248391048581232036211909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832260699054154690807939 10248391048581232036211909)
                  ·
                    refine ⟨1921573321608981006789733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10248391048581232036211909 1921573321608981006789733)
                    ·
                      refine ⟨360294997801683938773075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1921573321608981006789733 360294997801683938773075)
                      ·
                        rfl

theorem cell23_701672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_701672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701672 prefixEnd_701672 := by exact prefixLift 701672
  have htrace : WordTrace (prefixWord ++ tailWord_701672) baseStart_701672 baseEnd_701672 := by
    simpa [prefixWord, tailWord_701672, baseEnd_701672] using wordTrace_append hprefix tailTrace_701672
  have hstable : (prefixWord ++ tailWord_701672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701672).length < 2 ^ (prefixWord ++ tailWord_701672).sum := by decide
  have hdescent : baseEnd_701672 < baseStart_701672 := by decide
  rcases family_descends (prefixWord ++ tailWord_701672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701699 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 5]
def baseStart_701699 : Nat := 118140960795 + 701699 * 2 ^ 59
def prefixEnd_701699 : Nat := 4983230072969 + 3 ^ 40 * 701699 * 2
def baseEnd_701699 : Nat := 40034317975483925903939

theorem tailTrace_701699 : CollatzResearch.WordTrace tailWord_701699 prefixEnd_701699 40034317975483925903939 := by
  unfold tailWord_701699
  simp only [CollatzResearch.WordTrace]
  refine ⟨25593065084871838493308151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17062043389914558995538767 25593065084871838493308151)
  ·
    refine ⟨38389597627307757739962227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25593065084871838493308151 38389597627307757739962227)
    ·
      refine ⟨57584396440961636609943341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38389597627307757739962227 57584396440961636609943341)
      ·
        refine ⟨21594148665360613728728753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57584396440961636609943341 21594148665360613728728753)
        ·
          refine ⟨16195611499020460296546565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21594148665360613728728753 16195611499020460296546565)
          ·
            refine ⟨3036677156066336305602481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16195611499020460296546565 3036677156066336305602481)
            ·
              refine ⟨2277507867049752229201861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036677156066336305602481 2277507867049752229201861)
              ·
                refine ⟨427032725071828542975349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2277507867049752229201861 427032725071828542975349)
                ·
                  refine ⟨40034317975483925903939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427032725071828542975349 40034317975483925903939)
                  ·
                    rfl

theorem cell23_701699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 5].length) (baseStart_701699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701699 prefixEnd_701699 := by exact prefixLift 701699
  have htrace : WordTrace (prefixWord ++ tailWord_701699) baseStart_701699 baseEnd_701699 := by
    simpa [prefixWord, tailWord_701699, baseEnd_701699] using wordTrace_append hprefix tailTrace_701699
  have hstable : (prefixWord ++ tailWord_701699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701699).length < 2 ^ (prefixWord ++ tailWord_701699).sum := by decide
  have hdescent : baseEnd_701699 < baseStart_701699 := by decide
  rcases family_descends (prefixWord ++ tailWord_701699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701710 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_701710 : Nat := 118140960795 + 701710 * 2 ^ 59
def prefixEnd_701710 : Nat := 4983230072969 + 3 ^ 40 * 701710 * 2
def baseEnd_701710 : Nat := 360314510066554790097901

theorem tailTrace_701710 : CollatzResearch.WordTrace tailWord_701710 prefixEnd_701710 360314510066554790097901 := by
  unfold tailWord_701710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199183285978998421494823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17062310858554658247972389 3199183285978998421494823)
  ·
    refine ⟨4798774928968497632242235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3199183285978998421494823 4798774928968497632242235)
    ·
      refine ⟨7198162393452746448363353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4798774928968497632242235 7198162393452746448363353)
      ·
        refine ⟨5398621795089559836272515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7198162393452746448363353 5398621795089559836272515)
        ·
          refine ⟨8097932692634339754408773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398621795089559836272515 8097932692634339754408773)
          ·
            refine ⟨1518362379868938703951645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8097932692634339754408773 1518362379868938703951645)
            ·
              refine ⟨569385892450852013981867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1518362379868938703951645 569385892450852013981867)
              ·
                refine ⟨854078838676278020972801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569385892450852013981867 854078838676278020972801)
                ·
                  refine ⟨640559129007208515729601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 854078838676278020972801 640559129007208515729601)
                  ·
                    refine ⟨480419346755406386797201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 640559129007208515729601 480419346755406386797201)
                    ·
                      refine ⟨360314510066554790097901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480419346755406386797201 360314510066554790097901)
                      ·
                        rfl

theorem cell23_701710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_701710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701710 prefixEnd_701710 := by exact prefixLift 701710
  have htrace : WordTrace (prefixWord ++ tailWord_701710) baseStart_701710 baseEnd_701710 := by
    simpa [prefixWord, tailWord_701710, baseEnd_701710] using wordTrace_append hprefix tailTrace_701710
  have hstable : (prefixWord ++ tailWord_701710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701710).length < 2 ^ (prefixWord ++ tailWord_701710).sum := by decide
  have hdescent : baseEnd_701710 < baseStart_701710 := by decide
  rcases family_descends (prefixWord ++ tailWord_701710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701749 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_701749 : Nat := 118140960795 + 701749 * 2 ^ 59
def prefixEnd_701749 : Nat := 4983230072969 + 3 ^ 40 * 701749 * 2
def baseEnd_701749 : Nat := 360334535812080137510221

theorem tailTrace_701749 : CollatzResearch.WordTrace tailWord_701749 prefixEnd_701749 360334535812080137510221 := by
  unfold tailWord_701749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25594888734690697032628301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17063259156460464688418867 25594888734690697032628301)
  ·
    refine ⟨9598083275509011387235613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25594888734690697032628301 9598083275509011387235613)
    ·
      refine ⟨3599281228315879270213355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9598083275509011387235613 3599281228315879270213355)
      ·
        refine ⟨5398921842473818905320033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3599281228315879270213355 5398921842473818905320033)
        ·
          refine ⟨4049191381855364178990025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5398921842473818905320033 4049191381855364178990025)
          ·
            refine ⟨3036893536391523134242519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4049191381855364178990025 3036893536391523134242519)
            ·
              refine ⟨4555340304587284701363779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036893536391523134242519 4555340304587284701363779)
              ·
                refine ⟨6833010456880927052045669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555340304587284701363779 6833010456880927052045669)
                ·
                  refine ⟨1281189460665173822258563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6833010456880927052045669 1281189460665173822258563)
                  ·
                    refine ⟨1921784190997760733387845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1281189460665173822258563 1921784190997760733387845)
                    ·
                      refine ⟨360334535812080137510221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1921784190997760733387845 360334535812080137510221)
                      ·
                        rfl

theorem cell23_701749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_701749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701749 prefixEnd_701749 := by exact prefixLift 701749
  have htrace : WordTrace (prefixWord ++ tailWord_701749) baseStart_701749 baseEnd_701749 := by
    simpa [prefixWord, tailWord_701749, baseEnd_701749] using wordTrace_append hprefix tailTrace_701749
  have hstable : (prefixWord ++ tailWord_701749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701749).length < 2 ^ (prefixWord ++ tailWord_701749).sum := by decide
  have hdescent : baseEnd_701749 < baseStart_701749 := by decide
  rcases family_descends (prefixWord ++ tailWord_701749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701750 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_701750 : Nat := 118140960795 + 701750 * 2 ^ 59
def prefixEnd_701750 : Nat := 4983230072969 + 3 ^ 40 * 701750 * 2
def baseEnd_701750 : Nat := 40037227699192737066413

theorem tailTrace_701750 : CollatzResearch.WordTrace tailWord_701750 prefixEnd_701750 40037227699192737066413 := by
  unfold tailWord_701750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599682825480442137713419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17063283471791382802276469 1599682825480442137713419)
  ·
    refine ⟨2399524238220663206570129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1599682825480442137713419 2399524238220663206570129)
    ·
      refine ⟨1799643178665497404927597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2399524238220663206570129 1799643178665497404927597)
      ·
        refine ⟨674866191999561526847849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1799643178665497404927597 674866191999561526847849)
        ·
          refine ⟨506149643999671145135887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674866191999561526847849 506149643999671145135887)
          ·
            refine ⟨759224465999506717703831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506149643999671145135887 759224465999506717703831)
            ·
              refine ⟨1138836698999260076555747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759224465999506717703831 1138836698999260076555747)
              ·
                refine ⟨1708255048498890114833621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138836698999260076555747 1708255048498890114833621)
                ·
                  refine ⟨40037227699192737066413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1708255048498890114833621 40037227699192737066413)
                  ·
                    rfl

theorem cell23_701750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_701750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701750 prefixEnd_701750 := by exact prefixLift 701750
  have htrace : WordTrace (prefixWord ++ tailWord_701750) baseStart_701750 baseEnd_701750 := by
    simpa [prefixWord, tailWord_701750, baseEnd_701750] using wordTrace_append hprefix tailTrace_701750
  have hstable : (prefixWord ++ tailWord_701750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701750).length < 2 ^ (prefixWord ++ tailWord_701750).sum := by decide
  have hdescent : baseEnd_701750 < baseStart_701750 := by decide
  rcases family_descends (prefixWord ++ tailWord_701750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701833 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 3]
def baseStart_701833 : Nat := 118140960795 + 701833 * 2 ^ 59
def prefixEnd_701833 : Nat := 4983230072969 + 3 ^ 40 * 701833 * 2
def baseEnd_701833 : Nat := 360377668187057808859835

theorem tailTrace_701833 : CollatzResearch.WordTrace tailWord_701833 prefixEnd_701833 360377668187057808859835 := by
  unfold tailWord_701833
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597952466386379378686153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17065301644257586252457435 25597952466386379378686153)
  ·
    refine ⟨19198464349789784534014615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25597952466386379378686153 19198464349789784534014615)
    ·
      refine ⟨28797696524684676801021923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19198464349789784534014615 28797696524684676801021923)
      ·
        refine ⟨43196544787027015201532885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28797696524684676801021923 43196544787027015201532885)
        ·
          refine ⟨1012419018445945668785927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43196544787027015201532885 1012419018445945668785927)
          ·
            refine ⟨1518628527668918503178891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012419018445945668785927 1518628527668918503178891)
            ·
              refine ⟨2277942791503377754768337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518628527668918503178891 2277942791503377754768337)
              ·
                refine ⟨1708457093627533316076253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277942791503377754768337 1708457093627533316076253)
                ·
                  refine ⟨640671410110324993528595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1708457093627533316076253 640671410110324993528595)
                  ·
                    refine ⟨961007115165487490292893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640671410110324993528595 961007115165487490292893)
                    ·
                      refine ⟨360377668187057808859835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961007115165487490292893 360377668187057808859835)
                      ·
                        rfl

theorem cell23_701833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_701833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701833 prefixEnd_701833 := by exact prefixLift 701833
  have htrace : WordTrace (prefixWord ++ tailWord_701833) baseStart_701833 baseEnd_701833 := by
    simpa [prefixWord, tailWord_701833, baseEnd_701833] using wordTrace_append hprefix tailTrace_701833
  have hstable : (prefixWord ++ tailWord_701833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701833).length < 2 ^ (prefixWord ++ tailWord_701833).sum := by decide
  have hdescent : baseEnd_701833 < baseStart_701833 := by decide
  rcases family_descends (prefixWord ++ tailWord_701833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701849 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_701849 : Nat := 118140960795 + 701849 * 2 ^ 59
def prefixEnd_701849 : Nat := 4983230072969 + 3 ^ 40 * 701849 * 2
def baseEnd_701849 : Nat := 120128627959176582086587

theorem tailTrace_701849 : CollatzResearch.WordTrace tailWord_701849 prefixEnd_701849 120128627959176582086587 := by
  unfold tailWord_701849
  simp only [CollatzResearch.WordTrace]
  refine ⟨25598536034328414111268601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17065690689552276074179067 25598536034328414111268601)
  ·
    refine ⟨19198902025746310583451451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25598536034328414111268601 19198902025746310583451451)
    ·
      refine ⟨28798353038619465875177177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19198902025746310583451451 28798353038619465875177177)
      ·
        refine ⟨21598764778964599406382883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28798353038619465875177177 21598764778964599406382883)
        ·
          refine ⟨32398147168446899109574325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21598764778964599406382883 32398147168446899109574325)
          ·
            refine ⟨3037326297041896791522593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32398147168446899109574325 3037326297041896791522593)
            ·
              refine ⟨2277994722781422593641945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037326297041896791522593 2277994722781422593641945)
              ·
                refine ⟨1708496042086066945231459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277994722781422593641945 1708496042086066945231459)
                ·
                  refine ⟨2562744063129100417847189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708496042086066945231459 2562744063129100417847189)
                  ·
                    refine ⟨120128627959176582086587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2562744063129100417847189 120128627959176582086587)
                    ·
                      rfl

theorem cell23_701849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_701849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701849 prefixEnd_701849 := by exact prefixLift 701849
  have htrace : WordTrace (prefixWord ++ tailWord_701849) baseStart_701849 baseEnd_701849 := by
    simpa [prefixWord, tailWord_701849, baseEnd_701849] using wordTrace_append hprefix tailTrace_701849
  have hstable : (prefixWord ++ tailWord_701849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701849).length < 2 ^ (prefixWord ++ tailWord_701849).sum := by decide
  have hdescent : baseEnd_701849 < baseStart_701849 := by decide
  rcases family_descends (prefixWord ++ tailWord_701849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701850 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3]
def baseStart_701850 : Nat := 118140960795 + 701850 * 2 ^ 59
def prefixEnd_701850 : Nat := 4983230072969 + 3 ^ 40 * 701850 * 2
def baseEnd_701850 : Nat := 360386397358184242347257

theorem tailTrace_701850 : CollatzResearch.WordTrace tailWord_701850 prefixEnd_701850 360386397358184242347257 := by
  unfold tailWord_701850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399643126831197820513751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17065715004883194188036669 6399643126831197820513751)
  ·
    refine ⟨9599464690246796730770627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6399643126831197820513751 9599464690246796730770627)
    ·
      refine ⟨14399197035370195096155941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9599464690246796730770627 14399197035370195096155941)
      ·
        refine ⟨2699849444131911580529239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14399197035370195096155941 2699849444131911580529239)
        ·
          refine ⟨4049774166197867370793859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2699849444131911580529239 4049774166197867370793859)
          ·
            refine ⟨6074661249296801056190789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049774166197867370793859 6074661249296801056190789)
            ·
              refine ⟨1138998984243150198035773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6074661249296801056190789 1138998984243150198035773)
              ·
                refine ⟨427124619091181324263415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1138998984243150198035773 427124619091181324263415)
                ·
                  refine ⟨640686928636771986395123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427124619091181324263415 640686928636771986395123)
                  ·
                    refine ⟨961030392955157979592685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640686928636771986395123 961030392955157979592685)
                    ·
                      refine ⟨360386397358184242347257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961030392955157979592685 360386397358184242347257)
                      ·
                        rfl

theorem cell23_701850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_701850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701850 prefixEnd_701850 := by exact prefixLift 701850
  have htrace : WordTrace (prefixWord ++ tailWord_701850) baseStart_701850 baseEnd_701850 := by
    simpa [prefixWord, tailWord_701850, baseEnd_701850] using wordTrace_append hprefix tailTrace_701850
  have hstable : (prefixWord ++ tailWord_701850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701850).length < 2 ^ (prefixWord ++ tailWord_701850).sum := by decide
  have hdescent : baseEnd_701850 < baseStart_701850 := by decide
  rcases family_descends (prefixWord ++ tailWord_701850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701853 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_701853 : Nat := 118140960795 + 701853 * 2 ^ 59
def prefixEnd_701853 : Nat := 4983230072969 + 3 ^ 40 * 701853 * 2
def baseEnd_701853 : Nat := 120129312600049243536581

theorem tailTrace_701853 : CollatzResearch.WordTrace tailWord_701853 prefixEnd_701853 120129312600049243536581 := by
  unfold tailWord_701853
  simp only [CollatzResearch.WordTrace]
  refine ⟨25598681926313922794414213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17065787950875948529609475 25598681926313922794414213)
  ·
    refine ⟨4799752861183860523952665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25598681926313922794414213 4799752861183860523952665)
    ·
      refine ⟨3599814645887895392964499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4799752861183860523952665 3599814645887895392964499)
      ·
        refine ⟨5399721968831843089446749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3599814645887895392964499 5399721968831843089446749)
        ·
          refine ⟨2024895738311941158542531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5399721968831843089446749 2024895738311941158542531)
          ·
            refine ⟨3037343607467911737813797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024895738311941158542531 3037343607467911737813797)
            ·
              refine ⟨569501926400233450840087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3037343607467911737813797 569501926400233450840087)
              ·
                refine ⟨854252889600350176260131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569501926400233450840087 854252889600350176260131)
                ·
                  refine ⟨1281379334400525264390197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854252889600350176260131 1281379334400525264390197)
                  ·
                    refine ⟨120129312600049243536581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1281379334400525264390197 120129312600049243536581)
                    ·
                      rfl

theorem cell23_701853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_701853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701853 prefixEnd_701853 := by exact prefixLift 701853
  have htrace : WordTrace (prefixWord ++ tailWord_701853) baseStart_701853 baseEnd_701853 := by
    simpa [prefixWord, tailWord_701853, baseEnd_701853] using wordTrace_append hprefix tailTrace_701853
  have hstable : (prefixWord ++ tailWord_701853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701853).length < 2 ^ (prefixWord ++ tailWord_701853).sum := by decide
  have hdescent : baseEnd_701853 < baseStart_701853 := by decide
  rcases family_descends (prefixWord ++ tailWord_701853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701856 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4]
def baseStart_701856 : Nat := 118140960795 + 701856 * 2 ^ 59
def prefixEnd_701856 : Nat := 4983230072969 + 3 ^ 40 * 701856 * 2
def baseEnd_701856 : Nat := 360389478242111218872229

theorem tailTrace_701856 : CollatzResearch.WordTrace tailWord_701856 prefixEnd_701856 360389478242111218872229 := by
  unfold tailWord_701856
  simp only [CollatzResearch.WordTrace]
  refine ⟨12799395672651527153386711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17065860896868702871182281 12799395672651527153386711)
  ·
    refine ⟨19199093508977290730080067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12799395672651527153386711 19199093508977290730080067)
    ·
      refine ⟨28798640263465936095120101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19199093508977290730080067 28798640263465936095120101)
      ·
        refine ⟨5399745049399863017835019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28798640263465936095120101 5399745049399863017835019)
        ·
          refine ⟨8099617574099794526752529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399745049399863017835019 8099617574099794526752529)
          ·
            refine ⟨6074713180574845895064397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8099617574099794526752529 6074713180574845895064397)
            ·
              refine ⟨2278017442715567210649149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6074713180574845895064397 2278017442715567210649149)
              ·
                refine ⟨854256541018337703993431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2278017442715567210649149 854256541018337703993431)
                ·
                  refine ⟨1281384811527506555990147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854256541018337703993431 1281384811527506555990147)
                  ·
                    refine ⟨1922077217291259833985221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1281384811527506555990147 1922077217291259833985221)
                    ·
                      refine ⟨360389478242111218872229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1922077217291259833985221 360389478242111218872229)
                      ·
                        rfl

theorem cell23_701856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_701856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701856 prefixEnd_701856 := by exact prefixLift 701856
  have htrace : WordTrace (prefixWord ++ tailWord_701856) baseStart_701856 baseEnd_701856 := by
    simpa [prefixWord, tailWord_701856, baseEnd_701856] using wordTrace_append hprefix tailTrace_701856
  have hstable : (prefixWord ++ tailWord_701856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701856).length < 2 ^ (prefixWord ++ tailWord_701856).sum := by decide
  have hdescent : baseEnd_701856 < baseStart_701856 := by decide
  rcases family_descends (prefixWord ++ tailWord_701856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701859 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5]
def baseStart_701859 : Nat := 118140960795 + 701859 * 2 ^ 59
def prefixEnd_701859 : Nat := 4983230072969 + 3 ^ 40 * 701859 * 2
def baseEnd_701859 : Nat := 360391018684074707134715

theorem tailTrace_701859 : CollatzResearch.WordTrace tailWord_701859 prefixEnd_701859 360391018684074707134715 := by
  unfold tailWord_701859
  simp only [CollatzResearch.WordTrace]
  refine ⟨25598900764292185819132631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17065933842861457212755087 25598900764292185819132631)
  ·
    refine ⟨38398351146438278728698947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25598900764292185819132631 38398351146438278728698947)
    ·
      refine ⟨57597526719657418093048421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38398351146438278728698947 57597526719657418093048421)
      ·
        refine ⟨10799536259935765892446579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57597526719657418093048421 10799536259935765892446579)
        ·
          refine ⟨16199304389903648838669869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10799536259935765892446579 16199304389903648838669869)
          ·
            refine ⟨6074739146213868314501201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16199304389903648838669869 6074739146213868314501201)
            ·
              refine ⟨4556054359660401235875901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6074739146213868314501201 4556054359660401235875901)
              ·
                refine ⟨1708520384872650463453463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4556054359660401235875901 1708520384872650463453463)
                ·
                  refine ⟨2562780577308975695180195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708520384872650463453463 2562780577308975695180195)
                  ·
                    refine ⟨3844170865963463542770293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562780577308975695180195 3844170865963463542770293)
                    ·
                      refine ⟨360391018684074707134715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3844170865963463542770293 360391018684074707134715)
                      ·
                        rfl

theorem cell23_701859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_701859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701859 prefixEnd_701859 := by exact prefixLift 701859
  have htrace : WordTrace (prefixWord ++ tailWord_701859) baseStart_701859 baseEnd_701859 := by
    simpa [prefixWord, tailWord_701859, baseEnd_701859] using wordTrace_append hprefix tailTrace_701859
  have hstable : (prefixWord ++ tailWord_701859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701859).length < 2 ^ (prefixWord ++ tailWord_701859).sum := by decide
  have hdescent : baseEnd_701859 < baseStart_701859 := by decide
  rcases family_descends (prefixWord ++ tailWord_701859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701910 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_701910 : Nat := 118140960795 + 701910 * 2 ^ 59
def prefixEnd_701910 : Nat := 4983230072969 + 3 ^ 40 * 701910 * 2
def baseEnd_701910 : Nat := 360417206197454007596981

theorem tailTrace_701910 : CollatzResearch.WordTrace tailWord_701910 prefixEnd_701910 360417206197454007596981 := by
  unfold tailWord_701910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600047555444213845577449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17067173924738281019492789 1600047555444213845577449)
  ·
    refine ⟨1200035666583160384183087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1600047555444213845577449 1200035666583160384183087)
    ·
      refine ⟨1800053499874740576274631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200035666583160384183087 1800053499874740576274631)
      ·
        refine ⟨2700080249812110864411947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800053499874740576274631 2700080249812110864411947)
        ·
          refine ⟨4050120374718166296617921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700080249812110864411947 4050120374718166296617921)
          ·
            refine ⟨3037590281038624722463441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050120374718166296617921 3037590281038624722463441)
            ·
              refine ⟨2278192710778968541847581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037590281038624722463441 2278192710778968541847581)
              ·
                refine ⟨854322266542113203192843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2278192710778968541847581 854322266542113203192843)
                ·
                  refine ⟨1281483399813169804789265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854322266542113203192843 1281483399813169804789265)
                  ·
                    refine ⟨961112549859877353591949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1281483399813169804789265 961112549859877353591949)
                    ·
                      refine ⟨360417206197454007596981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961112549859877353591949 360417206197454007596981)
                      ·
                        rfl

theorem cell23_701910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_701910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701910 prefixEnd_701910 := by exact prefixLift 701910
  have htrace : WordTrace (prefixWord ++ tailWord_701910) baseStart_701910 baseEnd_701910 := by
    simpa [prefixWord, tailWord_701910, baseEnd_701910] using wordTrace_append hprefix tailTrace_701910
  have hstable : (prefixWord ++ tailWord_701910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701910).length < 2 ^ (prefixWord ++ tailWord_701910).sum := by decide
  have hdescent : baseEnd_701910 < baseStart_701910 := by decide
  rcases family_descends (prefixWord ++ tailWord_701910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701919 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_701919 : Nat := 118140960795 + 701919 * 2 ^ 59
def prefixEnd_701919 : Nat := 4983230072969 + 3 ^ 40 * 701919 * 2
def baseEnd_701919 : Nat := 360421827523344472384439

theorem tailTrace_701919 : CollatzResearch.WordTrace tailWord_701919 prefixEnd_701919 360421827523344472384439 := by
  unfold tailWord_701919
  simp only [CollatzResearch.WordTrace]
  refine ⟨25601089144074816066316811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17067392762716544044211207 25601089144074816066316811)
  ·
    refine ⟨38401633716112224099475217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25601089144074816066316811 38401633716112224099475217)
    ·
      refine ⟨28801225287084168074606413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38401633716112224099475217 28801225287084168074606413)
      ·
        refine ⟨10800459482656563027977405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28801225287084168074606413 10800459482656563027977405)
        ·
          refine ⟨4050172305996211135491527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10800459482656563027977405 4050172305996211135491527)
          ·
            refine ⟨6075258458994316703237291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4050172305996211135491527 6075258458994316703237291)
            ·
              refine ⟨9112887688491475054855937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6075258458994316703237291 9112887688491475054855937)
              ·
                refine ⟨6834665766368606291141953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9112887688491475054855937 6834665766368606291141953)
                ·
                  refine ⟨5125999324776454718356465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6834665766368606291141953 5125999324776454718356465)
                  ·
                    refine ⟨3844499493582341038767349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125999324776454718356465 3844499493582341038767349)
                    ·
                      refine ⟨360421827523344472384439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3844499493582341038767349 360421827523344472384439)
                      ·
                        rfl

theorem cell23_701919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_701919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701919 prefixEnd_701919 := by exact prefixLift 701919
  have htrace : WordTrace (prefixWord ++ tailWord_701919) baseStart_701919 baseEnd_701919 := by
    simpa [prefixWord, tailWord_701919, baseEnd_701919] using wordTrace_append hprefix tailTrace_701919
  have hstable : (prefixWord ++ tailWord_701919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701919).length < 2 ^ (prefixWord ++ tailWord_701919).sum := by decide
  have hdescent : baseEnd_701919 < baseStart_701919 := by decide
  rcases family_descends (prefixWord ++ tailWord_701919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701923 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 3]
def baseStart_701923 : Nat := 118140960795 + 701923 * 2 ^ 59
def prefixEnd_701923 : Nat := 4983230072969 + 3 ^ 40 * 701923 * 2
def baseEnd_701923 : Nat := 360423881445962456734421

theorem tailTrace_701923 : CollatzResearch.WordTrace tailWord_701923 prefixEnd_701923 360423881445962456734421 := by
  unfold tailWord_701923
  simp only [CollatzResearch.WordTrace]
  refine ⟨25601235036060324749462423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17067490024040216499641615 25601235036060324749462423)
  ·
    refine ⟨38401852554090487124193635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25601235036060324749462423 38401852554090487124193635)
    ·
      refine ⟨57602778831135730686290453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38401852554090487124193635 57602778831135730686290453)
      ·
        refine ⟨2700130257709487375919865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57602778831135730686290453 2700130257709487375919865)
        ·
          refine ⟨2025097693282115531939899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2700130257709487375919865 2025097693282115531939899)
          ·
            refine ⟨3037646539923173297909849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025097693282115531939899 3037646539923173297909849)
            ·
              refine ⟨2278234904942379973432387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037646539923173297909849 2278234904942379973432387)
              ·
                refine ⟨3417352357413569960148581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278234904942379973432387 3417352357413569960148581)
                ·
                  refine ⟨640753567015044367527859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3417352357413569960148581 640753567015044367527859)
                  ·
                    refine ⟨961130350522566551291789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640753567015044367527859 961130350522566551291789)
                    ·
                      refine ⟨360423881445962456734421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961130350522566551291789 360423881445962456734421)
                      ·
                        rfl

theorem cell23_701923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_701923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701923 prefixEnd_701923 := by exact prefixLift 701923
  have htrace : WordTrace (prefixWord ++ tailWord_701923) baseStart_701923 baseEnd_701923 := by
    simpa [prefixWord, tailWord_701923, baseEnd_701923] using wordTrace_append hprefix tailTrace_701923
  have hstable : (prefixWord ++ tailWord_701923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701923).length < 2 ^ (prefixWord ++ tailWord_701923).sum := by decide
  have hdescent : baseEnd_701923 < baseStart_701923 := by decide
  rcases family_descends (prefixWord ++ tailWord_701923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701989 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_701989 : Nat := 118140960795 + 701989 * 2 ^ 59
def prefixEnd_701989 : Nat := 4983230072969 + 3 ^ 40 * 701989 * 2
def baseEnd_701989 : Nat := 360457771169159198509117

theorem tailTrace_701989 : CollatzResearch.WordTrace tailWord_701989 prefixEnd_701989 360457771169159198509117 := by
  unfold tailWord_701989
  simp only [CollatzResearch.WordTrace]
  refine ⟨25603642253821218021365021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17069094835880812014243347 25603642253821218021365021)
  ·
    refine ⟨9601365845182956758011883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25603642253821218021365021 9601365845182956758011883)
    ·
      refine ⟨14402048767774435137017825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9601365845182956758011883 14402048767774435137017825)
      ·
        refine ⟨10801536575830826352763369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14402048767774435137017825 10801536575830826352763369)
        ·
          refine ⟨8101152431873119764572527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10801536575830826352763369 8101152431873119764572527)
          ·
            refine ⟨12151728647809679646858791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101152431873119764572527 12151728647809679646858791)
            ·
              refine ⟨18227592971714519470288187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12151728647809679646858791 18227592971714519470288187)
              ·
                refine ⟨27341389457571779205432281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18227592971714519470288187 27341389457571779205432281)
                ·
                  refine ⟨20506042093178834404074211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27341389457571779205432281 20506042093178834404074211)
                  ·
                    refine ⟨30759063139768251606111317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20506042093178834404074211 30759063139768251606111317)
                    ·
                      refine ⟨360457771169159198509117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 30759063139768251606111317 360457771169159198509117)
                      ·
                        rfl

theorem cell23_701989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_701989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_701989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_701989 prefixEnd_701989 := by exact prefixLift 701989
  have htrace : WordTrace (prefixWord ++ tailWord_701989) baseStart_701989 baseEnd_701989 := by
    simpa [prefixWord, tailWord_701989, baseEnd_701989] using wordTrace_append hprefix tailTrace_701989
  have hstable : (prefixWord ++ tailWord_701989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701989).length < 2 ^ (prefixWord ++ tailWord_701989).sum := by decide
  have hdescent : baseEnd_701989 < baseStart_701989 := by decide
  rcases family_descends (prefixWord ++ tailWord_701989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702073 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_702073 : Nat := 118140960795 + 702073 * 2 ^ 59
def prefixEnd_702073 : Nat := 4983230072969 + 3 ^ 40 * 702073 * 2
def baseEnd_702073 : Nat := 360500903544136869858731

theorem tailTrace_702073 : CollatzResearch.WordTrace tailWord_702073 prefixEnd_702073 360500903544136869858731 := by
  unfold tailWord_702073
  simp only [CollatzResearch.WordTrace]
  refine ⟨25606705985516900367422873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17071137323677933578281915 25606705985516900367422873)
  ·
    refine ⟨19205029489137675275567155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25606705985516900367422873 19205029489137675275567155)
    ·
      refine ⟨28807544233706512913350733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19205029489137675275567155 28807544233706512913350733)
      ·
        refine ⟨10802829087639942342506525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28807544233706512913350733 10802829087639942342506525)
        ·
          refine ⟨4051060907864978378439947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10802829087639942342506525 4051060907864978378439947)
          ·
            refine ⟨6076591361797467567659921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051060907864978378439947 6076591361797467567659921)
            ·
              refine ⟨4557443521348100675744941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6076591361797467567659921 4557443521348100675744941)
              ·
                refine ⟨1709041320505537753404353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4557443521348100675744941 1709041320505537753404353)
                ·
                  refine ⟨1281780990379153315053265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709041320505537753404353 1281780990379153315053265)
                  ·
                    refine ⟨961335742784364986289949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1281780990379153315053265 961335742784364986289949)
                    ·
                      refine ⟨360500903544136869858731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961335742784364986289949 360500903544136869858731)
                      ·
                        rfl

theorem cell23_702073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_702073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702073 prefixEnd_702073 := by exact prefixLift 702073
  have htrace : WordTrace (prefixWord ++ tailWord_702073) baseStart_702073 baseEnd_702073 := by
    simpa [prefixWord, tailWord_702073, baseEnd_702073] using wordTrace_append hprefix tailTrace_702073
  have hstable : (prefixWord ++ tailWord_702073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702073).length < 2 ^ (prefixWord ++ tailWord_702073).sum := by decide
  have hdescent : baseEnd_702073 < baseStart_702073 := by decide
  rcases family_descends (prefixWord ++ tailWord_702073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702090 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_702090 : Nat := 118140960795 + 702090 * 2 ^ 59
def prefixEnd_702090 : Nat := 4983230072969 + 3 ^ 40 * 702090 * 2
def baseEnd_702090 : Nat := 360509632715263303346153

theorem tailTrace_702090 : CollatzResearch.WordTrace tailWord_702090 prefixEnd_702090 360509632715263303346153 := by
  unfold tailWord_702090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401831506613828067697931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17071550684303541513861149 6401831506613828067697931)
  ·
    refine ⟨9602747259920742101546897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401831506613828067697931 9602747259920742101546897)
    ·
      refine ⟨7202060444940556576160173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9602747259920742101546897 7202060444940556576160173)
      ·
        refine ⟨2700772666852708716060065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7202060444940556576160173 2700772666852708716060065)
        ·
          refine ⟨2025579500139531537045049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2700772666852708716060065 2025579500139531537045049)
          ·
            refine ⟨1519184625104648652783787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2025579500139531537045049 1519184625104648652783787)
            ·
              refine ⟨2278776937656972979175681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519184625104648652783787 2278776937656972979175681)
              ·
                refine ⟨1709082703242729734381761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278776937656972979175681 1709082703242729734381761)
                ·
                  refine ⟨1281812027432047300786321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709082703242729734381761 1281812027432047300786321)
                  ·
                    refine ⟨961359020574035475589741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1281812027432047300786321 961359020574035475589741)
                    ·
                      refine ⟨360509632715263303346153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961359020574035475589741 360509632715263303346153)
                      ·
                        rfl

theorem cell23_702090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_702090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702090 prefixEnd_702090 := by exact prefixLift 702090
  have htrace : WordTrace (prefixWord ++ tailWord_702090) baseStart_702090 baseEnd_702090 := by
    simpa [prefixWord, tailWord_702090, baseEnd_702090] using wordTrace_append hprefix tailTrace_702090
  have hstable : (prefixWord ++ tailWord_702090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702090).length < 2 ^ (prefixWord ++ tailWord_702090).sum := by decide
  have hdescent : baseEnd_702090 < baseStart_702090 := by decide
  rcases family_descends (prefixWord ++ tailWord_702090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702110 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_702110 : Nat := 118140960795 + 702110 * 2 ^ 59
def prefixEnd_702110 : Nat := 4983230072969 + 3 ^ 40 * 702110 * 2
def baseEnd_702110 : Nat := 40057766925372580566229

theorem tailTrace_702110 : CollatzResearch.WordTrace tailWord_702110 prefixEnd_702110 40057766925372580566229 := by
  unfold tailWord_702110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201006935797856960814973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17072036990921903791013189 3201006935797856960814973)
  ·
    refine ⟨1200377600924196360305615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3201006935797856960814973 1200377600924196360305615)
    ·
      refine ⟨1800566401386294540458423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200377600924196360305615 1800566401386294540458423)
      ·
        refine ⟨2700849602079441810687635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800566401386294540458423 2700849602079441810687635)
        ·
          refine ⟨4051274403119162716031453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700849602079441810687635 4051274403119162716031453)
          ·
            refine ⟨1519227901169686018511795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4051274403119162716031453 1519227901169686018511795)
            ·
              refine ⟨2278841851754529027767693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519227901169686018511795 2278841851754529027767693)
              ·
                refine ⟨854565694407948385412885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2278841851754529027767693 854565694407948385412885)
                ·
                  refine ⟨40057766925372580566229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 854565694407948385412885 40057766925372580566229)
                  ·
                    rfl

theorem cell23_702110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_702110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702110 prefixEnd_702110 := by exact prefixLift 702110
  have htrace : WordTrace (prefixWord ++ tailWord_702110) baseStart_702110 baseEnd_702110 := by
    simpa [prefixWord, tailWord_702110, baseEnd_702110] using wordTrace_append hprefix tailTrace_702110
  have hstable : (prefixWord ++ tailWord_702110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702110).length < 2 ^ (prefixWord ++ tailWord_702110).sum := by decide
  have hdescent : baseEnd_702110 < baseStart_702110 := by decide
  rcases family_descends (prefixWord ++ tailWord_702110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702130 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_702130 : Nat := 118140960795 + 702130 * 2 ^ 59
def prefixEnd_702130 : Nat := 4983230072969 + 3 ^ 40 * 702130 * 2
def baseEnd_702130 : Nat := 360530171941443146845969

theorem tailTrace_702130 : CollatzResearch.WordTrace tailWord_702130 prefixEnd_702130 360530171941443146845969 := by
  unfold tailWord_702130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402196236577599775561961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17072523297540266068165229 6402196236577599775561961)
  ·
    refine ⟨4801647177433199831671471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6402196236577599775561961 4801647177433199831671471)
    ·
      refine ⟨7202470766149799747507207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801647177433199831671471 7202470766149799747507207)
      ·
        refine ⟨10803706149224699621260811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202470766149799747507207 10803706149224699621260811)
        ·
          refine ⟨16205559223837049431891217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10803706149224699621260811 16205559223837049431891217)
          ·
            refine ⟨12154169417877787073918413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16205559223837049431891217 12154169417877787073918413)
            ·
              refine ⟨4557813531704170152719405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12154169417877787073918413 4557813531704170152719405)
              ·
                refine ⟨1709180074389063807269777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4557813531704170152719405 1709180074389063807269777)
                ·
                  refine ⟨1281885055791797855452333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709180074389063807269777 1281885055791797855452333)
                  ·
                    refine ⟨480706895921924195794625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1281885055791797855452333 480706895921924195794625)
                    ·
                      refine ⟨360530171941443146845969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480706895921924195794625 360530171941443146845969)
                      ·
                        rfl

theorem cell23_702130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_702130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702130 prefixEnd_702130 := by exact prefixLift 702130
  have htrace : WordTrace (prefixWord ++ tailWord_702130) baseStart_702130 baseEnd_702130 := by
    simpa [prefixWord, tailWord_702130, baseEnd_702130] using wordTrace_append hprefix tailTrace_702130
  have hstable : (prefixWord ++ tailWord_702130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702130).length < 2 ^ (prefixWord ++ tailWord_702130).sum := by decide
  have hdescent : baseEnd_702130 < baseStart_702130 := by decide
  rcases family_descends (prefixWord ++ tailWord_702130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702154 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_702154 : Nat := 118140960795 + 702154 * 2 ^ 59
def prefixEnd_702154 : Nat := 4983230072969 + 3 ^ 40 * 702154 * 2
def baseEnd_702154 : Nat := 360542495477151052945859

theorem tailTrace_702154 : CollatzResearch.WordTrace tailWord_702154 prefixEnd_702154 360542495477151052945859 := by
  unfold tailWord_702154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402415074555862800280379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17073106865482300800747677 6402415074555862800280379)
  ·
    refine ⟨9603622611833794200420569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402415074555862800280379 9603622611833794200420569)
    ·
      refine ⟨7202716958875345650315427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9603622611833794200420569 7202716958875345650315427)
      ·
        refine ⟨10804075438313018475473141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202716958875345650315427 10804075438313018475473141)
        ·
          refine ⟨1012882072341845482075607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10804075438313018475473141 1012882072341845482075607)
          ·
            refine ⟨1519323108512768223113411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012882072341845482075607 1519323108512768223113411)
            ·
              refine ⟨2278984662769152334670117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519323108512768223113411 2278984662769152334670117)
              ·
                refine ⟨427309624269216062750647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2278984662769152334670117 427309624269216062750647)
                ·
                  refine ⟨640964436403824094125971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427309624269216062750647 640964436403824094125971)
                  ·
                    refine ⟨961446654605736141188957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640964436403824094125971 961446654605736141188957)
                    ·
                      refine ⟨360542495477151052945859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961446654605736141188957 360542495477151052945859)
                      ·
                        rfl

theorem cell23_702154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_702154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702154 prefixEnd_702154 := by exact prefixLift 702154
  have htrace : WordTrace (prefixWord ++ tailWord_702154) baseStart_702154 baseEnd_702154 := by
    simpa [prefixWord, tailWord_702154, baseEnd_702154] using wordTrace_append hprefix tailTrace_702154
  have hstable : (prefixWord ++ tailWord_702154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702154).length < 2 ^ (prefixWord ++ tailWord_702154).sum := by decide
  have hdescent : baseEnd_702154 < baseStart_702154 := by decide
  rcases family_descends (prefixWord ++ tailWord_702154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702170 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_702170 : Nat := 118140960795 + 702170 * 2 ^ 59
def prefixEnd_702170 : Nat := 4983230072969 + 3 ^ 40 * 702170 * 2
def baseEnd_702170 : Nat := 120183570389207663448595

theorem tailTrace_702170 : CollatzResearch.WordTrace tailWord_702170 prefixEnd_702170 120183570389207663448595 := by
  unfold tailWord_702170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402560966541371483425991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17073495910776990622469309 6402560966541371483425991)
  ·
    refine ⟨9603841449812057225138987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402560966541371483425991 9603841449812057225138987)
    ·
      refine ⟨14405762174718085837708481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9603841449812057225138987 14405762174718085837708481)
      ·
        refine ⟨10804321631038564378281361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14405762174718085837708481 10804321631038564378281361)
        ·
          refine ⟨8103241223278923283711021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10804321631038564378281361 8103241223278923283711021)
          ·
            refine ⟨3038715458729596231391633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8103241223278923283711021 3038715458729596231391633)
            ·
              refine ⟨2279036594047197173543725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038715458729596231391633 2279036594047197173543725)
              ·
                refine ⟨854638722767698940078897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2279036594047197173543725 854638722767698940078897)
                ·
                  refine ⟨640979042075774205059173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 854638722767698940078897 640979042075774205059173)
                  ·
                    refine ⟨120183570389207663448595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640979042075774205059173 120183570389207663448595)
                    ·
                      rfl

theorem cell23_702170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_702170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702170 prefixEnd_702170 := by exact prefixLift 702170
  have htrace : WordTrace (prefixWord ++ tailWord_702170) baseStart_702170 baseEnd_702170 := by
    simpa [prefixWord, tailWord_702170, baseEnd_702170] using wordTrace_append hprefix tailTrace_702170
  have hstable : (prefixWord ++ tailWord_702170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702170).length < 2 ^ (prefixWord ++ tailWord_702170).sum := by decide
  have hdescent : baseEnd_702170 < baseStart_702170 := by decide
  rcases family_descends (prefixWord ++ tailWord_702170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702180 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_702180 : Nat := 118140960795 + 702180 * 2 ^ 59
def prefixEnd_702180 : Nat := 4983230072969 + 3 ^ 40 * 702180 * 2
def baseEnd_702180 : Nat := 360555845974167951220739

theorem tailTrace_702180 : CollatzResearch.WordTrace tailWord_702180 prefixEnd_702180 360555845974167951220739 := by
  unfold tailWord_702180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12805304298064628820783997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17073739064086171761045329 12805304298064628820783997)
  ·
    refine ⟨4801989111774235807793999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12805304298064628820783997 4801989111774235807793999)
    ·
      refine ⟨7202983667661353711690999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801989111774235807793999 7202983667661353711690999)
      ·
        refine ⟨10804475501492030567536499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202983667661353711690999 10804475501492030567536499)
        ·
          refine ⟨16206713252238045851304749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804475501492030567536499 16206713252238045851304749)
          ·
            refine ⟨6077517469589267194239281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16206713252238045851304749 6077517469589267194239281)
            ·
              refine ⟨4558138102191950395679461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077517469589267194239281 4558138102191950395679461)
              ·
                refine ⟨854650894160990699189899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4558138102191950395679461 854650894160990699189899)
                ·
                  refine ⟨1281976341241486048784849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854650894160990699189899 1281976341241486048784849)
                  ·
                    refine ⟨961482255931114536588637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1281976341241486048784849 961482255931114536588637)
                    ·
                      refine ⟨360555845974167951220739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961482255931114536588637 360555845974167951220739)
                      ·
                        rfl

theorem cell23_702180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_702180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702180 prefixEnd_702180 := by exact prefixLift 702180
  have htrace : WordTrace (prefixWord ++ tailWord_702180) baseStart_702180 baseEnd_702180 := by
    simpa [prefixWord, tailWord_702180, baseEnd_702180] using wordTrace_append hprefix tailTrace_702180
  have hstable : (prefixWord ++ tailWord_702180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702180).length < 2 ^ (prefixWord ++ tailWord_702180).sum := by decide
  have hdescent : baseEnd_702180 < baseStart_702180 := by decide
  rcases family_descends (prefixWord ++ tailWord_702180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702220 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 5, 3, 2]
def baseStart_702220 : Nat := 118140960795 + 702220 * 2 ^ 59
def prefixEnd_702220 : Nat := 4983230072969 + 3 ^ 40 * 702220 * 2
def baseEnd_702220 : Nat := 360576385200347794720555

theorem tailTrace_702220 : CollatzResearch.WordTrace tailWord_702220 prefixEnd_702220 360576385200347794720555 := by
  unfold tailWord_702220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806033757992172236512057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17074711677322896315349409 12806033757992172236512057)
  ·
    refine ⟨9604525318494129177384043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12806033757992172236512057 9604525318494129177384043)
    ·
      refine ⟨14406787977741193766076065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9604525318494129177384043 14406787977741193766076065)
      ·
        refine ⟨10805090983305895324557049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14406787977741193766076065 10805090983305895324557049)
        ·
          refine ⟨8103818237479421493417787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10805090983305895324557049 8103818237479421493417787)
          ·
            refine ⟨12155727356219132240126681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103818237479421493417787 12155727356219132240126681)
            ·
              refine ⟨9116795517164349180095011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12155727356219132240126681 9116795517164349180095011)
              ·
                refine ⟨13675193275746523770142517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9116795517164349180095011 13675193275746523770142517)
                ·
                  refine ⟨1282049369601236603450861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13675193275746523770142517 1282049369601236603450861)
                  ·
                    refine ⟨480768513600463726294073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282049369601236603450861 480768513600463726294073)
                    ·
                      refine ⟨360576385200347794720555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480768513600463726294073 360576385200347794720555)
                      ·
                        rfl

theorem cell23_702220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_702220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702220 prefixEnd_702220 := by exact prefixLift 702220
  have htrace : WordTrace (prefixWord ++ tailWord_702220) baseStart_702220 baseEnd_702220 := by
    simpa [prefixWord, tailWord_702220, baseEnd_702220] using wordTrace_append hprefix tailTrace_702220
  have hstable : (prefixWord ++ tailWord_702220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702220).length < 2 ^ (prefixWord ++ tailWord_702220).sum := by decide
  have hdescent : baseEnd_702220 < baseStart_702220 := by decide
  rcases family_descends (prefixWord ++ tailWord_702220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702263 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_702263 : Nat := 118140960795 + 702263 * 2 ^ 59
def prefixEnd_702263 : Nat := 4983230072969 + 3 ^ 40 * 702263 * 2
def baseEnd_702263 : Nat := 360598464868491126482857

theorem tailTrace_702263 : CollatzResearch.WordTrace tailWord_702263 prefixEnd_702263 360598464868491126482857 := by
  unfold tailWord_702263
  simp only [CollatzResearch.WordTrace]
  refine ⟨25613635854828562816839443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17075757236552375211226295 25613635854828562816839443)
  ·
    refine ⟨38420453782242844225259165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25613635854828562816839443 38420453782242844225259165)
    ·
      refine ⟨14407670168341066584472187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38420453782242844225259165 14407670168341066584472187)
      ·
        refine ⟨21611505252511599876708281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14407670168341066584472187 21611505252511599876708281)
        ·
          refine ⟨16208628939383699907531211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21611505252511599876708281 16208628939383699907531211)
          ·
            refine ⟨24312943409075549861296817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16208628939383699907531211 24312943409075549861296817)
            ·
              refine ⟨18234707556806662395972613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24312943409075549861296817 18234707556806662395972613)
              ·
                refine ⟨3419007666901249199244865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18234707556806662395972613 3419007666901249199244865)
                ·
                  refine ⟨2564255750175936899433649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3419007666901249199244865 2564255750175936899433649)
                  ·
                    refine ⟨1923191812631952674575237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2564255750175936899433649 1923191812631952674575237)
                    ·
                      refine ⟨360598464868491126482857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1923191812631952674575237 360598464868491126482857)
                      ·
                        rfl

theorem cell23_702263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_702263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702263 prefixEnd_702263 := by exact prefixLift 702263
  have htrace : WordTrace (prefixWord ++ tailWord_702263) baseStart_702263 baseEnd_702263 := by
    simpa [prefixWord, tailWord_702263, baseEnd_702263] using wordTrace_append hprefix tailTrace_702263
  have hstable : (prefixWord ++ tailWord_702263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702263).length < 2 ^ (prefixWord ++ tailWord_702263).sum := by decide
  have hdescent : baseEnd_702263 < baseStart_702263 := by decide
  rcases family_descends (prefixWord ++ tailWord_702263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702278 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_702278 : Nat := 118140960795 + 702278 * 2 ^ 59
def prefixEnd_702278 : Nat := 4983230072969 + 3 ^ 40 * 702278 * 2
def baseEnd_702278 : Nat := 360606167078308567795289

theorem tailTrace_702278 : CollatzResearch.WordTrace tailWord_702278 prefixEnd_702278 360606167078308567795289 := by
  unfold tailWord_702278
  simp only [CollatzResearch.WordTrace]
  refine ⟨800443217180444386832359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17076121966516146919090325 800443217180444386832359)
  ·
    refine ⟨1200664825770666580248539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800443217180444386832359 1200664825770666580248539)
    ·
      refine ⟨1800997238655999870372809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200664825770666580248539 1800997238655999870372809)
      ·
        refine ⟨1350747928991999902779607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1800997238655999870372809 1350747928991999902779607)
        ·
          refine ⟨2026121893487999854169411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350747928991999902779607 2026121893487999854169411)
          ·
            refine ⟨3039182840231999781254117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026121893487999854169411 3039182840231999781254117)
            ·
              refine ⟨569846782543499958985147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3039182840231999781254117 569846782543499958985147)
              ·
                refine ⟨854770173815249938477721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569846782543499958985147 854770173815249938477721)
                ·
                  refine ⟨641077630361437453858291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 854770173815249938477721 641077630361437453858291)
                  ·
                    refine ⟨961616445542156180787437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 641077630361437453858291 961616445542156180787437)
                    ·
                      refine ⟨360606167078308567795289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961616445542156180787437 360606167078308567795289)
                      ·
                        rfl

theorem cell23_702278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_702278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702278 prefixEnd_702278 := by exact prefixLift 702278
  have htrace : WordTrace (prefixWord ++ tailWord_702278) baseStart_702278 baseEnd_702278 := by
    simpa [prefixWord, tailWord_702278, baseEnd_702278] using wordTrace_append hprefix tailTrace_702278
  have hstable : (prefixWord ++ tailWord_702278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702278).length < 2 ^ (prefixWord ++ tailWord_702278).sum := by decide
  have hdescent : baseEnd_702278 < baseStart_702278 := by decide
  rcases family_descends (prefixWord ++ tailWord_702278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702323 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4]
def baseStart_702323 : Nat := 118140960795 + 702323 * 2 ^ 59
def prefixEnd_702323 : Nat := 4983230072969 + 3 ^ 40 * 702323 * 2
def baseEnd_702323 : Nat := 360629273707760891732581

theorem tailTrace_702323 : CollatzResearch.WordTrace tailWord_702323 prefixEnd_702323 360629273707760891732581 := by
  unfold tailWord_702323
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615824234611193064023623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17077216156407462042682415 25615824234611193064023623)
  ·
    refine ⟨38423736351916789596035435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25615824234611193064023623 38423736351916789596035435)
    ·
      refine ⟨57635604527875184394053153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38423736351916789596035435 57635604527875184394053153)
      ·
        refine ⟨43226703395906388295539865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57635604527875184394053153 43226703395906388295539865)
        ·
          refine ⟨32420027546929791221654899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43226703395906388295539865 32420027546929791221654899)
          ·
            refine ⟨48630041320394686832482349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32420027546929791221654899 48630041320394686832482349)
            ·
              refine ⟨18236265495148007562180881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48630041320394686832482349 18236265495148007562180881)
              ·
                refine ⟨13677199121361005671635661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18236265495148007562180881 13677199121361005671635661)
                ·
                  refine ⟨5128949670510377126863373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13677199121361005671635661 5128949670510377126863373)
                  ·
                    refine ⟨1923356126441391422573765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5128949670510377126863373 1923356126441391422573765)
                    ·
                      refine ⟨360629273707760891732581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1923356126441391422573765 360629273707760891732581)
                      ·
                        rfl

theorem cell23_702323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_702323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702323 prefixEnd_702323 := by exact prefixLift 702323
  have htrace : WordTrace (prefixWord ++ tailWord_702323) baseStart_702323 baseEnd_702323 := by
    simpa [prefixWord, tailWord_702323, baseEnd_702323] using wordTrace_append hprefix tailTrace_702323
  have hstable : (prefixWord ++ tailWord_702323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702323).length < 2 ^ (prefixWord ++ tailWord_702323).sum := by decide
  have hdescent : baseEnd_702323 < baseStart_702323 := by decide
  rcases family_descends (prefixWord ++ tailWord_702323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702333 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_702333 : Nat := 118140960795 + 702333 * 2 ^ 59
def prefixEnd_702333 : Nat := 4983230072969 + 3 ^ 40 * 702333 * 2
def baseEnd_702333 : Nat := 120211469504768617535845

theorem tailTrace_702333 : CollatzResearch.WordTrace tailWord_702333 prefixEnd_702333 120211469504768617535845 := by
  unfold tailWord_702333
  simp only [CollatzResearch.WordTrace]
  refine ⟨25616188964574964771887653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17077459309716643181258435 25616188964574964771887653)
  ·
    refine ⟨4803035430857805894728935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25616188964574964771887653 4803035430857805894728935)
    ·
      refine ⟨7204553146286708842093403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4803035430857805894728935 7204553146286708842093403)
      ·
        refine ⟨10806829719430063263140105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204553146286708842093403 10806829719430063263140105)
        ·
          refine ⟨8105122289572547447355079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10806829719430063263140105 8105122289572547447355079)
          ·
            refine ⟨12157683434358821171032619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8105122289572547447355079 12157683434358821171032619)
            ·
              refine ⟨18236525151538231756548929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12157683434358821171032619 18236525151538231756548929)
              ·
                refine ⟨13677393863653673817411697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18236525151538231756548929 13677393863653673817411697)
                ·
                  refine ⟨10258045397740255363058773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13677393863653673817411697 10258045397740255363058773)
                  ·
                    refine ⟨120211469504768617535845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10258045397740255363058773 120211469504768617535845)
                    ·
                      rfl

theorem cell23_702333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_702333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702333 prefixEnd_702333 := by exact prefixLift 702333
  have htrace : WordTrace (prefixWord ++ tailWord_702333) baseStart_702333 baseEnd_702333 := by
    simpa [prefixWord, tailWord_702333, baseEnd_702333] using wordTrace_append hprefix tailTrace_702333
  have hstable : (prefixWord ++ tailWord_702333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702333).length < 2 ^ (prefixWord ++ tailWord_702333).sum := by decide
  have hdescent : baseEnd_702333 < baseStart_702333 := by decide
  rcases family_descends (prefixWord ++ tailWord_702333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702334 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_702334 : Nat := 118140960795 + 702334 * 2 ^ 59
def prefixEnd_702334 : Nat := 4983230072969 + 3 ^ 40 * 702334 * 2
def baseEnd_702334 : Nat := 360634921994960348695031

theorem tailTrace_702334 : CollatzResearch.WordTrace tailWord_702334 prefixEnd_702334 360634921994960348695031 := by
  unfold tailWord_702334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202028179696417742834257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17077483625047561295116037 3202028179696417742834257)
  ·
    refine ⟨2401521134772313307125693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3202028179696417742834257 2401521134772313307125693)
    ·
      refine ⟨900570425539617490172135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2401521134772313307125693 900570425539617490172135)
      ·
        refine ⟨1350855638309426235258203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900570425539617490172135 1350855638309426235258203)
        ·
          refine ⟨2026283457464139352887305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350855638309426235258203 2026283457464139352887305)
          ·
            refine ⟨1519712593098104514665479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2026283457464139352887305 1519712593098104514665479)
            ·
              refine ⟨2279568889647156771998219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519712593098104514665479 2279568889647156771998219)
              ·
                refine ⟨3419353334470735157997329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279568889647156771998219 3419353334470735157997329)
                ·
                  refine ⟨2564515000853051368497997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3419353334470735157997329 2564515000853051368497997)
                  ·
                    refine ⟨961693125319894263186749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2564515000853051368497997 961693125319894263186749)
                    ·
                      refine ⟨360634921994960348695031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961693125319894263186749 360634921994960348695031)
                      ·
                        rfl

theorem cell23_702334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_702334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702334 prefixEnd_702334 := by exact prefixLift 702334
  have htrace : WordTrace (prefixWord ++ tailWord_702334) baseStart_702334 baseEnd_702334 := by
    simpa [prefixWord, tailWord_702334, baseEnd_702334] using wordTrace_append hprefix tailTrace_702334
  have hstable : (prefixWord ++ tailWord_702334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702334).length < 2 ^ (prefixWord ++ tailWord_702334).sum := by decide
  have hdescent : baseEnd_702334 < baseStart_702334 := by decide
  rcases family_descends (prefixWord ++ tailWord_702334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702340 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_702340 : Nat := 118140960795 + 702340 * 2 ^ 59
def prefixEnd_702340 : Nat := 4983230072969 + 3 ^ 40 * 702340 * 2
def baseEnd_702340 : Nat := 360638002878887325220003

theorem tailTrace_702340 : CollatzResearch.WordTrace tailWord_702340 prefixEnd_702340 360638002878887325220003 := by
  unfold tailWord_702340
  simp only [CollatzResearch.WordTrace]
  refine ⟨12808222137774802483696237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17077629517033069978261649 12808222137774802483696237)
  ·
    refine ⟨4803083301665550931386089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12808222137774802483696237 4803083301665550931386089)
    ·
      refine ⟨3602312476249163198539567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4803083301665550931386089 3602312476249163198539567)
      ·
        refine ⟨5403468714373744797809351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602312476249163198539567 5403468714373744797809351)
        ·
          refine ⟨8105203071560617196714027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403468714373744797809351 8105203071560617196714027)
          ·
            refine ⟨12157804607340925795071041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8105203071560617196714027 12157804607340925795071041)
            ·
              refine ⟨9118353455505694346303281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12157804607340925795071041 9118353455505694346303281)
              ·
                refine ⟨6838765091629270759727461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9118353455505694346303281 6838765091629270759727461)
                ·
                  refine ⟨1282268454680488267448899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6838765091629270759727461 1282268454680488267448899)
                  ·
                    refine ⟨1923402682020732401173349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1282268454680488267448899 1923402682020732401173349)
                    ·
                      refine ⟨360638002878887325220003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1923402682020732401173349 360638002878887325220003)
                      ·
                        rfl

theorem cell23_702340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_702340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702340 prefixEnd_702340 := by exact prefixLift 702340
  have htrace : WordTrace (prefixWord ++ tailWord_702340) baseStart_702340 baseEnd_702340 := by
    simpa [prefixWord, tailWord_702340, baseEnd_702340] using wordTrace_append hprefix tailTrace_702340
  have hstable : (prefixWord ++ tailWord_702340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702340).length < 2 ^ (prefixWord ++ tailWord_702340).sum := by decide
  have hdescent : baseEnd_702340 < baseStart_702340 := by decide
  rcases family_descends (prefixWord ++ tailWord_702340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702354 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_702354 : Nat := 118140960795 + 702354 * 2 ^ 59
def prefixEnd_702354 : Nat := 4983230072969 + 3 ^ 40 * 702354 * 2
def baseEnd_702354 : Nat := 120215063869350090148313

theorem tailTrace_702354 : CollatzResearch.WordTrace tailWord_702354 prefixEnd_702354 120215063869350090148313 := by
  unfold tailWord_702354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6404238724374721339600529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17077969931665923572268077 6404238724374721339600529)
  ·
    refine ⟨4803179043281041004700397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6404238724374721339600529 4803179043281041004700397)
    ·
      refine ⟨1801192141230390376762649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4803179043281041004700397 1801192141230390376762649)
      ·
        refine ⟨1350894105922792782571987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1801192141230390376762649 1350894105922792782571987)
        ·
          refine ⟨2026341158884189173857981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350894105922792782571987 2026341158884189173857981)
          ·
            refine ⟨759877934581570940196743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2026341158884189173857981 759877934581570940196743)
            ·
              refine ⟨1139816901872356410295115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759877934581570940196743 1139816901872356410295115)
              ·
                refine ⟨1709725352808534615442673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139816901872356410295115 1709725352808534615442673)
                ·
                  refine ⟨1282294014606400961582005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709725352808534615442673 1282294014606400961582005)
                  ·
                    refine ⟨120215063869350090148313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1282294014606400961582005 120215063869350090148313)
                    ·
                      rfl

theorem cell23_702354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_702354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702354 prefixEnd_702354 := by exact prefixLift 702354
  have htrace : WordTrace (prefixWord ++ tailWord_702354) baseStart_702354 baseEnd_702354 := by
    simpa [prefixWord, tailWord_702354, baseEnd_702354] using wordTrace_append hprefix tailTrace_702354
  have hstable : (prefixWord ++ tailWord_702354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702354).length < 2 ^ (prefixWord ++ tailWord_702354).sum := by decide
  have hdescent : baseEnd_702354 < baseStart_702354 := by decide
  rcases family_descends (prefixWord ++ tailWord_702354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702358 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_702358 : Nat := 118140960795 + 702358 * 2 ^ 59
def prefixEnd_702358 : Nat := 4983230072969 + 3 ^ 40 * 702358 * 2
def baseEnd_702358 : Nat := 40071916170074250532769

theorem tailTrace_702358 : CollatzResearch.WordTrace tailWord_702358 prefixEnd_702358 40071916170074250532769 := by
  unfold tailWord_702358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601068799342774627596733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17078067192989596027698485 1601068799342774627596733)
  ·
    refine ⟨600400799753540485348775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1601068799342774627596733 600400799753540485348775)
    ·
      refine ⟨900601199630310728023163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600400799753540485348775 900601199630310728023163)
      ·
        refine ⟨1350901799445466092034745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900601199630310728023163 1350901799445466092034745)
        ·
          refine ⟨1013176349584099569026059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350901799445466092034745 1013176349584099569026059)
          ·
            refine ⟨1519764524376149353539089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013176349584099569026059 1519764524376149353539089)
            ·
              refine ⟨1139823393282112015154317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519764524376149353539089 1139823393282112015154317)
              ·
                refine ⟨427433772480792005682869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139823393282112015154317 427433772480792005682869)
                ·
                  refine ⟨40071916170074250532769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427433772480792005682869 40071916170074250532769)
                  ·
                    rfl

theorem cell23_702358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_702358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702358 prefixEnd_702358 := by exact prefixLift 702358
  have htrace : WordTrace (prefixWord ++ tailWord_702358) baseStart_702358 baseEnd_702358 := by
    simpa [prefixWord, tailWord_702358, baseEnd_702358] using wordTrace_append hprefix tailTrace_702358
  have hstable : (prefixWord ++ tailWord_702358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702358).length < 2 ^ (prefixWord ++ tailWord_702358).sum := by decide
  have hdescent : baseEnd_702358 < baseStart_702358 := by decide
  rcases family_descends (prefixWord ++ tailWord_702358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702383 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_702383 : Nat := 118140960795 + 702383 * 2 ^ 59
def prefixEnd_702383 : Nat := 4983230072969 + 3 ^ 40 * 702383 * 2
def baseEnd_702383 : Nat := 360660082547030656982305

theorem tailTrace_702383 : CollatzResearch.WordTrace tailWord_702383 prefixEnd_702383 360660082547030656982305 := by
  unfold tailWord_702383
  simp only [CollatzResearch.WordTrace]
  refine ⟨25618012614393823311207803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17078675076262548874138535 25618012614393823311207803)
  ·
    refine ⟨38427018921590734966811705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25618012614393823311207803 38427018921590734966811705)
    ·
      refine ⟨28820264191193051225108779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38427018921590734966811705 28820264191193051225108779)
      ·
        refine ⟨43230396286789576837663169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28820264191193051225108779 43230396286789576837663169)
        ·
          refine ⟨32422797215092182628247377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43230396286789576837663169 32422797215092182628247377)
          ·
            refine ⟨24317097911319136971185533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32422797215092182628247377 24317097911319136971185533)
            ·
              refine ⟨9118911716744676364194575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24317097911319136971185533 9118911716744676364194575)
              ·
                refine ⟨13678367575117014546291863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118911716744676364194575 13678367575117014546291863)
                ·
                  refine ⟨20517551362675521819437795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13678367575117014546291863 20517551362675521819437795)
                  ·
                    refine ⟨30776327044013282729156693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20517551362675521819437795 30776327044013282729156693)
                    ·
                      refine ⟨360660082547030656982305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 30776327044013282729156693 360660082547030656982305)
                      ·
                        rfl

theorem cell23_702383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_702383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702383 prefixEnd_702383 := by exact prefixLift 702383
  have htrace : WordTrace (prefixWord ++ tailWord_702383) baseStart_702383 baseEnd_702383 := by
    simpa [prefixWord, tailWord_702383, baseEnd_702383] using wordTrace_append hprefix tailTrace_702383
  have hstable : (prefixWord ++ tailWord_702383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702383).length < 2 ^ (prefixWord ++ tailWord_702383).sum := by decide
  have hdescent : baseEnd_702383 < baseStart_702383 := by decide
  rcases family_descends (prefixWord ++ tailWord_702383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702410 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_702410 : Nat := 118140960795 + 702410 * 2 ^ 59
def prefixEnd_702410 : Nat := 4983230072969 + 3 ^ 40 * 702410 * 2
def baseEnd_702410 : Nat := 120224648841567350448227

theorem tailTrace_702410 : CollatzResearch.WordTrace tailWord_702410 prefixEnd_702410 120224648841567350448227 := by
  unfold tailWord_702410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6404749346324001730610171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17079331590197337948293789 6404749346324001730610171)
  ·
    refine ⟨9607124019486002595915257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6404749346324001730610171 9607124019486002595915257)
    ·
      refine ⟨7205343014614501946936443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9607124019486002595915257 7205343014614501946936443)
      ·
        refine ⟨10808014521921752920404665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7205343014614501946936443 10808014521921752920404665)
        ·
          refine ⟨8106010891441314690303499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10808014521921752920404665 8106010891441314690303499)
          ·
            refine ⟨12159016337161972035455249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8106010891441314690303499 12159016337161972035455249)
            ·
              refine ⟨9119262252871479026591437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12159016337161972035455249 9119262252871479026591437)
              ·
                refine ⟨3419723344826804634971789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9119262252871479026591437 3419723344826804634971789)
                ·
                  refine ⟨1282396254310051738114421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3419723344826804634971789 1282396254310051738114421)
                  ·
                    refine ⟨120224648841567350448227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1282396254310051738114421 120224648841567350448227)
                    ·
                      rfl

theorem cell23_702410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_702410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702410 prefixEnd_702410 := by exact prefixLift 702410
  have htrace : WordTrace (prefixWord ++ tailWord_702410) baseStart_702410 baseEnd_702410 := by
    simpa [prefixWord, tailWord_702410, baseEnd_702410] using wordTrace_append hprefix tailTrace_702410
  have hstable : (prefixWord ++ tailWord_702410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702410).length < 2 ^ (prefixWord ++ tailWord_702410).sum := by decide
  have hdescent : baseEnd_702410 < baseStart_702410 := by decide
  rcases family_descends (prefixWord ++ tailWord_702410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702418 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_702418 : Nat := 118140960795 + 702418 * 2 ^ 59
def prefixEnd_702418 : Nat := 4983230072969 + 3 ^ 40 * 702418 * 2
def baseEnd_702418 : Nat := 120226018123312673348215

theorem tailTrace_702418 : CollatzResearch.WordTrace tailWord_702418 prefixEnd_702418 120226018123312673348215 := by
  unfold tailWord_702418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6404822292316756072182977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17079526112844682859154605 6404822292316756072182977)
  ·
    refine ⟨4803616719237567054137233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6404822292316756072182977 4803616719237567054137233)
    ·
      refine ⟨3602712539428175290602925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4803616719237567054137233 3602712539428175290602925)
      ·
        refine ⟨1351017202285565733976097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3602712539428175290602925 1351017202285565733976097)
        ·
          refine ⟨1013262901714174300482073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1351017202285565733976097 1013262901714174300482073)
          ·
            refine ⟨759947176285630725361555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013262901714174300482073 759947176285630725361555)
            ·
              refine ⟨1139920764428446088042333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759947176285630725361555 1139920764428446088042333)
              ·
                refine ⟨427470286660667283015875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139920764428446088042333 427470286660667283015875)
                ·
                  refine ⟨641205429991000924523813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427470286660667283015875 641205429991000924523813)
                  ·
                    refine ⟨120226018123312673348215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 641205429991000924523813 120226018123312673348215)
                    ·
                      rfl

theorem cell23_702418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_702418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702418 prefixEnd_702418 := by exact prefixLift 702418
  have htrace : WordTrace (prefixWord ++ tailWord_702418) baseStart_702418 baseEnd_702418 := by
    simpa [prefixWord, tailWord_702418, baseEnd_702418] using wordTrace_append hprefix tailTrace_702418
  have hstable : (prefixWord ++ tailWord_702418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702418).length < 2 ^ (prefixWord ++ tailWord_702418).sum := by decide
  have hdescent : baseEnd_702418 < baseStart_702418 := by decide
  rcases family_descends (prefixWord ++ tailWord_702418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702428 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_702428 : Nat := 118140960795 + 702428 * 2 ^ 59
def prefixEnd_702428 : Nat := 4983230072969 + 3 ^ 40 * 702428 * 2
def baseEnd_702428 : Nat := 360683189176482980919599

theorem tailTrace_702428 : CollatzResearch.WordTrace tailWord_702428 prefixEnd_702428 360683189176482980919599 := by
  unfold tailWord_702428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809826949615397998297969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17079769266153863997730625 12809826949615397998297969)
  ·
    refine ⟨9607370212211548498723477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12809826949615397998297969 9607370212211548498723477)
    ·
      refine ⟨450345478697416335877663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9607370212211548498723477 450345478697416335877663)
      ·
        refine ⟨675518218046124503816495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450345478697416335877663 675518218046124503816495)
        ·
          refine ⟨1013277327069186755724743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675518218046124503816495 1013277327069186755724743)
          ·
            refine ⟨1519915990603780133587115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013277327069186755724743 1519915990603780133587115)
            ·
              refine ⟨2279873985905670200380673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519915990603780133587115 2279873985905670200380673)
              ·
                refine ⟨1709905489429252650285505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279873985905670200380673 1709905489429252650285505)
                ·
                  refine ⟨1282429117071939487714129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1709905489429252650285505 1282429117071939487714129)
                  ·
                    refine ⟨961821837803954615785597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1282429117071939487714129 961821837803954615785597)
                    ·
                      refine ⟨360683189176482980919599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961821837803954615785597 360683189176482980919599)
                      ·
                        rfl

theorem cell23_702428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_702428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702428 prefixEnd_702428 := by exact prefixLift 702428
  have htrace : WordTrace (prefixWord ++ tailWord_702428) baseStart_702428 baseEnd_702428 := by
    simpa [prefixWord, tailWord_702428, baseEnd_702428] using wordTrace_append hprefix tailTrace_702428
  have hstable : (prefixWord ++ tailWord_702428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702428).length < 2 ^ (prefixWord ++ tailWord_702428).sum := by decide
  have hdescent : baseEnd_702428 < baseStart_702428 := by decide
  rcases family_descends (prefixWord ++ tailWord_702428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702460 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_702460 : Nat := 118140960795 + 702460 * 2 ^ 59
def prefixEnd_702460 : Nat := 4983230072969 + 3 ^ 40 * 702460 * 2
def baseEnd_702460 : Nat := 360699620557426855719451

theorem tailTrace_702460 : CollatzResearch.WordTrace tailWord_702460 prefixEnd_702460 360699620557426855719451 := by
  unfold tailWord_702460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810410517557432730880417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17080547356743243641173889 12810410517557432730880417)
  ·
    refine ⟨9607807888168074548160313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12810410517557432730880417 9607807888168074548160313)
    ·
      refine ⟨7205855916126055911120235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9607807888168074548160313 7205855916126055911120235)
      ·
        refine ⟨10808783874189083866680353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7205855916126055911120235 10808783874189083866680353)
        ·
          refine ⟨8106587905641812900010265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10808783874189083866680353 8106587905641812900010265)
          ·
            refine ⟨6079940929231359675007699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8106587905641812900010265 6079940929231359675007699)
            ·
              refine ⟨9119911393847039512511549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079940929231359675007699 9119911393847039512511549)
              ·
                refine ⟨3419966772692639817191831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9119911393847039512511549 3419966772692639817191831)
                ·
                  refine ⟨5129950159038959725787747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419966772692639817191831 5129950159038959725787747)
                  ·
                    refine ⟨7694925238558439588681621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129950159038959725787747 7694925238558439588681621)
                    ·
                      refine ⟨360699620557426855719451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7694925238558439588681621 360699620557426855719451)
                      ·
                        rfl

theorem cell23_702460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_702460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702460 prefixEnd_702460 := by exact prefixLift 702460
  have htrace : WordTrace (prefixWord ++ tailWord_702460) baseStart_702460 baseEnd_702460 := by
    simpa [prefixWord, tailWord_702460, baseEnd_702460] using wordTrace_append hprefix tailTrace_702460
  have hstable : (prefixWord ++ tailWord_702460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702460).length < 2 ^ (prefixWord ++ tailWord_702460).sum := by decide
  have hdescent : baseEnd_702460 < baseStart_702460 := by decide
  rcases family_descends (prefixWord ++ tailWord_702460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702468 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_702468 : Nat := 118140960795 + 702468 * 2 ^ 59
def prefixEnd_702468 : Nat := 4983230072969 + 3 ^ 40 * 702468 * 2
def baseEnd_702468 : Nat := 360703728402662824419415

theorem tailTrace_702468 : CollatzResearch.WordTrace tailWord_702468 prefixEnd_702468 360703728402662824419415 := by
  unfold tailWord_702468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810556409542941414026029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17080741879390588552034705 12810556409542941414026029)
  ·
    refine ⟨4803958653578603030259761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12810556409542941414026029 4803958653578603030259761)
    ·
      refine ⟨3602968990183952272694821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4803958653578603030259761 3602968990183952272694821)
      ·
        refine ⟨675556685659491051130279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3602968990183952272694821 675556685659491051130279)
        ·
          refine ⟨1013335028489236576695419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675556685659491051130279 1013335028489236576695419)
          ·
            refine ⟨1520002542733854865043129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013335028489236576695419 1520002542733854865043129)
            ·
              refine ⟨1140001907050391148782347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520002542733854865043129 1140001907050391148782347)
              ·
                refine ⟨1710002860575586723173521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140001907050391148782347 1710002860575586723173521)
                ·
                  refine ⟨1282502145431690042380141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710002860575586723173521 1282502145431690042380141)
                  ·
                    refine ⟨480938304536883765892553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282502145431690042380141 480938304536883765892553)
                    ·
                      refine ⟨360703728402662824419415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480938304536883765892553 360703728402662824419415)
                      ·
                        rfl

theorem cell23_702468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_702468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702468 prefixEnd_702468 := by exact prefixLift 702468
  have htrace : WordTrace (prefixWord ++ tailWord_702468) baseStart_702468 baseEnd_702468 := by
    simpa [prefixWord, tailWord_702468, baseEnd_702468] using wordTrace_append hprefix tailTrace_702468
  have hstable : (prefixWord ++ tailWord_702468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702468).length < 2 ^ (prefixWord ++ tailWord_702468).sum := by decide
  have hdescent : baseEnd_702468 < baseStart_702468 := by decide
  rcases family_descends (prefixWord ++ tailWord_702468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702487 : List Nat := [1, 1, 3, 5, 3, 10]
def baseStart_702487 : Nat := 118140960795 + 702487 * 2 ^ 59
def prefixEnd_702487 : Nat := 4983230072969 + 3 ^ 40 * 702487 * 2
def baseEnd_702487 : Nat := 1484417631831680041489

theorem tailTrace_702487 : CollatzResearch.WordTrace tailWord_702487 prefixEnd_702487 1484417631831680041489 := by
  unfold tailWord_702487
  simp only [CollatzResearch.WordTrace]
  refine ⟨25621805806017049072993715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17081203870678032715329143 25621805806017049072993715)
  ·
    refine ⟨38432708709025573609490573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25621805806017049072993715 38432708709025573609490573)
    ·
      refine ⟨14412265765884590103558965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38432708709025573609490573 14412265765884590103558965)
      ·
        refine ⟨1351149915551680322208653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14412265765884590103558965 1351149915551680322208653)
        ·
          refine ⟨506681218331880120828245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1351149915551680322208653 506681218331880120828245)
          ·
            refine ⟨1484417631831680041489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 506681218331880120828245 1484417631831680041489)
            ·
              rfl

theorem cell23_702487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 10].length) (baseStart_702487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702487 prefixEnd_702487 := by exact prefixLift 702487
  have htrace : WordTrace (prefixWord ++ tailWord_702487) baseStart_702487 baseEnd_702487 := by
    simpa [prefixWord, tailWord_702487, baseEnd_702487] using wordTrace_append hprefix tailTrace_702487
  have hstable : (prefixWord ++ tailWord_702487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702487).length < 2 ^ (prefixWord ++ tailWord_702487).sum := by decide
  have hdescent : baseEnd_702487 < baseStart_702487 := by decide
  rcases family_descends (prefixWord ++ tailWord_702487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702498 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_702498 : Nat := 118140960795 + 702498 * 2 ^ 59
def prefixEnd_702498 : Nat := 4983230072969 + 3 ^ 40 * 702498 * 2
def baseEnd_702498 : Nat := 360719132822297707044277

theorem tailTrace_702498 : CollatzResearch.WordTrace tailWord_702498 prefixEnd_702498 360719132822297707044277 := by
  unfold tailWord_702498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405551752244299487911037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17081471339318131967762765 6405551752244299487911037)
  ·
    refine ⟨2402081907091612307966639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6405551752244299487911037 2402081907091612307966639)
    ·
      refine ⟨3603122860637418461949959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402081907091612307966639 3603122860637418461949959)
      ·
        refine ⟨5404684290956127692924939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603122860637418461949959 5404684290956127692924939)
        ·
          refine ⟨8107026436434191539387409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404684290956127692924939 8107026436434191539387409)
          ·
            refine ⟨6080269827325643654540557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8107026436434191539387409 6080269827325643654540557)
            ·
              refine ⟨2280101185247116370452709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6080269827325643654540557 2280101185247116370452709)
              ·
                refine ⟨427518972233834319459883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2280101185247116370452709 427518972233834319459883)
                ·
                  refine ⟨641278458350751479189825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427518972233834319459883 641278458350751479189825)
                  ·
                    refine ⟨480958843763063609392369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 641278458350751479189825 480958843763063609392369)
                    ·
                      refine ⟨360719132822297707044277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480958843763063609392369 360719132822297707044277)
                      ·
                        rfl

theorem cell23_702498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_702498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702498 prefixEnd_702498 := by exact prefixLift 702498
  have htrace : WordTrace (prefixWord ++ tailWord_702498) baseStart_702498 baseEnd_702498 := by
    simpa [prefixWord, tailWord_702498, baseEnd_702498] using wordTrace_append hprefix tailTrace_702498
  have hstable : (prefixWord ++ tailWord_702498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702498).length < 2 ^ (prefixWord ++ tailWord_702498).sum := by decide
  have hdescent : baseEnd_702498 < baseStart_702498 := by decide
  rcases family_descends (prefixWord ++ tailWord_702498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702514 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_702514 : Nat := 118140960795 + 702514 * 2 ^ 59
def prefixEnd_702514 : Nat := 4983230072969 + 3 ^ 40 * 702514 * 2
def baseEnd_702514 : Nat := 360727348512769644444203

theorem tailTrace_702514 : CollatzResearch.WordTrace tailWord_702514 prefixEnd_702514 360727348512769644444203 := by
  unfold tailWord_702514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405697644229808171056649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17081860384612821789484397 6405697644229808171056649)
  ·
    refine ⟨4804273233172356128292487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6405697644229808171056649 4804273233172356128292487)
    ·
      refine ⟨7206409849758534192438731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804273233172356128292487 7206409849758534192438731)
      ·
        refine ⟨10809614774637801288658097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7206409849758534192438731 10809614774637801288658097)
        ·
          refine ⟨8107211080978350966493573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10809614774637801288658097 8107211080978350966493573)
          ·
            refine ⟨1520102077683440806217545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8107211080978350966493573 1520102077683440806217545)
            ·
              refine ⟨1140076558262580604663159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520102077683440806217545 1140076558262580604663159)
              ·
                refine ⟨1710114837393870906994739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140076558262580604663159 1710114837393870906994739)
                ·
                  refine ⟨2565172256090806360492109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710114837393870906994739 2565172256090806360492109)
                  ·
                    refine ⟨961939596034052385184541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565172256090806360492109 961939596034052385184541)
                    ·
                      refine ⟨360727348512769644444203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 961939596034052385184541 360727348512769644444203)
                      ·
                        rfl

theorem cell23_702514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_702514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702514 prefixEnd_702514 := by exact prefixLift 702514
  have htrace : WordTrace (prefixWord ++ tailWord_702514) baseStart_702514 baseEnd_702514 := by
    simpa [prefixWord, tailWord_702514, baseEnd_702514] using wordTrace_append hprefix tailTrace_702514
  have hstable : (prefixWord ++ tailWord_702514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702514).length < 2 ^ (prefixWord ++ tailWord_702514).sum := by decide
  have hdescent : baseEnd_702514 < baseStart_702514 := by decide
  rcases family_descends (prefixWord ++ tailWord_702514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702524 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_702524 : Nat := 118140960795 + 702524 * 2 ^ 59
def prefixEnd_702524 : Nat := 4983230072969 + 3 ^ 40 * 702524 * 2
def baseEnd_702524 : Nat := 360732483319314605319157

theorem tailTrace_702524 : CollatzResearch.WordTrace tailWord_702524 prefixEnd_702524 360732483319314605319157 := by
  unfold tailWord_702524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12811577653441502196045313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17082103537922002928060417 12811577653441502196045313)
  ·
    refine ⟨9608683240081126647033985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12811577653441502196045313 9608683240081126647033985)
    ·
      refine ⟨7206512430060844985275489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9608683240081126647033985 7206512430060844985275489)
      ·
        refine ⟨5404884322545633738956617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7206512430060844985275489 5404884322545633738956617)
        ·
          refine ⟨4053663241909225304217463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404884322545633738956617 4053663241909225304217463)
          ·
            refine ⟨6080494862863837956326195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053663241909225304217463 6080494862863837956326195)
            ·
              refine ⟨9120742294295756934489293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080494862863837956326195 9120742294295756934489293)
              ·
                refine ⟨3420278360360908850433485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9120742294295756934489293 3420278360360908850433485)
                ·
                  refine ⟨1282604385135340818912557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3420278360360908850433485 1282604385135340818912557)
                  ·
                    refine ⟨480976644425752807092209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282604385135340818912557 480976644425752807092209)
                    ·
                      refine ⟨360732483319314605319157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 480976644425752807092209 360732483319314605319157)
                      ·
                        rfl

theorem cell23_702524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_702524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702524 prefixEnd_702524 := by exact prefixLift 702524
  have htrace : WordTrace (prefixWord ++ tailWord_702524) baseStart_702524 baseEnd_702524 := by
    simpa [prefixWord, tailWord_702524, baseEnd_702524] using wordTrace_append hprefix tailTrace_702524
  have hstable : (prefixWord ++ tailWord_702524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702524).length < 2 ^ (prefixWord ++ tailWord_702524).sum := by decide
  have hdescent : baseEnd_702524 < baseStart_702524 := by decide
  rcases family_descends (prefixWord ++ tailWord_702524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702567 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_702567 : Nat := 118140960795 + 702567 * 2 ^ 59
def prefixEnd_702567 : Nat := 4983230072969 + 3 ^ 40 * 702567 * 2
def baseEnd_702567 : Nat := 360754562987457937081459

theorem tailTrace_702567 : CollatzResearch.WordTrace tailWord_702567 prefixEnd_702567 360754562987457937081459 := by
  unfold tailWord_702567
  simp only [CollatzResearch.WordTrace]
  refine ⟨25624723645727222735905955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17083149097151481823937303 25624723645727222735905955)
  ·
    refine ⟨38437085468590834103858933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25624723645727222735905955 38437085468590834103858933)
    ·
      refine ⟨3603476762680390697236775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38437085468590834103858933 3603476762680390697236775)
      ·
        refine ⟨5405215144020586045855163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603476762680390697236775 5405215144020586045855163)
        ·
          refine ⟨8107822716030879068782745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405215144020586045855163 8107822716030879068782745)
          ·
            refine ⟨6080867037023159301587059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8107822716030879068782745 6080867037023159301587059)
            ·
              refine ⟨9121300555534738952380589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080867037023159301587059 9121300555534738952380589)
              ·
                refine ⟨3420487708325527107142721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9121300555534738952380589 3420487708325527107142721)
                ·
                  refine ⟨2565365781244145330357041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3420487708325527107142721 2565365781244145330357041)
                  ·
                    refine ⟨1924024335933108997767781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2565365781244145330357041 1924024335933108997767781)
                    ·
                      refine ⟨360754562987457937081459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1924024335933108997767781 360754562987457937081459)
                      ·
                        rfl

theorem cell23_702567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_702567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702567 prefixEnd_702567 := by exact prefixLift 702567
  have htrace : WordTrace (prefixWord ++ tailWord_702567) baseStart_702567 baseEnd_702567 := by
    simpa [prefixWord, tailWord_702567, baseEnd_702567] using wordTrace_append hprefix tailTrace_702567
  have hstable : (prefixWord ++ tailWord_702567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702567).length < 2 ^ (prefixWord ++ tailWord_702567).sum := by decide
  have hdescent : baseEnd_702567 < baseStart_702567 := by decide
  rcases family_descends (prefixWord ++ tailWord_702567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702641 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 2, 5]
def baseStart_702641 : Nat := 118140960795 + 702641 * 2 ^ 59
def prefixEnd_702641 : Nat := 4983230072969 + 3 ^ 40 * 702641 * 2
def baseEnd_702641 : Nat := 120264186851963549185373

theorem tailTrace_702641 : CollatzResearch.WordTrace tailWord_702641 prefixEnd_702641 120264186851963549185373 := by
  unfold tailWord_702641
  simp only [CollatzResearch.WordTrace]
  refine ⟨25627422647459133374099777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17084948431639422249399851 25627422647459133374099777)
  ·
    refine ⟨19220566985594350030574833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25627422647459133374099777 19220566985594350030574833)
    ·
      refine ⟨14415425239195762522931125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19220566985594350030574833 14415425239195762522931125)
      ·
        refine ⟨1351446116174602736524793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14415425239195762522931125 1351446116174602736524793)
        ·
          refine ⟨1013584587130952052393595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1351446116174602736524793 1013584587130952052393595)
          ·
            refine ⟨1520376880696428078590393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013584587130952052393595 1520376880696428078590393)
            ·
              refine ⟨1140282660522321058942795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520376880696428078590393 1140282660522321058942795)
              ·
                refine ⟨1710423990783481588414193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140282660522321058942795 1710423990783481588414193)
                ·
                  refine ⟨1282817993087611191310645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710423990783481588414193 1282817993087611191310645)
                  ·
                    refine ⟨120264186851963549185373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1282817993087611191310645 120264186851963549185373)
                    ·
                      rfl

theorem cell23_702641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_702641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702641 prefixEnd_702641 := by exact prefixLift 702641
  have htrace : WordTrace (prefixWord ++ tailWord_702641) baseStart_702641 baseEnd_702641 := by
    simpa [prefixWord, tailWord_702641, baseEnd_702641] using wordTrace_append hprefix tailTrace_702641
  have hstable : (prefixWord ++ tailWord_702641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702641).length < 2 ^ (prefixWord ++ tailWord_702641).sum := by decide
  have hdescent : baseEnd_702641 < baseStart_702641 := by decide
  rcases family_descends (prefixWord ++ tailWord_702641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702658 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_702658 : Nat := 118140960795 + 702658 * 2 ^ 59
def prefixEnd_702658 : Nat := 4983230072969 + 3 ^ 40 * 702658 * 2
def baseEnd_702658 : Nat := 120267096575672360347847

theorem tailTrace_702658 : CollatzResearch.WordTrace tailWord_702658 prefixEnd_702658 120267096575672360347847 := by
  unfold tailWord_702658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6407010672099386319367157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17085361792265030184979085 6407010672099386319367157)
  ·
    refine ⟨600657250509317467440671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6407010672099386319367157 600657250509317467440671)
    ·
      refine ⟨900985875763976201161007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600657250509317467440671 900985875763976201161007)
      ·
        refine ⟨1351478813645964301741511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900985875763976201161007 1351478813645964301741511)
        ·
          refine ⟨2027218220468946452612267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351478813645964301741511 2027218220468946452612267)
          ·
            refine ⟨3040827330703419678918401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027218220468946452612267 3040827330703419678918401)
            ·
              refine ⟨2280620498027564759188801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040827330703419678918401 2280620498027564759188801)
              ·
                refine ⟨1710465373520673569391601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280620498027564759188801 1710465373520673569391601)
                ·
                  refine ⟨1282849030140505177043701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710465373520673569391601 1282849030140505177043701)
                  ·
                    refine ⟨120267096575672360347847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1282849030140505177043701 120267096575672360347847)
                    ·
                      rfl

theorem cell23_702658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_702658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702658 prefixEnd_702658 := by exact prefixLift 702658
  have htrace : WordTrace (prefixWord ++ tailWord_702658) baseStart_702658 baseEnd_702658 := by
    simpa [prefixWord, tailWord_702658, baseEnd_702658] using wordTrace_append hprefix tailTrace_702658
  have hstable : (prefixWord ++ tailWord_702658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702658).length < 2 ^ (prefixWord ++ tailWord_702658).sum := by decide
  have hdescent : baseEnd_702658 < baseStart_702658 := by decide
  rcases family_descends (prefixWord ++ tailWord_702658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702671 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 1, 4]
def baseStart_702671 : Nat := 118140960795 + 702671 * 2 ^ 59
def prefixEnd_702671 : Nat := 4983230072969 + 3 ^ 40 * 702671 * 2
def baseEnd_702671 : Nat := 120269321658508510060327

theorem tailTrace_702671 : CollatzResearch.WordTrace tailWord_702671 prefixEnd_702671 120269321658508510060327 := by
  unfold tailWord_702671
  simp only [CollatzResearch.WordTrace]
  refine ⟨25628516837350448497691867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17085677891566965665127911 25628516837350448497691867)
  ·
    refine ⟨38442775256025672746537801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25628516837350448497691867 38442775256025672746537801)
    ·
      refine ⟨28832081442019254559903351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38442775256025672746537801 28832081442019254559903351)
      ·
        refine ⟨43248122163028881839855027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28832081442019254559903351 43248122163028881839855027)
        ·
          refine ⟨64872183244543322759782541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43248122163028881839855027 64872183244543322759782541)
          ·
            refine ⟨24327068716703746034918453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64872183244543322759782541 24327068716703746034918453)
            ·
              refine ⟨2280662692190976190773605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24327068716703746034918453 2280662692190976190773605)
              ·
                refine ⟨427624254785808035770051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2280662692190976190773605 427624254785808035770051)
                ·
                  refine ⟨641436382178712053655077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427624254785808035770051 641436382178712053655077)
                  ·
                    refine ⟨120269321658508510060327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 641436382178712053655077 120269321658508510060327)
                    ·
                      rfl

theorem cell23_702671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 4].length) (baseStart_702671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702671 prefixEnd_702671 := by exact prefixLift 702671
  have htrace : WordTrace (prefixWord ++ tailWord_702671) baseStart_702671 baseEnd_702671 := by
    simpa [prefixWord, tailWord_702671, baseEnd_702671] using wordTrace_append hprefix tailTrace_702671
  have hstable : (prefixWord ++ tailWord_702671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702671).length < 2 ^ (prefixWord ++ tailWord_702671).sum := by decide
  have hdescent : baseEnd_702671 < baseStart_702671 := by decide
  rcases family_descends (prefixWord ++ tailWord_702671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702678 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_702678 : Nat := 118140960795 + 702678 * 2 ^ 59
def prefixEnd_702678 : Nat := 4983230072969 + 3 ^ 40 * 702678 * 2
def baseEnd_702678 : Nat := 360811559340107002793449

theorem tailTrace_702678 : CollatzResearch.WordTrace tailWord_702678 prefixEnd_702678 360811559340107002793449 := by
  unfold tailWord_702678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601798259270318043324793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17085848098883392462131125 1601798259270318043324793)
  ·
    refine ⟨1201348694452738532493595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1601798259270318043324793 1201348694452738532493595)
    ·
      refine ⟨1802023041679107798740393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201348694452738532493595 1802023041679107798740393)
      ·
        refine ⟨1351517281259330849055295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1802023041679107798740393 1351517281259330849055295)
        ·
          refine ⟨2027275921888996273582943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351517281259330849055295 2027275921888996273582943)
          ·
            refine ⟨3040913882833494410374415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027275921888996273582943 3040913882833494410374415)
            ·
              refine ⟨4561370824250241615561623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040913882833494410374415 4561370824250241615561623)
              ·
                refine ⟨6842056236375362423342435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561370824250241615561623 6842056236375362423342435)
                ·
                  refine ⟨10263084354563043635013653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6842056236375362423342435 10263084354563043635013653)
                  ·
                    refine ⟨481082079120142670391265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10263084354563043635013653 481082079120142670391265)
                    ·
                      refine ⟨360811559340107002793449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481082079120142670391265 360811559340107002793449)
                      ·
                        rfl

theorem cell23_702678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_702678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702678 prefixEnd_702678 := by exact prefixLift 702678
  have htrace : WordTrace (prefixWord ++ tailWord_702678) baseStart_702678 baseEnd_702678 := by
    simpa [prefixWord, tailWord_702678, baseEnd_702678] using wordTrace_append hprefix tailTrace_702678
  have hstable : (prefixWord ++ tailWord_702678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702678).length < 2 ^ (prefixWord ++ tailWord_702678).sum := by decide
  have hdescent : baseEnd_702678 < baseStart_702678 := by decide
  rcases family_descends (prefixWord ++ tailWord_702678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702721 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_702721 : Nat := 118140960795 + 702721 * 2 ^ 59
def prefixEnd_702721 : Nat := 4983230072969 + 3 ^ 40 * 702721 * 2
def baseEnd_702721 : Nat := 360833639008250334555751

theorem tailTrace_702721 : CollatzResearch.WordTrace tailWord_702721 prefixEnd_702721 360833639008250334555751 := by
  unfold tailWord_702721
  simp only [CollatzResearch.WordTrace]
  refine ⟨25630340487169307037012017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17086893658112871358008011 25630340487169307037012017)
  ·
    refine ⟨19222755365376980277759013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25630340487169307037012017 19222755365376980277759013)
    ·
      refine ⟨3604266631008183802079815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19222755365376980277759013 3604266631008183802079815)
      ·
        refine ⟨5406399946512275703119723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604266631008183802079815 5406399946512275703119723)
        ·
          refine ⟨8109599919768413554679585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5406399946512275703119723 8109599919768413554679585)
          ·
            refine ⟨6082199939826310166009689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8109599919768413554679585 6082199939826310166009689)
            ·
              refine ⟨4561649954869732624507267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082199939826310166009689 4561649954869732624507267)
              ·
                refine ⟨6842474932304598936760901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561649954869732624507267 6842474932304598936760901)
                ·
                  refine ⟨1282964049807112300642669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6842474932304598936760901 1282964049807112300642669)
                  ·
                    refine ⟨481111518677667112741001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1282964049807112300642669 481111518677667112741001)
                    ·
                      refine ⟨360833639008250334555751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481111518677667112741001 360833639008250334555751)
                      ·
                        rfl

theorem cell23_702721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_702721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702721 prefixEnd_702721 := by exact prefixLift 702721
  have htrace : WordTrace (prefixWord ++ tailWord_702721) baseStart_702721 baseEnd_702721 := by
    simpa [prefixWord, tailWord_702721, baseEnd_702721] using wordTrace_append hprefix tailTrace_702721
  have hstable : (prefixWord ++ tailWord_702721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702721).length < 2 ^ (prefixWord ++ tailWord_702721).sum := by decide
  have hdescent : baseEnd_702721 < baseStart_702721 := by decide
  rcases family_descends (prefixWord ++ tailWord_702721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702728 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_702728 : Nat := 118140960795 + 702728 * 2 ^ 59
def prefixEnd_702728 : Nat := 4983230072969 + 3 ^ 40 * 702728 * 2
def baseEnd_702728 : Nat := 360837233372831807168219

theorem tailTrace_702728 : CollatzResearch.WordTrace tailWord_702728 prefixEnd_702728 360837233372831807168219 := by
  unfold tailWord_702728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12815297899071973616258419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17087063865429298155011225 12815297899071973616258419)
  ·
    refine ⟨19222946848607960424387629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12815297899071973616258419 19222946848607960424387629)
    ·
      refine ⟨7208605068227985159145361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19222946848607960424387629 7208605068227985159145361)
      ·
        refine ⟨5406453801170988869359021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7208605068227985159145361 5406453801170988869359021)
        ·
          refine ⟨2027420175439120826009633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5406453801170988869359021 2027420175439120826009633)
          ·
            refine ⟨1520565131579340619507225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027420175439120826009633 1520565131579340619507225)
            ·
              refine ⟨1140423848684505464630419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520565131579340619507225 1140423848684505464630419)
              ·
                refine ⟨1710635773026758196945629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140423848684505464630419 1710635773026758196945629)
                ·
                  refine ⟨641488414885034323854611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1710635773026758196945629 641488414885034323854611)
                  ·
                    refine ⟨962232622327551485781917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 641488414885034323854611 962232622327551485781917)
                    ·
                      refine ⟨360837233372831807168219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962232622327551485781917 360837233372831807168219)
                      ·
                        rfl

theorem cell23_702728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_702728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702728 prefixEnd_702728 := by exact prefixLift 702728
  have htrace : WordTrace (prefixWord ++ tailWord_702728) baseStart_702728 baseEnd_702728 := by
    simpa [prefixWord, tailWord_702728, baseEnd_702728] using wordTrace_append hprefix tailTrace_702728
  have hstable : (prefixWord ++ tailWord_702728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702728).length < 2 ^ (prefixWord ++ tailWord_702728).sum := by decide
  have hdescent : baseEnd_702728 < baseStart_702728 := by decide
  rcases family_descends (prefixWord ++ tailWord_702728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702751 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 4]
def baseStart_702751 : Nat := 118140960795 + 702751 * 2 ^ 59
def prefixEnd_702751 : Nat := 4983230072969 + 3 ^ 40 * 702751 * 2
def baseEnd_702751 : Nat := 360849043427885217180613

theorem tailTrace_702751 : CollatzResearch.WordTrace tailWord_702751 prefixEnd_702751 360849043427885217180613 := by
  unfold tailWord_702751
  simp only [CollatzResearch.WordTrace]
  refine ⟨25631434677060622160604107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17087623118040414773736071 25631434677060622160604107)
  ·
    refine ⟨38447152015590933240906161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25631434677060622160604107 38447152015590933240906161)
    ·
      refine ⟨28835364011693199930679621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38447152015590933240906161 28835364011693199930679621)
      ·
        refine ⟨5406630752192474987002429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28835364011693199930679621 5406630752192474987002429)
        ·
          refine ⟨2027486532072178120125911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5406630752192474987002429 2027486532072178120125911)
          ·
            refine ⟨3041229798108267180188867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027486532072178120125911 3041229798108267180188867)
            ·
              refine ⟨4561844697162400770283301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041229798108267180188867 4561844697162400770283301)
              ·
                refine ⟨855345880717950144428119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4561844697162400770283301 855345880717950144428119)
                ·
                  refine ⟨1283018821076925216642179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855345880717950144428119 1283018821076925216642179)
                  ·
                    refine ⟨1924528231615387824963269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1283018821076925216642179 1924528231615387824963269)
                    ·
                      refine ⟨360849043427885217180613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1924528231615387824963269 360849043427885217180613)
                      ·
                        rfl

theorem cell23_702751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_702751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702751 prefixEnd_702751 := by exact prefixLift 702751
  have htrace : WordTrace (prefixWord ++ tailWord_702751) baseStart_702751 baseEnd_702751 := by
    simpa [prefixWord, tailWord_702751, baseEnd_702751] using wordTrace_append hprefix tailTrace_702751
  have hstable : (prefixWord ++ tailWord_702751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702751).length < 2 ^ (prefixWord ++ tailWord_702751).sum := by decide
  have hdescent : baseEnd_702751 < baseStart_702751 := by decide
  rcases family_descends (prefixWord ++ tailWord_702751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702764 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_702764 : Nat := 118140960795 + 702764 * 2 ^ 59
def prefixEnd_702764 : Nat := 4983230072969 + 3 ^ 40 * 702764 * 2
def baseEnd_702764 : Nat := 360855718676393666318053

theorem tailTrace_702764 : CollatzResearch.WordTrace tailWord_702764 prefixEnd_702764 360855718676393666318053 := by
  unfold tailWord_702764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12815954413006762690413673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17087939217342350253884897 12815954413006762690413673)
  ·
    refine ⟨9611965809755072017810255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12815954413006762690413673 9611965809755072017810255)
    ·
      refine ⟨14417948714632608026715383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9611965809755072017810255 14417948714632608026715383)
      ·
        refine ⟨21626923071948912040073075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14417948714632608026715383 21626923071948912040073075)
        ·
          refine ⟨32440384607923368060109613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21626923071948912040073075 32440384607923368060109613)
          ·
            refine ⟨12165144227971263022541105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32440384607923368060109613 12165144227971263022541105)
            ·
              refine ⟨9123858170978447266905829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12165144227971263022541105 9123858170978447266905829)
              ·
                refine ⟨1710723407058458862544843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9123858170978447266905829 1710723407058458862544843)
                ·
                  refine ⟨2566085110587688293817265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710723407058458862544843 2566085110587688293817265)
                  ·
                    refine ⟨1924563832940766220362949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566085110587688293817265 1924563832940766220362949)
                    ·
                      refine ⟨360855718676393666318053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1924563832940766220362949 360855718676393666318053)
                      ·
                        rfl

theorem cell23_702764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_702764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702764 prefixEnd_702764 := by exact prefixLift 702764
  have htrace : WordTrace (prefixWord ++ tailWord_702764) baseStart_702764 baseEnd_702764 := by
    simpa [prefixWord, tailWord_702764, baseEnd_702764] using wordTrace_append hprefix tailTrace_702764
  have hstable : (prefixWord ++ tailWord_702764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702764).length < 2 ^ (prefixWord ++ tailWord_702764).sum := by decide
  have hdescent : baseEnd_702764 < baseStart_702764 := by decide
  rcases family_descends (prefixWord ++ tailWord_702764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702771 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 3]
def baseStart_702771 : Nat := 118140960795 + 702771 * 2 ^ 59
def prefixEnd_702771 : Nat := 4983230072969 + 3 ^ 40 * 702771 * 2
def baseEnd_702771 : Nat := 360859313040975138930521

theorem tailTrace_702771 : CollatzResearch.WordTrace tailWord_702771 prefixEnd_702771 360859313040975138930521 := by
  unfold tailWord_702771
  simp only [CollatzResearch.WordTrace]
  refine ⟨25632164136988165576332167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17088109424658777050888111 25632164136988165576332167)
  ·
    refine ⟨38448246205482248364498251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25632164136988165576332167 38448246205482248364498251)
    ·
      refine ⟨57672369308223372546747377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38448246205482248364498251 57672369308223372546747377)
      ·
        refine ⟨43254276981167529410060533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57672369308223372546747377 43254276981167529410060533)
        ·
          refine ⟨4055088466984455882193175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43254276981167529410060533 4055088466984455882193175)
          ·
            refine ⟨6082632700476683823289763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055088466984455882193175 6082632700476683823289763)
            ·
              refine ⟨9123949050715025734934645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082632700476683823289763 9123949050715025734934645)
              ·
                refine ⟨855370223504533662650123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9123949050715025734934645 855370223504533662650123)
                ·
                  refine ⟨1283055335256800493975185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855370223504533662650123 1283055335256800493975185)
                  ·
                    refine ⟨962291501442600370481389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283055335256800493975185 962291501442600370481389)
                    ·
                      refine ⟨360859313040975138930521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962291501442600370481389 360859313040975138930521)
                      ·
                        rfl

theorem cell23_702771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_702771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702771 prefixEnd_702771 := by exact prefixLift 702771
  have htrace : WordTrace (prefixWord ++ tailWord_702771) baseStart_702771 baseEnd_702771 := by
    simpa [prefixWord, tailWord_702771, baseEnd_702771] using wordTrace_append hprefix tailTrace_702771
  have hstable : (prefixWord ++ tailWord_702771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702771).length < 2 ^ (prefixWord ++ tailWord_702771).sum := by decide
  have hdescent : baseEnd_702771 < baseStart_702771 := by decide
  rcases family_descends (prefixWord ++ tailWord_702771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702784 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_702784 : Nat := 118140960795 + 702784 * 2 ^ 59
def prefixEnd_702784 : Nat := 4983230072969 + 3 ^ 40 * 702784 * 2
def baseEnd_702784 : Nat := 360865988289483588067961

theorem tailTrace_702784 : CollatzResearch.WordTrace tailWord_702784 prefixEnd_702784 360865988289483588067961 := by
  unfold tailWord_702784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12816319142970534398277703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17088425523960712531036937 12816319142970534398277703)
  ·
    refine ⟨19224478714455801597416555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12816319142970534398277703 19224478714455801597416555)
    ·
      refine ⟨28836718071683702396124833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19224478714455801597416555 28836718071683702396124833)
      ·
        refine ⟨21627538553762776797093625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28836718071683702396124833 21627538553762776797093625)
        ·
          refine ⟨16220653915322082597820219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21627538553762776797093625 16220653915322082597820219)
          ·
            refine ⟨24330980872983123896730329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16220653915322082597820219 24330980872983123896730329)
            ·
              refine ⟨18248235654737342922547747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24330980872983123896730329 18248235654737342922547747)
              ·
                refine ⟨27372353482106014383821621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18248235654737342922547747 27372353482106014383821621)
                ·
                  refine ⟨2566158138947438848483277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27372353482106014383821621 2566158138947438848483277)
                  ·
                    refine ⟨962309302105289568181229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566158138947438848483277 962309302105289568181229)
                    ·
                      refine ⟨360865988289483588067961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962309302105289568181229 360865988289483588067961)
                      ·
                        rfl

theorem cell23_702784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_702784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702784 prefixEnd_702784 := by exact prefixLift 702784
  have htrace : WordTrace (prefixWord ++ tailWord_702784) baseStart_702784 baseEnd_702784 := by
    simpa [prefixWord, tailWord_702784, baseEnd_702784] using wordTrace_append hprefix tailTrace_702784
  have hstable : (prefixWord ++ tailWord_702784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702784).length < 2 ^ (prefixWord ++ tailWord_702784).sum := by decide
  have hdescent : baseEnd_702784 < baseStart_702784 := by decide
  rcases family_descends (prefixWord ++ tailWord_702784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702805 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_702805 : Nat := 118140960795 + 702805 * 2 ^ 59
def prefixEnd_702805 : Nat := 4983230072969 + 3 ^ 40 * 702805 * 2
def baseEnd_702805 : Nat := 360876771383228005905365

theorem tailTrace_702805 : CollatzResearch.WordTrace tailWord_702805 prefixEnd_702805 360876771383228005905365 := by
  unfold tailWord_702805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633404218864989383069869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17088936145909992922046579 25633404218864989383069869)
  ·
    refine ⟨9612526582074371018651201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25633404218864989383069869 9612526582074371018651201)
    ·
      refine ⟨7209394936555778263988401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9612526582074371018651201 7209394936555778263988401)
      ·
        refine ⟨5407046202416833697991301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7209394936555778263988401 5407046202416833697991301)
        ·
          refine ⟨1013821162953156318373369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5407046202416833697991301 1013821162953156318373369)
          ·
            refine ⟨760365872214867238780027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013821162953156318373369 760365872214867238780027)
            ·
              refine ⟨1140548808322300858170041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760365872214867238780027 1140548808322300858170041)
              ·
                refine ⟨855411606241725643627531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140548808322300858170041 855411606241725643627531)
                ·
                  refine ⟨1283117409362588465441297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855411606241725643627531 1283117409362588465441297)
                  ·
                    refine ⟨962338057021941349080973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283117409362588465441297 962338057021941349080973)
                    ·
                      refine ⟨360876771383228005905365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962338057021941349080973 360876771383228005905365)
                      ·
                        rfl

theorem cell23_702805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_702805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702805 prefixEnd_702805 := by exact prefixLift 702805
  have htrace : WordTrace (prefixWord ++ tailWord_702805) baseStart_702805 baseEnd_702805 := by
    simpa [prefixWord, tailWord_702805, baseEnd_702805] using wordTrace_append hprefix tailTrace_702805
  have hstable : (prefixWord ++ tailWord_702805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702805).length < 2 ^ (prefixWord ++ tailWord_702805).sum := by decide
  have hdescent : baseEnd_702805 < baseStart_702805 := by decide
  rcases family_descends (prefixWord ++ tailWord_702805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702818 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_702818 : Nat := 118140960795 + 702818 * 2 ^ 59
def prefixEnd_702818 : Nat := 4983230072969 + 3 ^ 40 * 702818 * 2
def baseEnd_702818 : Nat := 360883446631736455042805

theorem tailTrace_702818 : CollatzResearch.WordTrace tailWord_702818 prefixEnd_702818 360883446631736455042805 := by
  unfold tailWord_702818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6408469591954473150823277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17089252245211928402195405 6408469591954473150823277)
  ·
    refine ⟨2403176096982927431558729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6408469591954473150823277 2403176096982927431558729)
    ·
      refine ⟨1802382072737195573669047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2403176096982927431558729 1802382072737195573669047)
      ·
        refine ⟨2703573109105793360503571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802382072737195573669047 2703573109105793360503571)
        ·
          refine ⟨4055359663658690040755357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703573109105793360503571 4055359663658690040755357)
          ·
            refine ⟨1520759873872008765283259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4055359663658690040755357 1520759873872008765283259)
            ·
              refine ⟨2281139810808013147924889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520759873872008765283259 2281139810808013147924889)
              ·
                refine ⟨1710854858106009860943667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281139810808013147924889 1710854858106009860943667)
                ·
                  refine ⟨2566282287159014791415501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710854858106009860943667 2566282287159014791415501)
                  ·
                    refine ⟨962355857684630546780813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566282287159014791415501 962355857684630546780813)
                    ·
                      refine ⟨360883446631736455042805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962355857684630546780813 360883446631736455042805)
                      ·
                        rfl

theorem cell23_702818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_702818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702818 prefixEnd_702818 := by exact prefixLift 702818
  have htrace : WordTrace (prefixWord ++ tailWord_702818) baseStart_702818 baseEnd_702818 := by
    simpa [prefixWord, tailWord_702818, baseEnd_702818] using wordTrace_append hprefix tailTrace_702818
  have hstable : (prefixWord ++ tailWord_702818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702818).length < 2 ^ (prefixWord ++ tailWord_702818).sum := by decide
  have hdescent : baseEnd_702818 < baseStart_702818 := by decide
  rcases family_descends (prefixWord ++ tailWord_702818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702841 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 5, 4, 2]
def baseStart_702841 : Nat := 118140960795 + 702841 * 2 ^ 59
def prefixEnd_702841 : Nat := 4983230072969 + 3 ^ 40 * 702841 * 2
def baseEnd_702841 : Nat := 360895256686789865055199

theorem tailTrace_702841 : CollatzResearch.WordTrace tailWord_702841 prefixEnd_702841 360895256686789865055199 := by
  unfold tailWord_702841
  simp only [CollatzResearch.WordTrace]
  refine ⟨25634717246734567531380377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17089811497823045020920251 25634717246734567531380377)
  ·
    refine ⟨19226037935050925648535283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25634717246734567531380377 19226037935050925648535283)
    ·
      refine ⟨28839056902576388472802925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19226037935050925648535283 28839056902576388472802925)
      ·
        refine ⟨10814646338466145677301097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28839056902576388472802925 10814646338466145677301097)
        ·
          refine ⟨8110984753849609257975823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10814646338466145677301097 8110984753849609257975823)
          ·
            refine ⟨12166477130774413886963735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110984753849609257975823 12166477130774413886963735)
            ·
              refine ⟨18249715696161620830445603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12166477130774413886963735 18249715696161620830445603)
              ·
                refine ⟨27374573544242431245668405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18249715696161620830445603 27374573544242431245668405)
                ·
                  refine ⟨2566366269772727929281413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27374573544242431245668405 2566366269772727929281413)
                  ·
                    refine ⟨481193675582386486740265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566366269772727929281413 481193675582386486740265)
                    ·
                      refine ⟨360895256686789865055199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481193675582386486740265 360895256686789865055199)
                      ·
                        rfl

theorem cell23_702841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_702841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702841 prefixEnd_702841 := by exact prefixLift 702841
  have htrace : WordTrace (prefixWord ++ tailWord_702841) baseStart_702841 baseEnd_702841 := by
    simpa [prefixWord, tailWord_702841, baseEnd_702841] using wordTrace_append hprefix tailTrace_702841
  have hstable : (prefixWord ++ tailWord_702841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702841).length < 2 ^ (prefixWord ++ tailWord_702841).sum := by decide
  have hdescent : baseEnd_702841 < baseStart_702841 := by decide
  rcases family_descends (prefixWord ++ tailWord_702841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702844 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_702844 : Nat := 118140960795 + 702844 * 2 ^ 59
def prefixEnd_702844 : Nat := 4983230072969 + 3 ^ 40 * 702844 * 2
def baseEnd_702844 : Nat := 360896797128753353317685

theorem tailTrace_702844 : CollatzResearch.WordTrace tailWord_702844 prefixEnd_702844 360896797128753353317685 := by
  unfold tailWord_702844
  simp only [CollatzResearch.WordTrace]
  refine ⟨12817413332861849521869793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17089884443815799362493057 12817413332861849521869793)
  ·
    refine ⟨9613059999646387141402345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12817413332861849521869793 9613059999646387141402345)
    ·
      refine ⟨7209794999734790356051759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9613059999646387141402345 7209794999734790356051759)
      ·
        refine ⟨10814692499602185534077639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7209794999734790356051759 10814692499602185534077639)
        ·
          refine ⟨16222038749403278301116459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10814692499602185534077639 16222038749403278301116459)
          ·
            refine ⟨24333058124104917451674689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16222038749403278301116459 24333058124104917451674689)
            ·
              refine ⟨18249793593078688088756017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24333058124104917451674689 18249793593078688088756017)
              ·
                refine ⟨13687345194809016066567013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18249793593078688088756017 13687345194809016066567013)
                ·
                  refine ⟨2566377224026690512481315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13687345194809016066567013 2566377224026690512481315)
                  ·
                    refine ⟨3849565836040035768721973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2566377224026690512481315 3849565836040035768721973)
                    ·
                      refine ⟨360896797128753353317685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3849565836040035768721973 360896797128753353317685)
                      ·
                        rfl

theorem cell23_702844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_702844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702844 prefixEnd_702844 := by exact prefixLift 702844
  have htrace : WordTrace (prefixWord ++ tailWord_702844) baseStart_702844 baseEnd_702844 := by
    simpa [prefixWord, tailWord_702844, baseEnd_702844] using wordTrace_append hprefix tailTrace_702844
  have hstable : (prefixWord ++ tailWord_702844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702844).length < 2 ^ (prefixWord ++ tailWord_702844).sum := by decide
  have hdescent : baseEnd_702844 < baseStart_702844 := by decide
  rcases family_descends (prefixWord ++ tailWord_702844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702851 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 2, 6]
def baseStart_702851 : Nat := 118140960795 + 702851 * 2 ^ 59
def prefixEnd_702851 : Nat := 4983230072969 + 3 ^ 40 * 702851 * 2
def baseEnd_702851 : Nat := 120300130497778275310051

theorem tailTrace_702851 : CollatzResearch.WordTrace tailWord_702851 prefixEnd_702851 120300130497778275310051 := by
  unfold tailWord_702851
  simp only [CollatzResearch.WordTrace]
  refine ⟨25635081976698339239244407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17090054651132226159496271 25635081976698339239244407)
  ·
    refine ⟨38452622965047508858866611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25635081976698339239244407 38452622965047508858866611)
    ·
      refine ⟨57678934447571263288299917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38452622965047508858866611 57678934447571263288299917)
      ·
        refine ⟨21629600417839223733112469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57678934447571263288299917 21629600417839223733112469)
        ·
          refine ⟨1013887519586213612489647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21629600417839223733112469 1013887519586213612489647)
          ·
            refine ⟨1520831279379320418734471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013887519586213612489647 1520831279379320418734471)
            ·
              refine ⟨2281246919068980628101707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520831279379320418734471 2281246919068980628101707)
              ·
                refine ⟨3421870378603470942152561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281246919068980628101707 3421870378603470942152561)
                ·
                  refine ⟨2566402783952603206614421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3421870378603470942152561 2566402783952603206614421)
                  ·
                    refine ⟨120300130497778275310051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2566402783952603206614421 120300130497778275310051)
                    ·
                      rfl

theorem cell23_702851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 6].length) (baseStart_702851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702851 prefixEnd_702851 := by exact prefixLift 702851
  have htrace : WordTrace (prefixWord ++ tailWord_702851) baseStart_702851 baseEnd_702851 := by
    simpa [prefixWord, tailWord_702851, baseEnd_702851] using wordTrace_append hprefix tailTrace_702851
  have hstable : (prefixWord ++ tailWord_702851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702851).length < 2 ^ (prefixWord ++ tailWord_702851).sum := by decide
  have hdescent : baseEnd_702851 < baseStart_702851 := by decide
  rcases family_descends (prefixWord ++ tailWord_702851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702888 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_702888 : Nat := 118140960795 + 702888 * 2 ^ 59
def prefixEnd_702888 : Nat := 4983230072969 + 3 ^ 40 * 702888 * 2
def baseEnd_702888 : Nat := 360919390277551181167483

theorem tailTrace_702888 : CollatzResearch.WordTrace tailWord_702888 prefixEnd_702888 360919390277551181167483 := by
  unfold tailWord_702888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818215738782147279170659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17090954318376196372227545 12818215738782147279170659)
  ·
    refine ⟨19227323608173220918755989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12818215738782147279170659 19227323608173220918755989)
    ·
      refine ⟨901280794133119730566687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19227323608173220918755989 901280794133119730566687)
      ·
        refine ⟨1351921191199679595850031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901280794133119730566687 1351921191199679595850031)
        ·
          refine ⟨2027881786799519393775047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351921191199679595850031 2027881786799519393775047)
          ·
            refine ⟨3041822680199279090662571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027881786799519393775047 3041822680199279090662571)
            ·
              refine ⟨4562734020298918635993857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041822680199279090662571 4562734020298918635993857)
              ·
                refine ⟨3422050515224188976995393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562734020298918635993857 3422050515224188976995393)
                ·
                  refine ⟨2566537886418141732746545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422050515224188976995393 2566537886418141732746545)
                  ·
                    refine ⟨1924903414813606299559909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566537886418141732746545 1924903414813606299559909)
                    ·
                      refine ⟨360919390277551181167483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1924903414813606299559909 360919390277551181167483)
                      ·
                        rfl

theorem cell23_702888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_702888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702888 prefixEnd_702888 := by exact prefixLift 702888
  have htrace : WordTrace (prefixWord ++ tailWord_702888) baseStart_702888 baseEnd_702888 := by
    simpa [prefixWord, tailWord_702888, baseEnd_702888] using wordTrace_append hprefix tailTrace_702888
  have hstable : (prefixWord ++ tailWord_702888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702888).length < 2 ^ (prefixWord ++ tailWord_702888).sum := by decide
  have hdescent : baseEnd_702888 < baseStart_702888 := by decide
  rcases family_descends (prefixWord ++ tailWord_702888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702904 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_702904 : Nat := 118140960795 + 702904 * 2 ^ 59
def prefixEnd_702904 : Nat := 4983230072969 + 3 ^ 40 * 702904 * 2
def baseEnd_702904 : Nat := 360927605968023118567409

theorem tailTrace_702904 : CollatzResearch.WordTrace tailWord_702904 prefixEnd_702904 360927605968023118567409 := by
  unfold tailWord_702904
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818507522753164645461883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17091343363670886193949177 12818507522753164645461883)
  ·
    refine ⟨19227761284129746968192825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12818507522753164645461883 19227761284129746968192825)
    ·
      refine ⟨14420820963097310226144619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19227761284129746968192825 14420820963097310226144619)
      ·
        refine ⟨21631231444645965339216929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14420820963097310226144619 21631231444645965339216929)
        ·
          refine ⟨16223423583484474004412697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21631231444645965339216929 16223423583484474004412697)
          ·
            refine ⟨12167567687613355503309523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16223423583484474004412697 12167567687613355503309523)
            ·
              refine ⟨18251351531420033254964285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12167567687613355503309523 18251351531420033254964285)
              ·
                refine ⟨6844256824282512470611607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18251351531420033254964285 6844256824282512470611607)
                ·
                  refine ⟨10266385236423768705917411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844256824282512470611607 10266385236423768705917411)
                  ·
                    refine ⟨15399577854635653058876117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10266385236423768705917411 15399577854635653058876117)
                    ·
                      refine ⟨360927605968023118567409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15399577854635653058876117 360927605968023118567409)
                      ·
                        rfl

theorem cell23_702904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_702904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702904 prefixEnd_702904 := by exact prefixLift 702904
  have htrace : WordTrace (prefixWord ++ tailWord_702904) baseStart_702904 baseEnd_702904 := by
    simpa [prefixWord, tailWord_702904, baseEnd_702904] using wordTrace_append hprefix tailTrace_702904
  have hstable : (prefixWord ++ tailWord_702904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702904).length < 2 ^ (prefixWord ++ tailWord_702904).sum := by decide
  have hdescent : baseEnd_702904 < baseStart_702904 := by decide
  rcases family_descends (prefixWord ++ tailWord_702904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702908 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_702908 : Nat := 118140960795 + 702908 * 2 ^ 59
def prefixEnd_702908 : Nat := 4983230072969 + 3 ^ 40 * 702908 * 2
def baseEnd_702908 : Nat := 360929659890641102917391

theorem tailTrace_702908 : CollatzResearch.WordTrace tailWord_702908 prefixEnd_702908 360929659890641102917391 := by
  unfold tailWord_702908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818580468745918987034689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17091440624994558649379585 12818580468745918987034689)
  ·
    refine ⟨9613935351559439240276017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12818580468745918987034689 9613935351559439240276017)
    ·
      refine ⟨7210451513669579430207013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9613935351559439240276017 7210451513669579430207013)
      ·
        refine ⟨1351959658813046143163815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7210451513669579430207013 1351959658813046143163815)
        ·
          refine ⟨2027939488219569214745723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351959658813046143163815 2027939488219569214745723)
          ·
            refine ⟨3041909232329353822118585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027939488219569214745723 3041909232329353822118585)
            ·
              refine ⟨2281431924247015366588939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3041909232329353822118585 2281431924247015366588939)
              ·
                refine ⟨3422147886370523049883409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281431924247015366588939 3422147886370523049883409)
                ·
                  refine ⟨2566610914777892287412557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422147886370523049883409 2566610914777892287412557)
                  ·
                    refine ⟨962479093041709607779709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566610914777892287412557 962479093041709607779709)
                    ·
                      refine ⟨360929659890641102917391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962479093041709607779709 360929659890641102917391)
                      ·
                        rfl

theorem cell23_702908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_702908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702908 prefixEnd_702908 := by exact prefixLift 702908
  have htrace : WordTrace (prefixWord ++ tailWord_702908) baseStart_702908 baseEnd_702908 := by
    simpa [prefixWord, tailWord_702908, baseEnd_702908] using wordTrace_append hprefix tailTrace_702908
  have hstable : (prefixWord ++ tailWord_702908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702908).length < 2 ^ (prefixWord ++ tailWord_702908).sum := by decide
  have hdescent : baseEnd_702908 < baseStart_702908 := by decide
  rcases family_descends (prefixWord ++ tailWord_702908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702981 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_702981 : Nat := 118140960795 + 702981 * 2 ^ 59
def prefixEnd_702981 : Nat := 4983230072969 + 3 ^ 40 * 702981 * 2
def baseEnd_702981 : Nat := 360967143978419317304555

theorem tailTrace_702981 : CollatzResearch.WordTrace tailWord_702981 prefixEnd_702981 360967143978419317304555 := by
  unfold tailWord_702981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639823466227371441476797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17093215644151580960984531 25639823466227371441476797)
  ·
    refine ⟨9614933799835264290553799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25639823466227371441476797 9614933799835264290553799)
    ·
      refine ⟨14422400699752896435830699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9614933799835264290553799 14422400699752896435830699)
      ·
        refine ⟨21633601049629344653746049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14422400699752896435830699 21633601049629344653746049)
        ·
          refine ⟨16225200787222008490309537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21633601049629344653746049 16225200787222008490309537)
          ·
            refine ⟨12168900590416506367732153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16225200787222008490309537 12168900590416506367732153)
            ·
              refine ⟨9126675442812379775799115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12168900590416506367732153 9126675442812379775799115)
              ·
                refine ⟨13690013164218569663698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126675442812379775799115 13690013164218569663698673)
                ·
                  refine ⟨10267509873163927247774005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13690013164218569663698673 10267509873163927247774005)
                  ·
                    refine ⟨962579050609118179478813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10267509873163927247774005 962579050609118179478813)
                    ·
                      refine ⟨360967143978419317304555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962579050609118179478813 360967143978419317304555)
                      ·
                        rfl

theorem cell23_702981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_702981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_702981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_702981 prefixEnd_702981 := by exact prefixLift 702981
  have htrace : WordTrace (prefixWord ++ tailWord_702981) baseStart_702981 baseEnd_702981 := by
    simpa [prefixWord, tailWord_702981, baseEnd_702981] using wordTrace_append hprefix tailTrace_702981
  have hstable : (prefixWord ++ tailWord_702981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702981).length < 2 ^ (prefixWord ++ tailWord_702981).sum := by decide
  have hdescent : baseEnd_702981 < baseStart_702981 := by decide
  rcases family_descends (prefixWord ++ tailWord_702981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703018 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_703018 : Nat := 118140960795 + 703018 * 2 ^ 59
def prefixEnd_703018 : Nat := 4983230072969 + 3 ^ 40 * 703018 * 2
def baseEnd_703018 : Nat := 120328714254211890847295

theorem tailTrace_703018 : CollatzResearch.WordTrace tailWord_703018 prefixEnd_703018 120328714254211890847295 := by
  unfold tailWord_703018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410293241773331690143427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17094115311395551173715805 6410293241773331690143427)
  ·
    refine ⟨9615439862659997535215141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6410293241773331690143427 9615439862659997535215141)
    ·
      refine ⟨1802894974248749537852839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9615439862659997535215141 1802894974248749537852839)
      ·
        refine ⟨2704342461373124306779259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802894974248749537852839 2704342461373124306779259)
        ·
          refine ⟨4056513692059686460168889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704342461373124306779259 4056513692059686460168889)
          ·
            refine ⟨3042385269044764845126667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056513692059686460168889 3042385269044764845126667)
            ·
              refine ⟨4563577903567147267690001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042385269044764845126667 4563577903567147267690001)
              ·
                refine ⟨3422683427675360450767501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4563577903567147267690001 3422683427675360450767501)
                ·
                  refine ⟨1283506285378260169037813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3422683427675360450767501 1283506285378260169037813)
                  ·
                    refine ⟨120328714254211890847295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1283506285378260169037813 120328714254211890847295)
                    ·
                      rfl

theorem cell23_703018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_703018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703018 prefixEnd_703018 := by exact prefixLift 703018
  have htrace : WordTrace (prefixWord ++ tailWord_703018) baseStart_703018 baseEnd_703018 := by
    simpa [prefixWord, tailWord_703018, baseEnd_703018] using wordTrace_append hprefix tailTrace_703018
  have hstable : (prefixWord ++ tailWord_703018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703018).length < 2 ^ (prefixWord ++ tailWord_703018).sum := by decide
  have hdescent : baseEnd_703018 < baseStart_703018 := by decide
  rcases family_descends (prefixWord ++ tailWord_703018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703055 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 1, 1, 4]
def baseStart_703055 : Nat := 118140960795 + 703055 * 2 ^ 59
def prefixEnd_703055 : Nat := 4983230072969 + 3 ^ 40 * 703055 * 2
def baseEnd_703055 : Nat := 361005141546852027779215

theorem tailTrace_703055 : CollatzResearch.WordTrace tailWord_703055 prefixEnd_703055 361005141546852027779215 := by
  unfold tailWord_703055
  simp only [CollatzResearch.WordTrace]
  refine ⟨25642522467959282079670619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17095014978639521386447079 25642522467959282079670619)
  ·
    refine ⟨38463783701938923119505929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25642522467959282079670619 38463783701938923119505929)
    ·
      refine ⟨28847837776454192339629447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38463783701938923119505929 28847837776454192339629447)
      ·
        refine ⟨43271756664681288509444171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28847837776454192339629447 43271756664681288509444171)
        ·
          refine ⟨64907634997021932764166257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43271756664681288509444171 64907634997021932764166257)
          ·
            refine ⟨48680726247766449573124693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64907634997021932764166257 48680726247766449573124693)
            ·
              refine ⟨570477260716013080935055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 48680726247766449573124693 570477260716013080935055)
              ·
                refine ⟨855715891074019621402583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570477260716013080935055 855715891074019621402583)
                ·
                  refine ⟨1283573836611029432103875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855715891074019621402583 1283573836611029432103875)
                  ·
                    refine ⟨1925360754916544148155813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1283573836611029432103875 1925360754916544148155813)
                    ·
                      refine ⟨361005141546852027779215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1925360754916544148155813 361005141546852027779215)
                      ·
                        rfl

theorem cell23_703055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 1, 4].length) (baseStart_703055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703055 prefixEnd_703055 := by exact prefixLift 703055
  have htrace : WordTrace (prefixWord ++ tailWord_703055) baseStart_703055 baseEnd_703055 := by
    simpa [prefixWord, tailWord_703055, baseEnd_703055] using wordTrace_append hprefix tailTrace_703055
  have hstable : (prefixWord ++ tailWord_703055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703055).length < 2 ^ (prefixWord ++ tailWord_703055).sum := by decide
  have hdescent : baseEnd_703055 < baseStart_703055 := by decide
  rcases family_descends (prefixWord ++ tailWord_703055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703058 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_703058 : Nat := 118140960795 + 703058 * 2 ^ 59
def prefixEnd_703058 : Nat := 4983230072969 + 3 ^ 40 * 703058 * 2
def baseEnd_703058 : Nat := 361006681988815516041701

theorem tailTrace_703058 : CollatzResearch.WordTrace tailWord_703058 prefixEnd_703058 361006681988815516041701 := by
  unfold tailWord_703058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410657971737103398007457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17095087924632275728019885 6410657971737103398007457)
  ·
    refine ⟨4807993478802827548505593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6410657971737103398007457 4807993478802827548505593)
    ·
      refine ⟨3605995109102120661379195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4807993478802827548505593 3605995109102120661379195)
      ·
        refine ⟨5408992663653180992068793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605995109102120661379195 5408992663653180992068793)
        ·
          refine ⟨4056744497739885744051595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5408992663653180992068793 4056744497739885744051595)
          ·
            refine ⟨6085116746609828616077393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056744497739885744051595 6085116746609828616077393)
            ·
              refine ⟨4563837559957371462058045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6085116746609828616077393 4563837559957371462058045)
              ·
                refine ⟨1711439084984014298271767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4563837559957371462058045 1711439084984014298271767)
                ·
                  refine ⟨2567158627476021447407651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711439084984014298271767 2567158627476021447407651)
                  ·
                    refine ⟨3850737941214032171111477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2567158627476021447407651 3850737941214032171111477)
                    ·
                      refine ⟨361006681988815516041701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3850737941214032171111477 361006681988815516041701)
                      ·
                        rfl

theorem cell23_703058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_703058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703058 prefixEnd_703058 := by exact prefixLift 703058
  have htrace : WordTrace (prefixWord ++ tailWord_703058) baseStart_703058 baseEnd_703058 := by
    simpa [prefixWord, tailWord_703058, baseEnd_703058] using wordTrace_append hprefix tailTrace_703058
  have hstable : (prefixWord ++ tailWord_703058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703058).length < 2 ^ (prefixWord ++ tailWord_703058).sum := by decide
  have hdescent : baseEnd_703058 < baseStart_703058 := by decide
  rcases family_descends (prefixWord ++ tailWord_703058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703082 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_703082 : Nat := 118140960795 + 703082 * 2 ^ 59
def prefixEnd_703082 : Nat := 4983230072969 + 3 ^ 40 * 703082 * 2
def baseEnd_703082 : Nat := 120339668508174474047197

theorem tailTrace_703082 : CollatzResearch.WordTrace tailWord_703082 prefixEnd_703082 120339668508174474047197 := by
  unfold tailWord_703082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410876809715366422725875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17095671492574310460602333 6410876809715366422725875)
  ·
    refine ⟨9616315214573049634088813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6410876809715366422725875 9616315214573049634088813)
    ·
      refine ⟨3606118205464893612783305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9616315214573049634088813 3606118205464893612783305)
      ·
        refine ⟨2704588654098670209587479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3606118205464893612783305 2704588654098670209587479)
        ·
          refine ⟨4056882981148005314381219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704588654098670209587479 4056882981148005314381219)
          ·
            refine ⟨6085324471722007971571829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056882981148005314381219 6085324471722007971571829)
            ·
              refine ⟨570499169223938247334859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6085324471722007971571829 570499169223938247334859)
              ·
                refine ⟨855748753835907371002289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570499169223938247334859 855748753835907371002289)
                ·
                  refine ⟨641811565376930528251717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 855748753835907371002289 641811565376930528251717)
                  ·
                    refine ⟨120339668508174474047197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 641811565376930528251717 120339668508174474047197)
                    ·
                      rfl

theorem cell23_703082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_703082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703082 prefixEnd_703082 := by exact prefixLift 703082
  have htrace : WordTrace (prefixWord ++ tailWord_703082) baseStart_703082 baseEnd_703082 := by
    simpa [prefixWord, tailWord_703082, baseEnd_703082] using wordTrace_append hprefix tailTrace_703082
  have hstable : (prefixWord ++ tailWord_703082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703082).length < 2 ^ (prefixWord ++ tailWord_703082).sum := by decide
  have hdescent : baseEnd_703082 < baseStart_703082 := by decide
  rcases family_descends (prefixWord ++ tailWord_703082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703085 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_703085 : Nat := 118140960795 + 703085 * 2 ^ 59
def prefixEnd_703085 : Nat := 4983230072969 + 3 ^ 40 * 703085 * 2
def baseEnd_703085 : Nat := 361020545966486910404077

theorem tailTrace_703085 : CollatzResearch.WordTrace tailWord_703085 prefixEnd_703085 361020545966486910404077 := by
  unfold tailWord_703085
  simp only [CollatzResearch.WordTrace]
  refine ⟨25643616657850597203262709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17095744438567064802175139 25643616657850597203262709)
  ·
    refine ⟨2404089061673493487805879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25643616657850597203262709 2404089061673493487805879)
    ·
      refine ⟨3606133592510240231708819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404089061673493487805879 3606133592510240231708819)
      ·
        refine ⟨5409200388765360347563229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3606133592510240231708819 5409200388765360347563229)
        ·
          refine ⟨2028450145787010130336211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5409200388765360347563229 2028450145787010130336211)
          ·
            refine ⟨3042675218680515195504317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028450145787010130336211 3042675218680515195504317)
            ·
              refine ⟨1141003207005193198314119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3042675218680515195504317 1141003207005193198314119)
              ·
                refine ⟨1711504810507789797471179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141003207005193198314119 1711504810507789797471179)
                ·
                  refine ⟨2567257215761684696206769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711504810507789797471179 2567257215761684696206769)
                  ·
                    refine ⟨1925442911821263522155077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2567257215761684696206769 1925442911821263522155077)
                    ·
                      refine ⟨361020545966486910404077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1925442911821263522155077 361020545966486910404077)
                      ·
                        rfl

theorem cell23_703085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_703085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703085 prefixEnd_703085 := by exact prefixLift 703085
  have htrace : WordTrace (prefixWord ++ tailWord_703085) baseStart_703085 baseEnd_703085 := by
    simpa [prefixWord, tailWord_703085, baseEnd_703085] using wordTrace_append hprefix tailTrace_703085
  have hstable : (prefixWord ++ tailWord_703085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703085).length < 2 ^ (prefixWord ++ tailWord_703085).sum := by decide
  have hdescent : baseEnd_703085 < baseStart_703085 := by decide
  rcases family_descends (prefixWord ++ tailWord_703085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703105 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_703105 : Nat := 118140960795 + 703105 * 2 ^ 59
def prefixEnd_703105 : Nat := 4983230072969 + 3 ^ 40 * 703105 * 2
def baseEnd_703105 : Nat := 361030815579576832153985

theorem tailTrace_703105 : CollatzResearch.WordTrace tailWord_703105 prefixEnd_703105 361030815579576832153985 := by
  unfold tailWord_703105
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644346117778140618990769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17096230745185427079327179 25644346117778140618990769)
  ·
    refine ⟨19233259588333605464243077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25644346117778140618990769 19233259588333605464243077)
    ·
      refine ⟨3606236172812551024545577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19233259588333605464243077 3606236172812551024545577)
      ·
        refine ⟨2704677129609413268409183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3606236172812551024545577 2704677129609413268409183)
        ·
          refine ⟨4057015694414119902613775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704677129609413268409183 4057015694414119902613775)
          ·
            refine ⟨6085523541621179853920663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057015694414119902613775 6085523541621179853920663)
            ·
              refine ⟨9128285312431769780880995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085523541621179853920663 9128285312431769780880995)
              ·
                refine ⟨13692427968647654671321493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9128285312431769780880995 13692427968647654671321493)
                ·
                  refine ⟨641832561030358812718195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13692427968647654671321493 641832561030358812718195)
                  ·
                    refine ⟨962748841545538219077293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 641832561030358812718195 962748841545538219077293)
                    ·
                      refine ⟨361030815579576832153985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962748841545538219077293 361030815579576832153985)
                      ·
                        rfl

theorem cell23_703105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_703105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703105 prefixEnd_703105 := by exact prefixLift 703105
  have htrace : WordTrace (prefixWord ++ tailWord_703105) baseStart_703105 baseEnd_703105 := by
    simpa [prefixWord, tailWord_703105, baseEnd_703105] using wordTrace_append hprefix tailTrace_703105
  have hstable : (prefixWord ++ tailWord_703105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703105).length < 2 ^ (prefixWord ++ tailWord_703105).sum := by decide
  have hdescent : baseEnd_703105 < baseStart_703105 := by decide
  rcases family_descends (prefixWord ++ tailWord_703105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703118 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_703118 : Nat := 118140960795 + 703118 * 2 ^ 59
def prefixEnd_703118 : Nat := 4983230072969 + 3 ^ 40 * 703118 * 2
def baseEnd_703118 : Nat := 361037490828085281291425

theorem tailTrace_703118 : CollatzResearch.WordTrace tailWord_703118 prefixEnd_703118 361037490828085281291425 := by
  unfold tailWord_703118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3205602533341380479901751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17096546844487362559476005 3205602533341380479901751)
  ·
    refine ⟨4808403800012070719852627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3205602533341380479901751 4808403800012070719852627)
    ·
      refine ⟨7212605700018106079778941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808403800012070719852627 7212605700018106079778941)
      ·
        refine ⟨2704727137506789779917103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7212605700018106079778941 2704727137506789779917103)
        ·
          refine ⟨4057090706260184669875655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704727137506789779917103 4057090706260184669875655)
          ·
            refine ⟨6085636059390277004813483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057090706260184669875655 6085636059390277004813483)
            ·
              refine ⟨9128454089085415507220225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085636059390277004813483 9128454089085415507220225)
              ·
                refine ⟨6846340566814061630415169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9128454089085415507220225 6846340566814061630415169)
                ·
                  refine ⟨5134755425110546222811377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846340566814061630415169 5134755425110546222811377)
                  ·
                    refine ⟨3851066568832909667108533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5134755425110546222811377 3851066568832909667108533)
                    ·
                      refine ⟨361037490828085281291425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3851066568832909667108533 361037490828085281291425)
                      ·
                        rfl

theorem cell23_703118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_703118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703118 prefixEnd_703118 := by exact prefixLift 703118
  have htrace : WordTrace (prefixWord ++ tailWord_703118) baseStart_703118 baseEnd_703118 := by
    simpa [prefixWord, tailWord_703118, baseEnd_703118] using wordTrace_append hprefix tailTrace_703118
  have hstable : (prefixWord ++ tailWord_703118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703118).length < 2 ^ (prefixWord ++ tailWord_703118).sum := by decide
  have hdescent : baseEnd_703118 < baseStart_703118 := by decide
  rcases family_descends (prefixWord ++ tailWord_703118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703122 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_703122 : Nat := 118140960795 + 703122 * 2 ^ 59
def prefixEnd_703122 : Nat := 4983230072969 + 3 ^ 40 * 703122 * 2
def baseEnd_703122 : Nat := 361039544750703265641407

theorem tailTrace_703122 : CollatzResearch.WordTrace tailWord_703122 prefixEnd_703122 361039544750703265641407 := by
  unfold tailWord_703122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411241539679138130589905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17096644105811035014906413 6411241539679138130589905)
  ·
    refine ⟨4808431154759353597942429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6411241539679138130589905 4808431154759353597942429)
    ·
      refine ⟨1803161683034757599228411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4808431154759353597942429 1803161683034757599228411)
      ·
        refine ⟨2704742524552136398842617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803161683034757599228411 2704742524552136398842617)
        ·
          refine ⟨2028556893414102299131963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2704742524552136398842617 2028556893414102299131963)
          ·
            refine ⟨3042835340121153448697945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028556893414102299131963 3042835340121153448697945)
            ·
              refine ⟨2282126505090865086523459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042835340121153448697945 2282126505090865086523459)
              ·
                refine ⟨3423189757636297629785189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282126505090865086523459 3423189757636297629785189)
                ·
                  refine ⟨641848079556805805584723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3423189757636297629785189 641848079556805805584723)
                  ·
                    refine ⟨962772119335208708377085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 641848079556805805584723 962772119335208708377085)
                    ·
                      refine ⟨361039544750703265641407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962772119335208708377085 361039544750703265641407)
                      ·
                        rfl

theorem cell23_703122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_703122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703122 prefixEnd_703122 := by exact prefixLift 703122
  have htrace : WordTrace (prefixWord ++ tailWord_703122) baseStart_703122 baseEnd_703122 := by
    simpa [prefixWord, tailWord_703122, baseEnd_703122] using wordTrace_append hprefix tailTrace_703122
  have hstable : (prefixWord ++ tailWord_703122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703122).length < 2 ^ (prefixWord ++ tailWord_703122).sum := by decide
  have hdescent : baseEnd_703122 < baseStart_703122 := by decide
  rcases family_descends (prefixWord ++ tailWord_703122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703128 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_703128 : Nat := 118140960795 + 703128 * 2 ^ 59
def prefixEnd_703128 : Nat := 4983230072969 + 3 ^ 40 * 703128 * 2
def baseEnd_703128 : Nat := 361042625634630242166379

theorem tailTrace_703128 : CollatzResearch.WordTrace tailWord_703128 prefixEnd_703128 361042625634630242166379 := by
  unfold tailWord_703128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822592498347407773539019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17096789997796543698052025 12822592498347407773539019)
  ·
    refine ⟨19233888747521111660308529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12822592498347407773539019 19233888747521111660308529)
    ·
      refine ⟨14425416560640833745231397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19233888747521111660308529 14425416560640833745231397)
      ·
        refine ⟨2704765605120156327230887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14425416560640833745231397 2704765605120156327230887)
        ·
          refine ⟨4057148407680234490846331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704765605120156327230887 4057148407680234490846331)
          ·
            refine ⟨6085722611520351736269497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057148407680234490846331 6085722611520351736269497)
            ·
              refine ⟨4564291958640263802202123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6085722611520351736269497 4564291958640263802202123)
              ·
                refine ⟨6846437937960395703303185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4564291958640263802202123 6846437937960395703303185)
                ·
                  refine ⟨5134828453470296777477389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846437937960395703303185 5134828453470296777477389)
                  ·
                    refine ⟨1925560670051361291554021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5134828453470296777477389 1925560670051361291554021)
                    ·
                      refine ⟨361042625634630242166379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1925560670051361291554021 361042625634630242166379)
                      ·
                        rfl

theorem cell23_703128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_703128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703128 prefixEnd_703128 := by exact prefixLift 703128
  have htrace : WordTrace (prefixWord ++ tailWord_703128) baseStart_703128 baseEnd_703128 := by
    simpa [prefixWord, tailWord_703128, baseEnd_703128] using wordTrace_append hprefix tailTrace_703128
  have hstable : (prefixWord ++ tailWord_703128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703128).length < 2 ^ (prefixWord ++ tailWord_703128).sum := by decide
  have hdescent : baseEnd_703128 < baseStart_703128 := by decide
  rcases family_descends (prefixWord ++ tailWord_703128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703149 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_703149 : Nat := 118140960795 + 703149 * 2 ^ 59
def prefixEnd_703149 : Nat := 4983230072969 + 3 ^ 40 * 703149 * 2
def baseEnd_703149 : Nat := 361053408728374660003783

theorem tailTrace_703149 : CollatzResearch.WordTrace tailWord_703149 prefixEnd_703149 361053408728374660003783 := by
  unfold tailWord_703149
  simp only [CollatzResearch.WordTrace]
  refine ⟨25645950929618736133592501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17097300619745824089061667 25645950929618736133592501)
  ·
    refine ⟨2404307899651756512524297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25645950929618736133592501 2404307899651756512524297)
    ·
      refine ⟨1803230924738817384393223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2404307899651756512524297 1803230924738817384393223)
      ·
        refine ⟨2704846387108226076589835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803230924738817384393223 2704846387108226076589835)
        ·
          refine ⟨4057269580662339114884753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704846387108226076589835 4057269580662339114884753)
          ·
            refine ⟨3042952185496754336163565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4057269580662339114884753 3042952185496754336163565)
            ·
              refine ⟨1141107069561282876061337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3042952185496754336163565 1141107069561282876061337)
              ·
                refine ⟨855830302170962157046003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141107069561282876061337 855830302170962157046003)
                ·
                  refine ⟨1283745453256443235569005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855830302170962157046003 1283745453256443235569005)
                  ·
                    refine ⟨481404544971166213338377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1283745453256443235569005 481404544971166213338377)
                    ·
                      refine ⟨361053408728374660003783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481404544971166213338377 361053408728374660003783)
                      ·
                        rfl

theorem cell23_703149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_703149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703149 prefixEnd_703149 := by exact prefixLift 703149
  have htrace : WordTrace (prefixWord ++ tailWord_703149) baseStart_703149 baseEnd_703149 := by
    simpa [prefixWord, tailWord_703149, baseEnd_703149] using wordTrace_append hprefix tailTrace_703149
  have hstable : (prefixWord ++ tailWord_703149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703149).length < 2 ^ (prefixWord ++ tailWord_703149).sum := by decide
  have hdescent : baseEnd_703149 < baseStart_703149 := by decide
  rcases family_descends (prefixWord ++ tailWord_703149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703174 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_703174 : Nat := 118140960795 + 703174 * 2 ^ 59
def prefixEnd_703174 : Nat := 4983230072969 + 3 ^ 40 * 703174 * 2
def baseEnd_703174 : Nat := 361066245744737062191169

theorem tailTrace_703174 : CollatzResearch.WordTrace tailWord_703174 prefixEnd_703174 361066245744737062191169 := by
  unfold tailWord_703174
  simp only [CollatzResearch.WordTrace]
  refine ⟨801464461079005168851643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17097908503018776935501717 801464461079005168851643)
  ·
    refine ⟨1202196691618507753277465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801464461079005168851643 1202196691618507753277465)
    ·
      refine ⟨901647518713880814958099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1202196691618507753277465 901647518713880814958099)
      ·
        refine ⟨1352471278070821222437149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901647518713880814958099 1352471278070821222437149)
        ·
          refine ⟨507176729276557958413931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1352471278070821222437149 507176729276557958413931)
          ·
            refine ⟨760765093914836937620897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507176729276557958413931 760765093914836937620897)
            ·
              refine ⟨570573820436127703215673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760765093914836937620897 570573820436127703215673)
              ·
                refine ⟨427930365327095777411755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570573820436127703215673 427930365327095777411755)
                ·
                  refine ⟨641895547990643666117633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427930365327095777411755 641895547990643666117633)
                  ·
                    refine ⟨481421660992982749588225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 641895547990643666117633 481421660992982749588225)
                    ·
                      refine ⟨361066245744737062191169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481421660992982749588225 361066245744737062191169)
                      ·
                        rfl

theorem cell23_703174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_703174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703174 prefixEnd_703174 := by exact prefixLift 703174
  have htrace : WordTrace (prefixWord ++ tailWord_703174) baseStart_703174 baseEnd_703174 := by
    simpa [prefixWord, tailWord_703174, baseEnd_703174] using wordTrace_append hprefix tailTrace_703174
  have hstable : (prefixWord ++ tailWord_703174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703174).length < 2 ^ (prefixWord ++ tailWord_703174).sum := by decide
  have hdescent : baseEnd_703174 < baseStart_703174 := by decide
  rcases family_descends (prefixWord ++ tailWord_703174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703185 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 5]
def baseStart_703185 : Nat := 118140960795 + 703185 * 2 ^ 59
def prefixEnd_703185 : Nat := 4983230072969 + 3 ^ 40 * 703185 * 2
def baseEnd_703185 : Nat := 40119099336881835461513

theorem tailTrace_703185 : CollatzResearch.WordTrace tailWord_703185 prefixEnd_703185 40119099336881835461513 := by
  unfold tailWord_703185
  simp only [CollatzResearch.WordTrace]
  refine ⟨25647263957488314281903009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17098175971658876187935339 25647263957488314281903009)
  ·
    refine ⟨19235447968116235711427257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25647263957488314281903009 19235447968116235711427257)
    ·
      refine ⟨14426585976087176783570443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19235447968116235711427257 14426585976087176783570443)
      ·
        refine ⟨21639878964130765175355665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14426585976087176783570443 21639878964130765175355665)
        ·
          refine ⟨16229909223098073881516749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21639878964130765175355665 16229909223098073881516749)
          ·
            refine ⟨6086215958661777705568781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16229909223098073881516749 6086215958661777705568781)
            ·
              refine ⟨2282330984498166639588293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086215958661777705568781 2282330984498166639588293)
              ·
                refine ⟨427937059593406244922805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2282330984498166639588293 427937059593406244922805)
                ·
                  refine ⟨40119099336881835461513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427937059593406244922805 40119099336881835461513)
                  ·
                    rfl

theorem cell23_703185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 5].length) (baseStart_703185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703185 prefixEnd_703185 := by exact prefixLift 703185
  have htrace : WordTrace (prefixWord ++ tailWord_703185) baseStart_703185 baseEnd_703185 := by
    simpa [prefixWord, tailWord_703185, baseEnd_703185] using wordTrace_append hprefix tailTrace_703185
  have hstable : (prefixWord ++ tailWord_703185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703185).length < 2 ^ (prefixWord ++ tailWord_703185).sum := by decide
  have hdescent : baseEnd_703185 < baseStart_703185 := by decide
  rcases family_descends (prefixWord ++ tailWord_703185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703196 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_703196 : Nat := 118140960795 + 703196 * 2 ^ 59
def prefixEnd_703196 : Nat := 4983230072969 + 3 ^ 40 * 703196 * 2
def baseEnd_703196 : Nat := 361077542319135976116067

theorem tailTrace_703196 : CollatzResearch.WordTrace tailWord_703196 prefixEnd_703196 361077542319135976116067 := by
  unfold tailWord_703196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12823832580224231580276721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17098443440298975440368961 12823832580224231580276721)
  ·
    refine ⟨9617874435168173685207541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12823832580224231580276721 9617874435168173685207541)
    ·
      refine ⟨901675728297016282988207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9617874435168173685207541 901675728297016282988207)
      ·
        refine ⟨1352513592445524424482311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901675728297016282988207 1352513592445524424482311)
        ·
          refine ⟨2028770388668286636723467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352513592445524424482311 2028770388668286636723467)
          ·
            refine ⟨3043155583002429955085201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028770388668286636723467 3043155583002429955085201)
            ·
              refine ⟨2282366687251822466313901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043155583002429955085201 2282366687251822466313901)
              ·
                refine ⟨855887507719433424867713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282366687251822466313901 855887507719433424867713)
                ·
                  refine ⟨641915630789575068650785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 855887507719433424867713 641915630789575068650785)
                  ·
                    refine ⟨481436723092181301488089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 641915630789575068650785 481436723092181301488089)
                    ·
                      refine ⟨361077542319135976116067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481436723092181301488089 361077542319135976116067)
                      ·
                        rfl

theorem cell23_703196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_703196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703196 prefixEnd_703196 := by exact prefixLift 703196
  have htrace : WordTrace (prefixWord ++ tailWord_703196) baseStart_703196 baseEnd_703196 := by
    simpa [prefixWord, tailWord_703196, baseEnd_703196] using wordTrace_append hprefix tailTrace_703196
  have hstable : (prefixWord ++ tailWord_703196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703196).length < 2 ^ (prefixWord ++ tailWord_703196).sum := by decide
  have hdescent : baseEnd_703196 < baseStart_703196 := by decide
  rcases family_descends (prefixWord ++ tailWord_703196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703215 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 2, 5]
def baseStart_703215 : Nat := 118140960795 + 703215 * 2 ^ 59
def prefixEnd_703215 : Nat := 4983230072969 + 3 ^ 40 * 703215 * 2
def baseEnd_703215 : Nat := 120362432817190467259493

theorem tailTrace_703215 : CollatzResearch.WordTrace tailWord_703215 prefixEnd_703215 120362432817190467259493 := by
  unfold tailWord_703215
  simp only [CollatzResearch.WordTrace]
  refine ⟨25648358147379629405495099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17098905431586419603663399 25648358147379629405495099)
  ·
    refine ⟨38472537221069444108242649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25648358147379629405495099 38472537221069444108242649)
    ·
      refine ⟨28854402915802083081181987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38472537221069444108242649 28854402915802083081181987)
      ·
        refine ⟨43281604373703124621772981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28854402915802083081181987 43281604373703124621772981)
        ·
          refine ⟨4057650410034667933291217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43281604373703124621772981 4057650410034667933291217)
          ·
            refine ⟨3043237807526000949968413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4057650410034667933291217 3043237807526000949968413)
            ·
              refine ⟨1141214177822250356238155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043237807526000949968413 1141214177822250356238155)
              ·
                refine ⟨1711821266733375534357233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141214177822250356238155 1711821266733375534357233)
                ·
                  refine ⟨1283865950050031650767925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711821266733375534357233 1283865950050031650767925)
                  ·
                    refine ⟨120362432817190467259493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1283865950050031650767925 120362432817190467259493)
                    ·
                      rfl

theorem cell23_703215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_703215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703215 prefixEnd_703215 := by exact prefixLift 703215
  have htrace : WordTrace (prefixWord ++ tailWord_703215) baseStart_703215 baseEnd_703215 := by
    simpa [prefixWord, tailWord_703215, baseEnd_703215] using wordTrace_append hprefix tailTrace_703215
  have hstable : (prefixWord ++ tailWord_703215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703215).length < 2 ^ (prefixWord ++ tailWord_703215).sum := by decide
  have hdescent : baseEnd_703215 < baseStart_703215 := by decide
  rcases family_descends (prefixWord ++ tailWord_703215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703272 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_703272 : Nat := 118140960795 + 703272 * 2 ^ 59
def prefixEnd_703272 : Nat := 4983230072969 + 3 ^ 40 * 703272 * 2
def baseEnd_703272 : Nat := 361116566848877678765717

theorem tailTrace_703272 : CollatzResearch.WordTrace tailWord_703272 prefixEnd_703272 361116566848877678765717 := by
  unfold tailWord_703272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825218554086564070160035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17100291405448752093546713 12825218554086564070160035)
  ·
    refine ⟨19237827831129846105240053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12825218554086564070160035 19237827831129846105240053)
    ·
      refine ⟨1803546359168423072366255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19237827831129846105240053 1803546359168423072366255)
      ·
        refine ⟨2705319538752634608549383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803546359168423072366255 2705319538752634608549383)
        ·
          refine ⟨4057979308128951912824075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705319538752634608549383 4057979308128951912824075)
          ·
            refine ⟨6086968962193427869236113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057979308128951912824075 6086968962193427869236113)
            ·
              refine ⟨4565226721645070901927085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6086968962193427869236113 4565226721645070901927085)
              ·
                refine ⟨1711960020616901588222657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565226721645070901927085 1711960020616901588222657)
                ·
                  refine ⟨1283970015462676191166993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711960020616901588222657 1283970015462676191166993)
                  ·
                    refine ⟨962977511597007143375245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283970015462676191166993 962977511597007143375245)
                    ·
                      refine ⟨361116566848877678765717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 962977511597007143375245 361116566848877678765717)
                      ·
                        rfl

theorem cell23_703272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_703272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703272 prefixEnd_703272 := by exact prefixLift 703272
  have htrace : WordTrace (prefixWord ++ tailWord_703272) baseStart_703272 baseEnd_703272 := by
    simpa [prefixWord, tailWord_703272, baseEnd_703272] using wordTrace_append hprefix tailTrace_703272
  have hstable : (prefixWord ++ tailWord_703272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703272).length < 2 ^ (prefixWord ++ tailWord_703272).sum := by decide
  have hdescent : baseEnd_703272 < baseStart_703272 := by decide
  rcases family_descends (prefixWord ++ tailWord_703272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703309 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 6]
def baseStart_703309 : Nat := 118140960795 + 703309 * 2 ^ 59
def prefixEnd_703309 : Nat := 4983230072969 + 3 ^ 40 * 703309 * 2
def baseEnd_703309 : Nat := 40126173959232670444783

theorem tailTrace_703309 : CollatzResearch.WordTrace tailWord_703309 prefixEnd_703309 40126173959232670444783 := by
  unfold tailWord_703309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25651786609039083459416981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17101191072692722306277987 25651786609039083459416981)
  ·
    refine ⟨1202427497298707037160171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25651786609039083459416981 1202427497298707037160171)
    ·
      refine ⟨1803641245948060555740257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202427497298707037160171 1803641245948060555740257)
      ·
        refine ⟨1352730934461045416805193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1803641245948060555740257 1352730934461045416805193)
        ·
          refine ⟨1014548200845784062603895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352730934461045416805193 1014548200845784062603895)
          ·
            refine ⟨1521822301268676093905843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014548200845784062603895 1521822301268676093905843)
            ·
              refine ⟨2282733451903014140858765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521822301268676093905843 2282733451903014140858765)
              ·
                refine ⟨856025044463630302822037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282733451903014140858765 856025044463630302822037)
                ·
                  refine ⟨40126173959232670444783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 856025044463630302822037 40126173959232670444783)
                  ·
                    rfl

theorem cell23_703309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_703309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703309 prefixEnd_703309 := by exact prefixLift 703309
  have htrace : WordTrace (prefixWord ++ tailWord_703309) baseStart_703309 baseEnd_703309 := by
    simpa [prefixWord, tailWord_703309, baseEnd_703309] using wordTrace_append hprefix tailTrace_703309
  have hstable : (prefixWord ++ tailWord_703309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703309).length < 2 ^ (prefixWord ++ tailWord_703309).sum := by decide
  have hdescent : baseEnd_703309 < baseStart_703309 := by decide
  rcases family_descends (prefixWord ++ tailWord_703309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703322 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_703322 : Nat := 118140960795 + 703322 * 2 ^ 59
def prefixEnd_703322 : Nat := 4983230072969 + 3 ^ 40 * 703322 * 2
def baseEnd_703322 : Nat := 120380746960534161046829

theorem tailTrace_703322 : CollatzResearch.WordTrace tailWord_703322 prefixEnd_703322 120380746960534161046829 := by
  unfold tailWord_703322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6413065189497996669910055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17101507171994657786426813 6413065189497996669910055)
  ·
    refine ⟨9619597784246995004865083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6413065189497996669910055 9619597784246995004865083)
    ·
      refine ⟨14429396676370492507297625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9619597784246995004865083 14429396676370492507297625)
      ·
        refine ⟨10822047507277869380473219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14429396676370492507297625 10822047507277869380473219)
        ·
          refine ⟨16233071260916804070709829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822047507277869380473219 16233071260916804070709829)
          ·
            refine ⟨3043700861421900763258093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16233071260916804070709829 3043700861421900763258093)
            ·
              refine ⟨1141387823033212786221785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043700861421900763258093 1141387823033212786221785)
              ·
                refine ⟨856040867274909589666339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141387823033212786221785 856040867274909589666339)
                ·
                  refine ⟨1284061300912364384499509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856040867274909589666339 1284061300912364384499509)
                  ·
                    refine ⟨120380746960534161046829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1284061300912364384499509 120380746960534161046829)
                    ·
                      rfl

theorem cell23_703322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_703322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703322 prefixEnd_703322 := by exact prefixLift 703322
  have htrace : WordTrace (prefixWord ++ tailWord_703322) baseStart_703322 baseEnd_703322 := by
    simpa [prefixWord, tailWord_703322, baseEnd_703322] using wordTrace_append hprefix tailTrace_703322
  have hstable : (prefixWord ++ tailWord_703322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703322).length < 2 ^ (prefixWord ++ tailWord_703322).sum := by decide
  have hdescent : baseEnd_703322 < baseStart_703322 := by decide
  rcases family_descends (prefixWord ++ tailWord_703322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703335 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 3, 6]
def baseStart_703335 : Nat := 118140960795 + 703335 * 2 ^ 59
def prefixEnd_703335 : Nat := 4983230072969 + 3 ^ 40 * 703335 * 2
def baseEnd_703335 : Nat := 120382972043370310759309

theorem tailTrace_703335 : CollatzResearch.WordTrace tailWord_703335 prefixEnd_703335 120382972043370310759309 := by
  unfold tailWord_703335
  simp only [CollatzResearch.WordTrace]
  refine ⟨25652734906944889899863459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17101823271296593266575639 25652734906944889899863459)
  ·
    refine ⟨38479102360417334849795189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25652734906944889899863459 38479102360417334849795189)
    ·
      refine ⟨3607415846289125142168299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38479102360417334849795189 3607415846289125142168299)
      ·
        refine ⟨5411123769433687713252449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607415846289125142168299 5411123769433687713252449)
        ·
          refine ⟨4058342827075265784939337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5411123769433687713252449 4058342827075265784939337)
          ·
            refine ⟨3043757120306449338704503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4058342827075265784939337 3043757120306449338704503)
            ·
              refine ⟨4565635680459674008056755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043757120306449338704503 4565635680459674008056755)
              ·
                refine ⟨6848453520689511012085133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565635680459674008056755 6848453520689511012085133)
                ·
                  refine ⟨2568170070258566629531925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6848453520689511012085133 2568170070258566629531925)
                  ·
                    refine ⟨120382972043370310759309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2568170070258566629531925 120382972043370310759309)
                    ·
                      rfl

theorem cell23_703335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_703335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703335 prefixEnd_703335 := by exact prefixLift 703335
  have htrace : WordTrace (prefixWord ++ tailWord_703335) baseStart_703335 baseEnd_703335 := by
    simpa [prefixWord, tailWord_703335, baseEnd_703335] using wordTrace_append hprefix tailTrace_703335
  have hstable : (prefixWord ++ tailWord_703335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703335).length < 2 ^ (prefixWord ++ tailWord_703335).sum := by decide
  have hdescent : baseEnd_703335 < baseStart_703335 := by decide
  rcases family_descends (prefixWord ++ tailWord_703335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703348 : List Nat := [2, 21]
def baseStart_703348 : Nat := 118140960795 + 703348 * 2 ^ 59
def prefixEnd_703348 : Nat := 4983230072969 + 3 ^ 40 * 703348 * 2
def baseEnd_703348 : Nat := 18348604957507462349

theorem tailTrace_703348 : CollatzResearch.WordTrace tailWord_703348 prefixEnd_703348 18348604957507462349 := by
  unfold tailWord_703348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12826604527948896560043349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17102139370598528746724465 12826604527948896560043349)
  ·
    refine ⟨18348604957507462349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 21 12826604527948896560043349 18348604957507462349)
    ·
      rfl

theorem cell23_703348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 21].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 21].length) (baseStart_703348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703348 prefixEnd_703348 := by exact prefixLift 703348
  have htrace : WordTrace (prefixWord ++ tailWord_703348) baseStart_703348 baseEnd_703348 := by
    simpa [prefixWord, tailWord_703348, baseEnd_703348] using wordTrace_append hprefix tailTrace_703348
  have hstable : (prefixWord ++ tailWord_703348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703348).length < 2 ^ (prefixWord ++ tailWord_703348).sum := by decide
  have hdescent : baseEnd_703348 < baseStart_703348 := by decide
  rcases family_descends (prefixWord ++ tailWord_703348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703353 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 1, 1, 3]
def baseStart_703353 : Nat := 118140960795 + 703353 * 2 ^ 59
def prefixEnd_703353 : Nat := 4983230072969 + 3 ^ 40 * 703353 * 2
def baseEnd_703353 : Nat := 361158158781891861852845

theorem tailTrace_703353 : CollatzResearch.WordTrace tailWord_703353 prefixEnd_703353 361158158781891861852845 := by
  unfold tailWord_703353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653391420879678974018713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17102260947253119316012475 25653391420879678974018713)
  ·
    refine ⟨19240043565659759230514035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25653391420879678974018713 19240043565659759230514035)
    ·
      refine ⟨28860065348489638845771053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19240043565659759230514035 28860065348489638845771053)
      ·
        refine ⟨10822524505683614567164145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28860065348489638845771053 10822524505683614567164145)
        ·
          refine ⟨8116893379262710925373109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10822524505683614567164145 8116893379262710925373109)
          ·
            refine ⟨760958754305879149253729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8116893379262710925373109 760958754305879149253729)
            ·
              refine ⟨570719065729409361940297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760958754305879149253729 570719065729409361940297)
              ·
                refine ⟨428039299297057021455223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570719065729409361940297 428039299297057021455223)
                ·
                  refine ⟨642058948945585532182835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428039299297057021455223 642058948945585532182835)
                  ·
                    refine ⟨963088423418378298274253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 642058948945585532182835 963088423418378298274253)
                    ·
                      refine ⟨361158158781891861852845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963088423418378298274253 361158158781891861852845)
                      ·
                        rfl

theorem cell23_703353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_703353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703353 prefixEnd_703353 := by exact prefixLift 703353
  have htrace : WordTrace (prefixWord ++ tailWord_703353) baseStart_703353 baseEnd_703353 := by
    simpa [prefixWord, tailWord_703353, baseEnd_703353] using wordTrace_append hprefix tailTrace_703353
  have hstable : (prefixWord ++ tailWord_703353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703353).length < 2 ^ (prefixWord ++ tailWord_703353).sum := by decide
  have hdescent : baseEnd_703353 < baseStart_703353 := by decide
  rcases family_descends (prefixWord ++ tailWord_703353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703365 : List Nat := [1, 3, 1, 1, 3, 3, 3, 8]
def baseStart_703365 : Nat := 118140960795 + 703365 * 2 ^ 59
def prefixEnd_703365 : Nat := 4983230072969 + 3 ^ 40 * 703365 * 2
def baseEnd_703365 : Nat := 13376456316657252403807

theorem tailTrace_703365 : CollatzResearch.WordTrace tailWord_703365 prefixEnd_703365 13376456316657252403807 := by
  unfold tailWord_703365
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653829096836205023455549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17102552731224136682303699 25653829096836205023455549)
  ·
    refine ⟨9620185911313576883795831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25653829096836205023455549 9620185911313576883795831)
    ·
      refine ⟨14430278866970365325693747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9620185911313576883795831 14430278866970365325693747)
      ·
        refine ⟨21645418300455547988540621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14430278866970365325693747 21645418300455547988540621)
        ·
          refine ⟨8117031862670830495702733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21645418300455547988540621 8117031862670830495702733)
          ·
            refine ⟨3043886948501561435888525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8117031862670830495702733 3043886948501561435888525)
            ·
              refine ⟨1141457605688085538458197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043886948501561435888525 1141457605688085538458197)
              ·
                refine ⟨13376456316657252403807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1141457605688085538458197 13376456316657252403807)
                ·
                  rfl

theorem cell23_703365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 8].length) (baseStart_703365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703365 prefixEnd_703365 := by exact prefixLift 703365
  have htrace : WordTrace (prefixWord ++ tailWord_703365) baseStart_703365 baseEnd_703365 := by
    simpa [prefixWord, tailWord_703365, baseEnd_703365] using wordTrace_append hprefix tailTrace_703365
  have hstable : (prefixWord ++ tailWord_703365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703365).length < 2 ^ (prefixWord ++ tailWord_703365).sum := by decide
  have hdescent : baseEnd_703365 < baseStart_703365 := by decide
  rcases family_descends (prefixWord ++ tailWord_703365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703392 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_703392 : Nat := 118140960795 + 703392 * 2 ^ 59
def prefixEnd_703392 : Nat := 4983230072969 + 3 ^ 40 * 703392 * 2
def baseEnd_703392 : Nat := 361178184527417209265165

theorem tailTrace_703392 : CollatzResearch.WordTrace tailWord_703392 prefixEnd_703392 361178184527417209265165 := by
  unfold tailWord_703392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12827406933869194317344215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17103209245158925756458953 12827406933869194317344215)
  ·
    refine ⟨19241110400803791476016323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12827406933869194317344215 19241110400803791476016323)
    ·
      refine ⟨28861665601205687214024485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19241110400803791476016323 28861665601205687214024485)
      ·
        refine ⟨5411562300226066352629591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28861665601205687214024485 5411562300226066352629591)
        ·
          refine ⟨8117343450339099528944387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411562300226066352629591 8117343450339099528944387)
          ·
            refine ⟨12176015175508649293416581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8117343450339099528944387 12176015175508649293416581)
            ·
              refine ⟨2283002845407871742515609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12176015175508649293416581 2283002845407871742515609)
              ·
                refine ⟨1712252134055903806886707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2283002845407871742515609 1712252134055903806886707)
                ·
                  refine ⟨2568378201083855710330061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712252134055903806886707 2568378201083855710330061)
                  ·
                    refine ⟨963141825406445891373773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568378201083855710330061 963141825406445891373773)
                    ·
                      refine ⟨361178184527417209265165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963141825406445891373773 361178184527417209265165)
                      ·
                        rfl

theorem cell23_703392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_703392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703392 prefixEnd_703392 := by exact prefixLift 703392
  have htrace : WordTrace (prefixWord ++ tailWord_703392) baseStart_703392 baseEnd_703392 := by
    simpa [prefixWord, tailWord_703392, baseEnd_703392] using wordTrace_append hprefix tailTrace_703392
  have hstable : (prefixWord ++ tailWord_703392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703392).length < 2 ^ (prefixWord ++ tailWord_703392).sum := by decide
  have hdescent : baseEnd_703392 < baseStart_703392 := by decide
  rcases family_descends (prefixWord ++ tailWord_703392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703393 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_703393 : Nat := 118140960795 + 703393 * 2 ^ 59
def prefixEnd_703393 : Nat := 4983230072969 + 3 ^ 40 * 703393 * 2
def baseEnd_703393 : Nat := 361178698008071705352661

theorem tailTrace_703393 : CollatzResearch.WordTrace tailWord_703393 prefixEnd_703393 361178698008071705352661 := by
  unfold tailWord_703393
  simp only [CollatzResearch.WordTrace]
  refine ⟨25654850340734765805474833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17103233560489843870316555 25654850340734765805474833)
  ·
    refine ⟨19241137755551074354106125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25654850340734765805474833 19241137755551074354106125)
    ·
      refine ⟨7215426658331652882789797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19241137755551074354106125 7215426658331652882789797)
      ·
        refine ⟨1352892498437184915523087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7215426658331652882789797 1352892498437184915523087)
        ·
          refine ⟨2029338747655777373284631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352892498437184915523087 2029338747655777373284631)
          ·
            refine ⟨3044008121483666059926947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029338747655777373284631 3044008121483666059926947)
            ·
              refine ⟨4566012182225499089890421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044008121483666059926947 4566012182225499089890421)
              ·
                refine ⟨428063642083640539677227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4566012182225499089890421 428063642083640539677227)
                ·
                  refine ⟨642095463125460809515841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428063642083640539677227 642095463125460809515841)
                  ·
                    refine ⟨481571597344095607136881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 642095463125460809515841 481571597344095607136881)
                    ·
                      refine ⟨361178698008071705352661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481571597344095607136881 361178698008071705352661)
                      ·
                        rfl

theorem cell23_703393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_703393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703393 prefixEnd_703393 := by exact prefixLift 703393
  have htrace : WordTrace (prefixWord ++ tailWord_703393) baseStart_703393 baseEnd_703393 := by
    simpa [prefixWord, tailWord_703393, baseEnd_703393] using wordTrace_append hprefix tailTrace_703393
  have hstable : (prefixWord ++ tailWord_703393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703393).length < 2 ^ (prefixWord ++ tailWord_703393).sum := by decide
  have hdescent : baseEnd_703393 < baseStart_703393 := by decide
  rcases family_descends (prefixWord ++ tailWord_703393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703415 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_703415 : Nat := 118140960795 + 703415 * 2 ^ 59
def prefixEnd_703415 : Nat := 4983230072969 + 3 ^ 40 * 703415 * 2
def baseEnd_703415 : Nat := 361189994582470619277559

theorem tailTrace_703415 : CollatzResearch.WordTrace tailWord_703415 prefixEnd_703415 361189994582470619277559 := by
  unfold tailWord_703415
  simp only [CollatzResearch.WordTrace]
  refine ⟨25655652746655063562775699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17103768497770042375183799 25655652746655063562775699)
  ·
    refine ⟨38483479119982595344163549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25655652746655063562775699 38483479119982595344163549)
    ·
      refine ⟨14431304669993473254061331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38483479119982595344163549 14431304669993473254061331)
      ·
        refine ⟨21646957004990209881091997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14431304669993473254061331 21646957004990209881091997)
        ·
          refine ⟨8117608876871328705409499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21646957004990209881091997 8117608876871328705409499)
          ·
            refine ⟨12176413315306993058114249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8117608876871328705409499 12176413315306993058114249)
            ·
              refine ⟨9132309986480244793585687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12176413315306993058114249 9132309986480244793585687)
              ·
                refine ⟨13698464979720367190378531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132309986480244793585687 13698464979720367190378531)
                ·
                  refine ⟨20547697469580550785567797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13698464979720367190378531 20547697469580550785567797)
                  ·
                    refine ⟨1926346637773176636146981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20547697469580550785567797 1926346637773176636146981)
                    ·
                      refine ⟨361189994582470619277559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1926346637773176636146981 361189994582470619277559)
                      ·
                        rfl

theorem cell23_703415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_703415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703415 prefixEnd_703415 := by exact prefixLift 703415
  have htrace : WordTrace (prefixWord ++ tailWord_703415) baseStart_703415 baseEnd_703415 := by
    simpa [prefixWord, tailWord_703415, baseEnd_703415] using wordTrace_append hprefix tailTrace_703415
  have hstable : (prefixWord ++ tailWord_703415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703415).length < 2 ^ (prefixWord ++ tailWord_703415).sum := by decide
  have hdescent : baseEnd_703415 < baseStart_703415 := by decide
  rcases family_descends (prefixWord ++ tailWord_703415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703436 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 1, 3, 2]
def baseStart_703436 : Nat := 118140960795 + 703436 * 2 ^ 59
def prefixEnd_703436 : Nat := 4983230072969 + 3 ^ 40 * 703436 * 2
def baseEnd_703436 : Nat := 361200777676215037114963

theorem tailTrace_703436 : CollatzResearch.WordTrace tailWord_703436 prefixEnd_703436 361200777676215037114963 := by
  unfold tailWord_703436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828209339789492074645081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17104279119719322766193441 12828209339789492074645081)
  ·
    refine ⟨9621157004842119055983811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12828209339789492074645081 9621157004842119055983811)
    ·
      refine ⟨14431735507263178583975717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9621157004842119055983811 14431735507263178583975717)
      ·
        refine ⟨2705950407611845984495447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14431735507263178583975717 2705950407611845984495447)
        ·
          refine ⟨4058925611417768976743171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705950407611845984495447 4058925611417768976743171)
          ·
            refine ⟨6088388417126653465114757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058925611417768976743171 6088388417126653465114757)
            ·
              refine ⟨1141572828211247524709017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6088388417126653465114757 1141572828211247524709017)
              ·
                refine ⟨856179621158435643531763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141572828211247524709017 856179621158435643531763)
                ·
                  refine ⟨1284269431737653465297645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856179621158435643531763 1284269431737653465297645)
                  ·
                    refine ⟨481601036901620049486617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1284269431737653465297645 481601036901620049486617)
                    ·
                      refine ⟨361200777676215037114963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481601036901620049486617 361200777676215037114963)
                      ·
                        rfl

theorem cell23_703436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_703436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703436 prefixEnd_703436 := by exact prefixLift 703436
  have htrace : WordTrace (prefixWord ++ tailWord_703436) baseStart_703436 baseEnd_703436 := by
    simpa [prefixWord, tailWord_703436, baseEnd_703436] using wordTrace_append hprefix tailTrace_703436
  have hstable : (prefixWord ++ tailWord_703436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703436).length < 2 ^ (prefixWord ++ tailWord_703436).sum := by decide
  have hdescent : baseEnd_703436 < baseStart_703436 := by decide
  rcases family_descends (prefixWord ++ tailWord_703436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703466 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_703466 : Nat := 118140960795 + 703466 * 2 ^ 59
def prefixEnd_703466 : Nat := 4983230072969 + 3 ^ 40 * 703466 * 2
def baseEnd_703466 : Nat := 361216182095849919739825

theorem tailTrace_703466 : CollatzResearch.WordTrace tailWord_703466 prefixEnd_703466 361216182095849919739825 := by
  unfold tailWord_703466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414378217367574818220563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17105008579646866181921501 6414378217367574818220563)
  ·
    refine ⟨9621567326051362227330845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6414378217367574818220563 9621567326051362227330845)
    ·
      refine ⟨3608087747269260835249067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9621567326051362227330845 3608087747269260835249067)
      ·
        refine ⟨5412131620903891252873601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608087747269260835249067 5412131620903891252873601)
        ·
          refine ⟨4059098715677918439655201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5412131620903891252873601 4059098715677918439655201)
          ·
            refine ⟨3044324036758438829741401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4059098715677918439655201 3044324036758438829741401)
            ·
              refine ⟨2283243027568829122306051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044324036758438829741401 2283243027568829122306051)
              ·
                refine ⟨3424864541353243683459077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283243027568829122306051 3424864541353243683459077)
                ·
                  refine ⟨642162101503733190648577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3424864541353243683459077 642162101503733190648577)
                  ·
                    refine ⟨481621576127799892986433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 642162101503733190648577 481621576127799892986433)
                    ·
                      refine ⟨361216182095849919739825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481621576127799892986433 361216182095849919739825)
                      ·
                        rfl

theorem cell23_703466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_703466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703466 prefixEnd_703466 := by exact prefixLift 703466
  have htrace : WordTrace (prefixWord ++ tailWord_703466) baseStart_703466 baseEnd_703466 := by
    simpa [prefixWord, tailWord_703466, baseEnd_703466] using wordTrace_append hprefix tailTrace_703466
  have hstable : (prefixWord ++ tailWord_703466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703466).length < 2 ^ (prefixWord ++ tailWord_703466).sum := by decide
  have hdescent : baseEnd_703466 < baseStart_703466 := by decide
  rcases family_descends (prefixWord ++ tailWord_703466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703477 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_703477 : Nat := 118140960795 + 703477 * 2 ^ 59
def prefixEnd_703477 : Nat := 4983230072969 + 3 ^ 40 * 703477 * 2
def baseEnd_703477 : Nat := 361221830383049376702275

theorem tailTrace_703477 : CollatzResearch.WordTrace tailWord_703477 prefixEnd_703477 361221830383049376702275 := by
  unfold tailWord_703477
  simp only [CollatzResearch.WordTrace]
  refine ⟨25657914072430448151532685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17105276048286965434355123 25657914072430448151532685)
  ·
    refine ⟨9621717777161418056824757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25657914072430448151532685 9621717777161418056824757)
    ·
      refine ⟨902036041608882942827321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9621717777161418056824757 902036041608882942827321)
      ·
        refine ⟨676527031206662207120491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 902036041608882942827321 676527031206662207120491)
        ·
          refine ⟨1014790546809993310680737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676527031206662207120491 1014790546809993310680737)
          ·
            refine ⟨761092910107494983010553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014790546809993310680737 761092910107494983010553)
            ·
              refine ⟨570819682580621237257915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761092910107494983010553 570819682580621237257915)
              ·
                refine ⟨856229523870931855886873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570819682580621237257915 856229523870931855886873)
                ·
                  refine ⟨642172142903198891915155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 856229523870931855886873 642172142903198891915155)
                  ·
                    refine ⟨963258214354798337872733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 642172142903198891915155 963258214354798337872733)
                    ·
                      refine ⟨361221830383049376702275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963258214354798337872733 361221830383049376702275)
                      ·
                        rfl

theorem cell23_703477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_703477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703477 prefixEnd_703477 := by exact prefixLift 703477
  have htrace : WordTrace (prefixWord ++ tailWord_703477) baseStart_703477 baseEnd_703477 := by
    simpa [prefixWord, tailWord_703477, baseEnd_703477] using wordTrace_append hprefix tailTrace_703477
  have hstable : (prefixWord ++ tailWord_703477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703477).length < 2 ^ (prefixWord ++ tailWord_703477).sum := by decide
  have hdescent : baseEnd_703477 < baseStart_703477 := by decide
  rcases family_descends (prefixWord ++ tailWord_703477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703482 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_703482 : Nat := 118140960795 + 703482 * 2 ^ 59
def prefixEnd_703482 : Nat := 4983230072969 + 3 ^ 40 * 703482 * 2
def baseEnd_703482 : Nat := 361224397786321857139751

theorem tailTrace_703482 : CollatzResearch.WordTrace tailWord_703482 prefixEnd_703482 361224397786321857139751 := by
  unfold tailWord_703482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414524109353083501366175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17105397624941556003643133 6414524109353083501366175)
  ·
    refine ⟨9621786164029625252049263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6414524109353083501366175 9621786164029625252049263)
    ·
      refine ⟨14432679246044437878073895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9621786164029625252049263 14432679246044437878073895)
      ·
        refine ⟨21649018869066656817110843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14432679246044437878073895 21649018869066656817110843)
        ·
          refine ⟨32473528303599985225666265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21649018869066656817110843 32473528303599985225666265)
          ·
            refine ⟨24355146227699988919249699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32473528303599985225666265 24355146227699988919249699)
            ·
              refine ⟨36532719341549983378874549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24355146227699988919249699 36532719341549983378874549)
              ·
                refine ⟨3424942438270310941769489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36532719341549983378874549 3424942438270310941769489)
                ·
                  refine ⟨2568706828702733206327117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424942438270310941769489 2568706828702733206327117)
                  ·
                    refine ⟨963265060763524952372669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568706828702733206327117 963265060763524952372669)
                    ·
                      refine ⟨361224397786321857139751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963265060763524952372669 361224397786321857139751)
                      ·
                        rfl

theorem cell23_703482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_703482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703482 prefixEnd_703482 := by exact prefixLift 703482
  have htrace : WordTrace (prefixWord ++ tailWord_703482) baseStart_703482 baseEnd_703482 := by
    simpa [prefixWord, tailWord_703482, baseEnd_703482] using wordTrace_append hprefix tailTrace_703482
  have hstable : (prefixWord ++ tailWord_703482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703482).length < 2 ^ (prefixWord ++ tailWord_703482).sum := by decide
  have hdescent : baseEnd_703482 < baseStart_703482 := by decide
  rcases family_descends (prefixWord ++ tailWord_703482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703512 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_703512 : Nat := 118140960795 + 703512 * 2 ^ 59
def prefixEnd_703512 : Nat := 4983230072969 + 3 ^ 40 * 703512 * 2
def baseEnd_703512 : Nat := 361239802205956739764613

theorem tailTrace_703512 : CollatzResearch.WordTrace tailWord_703512 prefixEnd_703512 361239802205956739764613 := by
  unfold tailWord_703512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829595313651824564528395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17106127084869099419371193 12829595313651824564528395)
  ·
    refine ⟨19244392970477736846792593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12829595313651824564528395 19244392970477736846792593)
    ·
      refine ⟨14433294727858302635094445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19244392970477736846792593 14433294727858302635094445)
      ·
        refine ⟨5412485522946863488160417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14433294727858302635094445 5412485522946863488160417)
        ·
          refine ⟨4059364142210147616120313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5412485522946863488160417 4059364142210147616120313)
          ·
            refine ⟨3044523106657610712090235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4059364142210147616120313 3044523106657610712090235)
            ·
              refine ⟨4566784659986416068135353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044523106657610712090235 4566784659986416068135353)
              ·
                refine ⟨3425088494989812051101515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4566784659986416068135353 3425088494989812051101515)
                ·
                  refine ⟨5137632742484718076652273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425088494989812051101515 5137632742484718076652273)
                  ·
                    refine ⟨3853224556863538557489205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5137632742484718076652273 3853224556863538557489205)
                    ·
                      refine ⟨361239802205956739764613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3853224556863538557489205 361239802205956739764613)
                      ·
                        rfl

theorem cell23_703512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_703512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703512 prefixEnd_703512 := by exact prefixLift 703512
  have htrace : WordTrace (prefixWord ++ tailWord_703512) baseStart_703512 baseEnd_703512 := by
    simpa [prefixWord, tailWord_703512, baseEnd_703512] using wordTrace_append hprefix tailTrace_703512
  have hstable : (prefixWord ++ tailWord_703512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703512).length < 2 ^ (prefixWord ++ tailWord_703512).sum := by decide
  have hdescent : baseEnd_703512 < baseStart_703512 := by decide
  rcases family_descends (prefixWord ++ tailWord_703512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703515 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 8]
def baseStart_703515 : Nat := 118140960795 + 703515 * 2 ^ 59
def prefixEnd_703515 : Nat := 4983230072969 + 3 ^ 40 * 703515 * 2
def baseEnd_703515 : Nat := 120413780882640076009033

theorem tailTrace_703515 : CollatzResearch.WordTrace tailWord_703515 prefixEnd_703515 120413780882640076009033 := by
  unfold tailWord_703515
  simp only [CollatzResearch.WordTrace]
  refine ⟨25659300046292780641415999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17106200030861853760943999 25659300046292780641415999)
  ·
    refine ⟨38488950069439170962123999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25659300046292780641415999 38488950069439170962123999)
    ·
      refine ⟨57733425104158756443185999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38488950069439170962123999 57733425104158756443185999)
      ·
        refine ⟨86600137656238134664778999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57733425104158756443185999 86600137656238134664778999)
        ·
          refine ⟨129900206484357201997168499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86600137656238134664778999 129900206484357201997168499)
          ·
            refine ⟨194850309726535802995752749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129900206484357201997168499 194850309726535802995752749)
            ·
              refine ⟨73068866147450926123407281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194850309726535802995752749 73068866147450926123407281)
              ·
                refine ⟨54801649610588194592555461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73068866147450926123407281 54801649610588194592555461)
                ·
                  refine ⟨10275309301985286486104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54801649610588194592555461 10275309301985286486104149)
                  ·
                    refine ⟨120413780882640076009033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10275309301985286486104149 120413780882640076009033)
                    ·
                      rfl

theorem cell23_703515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_703515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703515 prefixEnd_703515 := by exact prefixLift 703515
  have htrace : WordTrace (prefixWord ++ tailWord_703515) baseStart_703515 baseEnd_703515 := by
    simpa [prefixWord, tailWord_703515, baseEnd_703515] using wordTrace_append hprefix tailTrace_703515
  have hstable : (prefixWord ++ tailWord_703515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703515).length < 2 ^ (prefixWord ++ tailWord_703515).sum := by decide
  have hdescent : baseEnd_703515 < baseStart_703515 := by decide
  rcases family_descends (prefixWord ++ tailWord_703515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703549 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_703549 : Nat := 118140960795 + 703549 * 2 ^ 59
def prefixEnd_703549 : Nat := 4983230072969 + 3 ^ 40 * 703549 * 2
def baseEnd_703549 : Nat := 120419600330057698333981

theorem tailTrace_703549 : CollatzResearch.WordTrace tailWord_703549 prefixEnd_703549 120419600330057698333981 := by
  unfold tailWord_703549
  simp only [CollatzResearch.WordTrace]
  refine ⟨25660540128169604448153701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17107026752113069632102467 25660540128169604448153701)
  ·
    refine ⟨4811351274031800834028819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25660540128169604448153701 4811351274031800834028819)
    ·
      refine ⟨7217026911047701251043229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4811351274031800834028819 7217026911047701251043229)
      ·
        refine ⟨2706385091642887969141211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7217026911047701251043229 2706385091642887969141211)
        ·
          refine ⟨4059577637464331953711817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706385091642887969141211 4059577637464331953711817)
          ·
            refine ⟨3044683228098248965283863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4059577637464331953711817 3044683228098248965283863)
            ·
              refine ⟨4567024842147373447925795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044683228098248965283863 4567024842147373447925795)
              ·
                refine ⟨6850537263221060171888693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567024842147373447925795 6850537263221060171888693)
                ·
                  refine ⟨642237868426974391114565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6850537263221060171888693 642237868426974391114565)
                  ·
                    refine ⟨120419600330057698333981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 642237868426974391114565 120419600330057698333981)
                    ·
                      rfl

theorem cell23_703549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_703549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703549 prefixEnd_703549 := by exact prefixLift 703549
  have htrace : WordTrace (prefixWord ++ tailWord_703549) baseStart_703549 baseEnd_703549 := by
    simpa [prefixWord, tailWord_703549, baseEnd_703549] using wordTrace_append hprefix tailTrace_703549
  have hstable : (prefixWord ++ tailWord_703549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703549).length < 2 ^ (prefixWord ++ tailWord_703549).sum := by decide
  have hdescent : baseEnd_703549 < baseStart_703549 := by decide
  rcases family_descends (prefixWord ++ tailWord_703549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703553 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 2, 5]
def baseStart_703553 : Nat := 118140960795 + 703553 * 2 ^ 59
def prefixEnd_703553 : Nat := 4983230072969 + 3 ^ 40 * 703553 * 2
def baseEnd_703553 : Nat := 120420284970930359783975

theorem tailTrace_703553 : CollatzResearch.WordTrace tailWord_703553 prefixEnd_703553 120420284970930359783975 := by
  unfold tailWord_703553
  simp only [CollatzResearch.WordTrace]
  refine ⟨25660686020155113131299313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17107124013436742087532875 25660686020155113131299313)
  ·
    refine ⟨19245514515116334848474485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25660686020155113131299313 19245514515116334848474485)
    ·
      refine ⟨1804266985792156392044483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19245514515116334848474485 1804266985792156392044483)
      ·
        refine ⟨2706400478688234588066725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804266985792156392044483 2706400478688234588066725)
        ·
          refine ⟨507450089754043985262511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2706400478688234588066725 507450089754043985262511)
          ·
            refine ⟨761175134631065977893767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507450089754043985262511 761175134631065977893767)
            ·
              refine ⟨1141762701946598966840651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761175134631065977893767 1141762701946598966840651)
              ·
                refine ⟨1712644052919898450260977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141762701946598966840651 1712644052919898450260977)
                ·
                  refine ⟨1284483039689923837695733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1712644052919898450260977 1284483039689923837695733)
                  ·
                    refine ⟨120420284970930359783975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1284483039689923837695733 120420284970930359783975)
                    ·
                      rfl

theorem cell23_703553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_703553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703553 prefixEnd_703553 := by exact prefixLift 703553
  have htrace : WordTrace (prefixWord ++ tailWord_703553) baseStart_703553 baseEnd_703553 := by
    simpa [prefixWord, tailWord_703553, baseEnd_703553] using wordTrace_append hprefix tailTrace_703553
  have hstable : (prefixWord ++ tailWord_703553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703553).length < 2 ^ (prefixWord ++ tailWord_703553).sum := by decide
  have hdescent : baseEnd_703553 < baseStart_703553 := by decide
  rcases family_descends (prefixWord ++ tailWord_703553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703559 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_703559 : Nat := 118140960795 + 703559 * 2 ^ 59
def prefixEnd_703559 : Nat := 4983230072969 + 3 ^ 40 * 703559 * 2
def baseEnd_703559 : Nat := 361263935796718055876897

theorem tailTrace_703559 : CollatzResearch.WordTrace tailWord_703559 prefixEnd_703559 361263935796718055876897 := by
  unfold tailWord_703559
  simp only [CollatzResearch.WordTrace]
  refine ⟨25660904858133376156017731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17107269905422250770678487 25660904858133376156017731)
  ·
    refine ⟨38491357287200064234026597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25660904858133376156017731 38491357287200064234026597)
    ·
      refine ⟨7217129491350012043879987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38491357287200064234026597 7217129491350012043879987)
      ·
        refine ⟨10825694237025018065819981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7217129491350012043879987 10825694237025018065819981)
        ·
          refine ⟨4059635338884381774682493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10825694237025018065819981 4059635338884381774682493)
          ·
            refine ⟨1522363252081643165505935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4059635338884381774682493 1522363252081643165505935)
            ·
              refine ⟨2283544878122464748258903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522363252081643165505935 2283544878122464748258903)
              ·
                refine ⟨3425317317183697122388355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283544878122464748258903 3425317317183697122388355)
                ·
                  refine ⟨5137975975775545683582533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425317317183697122388355 5137975975775545683582533)
                  ·
                    refine ⟨963370495457914815671725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137975975775545683582533 963370495457914815671725)
                    ·
                      refine ⟨361263935796718055876897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 963370495457914815671725 361263935796718055876897)
                      ·
                        rfl

theorem cell23_703559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_703559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703559 prefixEnd_703559 := by exact prefixLift 703559
  have htrace : WordTrace (prefixWord ++ tailWord_703559) baseStart_703559 baseEnd_703559 := by
    simpa [prefixWord, tailWord_703559, baseEnd_703559] using wordTrace_append hprefix tailTrace_703559
  have hstable : (prefixWord ++ tailWord_703559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703559).length < 2 ^ (prefixWord ++ tailWord_703559).sum := by decide
  have hdescent : baseEnd_703559 < baseStart_703559 := by decide
  rcases family_descends (prefixWord ++ tailWord_703559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703599 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 3, 5, 2]
def baseStart_703599 : Nat := 118140960795 + 703599 * 2 ^ 59
def prefixEnd_703599 : Nat := 4983230072969 + 3 ^ 40 * 703599 * 2
def baseEnd_703599 : Nat := 361284475022897899376713

theorem tailTrace_703599 : CollatzResearch.WordTrace tailWord_703599 prefixEnd_703599 361284475022897899376713 := by
  unfold tailWord_703599
  simp only [CollatzResearch.WordTrace]
  refine ⟨25662363777988462987473851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17108242518658975324982567 25662363777988462987473851)
  ·
    refine ⟨38493545666982694481210777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25662363777988462987473851 38493545666982694481210777)
    ·
      refine ⟨28870159250237020860908083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38493545666982694481210777 28870159250237020860908083)
      ·
        refine ⟨43305238875355531291362125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28870159250237020860908083 43305238875355531291362125)
        ·
          refine ⟨16239464578258324234260797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43305238875355531291362125 16239464578258324234260797)
          ·
            refine ⟨6089799216846871587847799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16239464578258324234260797 6089799216846871587847799)
            ·
              refine ⟨9134698825270307381771699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089799216846871587847799 9134698825270307381771699)
              ·
                refine ⟨13702048237905461072657549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9134698825270307381771699 13702048237905461072657549)
                ·
                  refine ⟨5138268089214547902246581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13702048237905461072657549 5138268089214547902246581)
                  ·
                    refine ⟨481712633363863865835617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5138268089214547902246581 481712633363863865835617)
                    ·
                      refine ⟨361284475022897899376713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 481712633363863865835617 361284475022897899376713)
                      ·
                        rfl

theorem cell23_703599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5, 2].length) (baseStart_703599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703599 prefixEnd_703599 := by exact prefixLift 703599
  have htrace : WordTrace (prefixWord ++ tailWord_703599) baseStart_703599 baseEnd_703599 := by
    simpa [prefixWord, tailWord_703599, baseEnd_703599] using wordTrace_append hprefix tailTrace_703599
  have hstable : (prefixWord ++ tailWord_703599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703599).length < 2 ^ (prefixWord ++ tailWord_703599).sum := by decide
  have hdescent : baseEnd_703599 < baseStart_703599 := by decide
  rcases family_descends (prefixWord ++ tailWord_703599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703649 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_703649 : Nat := 118140960795 + 703649 * 2 ^ 59
def prefixEnd_703649 : Nat := 4983230072969 + 3 ^ 40 * 703649 * 2
def baseEnd_703649 : Nat := 361310149055622703751483

theorem tailTrace_703649 : CollatzResearch.WordTrace tailWord_703649 prefixEnd_703649 361310149055622703751483 := by
  unfold tailWord_703649
  simp only [CollatzResearch.WordTrace]
  refine ⟨25664187427807321526794001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17109458285204881017862667 25664187427807321526794001)
  ·
    refine ⟨19248140570855491145095501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25664187427807321526794001 19248140570855491145095501)
    ·
      refine ⟨7218052714070809179410813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19248140570855491145095501 7218052714070809179410813)
      ·
        refine ⟨2706769767776553442279055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7218052714070809179410813 2706769767776553442279055)
        ·
          refine ⟨4060154651664830163418583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706769767776553442279055 4060154651664830163418583)
          ·
            refine ⟨6090231977497245245127875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060154651664830163418583 6090231977497245245127875)
            ·
              refine ⟨9135347966245867867691813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090231977497245245127875 9135347966245867867691813)
              ·
                refine ⟨1712877743671100225192215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9135347966245867867691813 1712877743671100225192215)
                ·
                  refine ⟨2569316615506650337788323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712877743671100225192215 2569316615506650337788323)
                  ·
                    refine ⟨3853974923259975506682485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2569316615506650337788323 3853974923259975506682485)
                    ·
                      refine ⟨361310149055622703751483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3853974923259975506682485 361310149055622703751483)
                      ·
                        rfl

theorem cell23_703649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_703649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_703649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_703649 prefixEnd_703649 := by exact prefixLift 703649
  have htrace : WordTrace (prefixWord ++ tailWord_703649) baseStart_703649 baseEnd_703649 := by
    simpa [prefixWord, tailWord_703649, baseEnd_703649] using wordTrace_append hprefix tailTrace_703649
  have hstable : (prefixWord ++ tailWord_703649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703649).length < 2 ^ (prefixWord ++ tailWord_703649).sum := by decide
  have hdescent : baseEnd_703649 < baseStart_703649 := by decide
  rcases family_descends (prefixWord ++ tailWord_703649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
