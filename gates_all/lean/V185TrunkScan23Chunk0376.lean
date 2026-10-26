import V185TrunkScan23Chunk0375

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2223217 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 6, 2]
def baseStart_2223217 : Nat := 118140960795 + 2223217 * 2 ^ 59
def prefixEnd_2223217 : Nat := 4983230072969 + 3 ^ 40 * 2223217 * 2
def baseEnd_2223217 : Nat := 1141578920246933386963117

theorem tailTrace_2223217 : CollatzResearch.WordTrace tailWord_2223217 prefixEnd_2223217 1141578920246933386963117 := by
  unfold tailWord_2223217
  simp only [CollatzResearch.WordTrace]
  refine ⟨81087385586671979079627905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54058257057781319386418603 81087385586671979079627905)
  ·
    refine ⟨60815539190003984309720929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81087385586671979079627905 60815539190003984309720929)
    ·
      refine ⟨45611654392502988232290697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60815539190003984309720929 45611654392502988232290697)
      ·
        refine ⟨34208740794377241174218023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45611654392502988232290697 34208740794377241174218023)
        ·
          refine ⟨51313111191565861761327035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34208740794377241174218023 51313111191565861761327035)
          ·
            refine ⟨76969666787348792641990553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51313111191565861761327035 76969666787348792641990553)
            ·
              refine ⟨57727250090511594481492915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76969666787348792641990553 57727250090511594481492915)
              ·
                refine ⟨86590875135767391722239373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57727250090511594481492915 86590875135767391722239373)
                ·
                  refine ⟨32471578175912771895839765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86590875135767391722239373 32471578175912771895839765)
                  ·
                    refine ⟨1522105226995911182617489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32471578175912771895839765 1522105226995911182617489)
                    ·
                      refine ⟨1141578920246933386963117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522105226995911182617489 1141578920246933386963117)
                      ·
                        rfl

theorem cell23_2223217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_2223217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223217 prefixEnd_2223217 := by exact prefixLift 2223217
  have htrace : WordTrace (prefixWord ++ tailWord_2223217) baseStart_2223217 baseEnd_2223217 := by
    simpa [prefixWord, tailWord_2223217, baseEnd_2223217] using wordTrace_append hprefix tailTrace_2223217
  have hstable : (prefixWord ++ tailWord_2223217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223217).length < 2 ^ (prefixWord ++ tailWord_2223217).sum := by decide
  have hdescent : baseEnd_2223217 < baseStart_2223217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223271 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2223271 : Nat := 118140960795 + 2223271 * 2 ^ 59
def prefixEnd_2223271 : Nat := 4983230072969 + 3 ^ 40 * 2223271 * 2
def baseEnd_2223271 : Nat := 1141606648202276175687869

theorem tailTrace_2223271 : CollatzResearch.WordTrace tailWord_2223271 prefixEnd_2223271 1141606648202276175687869 := by
  unfold tailWord_2223271
  simp only [CollatzResearch.WordTrace]
  refine ⟨81089355128476346302093667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54059570085650897534729111 81089355128476346302093667)
  ·
    refine ⟨121634032692714519453140501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81089355128476346302093667 121634032692714519453140501)
    ·
      refine ⟨5701595282470993099365961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121634032692714519453140501 5701595282470993099365961)
      ·
        refine ⟨4276196461853244824524471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5701595282470993099365961 4276196461853244824524471)
        ·
          refine ⟨6414294692779867236786707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276196461853244824524471 6414294692779867236786707)
          ·
            refine ⟨9621442039169800855180061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6414294692779867236786707 9621442039169800855180061)
            ·
              refine ⟨3608040764688675320692523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9621442039169800855180061 3608040764688675320692523)
              ·
                refine ⟨5412061147033012981038785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608040764688675320692523 5412061147033012981038785)
                ·
                  refine ⟨4059045860274759735779089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5412061147033012981038785 4059045860274759735779089)
                  ·
                    refine ⟨3044284395206069801834317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4059045860274759735779089 3044284395206069801834317)
                    ·
                      refine ⟨1141606648202276175687869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3044284395206069801834317 1141606648202276175687869)
                      ·
                        rfl

theorem cell23_2223271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2223271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223271 prefixEnd_2223271 := by exact prefixLift 2223271
  have htrace : WordTrace (prefixWord ++ tailWord_2223271) baseStart_2223271 baseEnd_2223271 := by
    simpa [prefixWord, tailWord_2223271, baseEnd_2223271] using wordTrace_append hprefix tailTrace_2223271
  have hstable : (prefixWord ++ tailWord_2223271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223271).length < 2 ^ (prefixWord ++ tailWord_2223271).sum := by decide
  have hdescent : baseEnd_2223271 < baseStart_2223271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223280 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2223280 : Nat := 118140960795 + 2223280 * 2 ^ 59
def prefixEnd_2223280 : Nat := 4983230072969 + 3 ^ 40 * 2223280 * 2
def baseEnd_2223280 : Nat := 1141611269528166640475327

theorem tailTrace_2223280 : CollatzResearch.WordTrace tailWord_2223280 prefixEnd_2223280 1141611269528166640475327 := by
  unfold tailWord_2223280
  simp only [CollatzResearch.WordTrace]
  refine ⟨40544841692721870419585647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54059788923629160559447529 40544841692721870419585647)
  ·
    refine ⟨60817262539082805629378471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40544841692721870419585647 60817262539082805629378471)
    ·
      refine ⟨91225893808624208444067707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60817262539082805629378471 91225893808624208444067707)
      ·
        refine ⟨136838840712936312666101561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91225893808624208444067707 136838840712936312666101561)
        ·
          refine ⟨102629130534702234499576171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136838840712936312666101561 102629130534702234499576171)
          ·
            refine ⟨153943695802053351749364257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102629130534702234499576171 153943695802053351749364257)
            ·
              refine ⟨115457771851540013812023193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153943695802053351749364257 115457771851540013812023193)
              ·
                refine ⟨86593328888655010359017395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115457771851540013812023193 86593328888655010359017395)
                ·
                  refine ⟨129889993332982515538526093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86593328888655010359017395 129889993332982515538526093)
                  ·
                    refine ⟨48708747499868443326947285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129889993332982515538526093 48708747499868443326947285)
                    ·
                      refine ⟨1141611269528166640475327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48708747499868443326947285 1141611269528166640475327)
                      ·
                        rfl

theorem cell23_2223280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2223280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223280 prefixEnd_2223280 := by exact prefixLift 2223280
  have htrace : WordTrace (prefixWord ++ tailWord_2223280) baseStart_2223280 baseEnd_2223280 := by
    simpa [prefixWord, tailWord_2223280, baseEnd_2223280] using wordTrace_append hprefix tailTrace_2223280
  have hstable : (prefixWord ++ tailWord_2223280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223280).length < 2 ^ (prefixWord ++ tailWord_2223280).sum := by decide
  have hdescent : baseEnd_2223280 < baseStart_2223280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223307 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 4]
def baseStart_2223307 : Nat := 118140960795 + 2223307 * 2 ^ 59
def prefixEnd_2223307 : Nat := 4983230072969 + 3 ^ 40 * 2223307 * 2
def baseEnd_2223307 : Nat := 1141625133505838034837703

theorem tailTrace_2223307 : CollatzResearch.WordTrace tailWord_2223307 prefixEnd_2223307 1141625133505838034837703 := by
  unfold tailWord_2223307
  simp only [CollatzResearch.WordTrace]
  refine ⟨81090668156345924450404175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54060445437563949633602783 81090668156345924450404175)
  ·
    refine ⟨121636002234518886675606263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81090668156345924450404175 121636002234518886675606263)
    ·
      refine ⟨182454003351778330013409395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121636002234518886675606263 182454003351778330013409395)
      ·
        refine ⟨273681005027667495020114093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182454003351778330013409395 273681005027667495020114093)
        ·
          refine ⟨102630376885375310632542785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273681005027667495020114093 102630376885375310632542785)
          ·
            refine ⟨76972782664031482974407089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102630376885375310632542785 76972782664031482974407089)
            ·
              refine ⟨57729586998023612230805317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76972782664031482974407089 57729586998023612230805317)
              ·
                refine ⟨10824297562129427293275997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57729586998023612230805317 10824297562129427293275997)
                ·
                  refine ⟨4059111585798535234978499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10824297562129427293275997 4059111585798535234978499)
                  ·
                    refine ⟨6088667378697802852467749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4059111585798535234978499 6088667378697802852467749)
                    ·
                      refine ⟨1141625133505838034837703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6088667378697802852467749 1141625133505838034837703)
                      ·
                        rfl

theorem cell23_2223307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 4].length) (baseStart_2223307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223307 prefixEnd_2223307 := by exact prefixLift 2223307
  have htrace : WordTrace (prefixWord ++ tailWord_2223307) baseStart_2223307 baseEnd_2223307 := by
    simpa [prefixWord, tailWord_2223307, baseEnd_2223307] using wordTrace_append hprefix tailTrace_2223307
  have hstable : (prefixWord ++ tailWord_2223307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223307).length < 2 ^ (prefixWord ++ tailWord_2223307).sum := by decide
  have hdescent : baseEnd_2223307 < baseStart_2223307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223341 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2223341 : Nat := 118140960795 + 2223341 * 2 ^ 59
def prefixEnd_2223341 : Nat := 4983230072969 + 3 ^ 40 * 2223341 * 2
def baseEnd_2223341 : Nat := 1141642591848090901812547

theorem tailTrace_2223341 : CollatzResearch.WordTrace tailWord_2223341 prefixEnd_2223341 1141642591848090901812547 := by
  unfold tailWord_2223341
  simp only [CollatzResearch.WordTrace]
  refine ⟨81091908238222748257141877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54061272158815165504761251 81091908238222748257141877)
  ·
    refine ⟨7602366397333382649107051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81091908238222748257141877 7602366397333382649107051)
    ·
      refine ⟨11403549596000073973660577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7602366397333382649107051 11403549596000073973660577)
      ·
        refine ⟨8552662197000055480245433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11403549596000073973660577 8552662197000055480245433)
        ·
          refine ⟨6414496647750041610184075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8552662197000055480245433 6414496647750041610184075)
          ·
            refine ⟨9621744971625062415276113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6414496647750041610184075 9621744971625062415276113)
            ·
              refine ⟨7216308728718796811457085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9621744971625062415276113 7216308728718796811457085)
              ·
                refine ⟨2706115773269548804296407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7216308728718796811457085 2706115773269548804296407)
                ·
                  refine ⟨4059173659904323206444611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706115773269548804296407 4059173659904323206444611)
                  ·
                    refine ⟨6088760489856484809666917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4059173659904323206444611 6088760489856484809666917)
                    ·
                      refine ⟨1141642591848090901812547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6088760489856484809666917 1141642591848090901812547)
                      ·
                        rfl

theorem cell23_2223341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2223341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223341 prefixEnd_2223341 := by exact prefixLift 2223341
  have htrace : WordTrace (prefixWord ++ tailWord_2223341) baseStart_2223341 baseEnd_2223341 := by
    simpa [prefixWord, tailWord_2223341, baseEnd_2223341] using wordTrace_append hprefix tailTrace_2223341
  have hstable : (prefixWord ++ tailWord_2223341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223341).length < 2 ^ (prefixWord ++ tailWord_2223341).sum := by decide
  have hdescent : baseEnd_2223341 < baseStart_2223341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223347 : List Nat := [1, 1, 1, 2, 2, 7, 9]
def baseStart_2223347 : Nat := 118140960795 + 2223347 * 2 ^ 59
def prefixEnd_2223347 : Nat := 4983230072969 + 3 ^ 40 * 2223347 * 2
def baseEnd_2223347 : Nat := 14094391021382936769599

theorem tailTrace_2223347 : CollatzResearch.WordTrace tailWord_2223347 prefixEnd_2223347 14094391021382936769599 := by
  unfold tailWord_2223347
  simp only [CollatzResearch.WordTrace]
  refine ⟨81092127076201011281860295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54061418050800674187906863 81092127076201011281860295)
  ·
    refine ⟨121638190614301516922790443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81092127076201011281860295 121638190614301516922790443)
    ·
      refine ⟨182457285921452275384185665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121638190614301516922790443 182457285921452275384185665)
      ·
        refine ⟨136842964441089206538139249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182457285921452275384185665 136842964441089206538139249)
        ·
          refine ⟨102632223330816904903604437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136842964441089206538139249 102632223330816904903604437)
          ·
            refine ⟨2405442734316021208678229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 102632223330816904903604437 2405442734316021208678229)
            ·
              refine ⟨14094391021382936769599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2405442734316021208678229 14094391021382936769599)
              ·
                rfl

theorem cell23_2223347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 9].length) (baseStart_2223347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223347 prefixEnd_2223347 := by exact prefixLift 2223347
  have htrace : WordTrace (prefixWord ++ tailWord_2223347) baseStart_2223347 baseEnd_2223347 := by
    simpa [prefixWord, tailWord_2223347, baseEnd_2223347] using wordTrace_append hprefix tailTrace_2223347
  have hstable : (prefixWord ++ tailWord_2223347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223347).length < 2 ^ (prefixWord ++ tailWord_2223347).sum := by decide
  have hdescent : baseEnd_2223347 < baseStart_2223347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223364 : List Nat := [2, 3, 2, 2, 2, 2, 2, 8]
def baseStart_2223364 : Nat := 118140960795 + 2223364 * 2 ^ 59
def prefixEnd_2223364 : Nat := 4983230072969 + 3 ^ 40 * 2223364 * 2
def baseEnd_2223364 : Nat := 42283496366783122660183

theorem tailTrace_2223364 : CollatzResearch.WordTrace tailWord_2223364 prefixEnd_2223364 42283496366783122660183 := by
  unfold tailWord_2223364
  simp only [CollatzResearch.WordTrace]
  refine ⟨40546373558569711592614573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54061831411426282123486097 40546373558569711592614573)
  ·
    refine ⟨15204890084463641847230465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40546373558569711592614573 15204890084463641847230465)
    ·
      refine ⟨11403667563347731385422849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15204890084463641847230465 11403667563347731385422849)
      ·
        refine ⟨8552750672510798539067137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11403667563347731385422849 8552750672510798539067137)
        ·
          refine ⟨6414563004383098904300353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8552750672510798539067137 6414563004383098904300353)
          ·
            refine ⟨4810922253287324178225265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6414563004383098904300353 4810922253287324178225265)
            ·
              refine ⟨3608191689965493133668949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810922253287324178225265 3608191689965493133668949)
              ·
                refine ⟨42283496366783122660183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3608191689965493133668949 42283496366783122660183)
                ·
                  rfl

theorem cell23_2223364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 8].length) (baseStart_2223364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223364 prefixEnd_2223364 := by exact prefixLift 2223364
  have htrace : WordTrace (prefixWord ++ tailWord_2223364) baseStart_2223364 baseEnd_2223364 := by
    simpa [prefixWord, tailWord_2223364, baseEnd_2223364] using wordTrace_append hprefix tailTrace_2223364
  have hstable : (prefixWord ++ tailWord_2223364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223364).length < 2 ^ (prefixWord ++ tailWord_2223364).sum := by decide
  have hdescent : baseEnd_2223364 < baseStart_2223364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223391 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2223391 : Nat := 118140960795 + 2223391 * 2 ^ 59
def prefixEnd_2223391 : Nat := 4983230072969 + 3 ^ 40 * 2223391 * 2
def baseEnd_2223391 : Nat := 1141668265880815706187317

theorem tailTrace_2223391 : CollatzResearch.WordTrace tailWord_2223391 prefixEnd_2223391 1141668265880815706187317 := by
  unfold tailWord_2223391
  simp only [CollatzResearch.WordTrace]
  refine ⟨81093731888041606796462027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54062487925361071197641351 81093731888041606796462027)
  ·
    refine ⟨121640597832062410194693041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81093731888041606796462027 121640597832062410194693041)
    ·
      refine ⟨91230448374046807646019781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121640597832062410194693041 91230448374046807646019781)
      ·
        refine ⟨17105709070133776433628709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91230448374046807646019781 17105709070133776433628709)
        ·
          refine ⟨3207320450650083081305383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17105709070133776433628709 3207320450650083081305383)
          ·
            refine ⟨4810980675975124621958075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207320450650083081305383 4810980675975124621958075)
            ·
              refine ⟨7216471013962686932937113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810980675975124621958075 7216471013962686932937113)
              ·
                refine ⟨5412353260472015199702835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7216471013962686932937113 5412353260472015199702835)
                ·
                  refine ⟨8118529890708022799554253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412353260472015199702835 8118529890708022799554253)
                  ·
                    refine ⟨3044448709015508549832845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8118529890708022799554253 3044448709015508549832845)
                    ·
                      refine ⟨1141668265880815706187317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3044448709015508549832845 1141668265880815706187317)
                      ·
                        rfl

theorem cell23_2223391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2223391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223391 prefixEnd_2223391 := by exact prefixLift 2223391
  have htrace : WordTrace (prefixWord ++ tailWord_2223391) baseStart_2223391 baseEnd_2223391 := by
    simpa [prefixWord, tailWord_2223391, baseEnd_2223391] using wordTrace_append hprefix tailTrace_2223391
  have hstable : (prefixWord ++ tailWord_2223391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223391).length < 2 ^ (prefixWord ++ tailWord_2223391).sum := by decide
  have hdescent : baseEnd_2223391 < baseStart_2223391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223407 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 2, 6]
def baseStart_2223407 : Nat := 118140960795 + 2223407 * 2 ^ 59
def prefixEnd_2223407 : Nat := 4983230072969 + 3 ^ 40 * 2223407 * 2
def baseEnd_2223407 : Nat := 380558827190429214529081

theorem tailTrace_2223407 : CollatzResearch.WordTrace tailWord_2223407 prefixEnd_2223407 380558827190429214529081 := by
  unfold tailWord_2223407
  simp only [CollatzResearch.WordTrace]
  refine ⟨81094315455983641529044475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54062876970655761019362983 81094315455983641529044475)
  ·
    refine ⟨121641473183975462293566713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81094315455983641529044475 121641473183975462293566713)
    ·
      refine ⟨91231104887981596720175035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121641473183975462293566713 91231104887981596720175035)
      ·
        refine ⟨136846657331972395080262553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91231104887981596720175035 136846657331972395080262553)
        ·
          refine ⟨102634992998979296310196915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136846657331972395080262553 102634992998979296310196915)
          ·
            refine ⟨153952489498468944465295373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102634992998979296310196915 153952489498468944465295373)
            ·
              refine ⟨57732183561925854174485765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153952489498468944465295373 57732183561925854174485765)
              ·
                refine ⟨10824784417861097657716081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57732183561925854174485765 10824784417861097657716081)
                ·
                  refine ⟨8118588313395823243287061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10824784417861097657716081 8118588313395823243287061)
                  ·
                    refine ⟨380558827190429214529081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8118588313395823243287061 380558827190429214529081)
                    ·
                      rfl

theorem cell23_2223407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_2223407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223407 prefixEnd_2223407 := by exact prefixLift 2223407
  have htrace : WordTrace (prefixWord ++ tailWord_2223407) baseStart_2223407 baseEnd_2223407 := by
    simpa [prefixWord, tailWord_2223407, baseEnd_2223407] using wordTrace_append hprefix tailTrace_2223407
  have hstable : (prefixWord ++ tailWord_2223407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223407).length < 2 ^ (prefixWord ++ tailWord_2223407).sum := by decide
  have hdescent : baseEnd_2223407 < baseStart_2223407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223431 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_2223431 : Nat := 118140960795 + 2223431 * 2 ^ 59
def prefixEnd_2223431 : Nat := 4983230072969 + 3 ^ 40 * 2223431 * 2
def baseEnd_2223431 : Nat := 1141688805106995549687133

theorem tailTrace_2223431 : CollatzResearch.WordTrace tailWord_2223431 prefixEnd_2223431 1141688805106995549687133 := by
  unfold tailWord_2223431
  simp only [CollatzResearch.WordTrace]
  refine ⟨81095190807896693627918147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54063460538597795751945431 81095190807896693627918147)
  ·
    refine ⟨121642786211845040441877221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81095190807896693627918147 121642786211845040441877221)
    ·
      refine ⟨22808022414720945082851979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121642786211845040441877221 22808022414720945082851979)
      ·
        refine ⟨34212033622081417624277969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22808022414720945082851979 34212033622081417624277969)
        ·
          refine ⟨25659025216561063218208477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34212033622081417624277969 25659025216561063218208477)
          ·
            refine ⟨9622134456210398706828179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25659025216561063218208477 9622134456210398706828179)
            ·
              refine ⟨14433201684315598060242269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9622134456210398706828179 14433201684315598060242269)
              ·
                refine ⟨5412450631618349272590851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14433201684315598060242269 5412450631618349272590851)
                ·
                  refine ⟨8118675947427523908886277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412450631618349272590851 8118675947427523908886277)
                  ·
                    refine ⟨1522251740142660732916177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8118675947427523908886277 1522251740142660732916177)
                    ·
                      refine ⟨1141688805106995549687133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522251740142660732916177 1141688805106995549687133)
                      ·
                        rfl

theorem cell23_2223431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_2223431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223431 prefixEnd_2223431 := by exact prefixLift 2223431
  have htrace : WordTrace (prefixWord ++ tailWord_2223431) baseStart_2223431 baseEnd_2223431 := by
    simpa [prefixWord, tailWord_2223431, baseEnd_2223431] using wordTrace_append hprefix tailTrace_2223431
  have hstable : (prefixWord ++ tailWord_2223431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223431).length < 2 ^ (prefixWord ++ tailWord_2223431).sum := by decide
  have hdescent : baseEnd_2223431 < baseStart_2223431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223444 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2223444 : Nat := 118140960795 + 2223444 * 2 ^ 59
def prefixEnd_2223444 : Nat := 4983230072969 + 3 ^ 40 * 2223444 * 2
def baseEnd_2223444 : Nat := 1141695480355503998824573

theorem tailTrace_2223444 : CollatzResearch.WordTrace tailWord_2223444 prefixEnd_2223444 1141695480355503998824573 := by
  unfold tailWord_2223444
  simp only [CollatzResearch.WordTrace]
  refine ⟨40547832478424798424070693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54063776637899731232094257 40547832478424798424070693)
  ·
    refine ⟨7602718589704649704513255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40547832478424798424070693 7602718589704649704513255)
    ·
      refine ⟨11404077884556974556769883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7602718589704649704513255 11404077884556974556769883)
      ·
        refine ⟨17106116826835461835154825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11404077884556974556769883 17106116826835461835154825)
        ·
          refine ⟨12829587620126596376366119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17106116826835461835154825 12829587620126596376366119)
          ·
            refine ⟨19244381430189894564549179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12829587620126596376366119 19244381430189894564549179)
            ·
              refine ⟨28866572145284841846823769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19244381430189894564549179 28866572145284841846823769)
              ·
                refine ⟨21649929108963631385117827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28866572145284841846823769 21649929108963631385117827)
                ·
                  refine ⟨32474893663445447077676741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21649929108963631385117827 32474893663445447077676741)
                  ·
                    refine ⟨6089042561896021327064389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32474893663445447077676741 6089042561896021327064389)
                    ·
                      refine ⟨1141695480355503998824573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6089042561896021327064389 1141695480355503998824573)
                      ·
                        rfl

theorem cell23_2223444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2223444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223444 prefixEnd_2223444 := by exact prefixLift 2223444
  have htrace : WordTrace (prefixWord ++ tailWord_2223444) baseStart_2223444 baseEnd_2223444 := by
    simpa [prefixWord, tailWord_2223444, baseEnd_2223444] using wordTrace_append hprefix tailTrace_2223444
  have hstable : (prefixWord ++ tailWord_2223444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223444).length < 2 ^ (prefixWord ++ tailWord_2223444).sum := by decide
  have hdescent : baseEnd_2223444 < baseStart_2223444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223446 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2223446 : Nat := 118140960795 + 2223446 * 2 ^ 59
def prefixEnd_2223446 : Nat := 4983230072969 + 3 ^ 40 * 2223446 * 2
def baseEnd_2223446 : Nat := 1141696507316812990999565

theorem tailTrace_2223446 : CollatzResearch.WordTrace tailWord_2223446 prefixEnd_2223446 1141696507316812990999565 := by
  unfold tailWord_2223446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5068483618927646949357137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54063825268561567459809461 5068483618927646949357137)
  ·
    refine ⟨3801362714195735212017853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5068483618927646949357137 3801362714195735212017853)
    ·
      refine ⟨1425511017823400704506695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3801362714195735212017853 1425511017823400704506695)
      ·
        refine ⟨2138266526735101056760043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425511017823400704506695 2138266526735101056760043)
        ·
          refine ⟨3207399790102651585140065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138266526735101056760043 3207399790102651585140065)
          ·
            refine ⟨2405549842576988688855049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3207399790102651585140065 2405549842576988688855049)
            ·
              refine ⟨1804162381932741516641287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405549842576988688855049 1804162381932741516641287)
              ·
                refine ⟨2706243572899112274961931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804162381932741516641287 2706243572899112274961931)
                ·
                  refine ⟨4059365359348668412442897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706243572899112274961931 4059365359348668412442897)
                  ·
                    refine ⟨3044524019511501309332173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4059365359348668412442897 3044524019511501309332173)
                    ·
                      refine ⟨1141696507316812990999565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3044524019511501309332173 1141696507316812990999565)
                      ·
                        rfl

theorem cell23_2223446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2223446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223446 prefixEnd_2223446 := by exact prefixLift 2223446
  have htrace : WordTrace (prefixWord ++ tailWord_2223446) baseStart_2223446 baseEnd_2223446 := by
    simpa [prefixWord, tailWord_2223446, baseEnd_2223446] using wordTrace_append hprefix tailTrace_2223446
  have hstable : (prefixWord ++ tailWord_2223446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223446).length < 2 ^ (prefixWord ++ tailWord_2223446).sum := by decide
  have hdescent : baseEnd_2223446 < baseStart_2223446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223467 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 5, 7]
def baseStart_2223467 : Nat := 118140960795 + 2223467 * 2 ^ 59
def prefixEnd_2223467 : Nat := 4983230072969 + 3 ^ 40 * 2223467 * 2
def baseEnd_2223467 : Nat := 380569096803519136278989

theorem tailTrace_2223467 : CollatzResearch.WordTrace tailWord_2223467 prefixEnd_2223467 380569096803519136278989 := by
  unfold tailWord_2223467
  simp only [CollatzResearch.WordTrace]
  refine ⟨81096503835766271776228655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54064335890510847850819103 81096503835766271776228655)
  ·
    refine ⟨121644755753649407664342983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81096503835766271776228655 121644755753649407664342983)
    ·
      refine ⟨182467133630474111496514475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121644755753649407664342983 182467133630474111496514475)
      ·
        refine ⟨273700700445711167244771713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182467133630474111496514475 273700700445711167244771713)
        ·
          refine ⟨205275525334283375433578785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273700700445711167244771713 205275525334283375433578785)
          ·
            refine ⟨153956644000712531575184089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205275525334283375433578785 153956644000712531575184089)
            ·
              refine ⟨115467483000534398681388067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153956644000712531575184089 115467483000534398681388067)
              ·
                refine ⟨173201224500801598022082101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115467483000534398681388067 173201224500801598022082101)
                ·
                  refine ⟨16237614796950149814570197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173201224500801598022082101 16237614796950149814570197)
                  ·
                    refine ⟨380569096803519136278989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16237614796950149814570197 380569096803519136278989)
                    ·
                      rfl

theorem cell23_2223467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_2223467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223467 prefixEnd_2223467 := by exact prefixLift 2223467
  have htrace : WordTrace (prefixWord ++ tailWord_2223467) baseStart_2223467 baseEnd_2223467 := by
    simpa [prefixWord, tailWord_2223467, baseEnd_2223467] using wordTrace_append hprefix tailTrace_2223467
  have hstable : (prefixWord ++ tailWord_2223467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223467).length < 2 ^ (prefixWord ++ tailWord_2223467).sum := by decide
  have hdescent : baseEnd_2223467 < baseStart_2223467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223528 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2223528 : Nat := 118140960795 + 2223528 * 2 ^ 59
def prefixEnd_2223528 : Nat := 4983230072969 + 3 ^ 40 * 2223528 * 2
def baseEnd_2223528 : Nat := 1141738612730481670174187

theorem tailTrace_2223528 : CollatzResearch.WordTrace tailWord_2223528 prefixEnd_2223528 1141738612730481670174187 := by
  unfold tailWord_2223528
  simp only [CollatzResearch.WordTrace]
  refine ⟨40549364344272639597099619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54065819125696852796132825 40549364344272639597099619)
  ·
    refine ⟨60824046516408959395649429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40549364344272639597099619 60824046516408959395649429)
    ·
      refine ⟨2851127180456669971671067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60824046516408959395649429 2851127180456669971671067)
      ·
        refine ⟨4276690770685004957506601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851127180456669971671067 4276690770685004957506601)
        ·
          refine ⟨3207518078013753718129951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4276690770685004957506601 3207518078013753718129951)
          ·
            refine ⟨4811277117020630577194927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207518078013753718129951 4811277117020630577194927)
            ·
              refine ⟨7216915675530945865792391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811277117020630577194927 7216915675530945865792391)
              ·
                refine ⟨10825373513296418798688587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7216915675530945865792391 10825373513296418798688587)
                ·
                  refine ⟨16238060269944628198032881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10825373513296418798688587 16238060269944628198032881)
                  ·
                    refine ⟨12178545202458471148524661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16238060269944628198032881 12178545202458471148524661)
                    ·
                      refine ⟨1141738612730481670174187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12178545202458471148524661 1141738612730481670174187)
                      ·
                        rfl

theorem cell23_2223528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2223528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223528 prefixEnd_2223528 := by exact prefixLift 2223528
  have htrace : WordTrace (prefixWord ++ tailWord_2223528) baseStart_2223528 baseEnd_2223528 := by
    simpa [prefixWord, tailWord_2223528, baseEnd_2223528] using wordTrace_append hprefix tailTrace_2223528
  have hstable : (prefixWord ++ tailWord_2223528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223528).length < 2 ^ (prefixWord ++ tailWord_2223528).sum := by decide
  have hdescent : baseEnd_2223528 < baseStart_2223528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223591 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2223591 : Nat := 118140960795 + 2223591 * 2 ^ 59
def prefixEnd_2223591 : Nat := 4983230072969 + 3 ^ 40 * 2223591 * 2
def baseEnd_2223591 : Nat := 380590320670571641228799

theorem tailTrace_2223591 : CollatzResearch.WordTrace tailWord_2223591 prefixEnd_2223591 380590320670571641228799 := by
  unfold tailWord_2223591
  simp only [CollatzResearch.WordTrace]
  refine ⟨81101026487317040953742627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54067350991544693969161751 81101026487317040953742627)
  ·
    refine ⟨121651539730975561430613941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81101026487317040953742627 121651539730975561430613941)
    ·
      refine ⟨11404831849778958884120057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121651539730975561430613941 11404831849778958884120057)
      ·
        refine ⟨8553623887334219163090043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11404831849778958884120057 8553623887334219163090043)
        ·
          refine ⟨12830435831001328744635065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8553623887334219163090043 12830435831001328744635065)
          ·
            refine ⟨9622826873250996558476299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12830435831001328744635065 9622826873250996558476299)
            ·
              refine ⟨14434240309876494837714449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9622826873250996558476299 14434240309876494837714449)
              ·
                refine ⟨10825680232407371128285837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14434240309876494837714449 10825680232407371128285837)
                ·
                  refine ⟨4059630087152764173107189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10825680232407371128285837 4059630087152764173107189)
                  ·
                    refine ⟨380590320670571641228799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4059630087152764173107189 380590320670571641228799)
                    ·
                      rfl

theorem cell23_2223591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2223591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223591 prefixEnd_2223591 := by exact prefixLift 2223591
  have htrace : WordTrace (prefixWord ++ tailWord_2223591) baseStart_2223591 baseEnd_2223591 := by
    simpa [prefixWord, tailWord_2223591, baseEnd_2223591] using wordTrace_append hprefix tailTrace_2223591
  have hstable : (prefixWord ++ tailWord_2223591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223591).length < 2 ^ (prefixWord ++ tailWord_2223591).sum := by decide
  have hdescent : baseEnd_2223591 < baseStart_2223591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223598 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_2223598 : Nat := 118140960795 + 2223598 * 2 ^ 59
def prefixEnd_2223598 : Nat := 4983230072969 + 3 ^ 40 * 2223598 * 2
def baseEnd_2223598 : Nat := 1141774556376296396298865

theorem tailTrace_2223598 : CollatzResearch.WordTrace tailWord_2223598 prefixEnd_2223598 1141774556376296396298865 := by
  unfold tailWord_2223598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10137660224786460143655931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54067521198861120766164965 10137660224786460143655931)
  ·
    refine ⟨15206490337179690215483897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10137660224786460143655931 15206490337179690215483897)
    ·
      refine ⟨11404867752884767661612923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15206490337179690215483897 11404867752884767661612923)
      ·
        refine ⟨17107301629327151492419385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11404867752884767661612923 17107301629327151492419385)
        ·
          refine ⟨12830476221995363619314539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17107301629327151492419385 12830476221995363619314539)
          ·
            refine ⟨19245714332993045428971809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12830476221995363619314539 19245714332993045428971809)
            ·
              refine ⟨14434285749744784071728857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19245714332993045428971809 14434285749744784071728857)
              ·
                refine ⟨10825714312308588053796643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14434285749744784071728857 10825714312308588053796643)
                ·
                  refine ⟨16238571468462882080694965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10825714312308588053796643 16238571468462882080694965)
                  ·
                    refine ⟨1522366075168395195065153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16238571468462882080694965 1522366075168395195065153)
                    ·
                      refine ⟨1141774556376296396298865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522366075168395195065153 1141774556376296396298865)
                      ·
                        rfl

theorem cell23_2223598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_2223598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223598 prefixEnd_2223598 := by exact prefixLift 2223598
  have htrace : WordTrace (prefixWord ++ tailWord_2223598) baseStart_2223598 baseEnd_2223598 := by
    simpa [prefixWord, tailWord_2223598, baseEnd_2223598] using wordTrace_append hprefix tailTrace_2223598
  have hstable : (prefixWord ++ tailWord_2223598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223598).length < 2 ^ (prefixWord ++ tailWord_2223598).sum := by decide
  have hdescent : baseEnd_2223598 < baseStart_2223598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223605 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2223605 : Nat := 118140960795 + 2223605 * 2 ^ 59
def prefixEnd_2223605 : Nat := 4983230072969 + 3 ^ 40 * 2223605 * 2
def baseEnd_2223605 : Nat := 1141778150740877868911333

theorem tailTrace_2223605 : CollatzResearch.WordTrace tailWord_2223605 prefixEnd_2223605 1141778150740877868911333 := by
  unfold tailWord_2223605
  simp only [CollatzResearch.WordTrace]
  refine ⟨81101537109266321344752269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54067691406177547563168179 81101537109266321344752269)
  ·
    refine ⟨30413076415974870504282101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81101537109266321344752269 30413076415974870504282101)
    ·
      refine ⟨2851225913997644109776447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30413076415974870504282101 2851225913997644109776447)
      ·
        refine ⟨4276838870996466164664671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851225913997644109776447 4276838870996466164664671)
        ·
          refine ⟨6415258306494699246997007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276838870996466164664671 6415258306494699246997007)
          ·
            refine ⟨9622887459742048870495511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415258306494699246997007 9622887459742048870495511)
            ·
              refine ⟨14434331189613073305743267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9622887459742048870495511 14434331189613073305743267)
              ·
                refine ⟨21651496784419609958614901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14434331189613073305743267 21651496784419609958614901)
                ·
                  refine ⟨2029827823539338433620147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21651496784419609958614901 2029827823539338433620147)
                  ·
                    refine ⟨3044741735309007650430221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2029827823539338433620147 3044741735309007650430221)
                    ·
                      refine ⟨1141778150740877868911333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3044741735309007650430221 1141778150740877868911333)
                      ·
                        rfl

theorem cell23_2223605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2223605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223605 prefixEnd_2223605 := by exact prefixLift 2223605
  have htrace : WordTrace (prefixWord ++ tailWord_2223605) baseStart_2223605 baseEnd_2223605 := by
    simpa [prefixWord, tailWord_2223605, baseEnd_2223605] using wordTrace_append hprefix tailTrace_2223605
  have hstable : (prefixWord ++ tailWord_2223605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223605).length < 2 ^ (prefixWord ++ tailWord_2223605).sum := by decide
  have hdescent : baseEnd_2223605 < baseStart_2223605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223611 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 6, 2]
def baseStart_2223611 : Nat := 118140960795 + 2223611 * 2 ^ 59
def prefixEnd_2223611 : Nat := 4983230072969 + 3 ^ 40 * 2223611 * 2
def baseEnd_2223611 : Nat := 1141781231624804845436305

theorem tailTrace_2223611 : CollatzResearch.WordTrace tailWord_2223611 prefixEnd_2223611 1141781231624804845436305 := by
  unfold tailWord_2223611
  simp only [CollatzResearch.WordTrace]
  refine ⟨81101755947244584369470687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54067837298163056246313791 81101755947244584369470687)
  ·
    refine ⟨121652633920866876554206031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81101755947244584369470687 121652633920866876554206031)
    ·
      refine ⟨182478950881300314831309047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121652633920866876554206031 182478950881300314831309047)
      ·
        refine ⟨273718426321950472246963571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182478950881300314831309047 273718426321950472246963571)
        ·
          refine ⟨410577639482925708370445357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273718426321950472246963571 410577639482925708370445357)
          ·
            refine ⟨153966614806097140638917009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410577639482925708370445357 153966614806097140638917009)
            ·
              refine ⟨115474961104572855479187757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153966614806097140638917009 115474961104572855479187757)
              ·
                refine ⟨43303110414214820804695409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115474961104572855479187757 43303110414214820804695409)
                ·
                  refine ⟨32477332810661115603521557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43303110414214820804695409 32477332810661115603521557)
                  ·
                    refine ⟨1522374975499739793915073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32477332810661115603521557 1522374975499739793915073)
                    ·
                      refine ⟨1141781231624804845436305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522374975499739793915073 1141781231624804845436305)
                      ·
                        rfl

theorem cell23_2223611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6, 2].length) (baseStart_2223611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223611 prefixEnd_2223611 := by exact prefixLift 2223611
  have htrace : WordTrace (prefixWord ++ tailWord_2223611) baseStart_2223611 baseEnd_2223611 := by
    simpa [prefixWord, tailWord_2223611, baseEnd_2223611] using wordTrace_append hprefix tailTrace_2223611
  have hstable : (prefixWord ++ tailWord_2223611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223611).length < 2 ^ (prefixWord ++ tailWord_2223611).sum := by decide
  have hdescent : baseEnd_2223611 < baseStart_2223611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223621 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_2223621 : Nat := 118140960795 + 2223621 * 2 ^ 59
def prefixEnd_2223621 : Nat := 4983230072969 + 3 ^ 40 * 2223621 * 2
def baseEnd_2223621 : Nat := 380595455477116602103753

theorem tailTrace_2223621 : CollatzResearch.WordTrace tailWord_2223621 prefixEnd_2223621 380595455477116602103753 := by
  unfold tailWord_2223621
  simp only [CollatzResearch.WordTrace]
  refine ⟨81102120677208356077334717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54068080451472237384889811 81102120677208356077334717)
  ·
    refine ⟨30413295253953133529000519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81102120677208356077334717 30413295253953133529000519)
    ·
      refine ⟨45619942880929700293500779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30413295253953133529000519 45619942880929700293500779)
      ·
        refine ⟨68429914321394550440251169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45619942880929700293500779 68429914321394550440251169)
        ·
          refine ⟨51322435741045912830188377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68429914321394550440251169 51322435741045912830188377)
          ·
            refine ⟨38491826805784434622641283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51322435741045912830188377 38491826805784434622641283)
            ·
              refine ⟨57737740208676651933961925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38491826805784434622641283 57737740208676651933961925)
              ·
                refine ⟨10825826289126872237617861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57737740208676651933961925 10825826289126872237617861)
                ·
                  refine ⟨2029842429211288544553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10825826289126872237617861 2029842429211288544553349)
                  ·
                    refine ⟨380595455477116602103753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2029842429211288544553349 380595455477116602103753)
                    ·
                      rfl

theorem cell23_2223621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_2223621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223621 prefixEnd_2223621 := by exact prefixLift 2223621
  have htrace : WordTrace (prefixWord ++ tailWord_2223621) baseStart_2223621 baseEnd_2223621 := by
    simpa [prefixWord, tailWord_2223621, baseEnd_2223621] using wordTrace_append hprefix tailTrace_2223621
  have hstable : (prefixWord ++ tailWord_2223621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223621).length < 2 ^ (prefixWord ++ tailWord_2223621).sum := by decide
  have hdescent : baseEnd_2223621 < baseStart_2223621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223629 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2223629 : Nat := 118140960795 + 2223629 * 2 ^ 59
def prefixEnd_2223629 : Nat := 4983230072969 + 3 ^ 40 * 2223629 * 2
def baseEnd_2223629 : Nat := 126865608252953975001247

theorem tailTrace_2223629 : CollatzResearch.WordTrace tailWord_2223629 prefixEnd_2223629 126865608252953975001247 := by
  unfold tailWord_2223629
  simp only [CollatzResearch.WordTrace]
  refine ⟨81102412461179373443625941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54068274974119582295750627 81102412461179373443625941)
  ·
    refine ⟨1900837792058891565084983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 81102412461179373443625941 1900837792058891565084983)
    ·
      refine ⟨2851256688088337347627475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900837792058891565084983 2851256688088337347627475)
      ·
        refine ⟨4276885032132506021441213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851256688088337347627475 4276885032132506021441213)
        ·
          refine ⟨1603831887049689758040455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4276885032132506021441213 1603831887049689758040455)
          ·
            refine ⟨2405747830574534637060683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603831887049689758040455 2405747830574534637060683)
            ·
              refine ⟨3608621745861801955591025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405747830574534637060683 3608621745861801955591025)
              ·
                refine ⟨2706466309396351466693269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608621745861801955591025 2706466309396351466693269)
                ·
                  refine ⟨126865608252953975001247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2706466309396351466693269 126865608252953975001247)
                  ·
                    rfl

theorem cell23_2223629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2223629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223629 prefixEnd_2223629 := by exact prefixLift 2223629
  have htrace : WordTrace (prefixWord ++ tailWord_2223629) baseStart_2223629 baseEnd_2223629 := by
    simpa [prefixWord, tailWord_2223629, baseEnd_2223629] using wordTrace_append hprefix tailTrace_2223629
  have hstable : (prefixWord ++ tailWord_2223629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223629).length < 2 ^ (prefixWord ++ tailWord_2223629).sum := by decide
  have hdescent : baseEnd_2223629 < baseStart_2223629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223648 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2223648 : Nat := 118140960795 + 2223648 * 2 ^ 59
def prefixEnd_2223648 : Nat := 4983230072969 + 3 ^ 40 * 2223648 * 2
def baseEnd_2223648 : Nat := 1141800230409021200673635

theorem tailTrace_2223648 : CollatzResearch.WordTrace tailWord_2223648 prefixEnd_2223648 1141800230409021200673635 := by
  unfold tailWord_2223648
  simp only [CollatzResearch.WordTrace]
  refine ⟨40551552724055269844283799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54068736965407026459045065 40551552724055269844283799)
  ·
    refine ⟨60827329086082904766425699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40551552724055269844283799 60827329086082904766425699)
    ·
      refine ⟨91240993629124357149638549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60827329086082904766425699 91240993629124357149638549)
      ·
        refine ⟨4276921576365204241389307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91240993629124357149638549 4276921576365204241389307)
        ·
          refine ⟨6415382364547806362083961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276921576365204241389307 6415382364547806362083961)
          ·
            refine ⟨4811536773410854771562971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6415382364547806362083961 4811536773410854771562971)
            ·
              refine ⟨7217305160116282157344457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811536773410854771562971 7217305160116282157344457)
              ·
                refine ⟨5412978870087211618008343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217305160116282157344457 5412978870087211618008343)
                ·
                  refine ⟨8119468305130817427012515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412978870087211618008343 8119468305130817427012515)
                  ·
                    refine ⟨12179202457696226140518773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8119468305130817427012515 12179202457696226140518773)
                    ·
                      refine ⟨1141800230409021200673635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12179202457696226140518773 1141800230409021200673635)
                      ·
                        rfl

theorem cell23_2223648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2223648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223648 prefixEnd_2223648 := by exact prefixLift 2223648
  have htrace : WordTrace (prefixWord ++ tailWord_2223648) baseStart_2223648 baseEnd_2223648 := by
    simpa [prefixWord, tailWord_2223648, baseEnd_2223648] using wordTrace_append hprefix tailTrace_2223648
  have hstable : (prefixWord ++ tailWord_2223648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223648).length < 2 ^ (prefixWord ++ tailWord_2223648).sum := by decide
  have hdescent : baseEnd_2223648 < baseStart_2223648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223662 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_2223662 : Nat := 118140960795 + 2223662 * 2 ^ 59
def prefixEnd_2223662 : Nat := 4983230072969 + 3 ^ 40 * 2223662 * 2
def baseEnd_2223662 : Nat := 1141807419138184145898571

theorem tailTrace_2223662 : CollatzResearch.WordTrace tailWord_2223662 prefixEnd_2223662 1141807419138184145898571 := by
  unfold tailWord_2223662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10137952008757477509947155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54069077380039880053051493 10137952008757477509947155)
  ·
    refine ⟨15206928013136216264920733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10137952008757477509947155 15206928013136216264920733)
    ·
      refine ⟨5702598004926081099345275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15206928013136216264920733 5702598004926081099345275)
      ·
        refine ⟨8553897007389121649017913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702598004926081099345275 8553897007389121649017913)
        ·
          refine ⟨6415422755541841236763435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8553897007389121649017913 6415422755541841236763435)
          ·
            refine ⟨9623134133312761855145153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415422755541841236763435 9623134133312761855145153)
            ·
              refine ⟨7217350599984571391358865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9623134133312761855145153 7217350599984571391358865)
              ·
                refine ⟨5413012949988428543519149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217350599984571391358865 5413012949988428543519149)
                ·
                  refine ⟨2029879856245660703819681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5413012949988428543519149 2029879856245660703819681)
                  ·
                    refine ⟨1522409892184245527864761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029879856245660703819681 1522409892184245527864761)
                    ·
                      refine ⟨1141807419138184145898571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522409892184245527864761 1141807419138184145898571)
                      ·
                        rfl

theorem cell23_2223662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_2223662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223662 prefixEnd_2223662 := by exact prefixLift 2223662
  have htrace : WordTrace (prefixWord ++ tailWord_2223662) baseStart_2223662 baseEnd_2223662 := by
    simpa [prefixWord, tailWord_2223662, baseEnd_2223662] using wordTrace_append hprefix tailTrace_2223662
  have hstable : (prefixWord ++ tailWord_2223662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223662).length < 2 ^ (prefixWord ++ tailWord_2223662).sum := by decide
  have hdescent : baseEnd_2223662 < baseStart_2223662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223679 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 1, 2, 2]
def baseStart_2223679 : Nat := 118140960795 + 2223679 * 2 ^ 59
def prefixEnd_2223679 : Nat := 4983230072969 + 3 ^ 40 * 2223679 * 2
def baseEnd_2223679 : Nat := 1141816148309310579385993

theorem tailTrace_2223679 : CollatzResearch.WordTrace tailWord_2223679 prefixEnd_2223679 1141816148309310579385993 := by
  unfold tailWord_2223679
  simp only [CollatzResearch.WordTrace]
  refine ⟨81104236110998231982946091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54069490740665487988630727 81104236110998231982946091)
  ·
    refine ⟨121656354166497347974419137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81104236110998231982946091 121656354166497347974419137)
    ·
      refine ⟨91242265624873010980814353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121656354166497347974419137 91242265624873010980814353)
      ·
        refine ⟨68431699218654758235610765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91242265624873010980814353 68431699218654758235610765)
        ·
          refine ⟨25661887206995534338354037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68431699218654758235610765 25661887206995534338354037)
          ·
            refine ⟨2405801925655831344220691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25661887206995534338354037 2405801925655831344220691)
            ·
              refine ⟨3608702888483747016331037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405801925655831344220691 3608702888483747016331037)
              ·
                refine ⟨1353263583181405131124139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3608702888483747016331037 1353263583181405131124139)
                ·
                  refine ⟨2029895374772107696686209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353263583181405131124139 2029895374772107696686209)
                  ·
                    refine ⟨1522421531079080772514657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029895374772107696686209 1522421531079080772514657)
                    ·
                      refine ⟨1141816148309310579385993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522421531079080772514657 1141816148309310579385993)
                      ·
                        rfl

theorem cell23_2223679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_2223679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223679 prefixEnd_2223679 := by exact prefixLift 2223679
  have htrace : WordTrace (prefixWord ++ tailWord_2223679) baseStart_2223679 baseEnd_2223679 := by
    simpa [prefixWord, tailWord_2223679, baseEnd_2223679] using wordTrace_append hprefix tailTrace_2223679
  have hstable : (prefixWord ++ tailWord_2223679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223679).length < 2 ^ (prefixWord ++ tailWord_2223679).sum := by decide
  have hdescent : baseEnd_2223679 < baseStart_2223679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223688 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_2223688 : Nat := 118140960795 + 2223688 * 2 ^ 59
def prefixEnd_2223688 : Nat := 4983230072969 + 3 ^ 40 * 2223688 * 2
def baseEnd_2223688 : Nat := 1141820769635201044173451

theorem tailTrace_2223688 : CollatzResearch.WordTrace tailWord_2223688 prefixEnd_2223688 1141820769635201044173451 := by
  unfold tailWord_2223688
  simp only [CollatzResearch.WordTrace]
  refine ⟨40552282183982813260011859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54069709578643751013349145 40552282183982813260011859)
  ·
    refine ⟨60828423275974219890017789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40552282183982813260011859 60828423275974219890017789)
    ·
      refine ⟨22810658728490332458756671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60828423275974219890017789 22810658728490332458756671)
      ·
        refine ⟨34215988092735498688135007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22810658728490332458756671 34215988092735498688135007)
        ·
          refine ⟨51323982139103248032202511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34215988092735498688135007 51323982139103248032202511)
          ·
            refine ⟨76985973208654872048303767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51323982139103248032202511 76985973208654872048303767)
            ·
              refine ⟨115478959812982308072455651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76985973208654872048303767 115478959812982308072455651)
              ·
                refine ⟨173218439719473462108683477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115478959812982308072455651 173218439719473462108683477)
                ·
                  refine ⟨4059807180925159268172269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 173218439719473462108683477 4059807180925159268172269)
                  ·
                    refine ⟨1522427692846934725564601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4059807180925159268172269 1522427692846934725564601)
                    ·
                      refine ⟨1141820769635201044173451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522427692846934725564601 1141820769635201044173451)
                      ·
                        rfl

theorem cell23_2223688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_2223688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223688 prefixEnd_2223688 := by exact prefixLift 2223688
  have htrace : WordTrace (prefixWord ++ tailWord_2223688) baseStart_2223688 baseEnd_2223688 := by
    simpa [prefixWord, tailWord_2223688, baseEnd_2223688] using wordTrace_append hprefix tailTrace_2223688
  have hstable : (prefixWord ++ tailWord_2223688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223688).length < 2 ^ (prefixWord ++ tailWord_2223688).sum := by decide
  have hdescent : baseEnd_2223688 < baseStart_2223688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223701 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2223701 : Nat := 118140960795 + 2223701 * 2 ^ 59
def prefixEnd_2223701 : Nat := 4983230072969 + 3 ^ 40 * 2223701 * 2
def baseEnd_2223701 : Nat := 1141827444883709493310891

theorem tailTrace_2223701 : CollatzResearch.WordTrace tailWord_2223701 prefixEnd_2223701 1141827444883709493310891 := by
  unfold tailWord_2223701
  simp only [CollatzResearch.WordTrace]
  refine ⟨81105038516918529740246957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54070025677945686493497971 81105038516918529740246957)
  ·
    refine ⟨30414389443844448652592609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81105038516918529740246957 30414389443844448652592609)
    ·
      refine ⟨22810792082883336489444457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30414389443844448652592609 22810792082883336489444457)
      ·
        refine ⟨17108094062162502367083343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22810792082883336489444457 17108094062162502367083343)
        ·
          refine ⟨25662141093243753550625015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17108094062162502367083343 25662141093243753550625015)
          ·
            refine ⟨38493211639865630325937523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25662141093243753550625015 38493211639865630325937523)
            ·
              refine ⟨57739817459798445488906285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38493211639865630325937523 57739817459798445488906285)
              ·
                refine ⟨21652431547424417058339857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57739817459798445488906285 21652431547424417058339857)
                ·
                  refine ⟨16239323660568312793754893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21652431547424417058339857 16239323660568312793754893)
                  ·
                    refine ⟨6089746372713117297658085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16239323660568312793754893 6089746372713117297658085)
                    ·
                      refine ⟨1141827444883709493310891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6089746372713117297658085 1141827444883709493310891)
                      ·
                        rfl

theorem cell23_2223701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2223701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223701 prefixEnd_2223701 := by exact prefixLift 2223701
  have htrace : WordTrace (prefixWord ++ tailWord_2223701) baseStart_2223701 baseEnd_2223701 := by
    simpa [prefixWord, tailWord_2223701, baseEnd_2223701] using wordTrace_append hprefix tailTrace_2223701
  have hstable : (prefixWord ++ tailWord_2223701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223701).length < 2 ^ (prefixWord ++ tailWord_2223701).sum := by decide
  have hdescent : baseEnd_2223701 < baseStart_2223701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223702 : List Nat := [5, 2, 2, 2, 1, 1, 2, 8]
def baseStart_2223702 : Nat := 118140960795 + 2223702 * 2 ^ 59
def prefixEnd_2223702 : Nat := 4983230072969 + 3 ^ 40 * 2223702 * 2
def baseEnd_2223702 : Nat := 42289924383865332940681

theorem tailTrace_2223702 : CollatzResearch.WordTrace tailWord_2223702 prefixEnd_2223702 42289924383865332940681 := by
  unfold tailWord_2223702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069067186869681681939585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54070049993276604607355573 5069067186869681681939585)
  ·
    refine ⟨3801800390152261261454689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5069067186869681681939585 3801800390152261261454689)
    ·
      refine ⟨2851350292614195946091017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3801800390152261261454689 2851350292614195946091017)
      ·
        refine ⟨2138512719460646959568263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2851350292614195946091017 2138512719460646959568263)
        ·
          refine ⟨3207769079190970439352395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138512719460646959568263 3207769079190970439352395)
          ·
            refine ⟨4811653618786455659028593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207769079190970439352395 4811653618786455659028593)
            ·
              refine ⟨3608740214089841744271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4811653618786455659028593 3608740214089841744271445)
              ·
                refine ⟨42289924383865332940681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3608740214089841744271445 42289924383865332940681)
                ·
                  rfl

theorem cell23_2223702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_2223702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223702 prefixEnd_2223702 := by exact prefixLift 2223702
  have htrace : WordTrace (prefixWord ++ tailWord_2223702) baseStart_2223702 baseEnd_2223702 := by
    simpa [prefixWord, tailWord_2223702, baseEnd_2223702] using wordTrace_append hprefix tailTrace_2223702
  have hstable : (prefixWord ++ tailWord_2223702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223702).length < 2 ^ (prefixWord ++ tailWord_2223702).sum := by decide
  have hdescent : baseEnd_2223702 < baseStart_2223702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223721 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_2223721 : Nat := 118140960795 + 2223721 * 2 ^ 59
def prefixEnd_2223721 : Nat := 4983230072969 + 3 ^ 40 * 2223721 * 2
def baseEnd_2223721 : Nat := 1141837714496799415060799

theorem tailTrace_2223721 : CollatzResearch.WordTrace tailWord_2223721 prefixEnd_2223721 1141837714496799415060799 := by
  unfold tailWord_2223721
  simp only [CollatzResearch.WordTrace]
  refine ⟨81105767976846073155975017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54070511984564048770650011 81105767976846073155975017)
  ·
    refine ⟨60829325982634554866981263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81105767976846073155975017 60829325982634554866981263)
    ·
      refine ⟨91243988973951832300471895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60829325982634554866981263 91243988973951832300471895)
      ·
        refine ⟨136865983460927748450707843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91243988973951832300471895 136865983460927748450707843)
        ·
          refine ⟨205298975191391622676061765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136865983460927748450707843 205298975191391622676061765)
          ·
            refine ⟨38493557848385929251761581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205298975191391622676061765 38493557848385929251761581)
            ·
              refine ⟨14435084193144723469410593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38493557848385929251761581 14435084193144723469410593)
              ·
                refine ⟨10826313144858542602057945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14435084193144723469410593 10826313144858542602057945)
                ·
                  refine ⟨8119734858643906951543459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10826313144858542602057945 8119734858643906951543459)
                  ·
                    refine ⟨12179602287965860427315189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8119734858643906951543459 12179602287965860427315189)
                    ·
                      refine ⟨1141837714496799415060799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12179602287965860427315189 1141837714496799415060799)
                      ·
                        rfl

theorem cell23_2223721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_2223721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223721 prefixEnd_2223721 := by exact prefixLift 2223721
  have htrace : WordTrace (prefixWord ++ tailWord_2223721) baseStart_2223721 baseEnd_2223721 := by
    simpa [prefixWord, tailWord_2223721, baseEnd_2223721] using wordTrace_append hprefix tailTrace_2223721
  have hstable : (prefixWord ++ tailWord_2223721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223721).length < 2 ^ (prefixWord ++ tailWord_2223721).sum := by decide
  have hdescent : baseEnd_2223721 < baseStart_2223721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223722 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2223722 : Nat := 118140960795 + 2223722 * 2 ^ 59
def prefixEnd_2223722 : Nat := 4983230072969 + 3 ^ 40 * 2223722 * 2
def baseEnd_2223722 : Nat := 1141838227977453911148295

theorem tailTrace_2223722 : CollatzResearch.WordTrace tailWord_2223722 prefixEnd_2223722 1141838227977453911148295 := by
  unfold tailWord_2223722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20276451112460612581690355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54070536299894966884507613 20276451112460612581690355)
  ·
    refine ⟨30414676668690918872535533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20276451112460612581690355 30414676668690918872535533)
    ·
      refine ⟨11405503750759094577200825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30414676668690918872535533 11405503750759094577200825)
      ·
        refine ⟨8554127813069320932900619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11405503750759094577200825 8554127813069320932900619)
        ·
          refine ⟨12831191719603981399350929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8554127813069320932900619 12831191719603981399350929)
          ·
            refine ⟨9623393789702986049513197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12831191719603981399350929 9623393789702986049513197)
            ·
              refine ⟨3608772671138619768567449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9623393789702986049513197 3608772671138619768567449)
              ·
                refine ⟨2706579503353964826425587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608772671138619768567449 2706579503353964826425587)
                ·
                  refine ⟨4059869255030947239638381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706579503353964826425587 4059869255030947239638381)
                  ·
                    refine ⟨1522450970636605214864393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4059869255030947239638381 1522450970636605214864393)
                    ·
                      refine ⟨1141838227977453911148295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522450970636605214864393 1141838227977453911148295)
                      ·
                        rfl

theorem cell23_2223722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2223722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223722 prefixEnd_2223722 := by exact prefixLift 2223722
  have htrace : WordTrace (prefixWord ++ tailWord_2223722) baseStart_2223722 baseEnd_2223722 := by
    simpa [prefixWord, tailWord_2223722, baseEnd_2223722] using wordTrace_append hprefix tailTrace_2223722
  have hstable : (prefixWord ++ tailWord_2223722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223722).length < 2 ^ (prefixWord ++ tailWord_2223722).sum := by decide
  have hdescent : baseEnd_2223722 < baseStart_2223722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223768 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2223768 : Nat := 118140960795 + 2223768 * 2 ^ 59
def prefixEnd_2223768 : Nat := 4983230072969 + 3 ^ 40 * 2223768 * 2
def baseEnd_2223768 : Nat := 1141861848087560731173083

theorem tailTrace_2223768 : CollatzResearch.WordTrace tailWord_2223768 prefixEnd_2223768 1141861848087560731173083 := by
  unfold tailWord_2223768
  simp only [CollatzResearch.WordTrace]
  refine ⟨40553741103837900091467979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54071654805117200121957305 40553741103837900091467979)
  ·
    refine ⟨60830611655756850137201969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40553741103837900091467979 60830611655756850137201969)
    ·
      refine ⟨45622958741817637602901477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60830611655756850137201969 45622958741817637602901477)
      ·
        refine ⟨8554304764090807050544027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45622958741817637602901477 8554304764090807050544027)
        ·
          refine ⟨12831457146136210575816041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8554304764090807050544027 12831457146136210575816041)
          ·
            refine ⟨9623592859602157931862031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12831457146136210575816041 9623592859602157931862031)
            ·
              refine ⟨14435389289403236897793047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9623592859602157931862031 14435389289403236897793047)
              ·
                refine ⟨21653083934104855346689571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14435389289403236897793047 21653083934104855346689571)
                ·
                  refine ⟨32479625901157283020034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21653083934104855346689571 32479625901157283020034357)
                  ·
                    refine ⟨3044964928233495283128221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32479625901157283020034357 3044964928233495283128221)
                    ·
                      refine ⟨1141861848087560731173083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3044964928233495283128221 1141861848087560731173083)
                      ·
                        rfl

theorem cell23_2223768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2223768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223768 prefixEnd_2223768 := by exact prefixLift 2223768
  have htrace : WordTrace (prefixWord ++ tailWord_2223768) baseStart_2223768 baseEnd_2223768 := by
    simpa [prefixWord, tailWord_2223768, baseEnd_2223768] using wordTrace_append hprefix tailTrace_2223768
  have hstable : (prefixWord ++ tailWord_2223768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223768).length < 2 ^ (prefixWord ++ tailWord_2223768).sum := by decide
  have hdescent : baseEnd_2223768 < baseStart_2223768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223775 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 7]
def baseStart_2223775 : Nat := 118140960795 + 2223775 * 2 ^ 59
def prefixEnd_2223775 : Nat := 4983230072969 + 3 ^ 40 * 2223775 * 2
def baseEnd_2223775 : Nat := 126873938050238022642839

theorem tailTrace_2223775 : CollatzResearch.WordTrace tailWord_2223775 prefixEnd_2223775 126873938050238022642839 := by
  unfold tailWord_2223775
  simp only [CollatzResearch.WordTrace]
  refine ⟨81107737518650440378440779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54071825012433626918960519 81107737518650440378440779)
  ·
    refine ⟨121661606277975660567661169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81107737518650440378440779 121661606277975660567661169)
    ·
      refine ⟨91246204708481745425745877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121661606277975660567661169 91246204708481745425745877)
      ·
        refine ⟨2138582922855040908415919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 91246204708481745425745877 2138582922855040908415919)
        ·
          refine ⟨3207874384282561362623879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138582922855040908415919 3207874384282561362623879)
          ·
            refine ⟨4811811576423842043935819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207874384282561362623879 4811811576423842043935819)
            ·
              refine ⟨7217717364635763065903729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811811576423842043935819 7217717364635763065903729)
              ·
                refine ⟨5413288023476822299427797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217717364635763065903729 5413288023476822299427797)
                ·
                  refine ⟨126873938050238022642839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5413288023476822299427797 126873938050238022642839)
                  ·
                    rfl

theorem cell23_2223775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 7].length) (baseStart_2223775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223775 prefixEnd_2223775 := by exact prefixLift 2223775
  have htrace : WordTrace (prefixWord ++ tailWord_2223775) baseStart_2223775 baseEnd_2223775 := by
    simpa [prefixWord, tailWord_2223775, baseEnd_2223775] using wordTrace_append hprefix tailTrace_2223775
  have hstable : (prefixWord ++ tailWord_2223775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223775).length < 2 ^ (prefixWord ++ tailWord_2223775).sum := by decide
  have hdescent : baseEnd_2223775 < baseStart_2223775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223781 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_2223781 : Nat := 118140960795 + 2223781 * 2 ^ 59
def prefixEnd_2223781 : Nat := 4983230072969 + 3 ^ 40 * 2223781 * 2
def baseEnd_2223781 : Nat := 1141868523336069180310523

theorem tailTrace_2223781 : CollatzResearch.WordTrace tailWord_2223781 prefixEnd_2223781 1141868523336069180310523 := by
  unfold tailWord_2223781
  simp only [CollatzResearch.WordTrace]
  refine ⟨81107956356628703403159197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54071970904419135602106131 81107956356628703403159197)
  ·
    refine ⟨30415483633735763776184699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81107956356628703403159197 30415483633735763776184699)
    ·
      refine ⟨45623225450603645664277049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30415483633735763776184699 45623225450603645664277049)
      ·
        refine ⟨34217419087952734248207787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45623225450603645664277049 34217419087952734248207787)
        ·
          refine ⟨51326128631929101372311681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34217419087952734248207787 51326128631929101372311681)
          ·
            refine ⟨38494596473946826029233761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51326128631929101372311681 38494596473946826029233761)
            ·
              refine ⟨28870947355460119521925321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38494596473946826029233761 28870947355460119521925321)
              ·
                refine ⟨21653210516595089641443991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28870947355460119521925321 21653210516595089641443991)
                ·
                  refine ⟨32479815774892634462165987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21653210516595089641443991 32479815774892634462165987)
                  ·
                    refine ⟨48719723662338951693248981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32479815774892634462165987 48719723662338951693248981)
                    ·
                      refine ⟨1141868523336069180310523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48719723662338951693248981 1141868523336069180310523)
                      ·
                        rfl

theorem cell23_2223781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_2223781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223781 prefixEnd_2223781 := by exact prefixLift 2223781
  have htrace : WordTrace (prefixWord ++ tailWord_2223781) baseStart_2223781 baseEnd_2223781 := by
    simpa [prefixWord, tailWord_2223781, baseEnd_2223781] using wordTrace_append hprefix tailTrace_2223781
  have hstable : (prefixWord ++ tailWord_2223781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223781).length < 2 ^ (prefixWord ++ tailWord_2223781).sum := by decide
  have hdescent : baseEnd_2223781 < baseStart_2223781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223808 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_2223808 : Nat := 118140960795 + 2223808 * 2 ^ 59
def prefixEnd_2223808 : Nat := 4983230072969 + 3 ^ 40 * 2223808 * 2
def baseEnd_2223808 : Nat := 1141882387313740574672899

theorem tailTrace_2223808 : CollatzResearch.WordTrace tailWord_2223808 prefixEnd_2223808 1141882387313740574672899 := by
  unfold tailWord_2223808
  simp only [CollatzResearch.WordTrace]
  refine ⟨40554470563765443507196039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54072627418353924676261385 40554470563765443507196039)
  ·
    refine ⟨60831705845648165260794059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40554470563765443507196039 60831705845648165260794059)
    ·
      refine ⟨91247558768472247891191089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60831705845648165260794059 91247558768472247891191089)
      ·
        refine ⟨68435669076354185918393317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91247558768472247891191089 68435669076354185918393317)
        ·
          refine ⟨12831687951816409859698747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68435669076354185918393317 12831687951816409859698747)
          ·
            refine ⟨19247531927724614789548121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12831687951816409859698747 19247531927724614789548121)
            ·
              refine ⟨14435648945793461092161091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19247531927724614789548121 14435648945793461092161091)
              ·
                refine ⟨21653473418690191638241637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14435648945793461092161091 21653473418690191638241637)
                ·
                  refine ⟨4060026266004410932170307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21653473418690191638241637 4060026266004410932170307)
                  ·
                    refine ⟨6090039399006616398255461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4060026266004410932170307 6090039399006616398255461)
                    ·
                      refine ⟨1141882387313740574672899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6090039399006616398255461 1141882387313740574672899)
                      ·
                        rfl

theorem cell23_2223808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_2223808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223808 prefixEnd_2223808 := by exact prefixLift 2223808
  have htrace : WordTrace (prefixWord ++ tailWord_2223808) baseStart_2223808 baseEnd_2223808 := by
    simpa [prefixWord, tailWord_2223808, baseEnd_2223808] using wordTrace_append hprefix tailTrace_2223808
  have hstable : (prefixWord ++ tailWord_2223808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223808).length < 2 ^ (prefixWord ++ tailWord_2223808).sum := by decide
  have hdescent : baseEnd_2223808 < baseStart_2223808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223825 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 2, 4, 2]
def baseStart_2223825 : Nat := 118140960795 + 2223825 * 2 ^ 59
def prefixEnd_2223825 : Nat := 4983230072969 + 3 ^ 40 * 2223825 * 2
def baseEnd_2223825 : Nat := 1141891116484867008160321

theorem tailTrace_2223825 : CollatzResearch.WordTrace tailWord_2223825 prefixEnd_2223825 1141891116484867008160321 := by
  unfold tailWord_2223825
  simp only [CollatzResearch.WordTrace]
  refine ⟨81109561168469298917760929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54073040778979532611840619 81109561168469298917760929)
  ·
    refine ⟨60832170876351974188320697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81109561168469298917760929 60832170876351974188320697)
    ·
      refine ⟨45624128157263980641240523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60832170876351974188320697 45624128157263980641240523)
      ·
        refine ⟨68436192235895970961860785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45624128157263980641240523 68436192235895970961860785)
        ·
          refine ⟨51327144176921978221395589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68436192235895970961860785 51327144176921978221395589)
          ·
            refine ⟨9623839533172870916511673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51327144176921978221395589 9623839533172870916511673)
            ·
              refine ⟨7217879649879653187383755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9623839533172870916511673 7217879649879653187383755)
              ·
                refine ⟨10826819474819479781075633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7217879649879653187383755 10826819474819479781075633)
                ·
                  refine ⟨8120114606114609835806725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10826819474819479781075633 8120114606114609835806725)
                  ·
                    refine ⟨1522521488646489344213761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8120114606114609835806725 1522521488646489344213761)
                    ·
                      refine ⟨1141891116484867008160321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522521488646489344213761 1141891116484867008160321)
                      ·
                        rfl

theorem cell23_2223825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_2223825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223825 prefixEnd_2223825 := by exact prefixLift 2223825
  have htrace : WordTrace (prefixWord ++ tailWord_2223825) baseStart_2223825 baseEnd_2223825 := by
    simpa [prefixWord, tailWord_2223825, baseEnd_2223825] using wordTrace_append hprefix tailTrace_2223825
  have hstable : (prefixWord ++ tailWord_2223825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223825).length < 2 ^ (prefixWord ++ tailWord_2223825).sum := by decide
  have hdescent : baseEnd_2223825 < baseStart_2223825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223845 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2223845 : Nat := 118140960795 + 2223845 * 2 ^ 59
def prefixEnd_2223845 : Nat := 4983230072969 + 3 ^ 40 * 2223845 * 2
def baseEnd_2223845 : Nat := 1141901386097956929910229

theorem tailTrace_2223845 : CollatzResearch.WordTrace tailWord_2223845 prefixEnd_2223845 1141901386097956929910229 := by
  unfold tailWord_2223845
  simp only [CollatzResearch.WordTrace]
  refine ⟨81110290628396842333488989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54073527085597894888992659 81110290628396842333488989)
  ·
    refine ⟨30416358985648815875058371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81110290628396842333488989 30416358985648815875058371)
    ·
      refine ⟨45624538478473223812587557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30416358985648815875058371 45624538478473223812587557)
      ·
        refine ⟨8554600964713729464860167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45624538478473223812587557 8554600964713729464860167)
        ·
          refine ⟨12831901447070594197290251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8554600964713729464860167 12831901447070594197290251)
          ·
            refine ⟨19247852170605891295935377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12831901447070594197290251 19247852170605891295935377)
            ·
              refine ⟨14435889127954418471951533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19247852170605891295935377 14435889127954418471951533)
              ·
                refine ⟨5413458422982906926981825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14435889127954418471951533 5413458422982906926981825)
                ·
                  refine ⟨4060093817237180195236369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5413458422982906926981825 4060093817237180195236369)
                  ·
                    refine ⟨3045070362927885146427277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4060093817237180195236369 3045070362927885146427277)
                    ·
                      refine ⟨1141901386097956929910229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3045070362927885146427277 1141901386097956929910229)
                      ·
                        rfl

theorem cell23_2223845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2223845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223845 prefixEnd_2223845 := by exact prefixLift 2223845
  have htrace : WordTrace (prefixWord ++ tailWord_2223845) baseStart_2223845 baseEnd_2223845 := by
    simpa [prefixWord, tailWord_2223845, baseEnd_2223845] using wordTrace_append hprefix tailTrace_2223845
  have hstable : (prefixWord ++ tailWord_2223845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223845).length < 2 ^ (prefixWord ++ tailWord_2223845).sum := by decide
  have hdescent : baseEnd_2223845 < baseStart_2223845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223848 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 8]
def baseStart_2223848 : Nat := 118140960795 + 2223848 * 2 ^ 59
def prefixEnd_2223848 : Nat := 4983230072969 + 3 ^ 40 * 2223848 * 2
def baseEnd_2223848 : Nat := 126878102948880046463635

theorem tailTrace_2223848 : CollatzResearch.WordTrace tailWord_2223848 prefixEnd_2223848 126878102948880046463635 := by
  unfold tailWord_2223848
  simp only [CollatzResearch.WordTrace]
  refine ⟨40555200023692986922924099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54073600031590649230565465 40555200023692986922924099)
  ·
    refine ⟨60832800035539480384386149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40555200023692986922924099 60832800035539480384386149)
    ·
      refine ⟨11406150006663652572072403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60832800035539480384386149 11406150006663652572072403)
      ·
        refine ⟨17109225009995478858108605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11406150006663652572072403 17109225009995478858108605)
        ·
          refine ⟨6415959378748304571790727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17109225009995478858108605 6415959378748304571790727)
          ·
            refine ⟨9623939068122456857686091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415959378748304571790727 9623939068122456857686091)
            ·
              refine ⟨14435908602183685286529137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9623939068122456857686091 14435908602183685286529137)
              ·
                refine ⟨10826931451637763964896853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14435908602183685286529137 10826931451637763964896853)
                ·
                  refine ⟨126878102948880046463635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10826931451637763964896853 126878102948880046463635)
                  ·
                    rfl

theorem cell23_2223848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_2223848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223848 prefixEnd_2223848 := by exact prefixLift 2223848
  have htrace : WordTrace (prefixWord ++ tailWord_2223848) baseStart_2223848 baseEnd_2223848 := by
    simpa [prefixWord, tailWord_2223848, baseEnd_2223848] using wordTrace_append hprefix tailTrace_2223848
  have hstable : (prefixWord ++ tailWord_2223848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223848).length < 2 ^ (prefixWord ++ tailWord_2223848).sum := by decide
  have hdescent : baseEnd_2223848 < baseStart_2223848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223852 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_2223852 : Nat := 118140960795 + 2223852 * 2 ^ 59
def prefixEnd_2223852 : Nat := 4983230072969 + 3 ^ 40 * 2223852 * 2
def baseEnd_2223852 : Nat := 380634993487512800840899

theorem tailTrace_2223852 : CollatzResearch.WordTrace tailWord_2223852 prefixEnd_2223852 380634993487512800840899 := by
  unfold tailWord_2223852
  simp only [CollatzResearch.WordTrace]
  refine ⟨40555272969685741264496905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54073697292914321685995873 40555272969685741264496905)
  ·
    refine ⟨30416454727264305948372679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40555272969685741264496905 30416454727264305948372679)
    ·
      refine ⟨45624682090896458922559019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30416454727264305948372679 45624682090896458922559019)
      ·
        refine ⟨68437023136344688383838529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45624682090896458922559019 68437023136344688383838529)
        ·
          refine ⟨51327767352258516287878897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68437023136344688383838529 51327767352258516287878897)
          ·
            refine ⟨38495825514193887215909173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51327767352258516287878897 38495825514193887215909173)
            ·
              refine ⟨3608983641955676926491485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38495825514193887215909173 3608983641955676926491485)
              ·
                refine ⟨1353368865733378847434307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3608983641955676926491485 1353368865733378847434307)
                ·
                  refine ⟨2030053298600068271151461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353368865733378847434307 2030053298600068271151461)
                  ·
                    refine ⟨380634993487512800840899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2030053298600068271151461 380634993487512800840899)
                    ·
                      rfl

theorem cell23_2223852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_2223852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223852 prefixEnd_2223852 := by exact prefixLift 2223852
  have htrace : WordTrace (prefixWord ++ tailWord_2223852) baseStart_2223852 baseEnd_2223852 := by
    simpa [prefixWord, tailWord_2223852, baseEnd_2223852] using wordTrace_append hprefix tailTrace_2223852
  have hstable : (prefixWord ++ tailWord_2223852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223852).length < 2 ^ (prefixWord ++ tailWord_2223852).sum := by decide
  have hdescent : baseEnd_2223852 < baseStart_2223852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223862 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2223862 : Nat := 118140960795 + 2223862 * 2 ^ 59
def prefixEnd_2223862 : Nat := 4983230072969 + 3 ^ 40 * 2223862 * 2
def baseEnd_2223862 : Nat := 1141910115269083363397651

theorem tailTrace_2223862 : CollatzResearch.WordTrace tailWord_2223862 prefixEnd_2223862 1141910115269083363397651 := by
  unfold tailWord_2223862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069431916833453389803615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54073940446223502824571893 5069431916833453389803615)
  ·
    refine ⟨7604147875250180084705423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069431916833453389803615 7604147875250180084705423)
    ·
      refine ⟨11406221812875270127058135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7604147875250180084705423 11406221812875270127058135)
      ·
        refine ⟨17109332719312905190587203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11406221812875270127058135 17109332719312905190587203)
        ·
          refine ⟨25663999078969357785880805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17109332719312905190587203 25663999078969357785880805)
          ·
            refine ⟨4811999827306754584852651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25663999078969357785880805 4811999827306754584852651)
            ·
              refine ⟨7217999740960131877278977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811999827306754584852651 7217999740960131877278977)
              ·
                refine ⟨5413499805720098907959233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217999740960131877278977 5413499805720098907959233)
                ·
                  refine ⟨4060124854290074180969425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5413499805720098907959233 4060124854290074180969425)
                  ·
                    refine ⟨3045093640717555635727069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4060124854290074180969425 3045093640717555635727069)
                    ·
                      refine ⟨1141910115269083363397651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3045093640717555635727069 1141910115269083363397651)
                      ·
                        rfl

theorem cell23_2223862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2223862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223862 prefixEnd_2223862 := by exact prefixLift 2223862
  have htrace : WordTrace (prefixWord ++ tailWord_2223862) baseStart_2223862 baseEnd_2223862 := by
    simpa [prefixWord, tailWord_2223862, baseEnd_2223862] using wordTrace_append hprefix tailTrace_2223862
  have hstable : (prefixWord ++ tailWord_2223862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223862).length < 2 ^ (prefixWord ++ tailWord_2223862).sum := by decide
  have hdescent : baseEnd_2223862 < baseStart_2223862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223882 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_2223882 : Nat := 118140960795 + 2223882 * 2 ^ 59
def prefixEnd_2223882 : Nat := 4983230072969 + 3 ^ 40 * 2223882 * 2
def baseEnd_2223882 : Nat := 126880042764685920571951

theorem tailTrace_2223882 : CollatzResearch.WordTrace tailWord_2223882 prefixEnd_2223882 126880042764685920571951 := by
  unfold tailWord_2223882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20277910032315699413146475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54074426752841865101723933 20277910032315699413146475)
  ·
    refine ⟨30416865048473549119719713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20277910032315699413146475 30416865048473549119719713)
    ·
      refine ⟨22812648786355161839789785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30416865048473549119719713 22812648786355161839789785)
      ·
        refine ⟨17109486589766371379842339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22812648786355161839789785 17109486589766371379842339)
        ·
          refine ⟨25664229884649557069763509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17109486589766371379842339 25664229884649557069763509)
          ·
            refine ⟨2406021551685895975290329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25664229884649557069763509 2406021551685895975290329)
            ·
              refine ⟨1804516163764421981467747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406021551685895975290329 1804516163764421981467747)
              ·
                refine ⟨2706774245646632972201621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804516163764421981467747 2706774245646632972201621)
                ·
                  refine ⟨126880042764685920571951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2706774245646632972201621 126880042764685920571951)
                  ·
                    rfl

theorem cell23_2223882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_2223882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223882 prefixEnd_2223882 := by exact prefixLift 2223882
  have htrace : WordTrace (prefixWord ++ tailWord_2223882) baseStart_2223882 baseEnd_2223882 := by
    simpa [prefixWord, tailWord_2223882, baseEnd_2223882] using wordTrace_append hprefix tailTrace_2223882
  have hstable : (prefixWord ++ tailWord_2223882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223882).length < 2 ^ (prefixWord ++ tailWord_2223882).sum := by decide
  have hdescent : baseEnd_2223882 < baseStart_2223882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223895 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 3, 5]
def baseStart_2223895 : Nat := 118140960795 + 2223895 * 2 ^ 59
def prefixEnd_2223895 : Nat := 4983230072969 + 3 ^ 40 * 2223895 * 2
def baseEnd_2223895 : Nat := 380642353376893911428333

theorem tailTrace_2223895 : CollatzResearch.WordTrace tailWord_2223895 prefixEnd_2223895 380642353376893911428333 := by
  unfold tailWord_2223895
  simp only [CollatzResearch.WordTrace]
  refine ⟨81112114278215700872809139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54074742852143800581872759 81112114278215700872809139)
  ·
    refine ⟨121668171417323551309213709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81112114278215700872809139 121668171417323551309213709)
    ·
      refine ⟨45625564281496331740955141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121668171417323551309213709 45625564281496331740955141)
      ·
        refine ⟨8554793302780562201429089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45625564281496331740955141 8554793302780562201429089)
        ·
          refine ⟨6416094977085421651071817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8554793302780562201429089 6416094977085421651071817)
          ·
            refine ⟨4812071232814066238303863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6416094977085421651071817 4812071232814066238303863)
            ·
              refine ⟨7218106849221099357455795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812071232814066238303863 7218106849221099357455795)
              ·
                refine ⟨10827160273831649036183693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7218106849221099357455795 10827160273831649036183693)
                ·
                  refine ⟨4060185102686868388568885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10827160273831649036183693 4060185102686868388568885)
                  ·
                    refine ⟨380642353376893911428333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4060185102686868388568885 380642353376893911428333)
                    ·
                      rfl

theorem cell23_2223895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_2223895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223895 prefixEnd_2223895 := by exact prefixLift 2223895
  have htrace : WordTrace (prefixWord ++ tailWord_2223895) baseStart_2223895 baseEnd_2223895 := by
    simpa [prefixWord, tailWord_2223895, baseEnd_2223895] using wordTrace_append hprefix tailTrace_2223895
  have hstable : (prefixWord ++ tailWord_2223895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223895).length < 2 ^ (prefixWord ++ tailWord_2223895).sum := by decide
  have hdescent : baseEnd_2223895 < baseStart_2223895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223945 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_2223945 : Nat := 118140960795 + 2223945 * 2 ^ 59
def prefixEnd_2223945 : Nat := 4983230072969 + 3 ^ 40 * 2223945 * 2
def baseEnd_2223945 : Nat := 1141952734163406538659769

theorem tailTrace_2223945 : CollatzResearch.WordTrace tailWord_2223945 prefixEnd_2223945 1141952734163406538659769 := by
  unfold tailWord_2223945
  simp only [CollatzResearch.WordTrace]
  refine ⟨81113937928034559412129289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54075958618689706274752859 81113937928034559412129289)
  ·
    refine ⟨60835453446025919559096967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81113937928034559412129289 60835453446025919559096967)
    ·
      refine ⟨91253180169038879338645451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60835453446025919559096967 91253180169038879338645451)
      ·
        refine ⟨136879770253558319007968177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91253180169038879338645451 136879770253558319007968177)
        ·
          refine ⟨102659827690168739255976133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136879770253558319007968177 102659827690168739255976133)
          ·
            refine ⟨19248717691906638610495525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102659827690168739255976133 19248717691906638610495525)
            ·
              refine ⟨3609134567232494739467911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19248717691906638610495525 3609134567232494739467911)
              ·
                refine ⟨5413701850848742109201867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3609134567232494739467911 5413701850848742109201867)
                ·
                  refine ⟨8120552776273113163802801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5413701850848742109201867 8120552776273113163802801)
                  ·
                    refine ⟨6090414582204834872852101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8120552776273113163802801 6090414582204834872852101)
                    ·
                      refine ⟨1141952734163406538659769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6090414582204834872852101 1141952734163406538659769)
                      ·
                        rfl

theorem cell23_2223945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_2223945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223945 prefixEnd_2223945 := by exact prefixLift 2223945
  have htrace : WordTrace (prefixWord ++ tailWord_2223945) baseStart_2223945 baseEnd_2223945 := by
    simpa [prefixWord, tailWord_2223945, baseEnd_2223945] using wordTrace_append hprefix tailTrace_2223945
  have hstable : (prefixWord ++ tailWord_2223945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223945).length < 2 ^ (prefixWord ++ tailWord_2223945).sum := by decide
  have hdescent : baseEnd_2223945 < baseStart_2223945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224009 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 1, 3, 2]
def baseStart_2224009 : Nat := 118140960795 + 2224009 * 2 ^ 59
def prefixEnd_2224009 : Nat := 4983230072969 + 3 ^ 40 * 2224009 * 2
def baseEnd_2224009 : Nat := 1141985596925294288259475

theorem tailTrace_2224009 : CollatzResearch.WordTrace tailWord_2224009 prefixEnd_2224009 1141985596925294288259475 := by
  unfold tailWord_2224009
  simp only [CollatzResearch.WordTrace]
  refine ⟨81116272199802698342459081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54077514799868465561639387 81116272199802698342459081)
  ·
    refine ⟨60837204149852023756844311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81116272199802698342459081 60837204149852023756844311)
    ·
      refine ⟨91255806224778035635266467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60837204149852023756844311 91255806224778035635266467)
      ·
        refine ⟨136883709337167053452899701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91255806224778035635266467 136883709337167053452899701)
        ·
          refine ⟨12832847750359411261209347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136883709337167053452899701 12832847750359411261209347)
          ·
            refine ⟨19249271625539116891814021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12832847750359411261209347 19249271625539116891814021)
            ·
              refine ⟨3609238429788584417215129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19249271625539116891814021 3609238429788584417215129)
              ·
                refine ⟨2706928822341438312911347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3609238429788584417215129 2706928822341438312911347)
                ·
                  refine ⟨4060393233512157469367021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706928822341438312911347 4060393233512157469367021)
                  ·
                    refine ⟨1522647462567059051012633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4060393233512157469367021 1522647462567059051012633)
                    ·
                      refine ⟨1141985596925294288259475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522647462567059051012633 1141985596925294288259475)
                      ·
                        rfl

theorem cell23_2224009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 3, 2].length) (baseStart_2224009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224009 prefixEnd_2224009 := by exact prefixLift 2224009
  have htrace : WordTrace (prefixWord ++ tailWord_2224009) baseStart_2224009 baseEnd_2224009 := by
    simpa [prefixWord, tailWord_2224009, baseEnd_2224009] using wordTrace_append hprefix tailTrace_2224009
  have hstable : (prefixWord ++ tailWord_2224009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224009).length < 2 ^ (prefixWord ++ tailWord_2224009).sum := by decide
  have hdescent : baseEnd_2224009 < baseStart_2224009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224055 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_2224055 : Nat := 118140960795 + 2224055 * 2 ^ 59
def prefixEnd_2224055 : Nat := 4983230072969 + 3 ^ 40 * 2224055 * 2
def baseEnd_2224055 : Nat := 1142009217035401108284263

theorem tailTrace_2224055 : CollatzResearch.WordTrace tailWord_2224055 prefixEnd_2224055 1142009217035401108284263 := by
  unfold tailWord_2224055
  simp only [CollatzResearch.WordTrace]
  refine ⟨81117949957636048198633619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54078633305090698799089079 81117949957636048198633619)
  ·
    refine ⟨121676924936454072297950429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81117949957636048198633619 121676924936454072297950429)
    ·
      refine ⟨45628846851170277111731411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121676924936454072297950429 45628846851170277111731411)
      ·
        refine ⟨68443270276755415667597117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45628846851170277111731411 68443270276755415667597117)
        ·
          refine ⟨25666226353783280875348919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68443270276755415667597117 25666226353783280875348919)
          ·
            refine ⟨38499339530674921313023379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25666226353783280875348919 38499339530674921313023379)
            ·
              refine ⟨57749009296012381969535069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38499339530674921313023379 57749009296012381969535069)
              ·
                refine ⟨21655878486004643238575651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57749009296012381969535069 21655878486004643238575651)
                ·
                  refine ⟨32483817729006964857863477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21655878486004643238575651 32483817729006964857863477)
                  ·
                    refine ⟨3045357912094402955424701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32483817729006964857863477 3045357912094402955424701)
                    ·
                      refine ⟨1142009217035401108284263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3045357912094402955424701 1142009217035401108284263)
                      ·
                        rfl

theorem cell23_2224055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_2224055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224055 prefixEnd_2224055 := by exact prefixLift 2224055
  have htrace : WordTrace (prefixWord ++ tailWord_2224055) baseStart_2224055 baseEnd_2224055 := by
    simpa [prefixWord, tailWord_2224055, baseEnd_2224055] using wordTrace_append hprefix tailTrace_2224055
  have hstable : (prefixWord ++ tailWord_2224055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224055).length < 2 ^ (prefixWord ++ tailWord_2224055).sum := by decide
  have hdescent : baseEnd_2224055 < baseStart_2224055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224060 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2224060 : Nat := 118140960795 + 2224060 * 2 ^ 59
def prefixEnd_2224060 : Nat := 4983230072969 + 3 ^ 40 * 2224060 * 2
def baseEnd_2224060 : Nat := 1142011784438673588721741

theorem tailTrace_2224060 : CollatzResearch.WordTrace tailWord_2224060 prefixEnd_2224060 1142011784438673588721741 := by
  unfold tailWord_2224060
  simp only [CollatzResearch.WordTrace]
  refine ⟨40559066161308967026282817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54078754881745289368377089 40559066161308967026282817)
  ·
    refine ⟨30419299620981725269712113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40559066161308967026282817 30419299620981725269712113)
    ·
      refine ⟨22814474715736293952284085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30419299620981725269712113 22814474715736293952284085)
      ·
        refine ⟨2138857004600277558026633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22814474715736293952284085 2138857004600277558026633)
        ·
          refine ⟨1604142753450208168519975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2138857004600277558026633 1604142753450208168519975)
          ·
            refine ⟨2406214130175312252779963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604142753450208168519975 2406214130175312252779963)
            ·
              refine ⟨3609321195262968379169945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406214130175312252779963 3609321195262968379169945)
              ·
                refine ⟨2706990896447226284377459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3609321195262968379169945 2706990896447226284377459)
                ·
                  refine ⟨4060486344670839426566189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706990896447226284377459 4060486344670839426566189)
                  ·
                    refine ⟨1522682379251564784962321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4060486344670839426566189 1522682379251564784962321)
                    ·
                      refine ⟨1142011784438673588721741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522682379251564784962321 1142011784438673588721741)
                      ·
                        rfl

theorem cell23_2224060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2224060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224060 prefixEnd_2224060 := by exact prefixLift 2224060
  have htrace : WordTrace (prefixWord ++ tailWord_2224060) baseStart_2224060 baseEnd_2224060 := by
    simpa [prefixWord, tailWord_2224060, baseEnd_2224060] using wordTrace_append hprefix tailTrace_2224060
  have hstable : (prefixWord ++ tailWord_2224060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224060).length < 2 ^ (prefixWord ++ tailWord_2224060).sum := by decide
  have hdescent : baseEnd_2224060 < baseStart_2224060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224112 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 6, 2]
def baseStart_2224112 : Nat := 118140960795 + 2224112 * 2 ^ 59
def prefixEnd_2224112 : Nat := 4983230072969 + 3 ^ 40 * 2224112 * 2
def baseEnd_2224112 : Nat := 1142038485432707385271501

theorem tailTrace_2224112 : CollatzResearch.WordTrace tailWord_2224112 prefixEnd_2224112 1142038485432707385271501 := by
  unfold tailWord_2224112
  simp only [CollatzResearch.WordTrace]
  refine ⟨40560014459214773466729295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54080019278953031288972393 40560014459214773466729295)
  ·
    refine ⟨60840021688822160200093943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40560014459214773466729295 60840021688822160200093943)
    ·
      refine ⟨91260032533233240300140915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60840021688822160200093943 91260032533233240300140915)
      ·
        refine ⟨136890048799849860450211373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91260032533233240300140915 136890048799849860450211373)
        ·
          refine ⟨51333768299943697668829265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136890048799849860450211373 51333768299943697668829265)
          ·
            refine ⟨38500326224957773251621949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51333768299943697668829265 38500326224957773251621949)
            ·
              refine ⟨14437622334359164969358231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38500326224957773251621949 14437622334359164969358231)
              ·
                refine ⟨21656433501538747454037347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14437622334359164969358231 21656433501538747454037347)
                ·
                  refine ⟨32484650252308121181056021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21656433501538747454037347 32484650252308121181056021)
                  ·
                    refine ⟨1522717980576943180362001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32484650252308121181056021 1522717980576943180362001)
                    ·
                      refine ⟨1142038485432707385271501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522717980576943180362001 1142038485432707385271501)
                      ·
                        rfl

theorem cell23_2224112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 6, 2].length) (baseStart_2224112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224112 prefixEnd_2224112 := by exact prefixLift 2224112
  have htrace : WordTrace (prefixWord ++ tailWord_2224112) baseStart_2224112 baseEnd_2224112 := by
    simpa [prefixWord, tailWord_2224112, baseEnd_2224112] using wordTrace_append hprefix tailTrace_2224112
  have hstable : (prefixWord ++ tailWord_2224112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224112).length < 2 ^ (prefixWord ++ tailWord_2224112).sum := by decide
  have hdescent : baseEnd_2224112 < baseStart_2224112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224126 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2224126 : Nat := 118140960795 + 2224126 * 2 ^ 59
def prefixEnd_2224126 : Nat := 4983230072969 + 3 ^ 40 * 2224126 * 2
def baseEnd_2224126 : Nat := 380681891387290110165479

theorem tailTrace_2224126 : CollatzResearch.WordTrace tailWord_2224126 prefixEnd_2224126 380681891387290110165479 := by
  unfold tailWord_2224126
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140067442547353415558529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54080359693585884882978821 10140067442547353415558529)
  ·
    refine ⟨7605050581910515061668897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10140067442547353415558529 7605050581910515061668897)
    ·
      refine ⟨5703787936432886296251673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7605050581910515061668897 5703787936432886296251673)
      ·
        refine ⟨4277840952324664722188755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5703787936432886296251673 4277840952324664722188755)
        ·
          refine ⟨6416761428486997083283133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277840952324664722188755 6416761428486997083283133)
          ·
            refine ⟨2406285535682623906231175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6416761428486997083283133 2406285535682623906231175)
            ·
              refine ⟨3609428303523935859346763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406285535682623906231175 3609428303523935859346763)
              ·
                refine ⟨5414142455285903789020145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3609428303523935859346763 5414142455285903789020145)
                ·
                  refine ⟨4060606841464427841765109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5414142455285903789020145 4060606841464427841765109)
                  ·
                    refine ⟨380681891387290110165479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4060606841464427841765109 380681891387290110165479)
                    ·
                      rfl

theorem cell23_2224126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2224126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224126 prefixEnd_2224126 := by exact prefixLift 2224126
  have htrace : WordTrace (prefixWord ++ tailWord_2224126) baseStart_2224126 baseEnd_2224126 := by
    simpa [prefixWord, tailWord_2224126, baseEnd_2224126] using wordTrace_append hprefix tailTrace_2224126
  have hstable : (prefixWord ++ tailWord_2224126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224126).length < 2 ^ (prefixWord ++ tailWord_2224126).sum := by decide
  have hdescent : baseEnd_2224126 < baseStart_2224126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224156 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_2224156 : Nat := 118140960795 + 2224156 * 2 ^ 59
def prefixEnd_2224156 : Nat := 4983230072969 + 3 ^ 40 * 2224156 * 2
def baseEnd_2224156 : Nat := 380687026193835071040433

theorem tailTrace_2224156 : CollatzResearch.WordTrace tailWord_2224156 prefixEnd_2224156 380687026193835071040433 := by
  unfold tailWord_2224156
  simp only [CollatzResearch.WordTrace]
  refine ⟨40560816865135071224030161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54081089153513428298706881 40560816865135071224030161)
  ·
    refine ⟨30420612648851303418022621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40560816865135071224030161 30420612648851303418022621)
    ·
      refine ⟨11407729743319238781758483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30420612648851303418022621 11407729743319238781758483)
      ·
        refine ⟨17111594614978858172637725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11407729743319238781758483 17111594614978858172637725)
        ·
          refine ⟨6416847980617071814739147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17111594614978858172637725 6416847980617071814739147)
          ·
            refine ⟨9625271970925607722108721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6416847980617071814739147 9625271970925607722108721)
            ·
              refine ⟨7218953978194205791581541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9625271970925607722108721 7218953978194205791581541)
              ·
                refine ⟨1353553870911413585921539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7218953978194205791581541 1353553870911413585921539)
                ·
                  refine ⟨2030330806367120378882309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353553870911413585921539 2030330806367120378882309)
                  ·
                    refine ⟨380687026193835071040433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2030330806367120378882309 380687026193835071040433)
                    ·
                      rfl

theorem cell23_2224156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_2224156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224156 prefixEnd_2224156 := by exact prefixLift 2224156
  have htrace : WordTrace (prefixWord ++ tailWord_2224156) baseStart_2224156 baseEnd_2224156 := by
    simpa [prefixWord, tailWord_2224156, baseEnd_2224156] using wordTrace_append hprefix tailTrace_2224156
  have hstable : (prefixWord ++ tailWord_2224156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224156).length < 2 ^ (prefixWord ++ tailWord_2224156).sum := by decide
  have hdescent : baseEnd_2224156 < baseStart_2224156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224179 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 3]
def baseStart_2224179 : Nat := 118140960795 + 2224179 * 2 ^ 59
def prefixEnd_2224179 : Nat := 4983230072969 + 3 ^ 40 * 2224179 * 2
def baseEnd_2224179 : Nat := 1142072888636558623133693

theorem tailTrace_2224179 : CollatzResearch.WordTrace tailWord_2224179 prefixEnd_2224179 1142072888636558623133693 := by
  unfold tailWord_2224179
  simp only [CollatzResearch.WordTrace]
  refine ⟨81122472609186817376147591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54081648406124544917431727 81122472609186817376147591)
  ·
    refine ⟨121683708913780226064221387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81122472609186817376147591 121683708913780226064221387)
    ·
      refine ⟨182525563370670339096332081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121683708913780226064221387 182525563370670339096332081)
      ·
        refine ⟨136894172528002754322249061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182525563370670339096332081 136894172528002754322249061)
        ·
          refine ⟨25667657349000516435421699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136894172528002754322249061 25667657349000516435421699)
          ·
            refine ⟨38501486023500774653132549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25667657349000516435421699 38501486023500774653132549)
            ·
              refine ⟨7219028629406395247462353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38501486023500774653132549 7219028629406395247462353)
              ·
                refine ⟨5414271472054796435596765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7219028629406395247462353 5414271472054796435596765)
                ·
                  refine ⟨2030351802020548663348787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5414271472054796435596765 2030351802020548663348787)
                  ·
                    refine ⟨3045527703030822995023181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2030351802020548663348787 3045527703030822995023181)
                    ·
                      refine ⟨1142072888636558623133693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3045527703030822995023181 1142072888636558623133693)
                      ·
                        rfl

theorem cell23_2224179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_2224179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224179 prefixEnd_2224179 := by exact prefixLift 2224179
  have htrace : WordTrace (prefixWord ++ tailWord_2224179) baseStart_2224179 baseEnd_2224179 := by
    simpa [prefixWord, tailWord_2224179, baseEnd_2224179] using wordTrace_append hprefix tailTrace_2224179
  have hstable : (prefixWord ++ tailWord_2224179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224179).length < 2 ^ (prefixWord ++ tailWord_2224179).sum := by decide
  have hdescent : baseEnd_2224179 < baseStart_2224179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224189 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_2224189 : Nat := 118140960795 + 2224189 * 2 ^ 59
def prefixEnd_2224189 : Nat := 4983230072969 + 3 ^ 40 * 2224189 * 2
def baseEnd_2224189 : Nat := 1142078023443103584008647

theorem tailTrace_2224189 : CollatzResearch.WordTrace tailWord_2224189 prefixEnd_2224189 1142078023443103584008647 := by
  unfold tailWord_2224189
  simp only [CollatzResearch.WordTrace]
  refine ⟨81122837339150589084011621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54081891559433726056007747 81122837339150589084011621)
  ·
    refine ⟨15210532001090735453252179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81122837339150589084011621 15210532001090735453252179)
    ·
      refine ⟨22815798001636103179878269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15210532001090735453252179 22815798001636103179878269)
      ·
        refine ⟨8555924250613538692454351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22815798001636103179878269 8555924250613538692454351)
        ·
          refine ⟨12833886375920308038681527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8555924250613538692454351 12833886375920308038681527)
          ·
            refine ⟨19250829563880462058022291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12833886375920308038681527 19250829563880462058022291)
            ·
              refine ⟨28876244345820693087033437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19250829563880462058022291 28876244345820693087033437)
              ·
                refine ⟨10828591629682759907637539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28876244345820693087033437 10828591629682759907637539)
                ·
                  refine ⟨16242887444524139861456309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10828591629682759907637539 16242887444524139861456309)
                  ·
                    refine ⟨1522770697924138112011529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16242887444524139861456309 1522770697924138112011529)
                    ·
                      refine ⟨1142078023443103584008647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522770697924138112011529 1142078023443103584008647)
                      ·
                        rfl

theorem cell23_2224189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_2224189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224189 prefixEnd_2224189 := by exact prefixLift 2224189
  have htrace : WordTrace (prefixWord ++ tailWord_2224189) baseStart_2224189 baseEnd_2224189 := by
    simpa [prefixWord, tailWord_2224189, baseEnd_2224189] using wordTrace_append hprefix tailTrace_2224189
  have hstable : (prefixWord ++ tailWord_2224189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224189).length < 2 ^ (prefixWord ++ tailWord_2224189).sum := by decide
  have hdescent : baseEnd_2224189 < baseStart_2224189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224190 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2224190 : Nat := 118140960795 + 2224190 * 2 ^ 59
def prefixEnd_2224190 : Nat := 4983230072969 + 3 ^ 40 * 2224190 * 2
def baseEnd_2224190 : Nat := 380692845641252693365381

theorem tailTrace_2224190 : CollatzResearch.WordTrace tailWord_2224190 prefixEnd_2224190 380692845641252693365381 := by
  unfold tailWord_2224190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140359226518370781849753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54081915874764644169865349 10140359226518370781849753)
  ·
    refine ⟨7605269419888778086387315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10140359226518370781849753 7605269419888778086387315)
    ·
      refine ⟨11407904129833167129580973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7605269419888778086387315 11407904129833167129580973)
      ·
        refine ⟨4277964048687437673592865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11407904129833167129580973 4277964048687437673592865)
        ·
          refine ⟨3208473036515578255194649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277964048687437673592865 3208473036515578255194649)
          ·
            refine ⟨2406354777386683691395987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3208473036515578255194649 2406354777386683691395987)
            ·
              refine ⟨3609532166080025537093981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406354777386683691395987 3609532166080025537093981)
              ·
                refine ⟨1353574562280009576410243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3609532166080025537093981 1353574562280009576410243)
                ·
                  refine ⟨2030361843420014364615365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353574562280009576410243 2030361843420014364615365)
                  ·
                    refine ⟨380692845641252693365381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2030361843420014364615365 380692845641252693365381)
                    ·
                      rfl

theorem cell23_2224190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2224190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224190 prefixEnd_2224190 := by exact prefixLift 2224190
  have htrace : WordTrace (prefixWord ++ tailWord_2224190) baseStart_2224190 baseEnd_2224190 := by
    simpa [prefixWord, tailWord_2224190, baseEnd_2224190] using wordTrace_append hprefix tailTrace_2224190
  have hstable : (prefixWord ++ tailWord_2224190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224190).length < 2 ^ (prefixWord ++ tailWord_2224190).sum := by decide
  have hdescent : baseEnd_2224190 < baseStart_2224190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224202 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2224202 : Nat := 118140960795 + 2224202 * 2 ^ 59
def prefixEnd_2224202 : Nat := 4983230072969 + 3 ^ 40 * 2224202 * 2
def baseEnd_2224202 : Nat := 1142084698691612033146087

theorem tailTrace_2224202 : CollatzResearch.WordTrace tailWord_2224202 prefixEnd_2224202 1142084698691612033146087 := by
  unfold tailWord_2224202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20280827872025873076058715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54082207658735661536156573 20280827872025873076058715)
  ·
    refine ⟨30421241808038809614088073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20280827872025873076058715 30421241808038809614088073)
    ·
      refine ⟨22815931356029107210566055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30421241808038809614088073 22815931356029107210566055)
      ·
        refine ⟨34223897034043660815849083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22815931356029107210566055 34223897034043660815849083)
        ·
          refine ⟨51335845551065491223773625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34223897034043660815849083 51335845551065491223773625)
          ·
            refine ⟨38501884163299118417830219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51335845551065491223773625 38501884163299118417830219)
            ·
              refine ⟨57752826244948677626745329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38501884163299118417830219 57752826244948677626745329)
              ·
                refine ⟨43314619683711508220058997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57752826244948677626745329 43314619683711508220058997)
                ·
                  refine ⟨4060745595347953895630531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43314619683711508220058997 4060745595347953895630531)
                  ·
                    refine ⟨6091118393021930843445797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4060745595347953895630531 6091118393021930843445797)
                    ·
                      refine ⟨1142084698691612033146087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6091118393021930843445797 1142084698691612033146087)
                      ·
                        rfl

theorem cell23_2224202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2224202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224202 prefixEnd_2224202 := by exact prefixLift 2224202
  have htrace : WordTrace (prefixWord ++ tailWord_2224202) baseStart_2224202 baseEnd_2224202 := by
    simpa [prefixWord, tailWord_2224202, baseEnd_2224202] using wordTrace_append hprefix tailTrace_2224202
  have hstable : (prefixWord ++ tailWord_2224202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224202).length < 2 ^ (prefixWord ++ tailWord_2224202).sum := by decide
  have hdescent : baseEnd_2224202 < baseStart_2224202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224206 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_2224206 : Nat := 118140960795 + 2224206 * 2 ^ 59
def prefixEnd_2224206 : Nat := 4983230072969 + 3 ^ 40 * 2224206 * 2
def baseEnd_2224206 : Nat := 1142086752614230017496069

theorem tailTrace_2224206 : CollatzResearch.WordTrace tailWord_2224206 prefixEnd_2224206 1142086752614230017496069 := by
  unfold tailWord_2224206
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140432172511125123422559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54082304920059333991586981 10140432172511125123422559)
  ·
    refine ⟨15210648258766687685133839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10140432172511125123422559 15210648258766687685133839)
    ·
      refine ⟨22815972388150031527700759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15210648258766687685133839 22815972388150031527700759)
      ·
        refine ⟨34223958582225047291551139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22815972388150031527700759 34223958582225047291551139)
        ·
          refine ⟨51335937873337570937326709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34223958582225047291551139 51335937873337570937326709)
          ·
            refine ⟨4812744175625397275374379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51335937873337570937326709 4812744175625397275374379)
            ·
              refine ⟨7219116263438095913061569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812744175625397275374379 7219116263438095913061569)
              ·
                refine ⟨5414337197578571934796177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7219116263438095913061569 5414337197578571934796177)
                ·
                  refine ⟨4060752898183928951097133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5414337197578571934796177 4060752898183928951097133)
                  ·
                    refine ⟨1522782336818973356661425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4060752898183928951097133 1522782336818973356661425)
                    ·
                      refine ⟨1142086752614230017496069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522782336818973356661425 1142086752614230017496069)
                      ·
                        rfl

theorem cell23_2224206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_2224206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224206 prefixEnd_2224206 := by exact prefixLift 2224206
  have htrace : WordTrace (prefixWord ++ tailWord_2224206) baseStart_2224206 baseEnd_2224206 := by
    simpa [prefixWord, tailWord_2224206, baseEnd_2224206] using wordTrace_append hprefix tailTrace_2224206
  have hstable : (prefixWord ++ tailWord_2224206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224206).length < 2 ^ (prefixWord ++ tailWord_2224206).sum := by decide
  have hdescent : baseEnd_2224206 < baseStart_2224206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224236 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_2224236 : Nat := 118140960795 + 2224236 * 2 ^ 59
def prefixEnd_2224236 : Nat := 4983230072969 + 3 ^ 40 * 2224236 * 2
def baseEnd_2224236 : Nat := 1142102157033864900120931

theorem tailTrace_2224236 : CollatzResearch.WordTrace tailWord_2224236 prefixEnd_2224236 1142102157033864900120931 := by
  unfold tailWord_2224236
  simp only [CollatzResearch.WordTrace]
  refine ⟨40562275784990158055486281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54083034379986877407315041 40562275784990158055486281)
  ·
    refine ⟨30421706838742618541614711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40562275784990158055486281 30421706838742618541614711)
    ·
      refine ⟨45632560258113927812422067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30421706838742618541614711 45632560258113927812422067)
      ·
        refine ⟨68448840387170891718633101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45632560258113927812422067 68448840387170891718633101)
        ·
          refine ⟨25668315145189084394487413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68448840387170891718633101 25668315145189084394487413)
          ·
            refine ⟨2406404544861476661983195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25668315145189084394487413 2406404544861476661983195)
            ·
              refine ⟨3609606817292214992974793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406404544861476661983195 3609606817292214992974793)
              ·
                refine ⟨2707205112969161244731095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3609606817292214992974793 2707205112969161244731095)
                ·
                  refine ⟨4060807669453741867096643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707205112969161244731095 4060807669453741867096643)
                  ·
                    refine ⟨6091211504180612800644965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4060807669453741867096643 6091211504180612800644965)
                    ·
                      refine ⟨1142102157033864900120931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6091211504180612800644965 1142102157033864900120931)
                      ·
                        rfl

theorem cell23_2224236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_2224236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224236 prefixEnd_2224236 := by exact prefixLift 2224236
  have htrace : WordTrace (prefixWord ++ tailWord_2224236) baseStart_2224236 baseEnd_2224236 := by
    simpa [prefixWord, tailWord_2224236, baseEnd_2224236] using wordTrace_append hprefix tailTrace_2224236
  have hstable : (prefixWord ++ tailWord_2224236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224236).length < 2 ^ (prefixWord ++ tailWord_2224236).sum := by decide
  have hdescent : baseEnd_2224236 < baseStart_2224236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224239 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_2224239 : Nat := 118140960795 + 2224239 * 2 ^ 59
def prefixEnd_2224239 : Nat := 4983230072969 + 3 ^ 40 * 2224239 * 2
def baseEnd_2224239 : Nat := 1142103697475828388383417

theorem tailTrace_2224239 : CollatzResearch.WordTrace tailWord_2224239 prefixEnd_2224239 1142103697475828388383417 := by
  unfold tailWord_2224239
  simp only [CollatzResearch.WordTrace]
  refine ⟨81124660988969447623331771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54083107325979631748887847 81124660988969447623331771)
  ·
    refine ⟨121686991483454171434997657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81124660988969447623331771 121686991483454171434997657)
    ·
      refine ⟨91265243612590628576248243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121686991483454171434997657 91265243612590628576248243)
      ·
        refine ⟨136897865418885942864372365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91265243612590628576248243 136897865418885942864372365)
        ·
          refine ⟨51336699532082228574139637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136897865418885942864372365 51336699532082228574139637)
          ·
            refine ⟨4812815581132708928825591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51336699532082228574139637 4812815581132708928825591)
            ·
              refine ⟨7219223371699063393238387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812815581132708928825591 7219223371699063393238387)
              ·
                refine ⟨10828835057548595089857581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7219223371699063393238387 10828835057548595089857581)
                ·
                  refine ⟨4060813146580723158696593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10828835057548595089857581 4060813146580723158696593)
                  ·
                    refine ⟨3045609859935542369022445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4060813146580723158696593 3045609859935542369022445)
                    ·
                      refine ⟨1142103697475828388383417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3045609859935542369022445 1142103697475828388383417)
                      ·
                        rfl

theorem cell23_2224239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_2224239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224239 prefixEnd_2224239 := by exact prefixLift 2224239
  have htrace : WordTrace (prefixWord ++ tailWord_2224239) baseStart_2224239 baseEnd_2224239 := by
    simpa [prefixWord, tailWord_2224239, baseEnd_2224239] using wordTrace_append hprefix tailTrace_2224239
  have hstable : (prefixWord ++ tailWord_2224239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224239).length < 2 ^ (prefixWord ++ tailWord_2224239).sum := by decide
  have hdescent : baseEnd_2224239 < baseStart_2224239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224242 : List Nat := [3, 2, 1, 2, 2, 2, 2, 9]
def baseStart_2224242 : Nat := 118140960795 + 2224242 * 2 ^ 59
def prefixEnd_2224242 : Nat := 4983230072969 + 3 ^ 40 * 2224242 * 2
def baseEnd_2224242 : Nat := 42300193996955254690589

theorem tailTrace_2224242 : CollatzResearch.WordTrace tailWord_2224242 prefixEnd_2224242 42300193996955254690589 := by
  unfold tailWord_2224242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20281192601989644783922745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54083180271972386090460653 20281192601989644783922745)
  ·
    refine ⟨15210894451492233587942059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20281192601989644783922745 15210894451492233587942059)
    ·
      refine ⟨22816341677238350381913089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15210894451492233587942059 22816341677238350381913089)
      ·
        refine ⟨17112256257928762786434817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22816341677238350381913089 17112256257928762786434817)
        ·
          refine ⟨12834192193446572089826113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17112256257928762786434817 12834192193446572089826113)
          ·
            refine ⟨9625644145084929067369585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12834192193446572089826113 9625644145084929067369585)
            ·
              refine ⟨7219233108813696800527189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9625644145084929067369585 7219233108813696800527189)
              ·
                refine ⟨42300193996955254690589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7219233108813696800527189 42300193996955254690589)
                ·
                  rfl

theorem cell23_2224242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_2224242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224242 prefixEnd_2224242 := by exact prefixLift 2224242
  have htrace : WordTrace (prefixWord ++ tailWord_2224242) baseStart_2224242 baseEnd_2224242 := by
    simpa [prefixWord, tailWord_2224242, baseEnd_2224242] using wordTrace_append hprefix tailTrace_2224242
  have hstable : (prefixWord ++ tailWord_2224242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224242).length < 2 ^ (prefixWord ++ tailWord_2224242).sum := by decide
  have hdescent : baseEnd_2224242 < baseStart_2224242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224249 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2224249 : Nat := 118140960795 + 2224249 * 2 ^ 59
def prefixEnd_2224249 : Nat := 4983230072969 + 3 ^ 40 * 2224249 * 2
def baseEnd_2224249 : Nat := 1142108832282373349258371

theorem tailTrace_2224249 : CollatzResearch.WordTrace tailWord_2224249 prefixEnd_2224249 1142108832282373349258371 := by
  unfold tailWord_2224249
  simp only [CollatzResearch.WordTrace]
  refine ⟨81125025718933219331195801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54083350479288812887463867 81125025718933219331195801)
  ·
    refine ⟨60843769289199914498396851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81125025718933219331195801 60843769289199914498396851)
    ·
      refine ⟨91265653933799871747595277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60843769289199914498396851 91265653933799871747595277)
      ·
        refine ⟨34224620225174951905348229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91265653933799871747595277 34224620225174951905348229)
        ·
          refine ⟨6417116292220303482252793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34224620225174951905348229 6417116292220303482252793)
          ·
            refine ⟨4812837219165227611689595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6417116292220303482252793 4812837219165227611689595)
            ·
              refine ⟨7219255828747841417534393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812837219165227611689595 7219255828747841417534393)
              ·
                refine ⟨5414441871560881063150795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7219255828747841417534393 5414441871560881063150795)
                ·
                  refine ⟨8121662807341321594726193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5414441871560881063150795 8121662807341321594726193)
                  ·
                    refine ⟨6091247105505991196044645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8121662807341321594726193 6091247105505991196044645)
                    ·
                      refine ⟨1142108832282373349258371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6091247105505991196044645 1142108832282373349258371)
                      ·
                        rfl

theorem cell23_2224249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2224249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224249 prefixEnd_2224249 := by exact prefixLift 2224249
  have htrace : WordTrace (prefixWord ++ tailWord_2224249) baseStart_2224249 baseEnd_2224249 := by
    simpa [prefixWord, tailWord_2224249, baseEnd_2224249] using wordTrace_append hprefix tailTrace_2224249
  have hstable : (prefixWord ++ tailWord_2224249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224249).length < 2 ^ (prefixWord ++ tailWord_2224249).sum := by decide
  have hdescent : baseEnd_2224249 < baseStart_2224249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224312 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_2224312 : Nat := 118140960795 + 2224312 * 2 ^ 59
def prefixEnd_2224312 : Nat := 4983230072969 + 3 ^ 40 * 2224312 * 2
def baseEnd_2224312 : Nat := 1142141181563606602770581

theorem tailTrace_2224312 : CollatzResearch.WordTrace tailWord_2224312 prefixEnd_2224312 1142141181563606602770581 := by
  unfold tailWord_2224312
  simp only [CollatzResearch.WordTrace]
  refine ⟨40563661758852490545369595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54084882345136654060492793 40563661758852490545369595)
  ·
    refine ⟨60845492638278735818054393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40563661758852490545369595 60845492638278735818054393)
    ·
      refine ⟨45634119478709051863540795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60845492638278735818054393 45634119478709051863540795)
      ·
        refine ⟨68451179218063577795311193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45634119478709051863540795 68451179218063577795311193)
        ·
          refine ⟨51338384413547683346483395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68451179218063577795311193 51338384413547683346483395)
          ·
            refine ⟨77007576620321525019725093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51338384413547683346483395 77007576620321525019725093)
            ·
              refine ⟨14438920616310285941198455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77007576620321525019725093 14438920616310285941198455)
              ·
                refine ⟨21658380924465428911797683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14438920616310285941198455 21658380924465428911797683)
                ·
                  refine ⟨32487571386698143367696525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21658380924465428911797683 32487571386698143367696525)
                  ·
                    refine ⟨12182839270011803762886197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32487571386698143367696525 12182839270011803762886197)
                    ·
                      refine ⟨1142141181563606602770581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12182839270011803762886197 1142141181563606602770581)
                      ·
                        rfl

theorem cell23_2224312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_2224312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224312 prefixEnd_2224312 := by exact prefixLift 2224312
  have htrace : WordTrace (prefixWord ++ tailWord_2224312) baseStart_2224312 baseEnd_2224312 := by
    simpa [prefixWord, tailWord_2224312, baseEnd_2224312] using wordTrace_append hprefix tailTrace_2224312
  have hstable : (prefixWord ++ tailWord_2224312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224312).length < 2 ^ (prefixWord ++ tailWord_2224312).sum := by decide
  have hdescent : baseEnd_2224312 < baseStart_2224312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224413 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2224413 : Nat := 118140960795 + 2224413 * 2 ^ 59
def prefixEnd_2224413 : Nat := 4983230072969 + 3 ^ 40 * 2224413 * 2
def baseEnd_2224413 : Nat := 380731014369903569202539

theorem tailTrace_2224413 : CollatzResearch.WordTrace tailWord_2224413 prefixEnd_2224413 380731014369903569202539 := by
  unfold tailWord_2224413
  simp only [CollatzResearch.WordTrace]
  refine ⟨81131007290339075340165893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54087338193559383560110595 81131007290339075340165893)
  ·
    refine ⟨15212063866938576626281105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81131007290339075340165893 15212063866938576626281105)
    ·
      refine ⟨11409047900203932469710829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15212063866938576626281105 11409047900203932469710829)
      ·
        refine ⟨4278392962576474676141561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11409047900203932469710829 4278392962576474676141561)
        ·
          refine ⟨3208794721932356007106171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4278392962576474676141561 3208794721932356007106171)
          ·
            refine ⟨4813192082898534010659257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208794721932356007106171 4813192082898534010659257)
            ·
              refine ⟨3609894062173900507994443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4813192082898534010659257 3609894062173900507994443)
              ·
                refine ⟨5414841093260850761991665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3609894062173900507994443 5414841093260850761991665)
                ·
                  refine ⟨4061130819945638071493749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5414841093260850761991665 4061130819945638071493749)
                  ·
                    refine ⟨380731014369903569202539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4061130819945638071493749 380731014369903569202539)
                    ·
                      rfl

theorem cell23_2224413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2224413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224413 prefixEnd_2224413 := by exact prefixLift 2224413
  have htrace : WordTrace (prefixWord ++ tailWord_2224413) baseStart_2224413 baseEnd_2224413 := by
    simpa [prefixWord, tailWord_2224413, baseEnd_2224413] using wordTrace_append hprefix tailTrace_2224413
  have hstable : (prefixWord ++ tailWord_2224413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224413).length < 2 ^ (prefixWord ++ tailWord_2224413).sum := by decide
  have hdescent : baseEnd_2224413 < baseStart_2224413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224416 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2224416 : Nat := 118140960795 + 2224416 * 2 ^ 59
def prefixEnd_2224416 : Nat := 4983230072969 + 3 ^ 40 * 2224416 * 2
def baseEnd_2224416 : Nat := 1142194583551674195870103

theorem tailTrace_2224416 : CollatzResearch.WordTrace tailWord_2224416 prefixEnd_2224416 1142194583551674195870103 := by
  unfold tailWord_2224416
  simp only [CollatzResearch.WordTrace]
  refine ⟨40565558354664103426262551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54087411139552137901683401 40565558354664103426262551)
  ·
    refine ⟨60848337531996155139393827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40565558354664103426262551 60848337531996155139393827)
    ·
      refine ⟨91272506297994232709090741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60848337531996155139393827 91272506297994232709090741)
      ·
        refine ⟨8556797465436959316477257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91272506297994232709090741 8556797465436959316477257)
        ·
          refine ⟨6417598099077719487357943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8556797465436959316477257 6417598099077719487357943)
          ·
            refine ⟨9626397148616579231036915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417598099077719487357943 9626397148616579231036915)
            ·
              refine ⟨14439595722924868846555373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9626397148616579231036915 14439595722924868846555373)
              ·
                refine ⟨5414848396096825817458265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14439595722924868846555373 5414848396096825817458265)
                ·
                  refine ⟨4061136297072619363093699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5414848396096825817458265 4061136297072619363093699)
                  ·
                    refine ⟨6091704445608929044640549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4061136297072619363093699 6091704445608929044640549)
                    ·
                      refine ⟨1142194583551674195870103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6091704445608929044640549 1142194583551674195870103)
                      ·
                        rfl

theorem cell23_2224416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2224416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224416 prefixEnd_2224416 := by exact prefixLift 2224416
  have htrace : WordTrace (prefixWord ++ tailWord_2224416) baseStart_2224416 baseEnd_2224416 := by
    simpa [prefixWord, tailWord_2224416, baseEnd_2224416] using wordTrace_append hprefix tailTrace_2224416
  have hstable : (prefixWord ++ tailWord_2224416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224416).length < 2 ^ (prefixWord ++ tailWord_2224416).sum := by decide
  have hdescent : baseEnd_2224416 < baseStart_2224416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224493 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2224493 : Nat := 118140960795 + 2224493 * 2 ^ 59
def prefixEnd_2224493 : Nat := 4983230072969 + 3 ^ 40 * 2224493 * 2
def baseEnd_2224493 : Nat := 1142234121562070394607249

theorem tailTrace_2224493 : CollatzResearch.WordTrace tailWord_2224493 prefixEnd_2224493 1142234121562070394607249 := by
  unfold tailWord_2224493
  simp only [CollatzResearch.WordTrace]
  refine ⟨81133925130049249003078133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54089283420032832668718755 81133925130049249003078133)
  ·
    refine ⟨7606305480942117094038575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81133925130049249003078133 7606305480942117094038575)
    ·
      refine ⟨11409458221413175641057863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7606305480942117094038575 11409458221413175641057863)
      ·
        refine ⟨17114187332119763461586795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11409458221413175641057863 17114187332119763461586795)
        ·
          refine ⟨25671280998179645192380193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17114187332119763461586795 25671280998179645192380193)
          ·
            refine ⟨19253460748634733894285145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25671280998179645192380193 19253460748634733894285145)
            ·
              refine ⟨14440095561476050420713859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19253460748634733894285145 14440095561476050420713859)
              ·
                refine ⟨21660143342214075631070789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14440095561476050420713859 21660143342214075631070789)
                ·
                  refine ⟨4061276876665139180825773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21660143342214075631070789 4061276876665139180825773)
                  ·
                    refine ⟨1522978828749427192809665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4061276876665139180825773 1522978828749427192809665)
                    ·
                      refine ⟨1142234121562070394607249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522978828749427192809665 1142234121562070394607249)
                      ·
                        rfl

theorem cell23_2224493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2224493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224493 prefixEnd_2224493 := by exact prefixLift 2224493
  have htrace : WordTrace (prefixWord ++ tailWord_2224493) baseStart_2224493 baseEnd_2224493 := by
    simpa [prefixWord, tailWord_2224493, baseEnd_2224493] using wordTrace_append hprefix tailTrace_2224493
  have hstable : (prefixWord ++ tailWord_2224493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224493).length < 2 ^ (prefixWord ++ tailWord_2224493).sum := by decide
  have hdescent : baseEnd_2224493 < baseStart_2224493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224506 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2]
def baseStart_2224506 : Nat := 118140960795 + 2224506 * 2 ^ 59
def prefixEnd_2224506 : Nat := 4983230072969 + 3 ^ 40 * 2224506 * 2
def baseEnd_2224506 : Nat := 1142240796810578843744689

theorem tailTrace_2224506 : CollatzResearch.WordTrace tailWord_2224506 prefixEnd_2224506 1142240796810578843744689 := by
  unfold tailWord_2224506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20283599819750538055825343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54089599519334768148867581 20283599819750538055825343)
  ·
    refine ⟨30425399729625807083738015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20283599819750538055825343 30425399729625807083738015)
    ·
      refine ⟨45638099594438710625607023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30425399729625807083738015 45638099594438710625607023)
      ·
        refine ⟨68457149391658065938410535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45638099594438710625607023 68457149391658065938410535)
        ·
          refine ⟨102685724087487098907615803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68457149391658065938410535 102685724087487098907615803)
          ·
            refine ⟨154028586131230648361423705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102685724087487098907615803 154028586131230648361423705)
            ·
              refine ⟨115521439598422986271067779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154028586131230648361423705 115521439598422986271067779)
              ·
                refine ⟨173282159397634479406601669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115521439598422986271067779 173282159397634479406601669)
                ·
                  refine ⟨32490404887056464888737813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173282159397634479406601669 32490404887056464888737813)
                  ·
                    refine ⟨1522987729080771791659585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32490404887056464888737813 1522987729080771791659585)
                    ·
                      refine ⟨1142240796810578843744689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522987729080771791659585 1142240796810578843744689)
                      ·
                        rfl

theorem cell23_2224506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_2224506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224506 prefixEnd_2224506 := by exact prefixLift 2224506
  have htrace : WordTrace (prefixWord ++ tailWord_2224506) baseStart_2224506 baseEnd_2224506 := by
    simpa [prefixWord, tailWord_2224506, baseEnd_2224506] using wordTrace_append hprefix tailTrace_2224506
  have hstable : (prefixWord ++ tailWord_2224506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224506).length < 2 ^ (prefixWord ++ tailWord_2224506).sum := by decide
  have hdescent : baseEnd_2224506 < baseStart_2224506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224523 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 4]
def baseStart_2224523 : Nat := 118140960795 + 2224523 * 2 ^ 59
def prefixEnd_2224523 : Nat := 4983230072969 + 3 ^ 40 * 2224523 * 2
def baseEnd_2224523 : Nat := 1142249525981705277232111

theorem tailTrace_2224523 : CollatzResearch.WordTrace tailWord_2224523 prefixEnd_2224523 1142249525981705277232111 := by
  unfold tailWord_2224523
  simp only [CollatzResearch.WordTrace]
  refine ⟨81135019319940564126670223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54090012879960376084446815 81135019319940564126670223)
  ·
    refine ⟨121702528979910846190005335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81135019319940564126670223 121702528979910846190005335)
    ·
      refine ⟨182553793469866269285008003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121702528979910846190005335 182553793469866269285008003)
      ·
        refine ⟨273830690204799403927512005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182553793469866269285008003 273830690204799403927512005)
        ·
          refine ⟨51343254413399888236408501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273830690204799403927512005 51343254413399888236408501)
          ·
            refine ⟨4813430101256239522163297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51343254413399888236408501 4813430101256239522163297)
            ·
              refine ⟨3610072575942179641622473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4813430101256239522163297 3610072575942179641622473)
              ·
                refine ⟨2707554431956634731216855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610072575942179641622473 2707554431956634731216855)
                ·
                  refine ⟨4061331647934952096825283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707554431956634731216855 4061331647934952096825283)
                  ·
                    refine ⟨6091997471902428145237925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4061331647934952096825283 6091997471902428145237925)
                    ·
                      refine ⟨1142249525981705277232111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6091997471902428145237925 1142249525981705277232111)
                      ·
                        rfl

theorem cell23_2224523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 4].length) (baseStart_2224523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224523 prefixEnd_2224523 := by exact prefixLift 2224523
  have htrace : WordTrace (prefixWord ++ tailWord_2224523) baseStart_2224523 baseEnd_2224523 := by
    simpa [prefixWord, tailWord_2224523, baseEnd_2224523] using wordTrace_append hprefix tailTrace_2224523
  have hstable : (prefixWord ++ tailWord_2224523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224523).length < 2 ^ (prefixWord ++ tailWord_2224523).sum := by decide
  have hdescent : baseEnd_2224523 < baseStart_2224523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224543 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2224543 : Nat := 118140960795 + 2224543 * 2 ^ 59
def prefixEnd_2224543 : Nat := 4983230072969 + 3 ^ 40 * 2224543 * 2
def baseEnd_2224543 : Nat := 1142259795594795198982019

theorem tailTrace_2224543 : CollatzResearch.WordTrace tailWord_2224543 prefixEnd_2224543 1142259795594795198982019 := by
  unfold tailWord_2224543
  simp only [CollatzResearch.WordTrace]
  refine ⟨81135748779868107542398283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54090499186578738361598855 81135748779868107542398283)
  ·
    refine ⟨121703623169802161313597425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81135748779868107542398283 121703623169802161313597425)
    ·
      refine ⟨91277717377351620985198069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121703623169802161313597425 91277717377351620985198069)
      ·
        refine ⟨8557286004126714467362319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91277717377351620985198069 8557286004126714467362319)
        ·
          refine ⟨12835929006190071701043479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8557286004126714467362319 12835929006190071701043479)
          ·
            refine ⟨19253893509285107551565219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12835929006190071701043479 19253893509285107551565219)
            ·
              refine ⟨28880840263927661327347829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19253893509285107551565219 28880840263927661327347829)
              ·
                refine ⟨2707578774743218249438859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28880840263927661327347829 2707578774743218249438859)
                ·
                  refine ⟨4061368162114827374158289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707578774743218249438859 4061368162114827374158289)
                  ·
                    refine ⟨3046026121586120530618717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061368162114827374158289 3046026121586120530618717)
                    ·
                      refine ⟨1142259795594795198982019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046026121586120530618717 1142259795594795198982019)
                      ·
                        rfl

theorem cell23_2224543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2224543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224543 prefixEnd_2224543 := by exact prefixLift 2224543
  have htrace : WordTrace (prefixWord ++ tailWord_2224543) baseStart_2224543 baseEnd_2224543 := by
    simpa [prefixWord, tailWord_2224543, baseEnd_2224543] using wordTrace_append hprefix tailTrace_2224543
  have hstable : (prefixWord ++ tailWord_2224543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224543).length < 2 ^ (prefixWord ++ tailWord_2224543).sum := by decide
  have hdescent : baseEnd_2224543 < baseStart_2224543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224579 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_2224579 : Nat := 118140960795 + 2224579 * 2 ^ 59
def prefixEnd_2224579 : Nat := 4983230072969 + 3 ^ 40 * 2224579 * 2
def baseEnd_2224579 : Nat := 1142278280898357058131853

theorem tailTrace_2224579 : CollatzResearch.WordTrace tailWord_2224579 prefixEnd_2224579 1142278280898357058131853 := by
  unfold tailWord_2224579
  simp only [CollatzResearch.WordTrace]
  refine ⟨81137061807737685690708791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54091374538491790460472527 81137061807737685690708791)
  ·
    refine ⟨121705592711606528536063187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81137061807737685690708791 121705592711606528536063187)
    ·
      refine ⟨182558389067409792804094781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121705592711606528536063187 182558389067409792804094781)
      ·
        refine ⟨68459395900278672301535543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182558389067409792804094781 68459395900278672301535543)
        ·
          refine ⟨102689093850418008452303315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68459395900278672301535543 102689093850418008452303315)
          ·
            refine ⟨154033640775627012678454973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102689093850418008452303315 154033640775627012678454973)
            ·
              refine ⟨57762615290860129754420615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154033640775627012678454973 57762615290860129754420615)
              ·
                refine ⟨86643922936290194631630923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57762615290860129754420615 86643922936290194631630923)
                ·
                  refine ⟨129965884404435291947446385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86643922936290194631630923 129965884404435291947446385)
                  ·
                    refine ⟨97474413303326468960584789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129965884404435291947446385 97474413303326468960584789)
                    ·
                      refine ⟨1142278280898357058131853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 97474413303326468960584789 1142278280898357058131853)
                      ·
                        rfl

theorem cell23_2224579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_2224579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224579 prefixEnd_2224579 := by exact prefixLift 2224579
  have htrace : WordTrace (prefixWord ++ tailWord_2224579) baseStart_2224579 baseEnd_2224579 := by
    simpa [prefixWord, tailWord_2224579, baseEnd_2224579] using wordTrace_append hprefix tailTrace_2224579
  have hstable : (prefixWord ++ tailWord_2224579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224579).length < 2 ^ (prefixWord ++ tailWord_2224579).sum := by decide
  have hdescent : baseEnd_2224579 < baseStart_2224579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224594 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2224594 : Nat := 118140960795 + 2224594 * 2 ^ 59
def prefixEnd_2224594 : Nat := 4983230072969 + 3 ^ 40 * 2224594 * 2
def baseEnd_2224594 : Nat := 1142285983108174499444285

theorem tailTrace_2224594 : CollatzResearch.WordTrace tailWord_2224594 prefixEnd_2224594 1142285983108174499444285 := by
  unfold tailWord_2224594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20284402225670835813126209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54091739268455562168336557 20284402225670835813126209)
  ·
    refine ⟨15213301669253126859844657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20284402225670835813126209 15213301669253126859844657)
    ·
      refine ⟨11409976251939845144883493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15213301669253126859844657 11409976251939845144883493)
      ·
        refine ⟨2139370547238720964665655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11409976251939845144883493 2139370547238720964665655)
        ·
          refine ⟨3209055820858081446998483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139370547238720964665655 3209055820858081446998483)
          ·
            refine ⟨4813583731287122170497725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209055820858081446998483 4813583731287122170497725)
            ·
              refine ⟨1805093899232670813936647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4813583731287122170497725 1805093899232670813936647)
              ·
                refine ⟨2707640848849006220904971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805093899232670813936647 2707640848849006220904971)
                ·
                  refine ⟨4061461273273509331357457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707640848849006220904971 4061461273273509331357457)
                  ·
                    refine ⟨3046095954955131998518093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061461273273509331357457 3046095954955131998518093)
                    ·
                      refine ⟨1142285983108174499444285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046095954955131998518093 1142285983108174499444285)
                      ·
                        rfl

theorem cell23_2224594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2224594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224594 prefixEnd_2224594 := by exact prefixLift 2224594
  have htrace : WordTrace (prefixWord ++ tailWord_2224594) baseStart_2224594 baseEnd_2224594 := by
    simpa [prefixWord, tailWord_2224594, baseEnd_2224594] using wordTrace_append hprefix tailTrace_2224594
  have hstable : (prefixWord ++ tailWord_2224594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224594).length < 2 ^ (prefixWord ++ tailWord_2224594).sum := by decide
  have hdescent : baseEnd_2224594 < baseStart_2224594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224660 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2224660 : Nat := 118140960795 + 2224660 * 2 ^ 59
def prefixEnd_2224660 : Nat := 4983230072969 + 3 ^ 40 * 2224660 * 2
def baseEnd_2224660 : Nat := 1142319872831371241218981

theorem tailTrace_2224660 : CollatzResearch.WordTrace tailWord_2224660 prefixEnd_2224660 1142319872831371241218981 := by
  unfold tailWord_2224660
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570008060222118262203717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54093344080296157682938289 40570008060222118262203717)
  ·
    refine ⟨7606876511291647174163197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40570008060222118262203717 7606876511291647174163197)
    ·
      refine ⟨2852578691734367690311199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7606876511291647174163197 2852578691734367690311199)
      ·
        refine ⟨4278868037601551535466799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852578691734367690311199 4278868037601551535466799)
        ·
          refine ⟨6418302056402327303200199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278868037601551535466799 6418302056402327303200199)
          ·
            refine ⟨9627453084603490954800299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418302056402327303200199 9627453084603490954800299)
            ·
              refine ⟨14441179626905236432200449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9627453084603490954800299 14441179626905236432200449)
              ·
                refine ⟨10830884720178927324150337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14441179626905236432200449 10830884720178927324150337)
                ·
                  refine ⟨8123163540134195493112753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10830884720178927324150337 8123163540134195493112753)
                  ·
                    refine ⟨6092372655100646619834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8123163540134195493112753 6092372655100646619834565)
                    ·
                      refine ⟨1142319872831371241218981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6092372655100646619834565 1142319872831371241218981)
                      ·
                        rfl

theorem cell23_2224660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2224660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224660 prefixEnd_2224660 := by exact prefixLift 2224660
  have htrace : WordTrace (prefixWord ++ tailWord_2224660) baseStart_2224660 baseEnd_2224660 := by
    simpa [prefixWord, tailWord_2224660, baseEnd_2224660] using wordTrace_append hprefix tailTrace_2224660
  have hstable : (prefixWord ++ tailWord_2224660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224660).length < 2 ^ (prefixWord ++ tailWord_2224660).sum := by decide
  have hdescent : baseEnd_2224660 < baseStart_2224660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224664 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 2, 2, 2]
def baseStart_2224664 : Nat := 118140960795 + 2224664 * 2 ^ 59
def prefixEnd_2224664 : Nat := 4983230072969 + 3 ^ 40 * 2224664 * 2
def baseEnd_2224664 : Nat := 1142321926753989225568963

theorem tailTrace_2224664 : CollatzResearch.WordTrace tailWord_2224664 prefixEnd_2224664 1142321926753989225568963 := by
  unfold tailWord_2224664
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570081006214872603776523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54093441341619830138368697 40570081006214872603776523)
  ·
    refine ⟨60855121509322308905664785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40570081006214872603776523 60855121509322308905664785)
    ·
      refine ⟨45641341131991731679248589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60855121509322308905664785 45641341131991731679248589)
      ·
        refine ⟨17115502924496899379718221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45641341131991731679248589 17115502924496899379718221)
        ·
          refine ⟨6418313596686337267394333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17115502924496899379718221 6418313596686337267394333)
          ·
            refine ⟨2406867598757376475272875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6418313596686337267394333 2406867598757376475272875)
            ·
              refine ⟨3610301398136064712909313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406867598757376475272875 3610301398136064712909313)
              ·
                refine ⟨2707726048602048534681985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610301398136064712909313 2707726048602048534681985)
                ·
                  refine ⟨2030794536451536401011489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2707726048602048534681985 2030794536451536401011489)
                  ·
                    refine ⟨1523095902338652300758617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2030794536451536401011489 1523095902338652300758617)
                    ·
                      refine ⟨1142321926753989225568963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523095902338652300758617 1142321926753989225568963)
                      ·
                        rfl

theorem cell23_2224664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_2224664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224664 prefixEnd_2224664 := by exact prefixLift 2224664
  have htrace : WordTrace (prefixWord ++ tailWord_2224664) baseStart_2224664 baseEnd_2224664 := by
    simpa [prefixWord, tailWord_2224664, baseEnd_2224664] using wordTrace_append hprefix tailTrace_2224664
  have hstable : (prefixWord ++ tailWord_2224664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224664).length < 2 ^ (prefixWord ++ tailWord_2224664).sum := by decide
  have hdescent : baseEnd_2224664 < baseStart_2224664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224680 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2224680 : Nat := 118140960795 + 2224680 * 2 ^ 59
def prefixEnd_2224680 : Nat := 4983230072969 + 3 ^ 40 * 2224680 * 2
def baseEnd_2224680 : Nat := 1142330142444461162968889

theorem tailTrace_2224680 : CollatzResearch.WordTrace tailWord_2224680 prefixEnd_2224680 1142330142444461162968889 := by
  unfold tailWord_2224680
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570372790185889970067747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54093830386914519960090329 40570372790185889970067747)
  ·
    refine ⟨60855559185278834955101621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40570372790185889970067747 60855559185278834955101621)
    ·
      refine ⟨5705208673619890777040777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60855559185278834955101621 5705208673619890777040777)
      ·
        refine ⟨4278906505214918082780583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5705208673619890777040777 4278906505214918082780583)
        ·
          refine ⟨6418359757822377124170875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278906505214918082780583 6418359757822377124170875)
          ·
            refine ⟨9627539636733565686256313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418359757822377124170875 9627539636733565686256313)
            ·
              refine ⟨7220654727550174264692235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9627539636733565686256313 7220654727550174264692235)
              ·
                refine ⟨10830982091325261397038353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7220654727550174264692235 10830982091325261397038353)
                ·
                  refine ⟨8123236568493946047778765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10830982091325261397038353 8123236568493946047778765)
                  ·
                    refine ⟨3046213713185229767917037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8123236568493946047778765 3046213713185229767917037)
                    ·
                      refine ⟨1142330142444461162968889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046213713185229767917037 1142330142444461162968889)
                      ·
                        rfl

theorem cell23_2224680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2224680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224680 prefixEnd_2224680 := by exact prefixLift 2224680
  have htrace : WordTrace (prefixWord ++ tailWord_2224680) baseStart_2224680 baseEnd_2224680 := by
    simpa [prefixWord, tailWord_2224680, baseEnd_2224680] using wordTrace_append hprefix tailTrace_2224680
  have hstable : (prefixWord ++ tailWord_2224680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224680).length < 2 ^ (prefixWord ++ tailWord_2224680).sum := by decide
  have hdescent : baseEnd_2224680 < baseStart_2224680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224696 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_2224696 : Nat := 118140960795 + 2224696 * 2 ^ 59
def prefixEnd_2224696 : Nat := 4983230072969 + 3 ^ 40 * 2224696 * 2
def baseEnd_2224696 : Nat := 380779452711644366789605

theorem tailTrace_2224696 : CollatzResearch.WordTrace tailWord_2224696 prefixEnd_2224696 380779452711644366789605 := by
  unfold tailWord_2224696
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570664574156907336358971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54094219432209209781811961 40570664574156907336358971)
  ·
    refine ⟨60855996861235361004538457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40570664574156907336358971 60855996861235361004538457)
    ·
      refine ⟨45641997645926520753403843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60855996861235361004538457 45641997645926520753403843)
      ·
        refine ⟨68462996468889781130105765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45641997645926520753403843 68462996468889781130105765)
        ·
          refine ⟨12836811837916833961894831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68462996468889781130105765 12836811837916833961894831)
          ·
            refine ⟨19255217756875250942842247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12836811837916833961894831 19255217756875250942842247)
            ·
              refine ⟨28882826635312876414263371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19255217756875250942842247 28882826635312876414263371)
              ·
                refine ⟨43324239952969314621395057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28882826635312876414263371 43324239952969314621395057)
                ·
                  refine ⟨32493179964726985966046293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43324239952969314621395057 32493179964726985966046293)
                  ·
                    refine ⟨380779452711644366789605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32493179964726985966046293 380779452711644366789605)
                    ·
                      rfl

theorem cell23_2224696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_2224696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224696 prefixEnd_2224696 := by exact prefixLift 2224696
  have htrace : WordTrace (prefixWord ++ tailWord_2224696) baseStart_2224696 baseEnd_2224696 := by
    simpa [prefixWord, tailWord_2224696, baseEnd_2224696] using wordTrace_append hprefix tailTrace_2224696
  have hstable : (prefixWord ++ tailWord_2224696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224696).length < 2 ^ (prefixWord ++ tailWord_2224696).sum := by decide
  have hdescent : baseEnd_2224696 < baseStart_2224696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224703 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_2224703 : Nat := 118140960795 + 2224703 * 2 ^ 59
def prefixEnd_2224703 : Nat := 4983230072969 + 3 ^ 40 * 2224703 * 2
def baseEnd_2224703 : Nat := 1142341952499514572981283

theorem tailTrace_2224703 : CollatzResearch.WordTrace tailWord_2224703 prefixEnd_2224703 1142341952499514572981283 := by
  unfold tailWord_2224703
  simp only [CollatzResearch.WordTrace]
  refine ⟨81141584459288454868222763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54094389639525636578815175 81141584459288454868222763)
  ·
    refine ⟨121712376688932682302334145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81141584459288454868222763 121712376688932682302334145)
    ·
      refine ⟨91284282516699511726750609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121712376688932682302334145 91284282516699511726750609)
      ·
        refine ⟨68463211887524633795062957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91284282516699511726750609 68463211887524633795062957)
        ·
          refine ⟨25673704457821737673148609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68463211887524633795062957 25673704457821737673148609)
          ·
            refine ⟨19255278343366303254861457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25673704457821737673148609 19255278343366303254861457)
            ·
              refine ⟨14441458757524727441146093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19255278343366303254861457 14441458757524727441146093)
              ·
                refine ⟨5415547034071772790429785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14441458757524727441146093 5415547034071772790429785)
                ·
                  refine ⟨4061660275553829592822339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5415547034071772790429785 4061660275553829592822339)
                  ·
                    refine ⟨6092490413330744389233509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4061660275553829592822339 6092490413330744389233509)
                    ·
                      refine ⟨1142341952499514572981283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6092490413330744389233509 1142341952499514572981283)
                      ·
                        rfl

theorem cell23_2224703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_2224703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224703 prefixEnd_2224703 := by exact prefixLift 2224703
  have htrace : WordTrace (prefixWord ++ tailWord_2224703) baseStart_2224703 baseEnd_2224703 := by
    simpa [prefixWord, tailWord_2224703, baseEnd_2224703] using wordTrace_append hprefix tailTrace_2224703
  have hstable : (prefixWord ++ tailWord_2224703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224703).length < 2 ^ (prefixWord ++ tailWord_2224703).sum := by decide
  have hdescent : baseEnd_2224703 < baseStart_2224703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224780 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 4, 3, 2]
def baseStart_2224780 : Nat := 118140960795 + 2224780 * 2 ^ 59
def prefixEnd_2224780 : Nat := 4983230072969 + 3 ^ 40 * 2224780 * 2
def baseEnd_2224780 : Nat := 1142381490509910771718429

theorem tailTrace_2224780 : CollatzResearch.WordTrace tailWord_2224780 prefixEnd_2224780 1142381490509910771718429 := by
  unfold tailWord_2224780
  simp only [CollatzResearch.WordTrace]
  refine ⟨40572196440004748509387897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54096261920006331345850529 40572196440004748509387897)
  ·
    refine ⟨30429147330003561382040923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40572196440004748509387897 30429147330003561382040923)
    ·
      refine ⟨45643720995005342073061385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30429147330003561382040923 45643720995005342073061385)
      ·
        refine ⟨34232790746254006554796039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45643720995005342073061385 34232790746254006554796039)
        ·
          refine ⟨51349186119381009832194059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34232790746254006554796039 51349186119381009832194059)
          ·
            refine ⟨77023779179071514748291089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51349186119381009832194059 77023779179071514748291089)
            ·
              refine ⟨57767834384303636061218317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77023779179071514748291089 57767834384303636061218317)
              ·
                refine ⟨21662937894113863522956869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57767834384303636061218317 21662937894113863522956869)
                ·
                  refine ⟨4061800855146349410554413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21662937894113863522956869 4061800855146349410554413)
                  ·
                    refine ⟨1523175320679881028957905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4061800855146349410554413 1523175320679881028957905)
                    ·
                      refine ⟨1142381490509910771718429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523175320679881028957905 1142381490509910771718429)
                      ·
                        rfl

theorem cell23_2224780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_2224780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224780 prefixEnd_2224780 := by exact prefixLift 2224780
  have htrace : WordTrace (prefixWord ++ tailWord_2224780) baseStart_2224780 baseEnd_2224780 := by
    simpa [prefixWord, tailWord_2224780, baseEnd_2224780] using wordTrace_append hprefix tailTrace_2224780
  have hstable : (prefixWord ++ tailWord_2224780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224780).length < 2 ^ (prefixWord ++ tailWord_2224780).sum := by decide
  have hdescent : baseEnd_2224780 < baseStart_2224780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224787 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 1, 1, 3]
def baseStart_2224787 : Nat := 118140960795 + 2224787 * 2 ^ 59
def prefixEnd_2224787 : Nat := 4983230072969 + 3 ^ 40 * 2224787 * 2
def baseEnd_2224787 : Nat := 1142385084874492244330897

theorem tailTrace_2224787 : CollatzResearch.WordTrace tailWord_2224787 prefixEnd_2224787 1142385084874492244330897 := by
  unfold tailWord_2224787
  simp only [CollatzResearch.WordTrace]
  refine ⟨81144648190984137214280615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54096432127322758142853743 81144648190984137214280615)
  ·
    refine ⟨121716972286476205821420923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81144648190984137214280615 121716972286476205821420923)
    ·
      refine ⟨182575458429714308732131385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121716972286476205821420923 182575458429714308732131385)
      ·
        refine ⟨136931593822285731549098539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182575458429714308732131385 136931593822285731549098539)
        ·
          refine ⟨205397390733428597323647809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136931593822285731549098539 205397390733428597323647809)
          ·
            refine ⟨154048043050071447992735857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205397390733428597323647809 154048043050071447992735857)
            ·
              refine ⟨115536032287553585994551893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154048043050071447992735857 115536032287553585994551893)
              ·
                refine ⟨1353937878369768585873655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 115536032287553585994551893 1353937878369768585873655)
                ·
                  refine ⟨2030906817554652878810483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353937878369768585873655 2030906817554652878810483)
                  ·
                    refine ⟨3046360226331979318215725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2030906817554652878810483 3046360226331979318215725)
                    ·
                      refine ⟨1142385084874492244330897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046360226331979318215725 1142385084874492244330897)
                      ·
                        rfl

theorem cell23_2224787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 1, 3].length) (baseStart_2224787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224787 prefixEnd_2224787 := by exact prefixLift 2224787
  have htrace : WordTrace (prefixWord ++ tailWord_2224787) baseStart_2224787 baseEnd_2224787 := by
    simpa [prefixWord, tailWord_2224787, baseEnd_2224787] using wordTrace_append hprefix tailTrace_2224787
  have hstable : (prefixWord ++ tailWord_2224787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224787).length < 2 ^ (prefixWord ++ tailWord_2224787).sum := by decide
  have hdescent : baseEnd_2224787 < baseStart_2224787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224793 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_2224793 : Nat := 118140960795 + 2224793 * 2 ^ 59
def prefixEnd_2224793 : Nat := 4983230072969 + 3 ^ 40 * 2224793 * 2
def baseEnd_2224793 : Nat := 1142388165758419220855869

theorem tailTrace_2224793 : CollatzResearch.WordTrace tailWord_2224793 prefixEnd_2224793 1142388165758419220855869 := by
  unfold tailWord_2224793
  simp only [CollatzResearch.WordTrace]
  refine ⟨81144867028962400238999033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54096578019308266825999355 81144867028962400238999033)
  ·
    refine ⟨60858650271721800179249275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81144867028962400238999033 60858650271721800179249275)
    ·
      refine ⟨91287975407582700268873913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60858650271721800179249275 91287975407582700268873913)
      ·
        refine ⟨68465981555687025201655435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91287975407582700268873913 68465981555687025201655435)
        ·
          refine ⟨102698972333530537802483153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68465981555687025201655435 102698972333530537802483153)
          ·
            refine ⟨77024229250147903351862365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102698972333530537802483153 77024229250147903351862365)
            ·
              refine ⟨28884085968805463756948387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77024229250147903351862365 28884085968805463756948387)
              ·
                refine ⟨43326128953208195635422581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28884085968805463756948387 43326128953208195635422581)
                ·
                  refine ⟨4061824589363268340820867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43326128953208195635422581 4061824589363268340820867)
                  ·
                    refine ⟨6092736884044902511231301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4061824589363268340820867 6092736884044902511231301)
                    ·
                      refine ⟨1142388165758419220855869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6092736884044902511231301 1142388165758419220855869)
                      ·
                        rfl

theorem cell23_2224793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_2224793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224793 prefixEnd_2224793 := by exact prefixLift 2224793
  have htrace : WordTrace (prefixWord ++ tailWord_2224793) baseStart_2224793 baseEnd_2224793 := by
    simpa [prefixWord, tailWord_2224793, baseEnd_2224793] using wordTrace_append hprefix tailTrace_2224793
  have hstable : (prefixWord ++ tailWord_2224793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224793).length < 2 ^ (prefixWord ++ tailWord_2224793).sum := by decide
  have hdescent : baseEnd_2224793 < baseStart_2224793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224814 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2224814 : Nat := 118140960795 + 2224814 * 2 ^ 59
def prefixEnd_2224814 : Nat := 4983230072969 + 3 ^ 40 * 2224814 * 2
def baseEnd_2224814 : Nat := 1142398948852163638693273

theorem tailTrace_2224814 : CollatzResearch.WordTrace tailWord_2224814 prefixEnd_2224814 1142398948852163638693273 := by
  unfold tailWord_2224814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143204120235790103189187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54097088641257547217008997 10143204120235790103189187)
  ·
    refine ⟨15214806180353685154783781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10143204120235790103189187 15214806180353685154783781)
    ·
      refine ⟨2852776158816315966521959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15214806180353685154783781 2852776158816315966521959)
      ·
        refine ⟨4279164238224473949782939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852776158816315966521959 4279164238224473949782939)
        ·
          refine ⟨6418746357336710924674409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279164238224473949782939 6418746357336710924674409)
          ·
            refine ⟨4814059768002533193505807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418746357336710924674409 4814059768002533193505807)
            ·
              refine ⟨7221089652003799790258711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814059768002533193505807 7221089652003799790258711)
              ·
                refine ⟨10831634478005699685388067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7221089652003799790258711 10831634478005699685388067)
                ·
                  refine ⟨16247451717008549528082101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10831634478005699685388067 16247451717008549528082101)
                  ·
                    refine ⟨1523198598469551518257697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16247451717008549528082101 1523198598469551518257697)
                    ·
                      refine ⟨1142398948852163638693273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523198598469551518257697 1142398948852163638693273)
                      ·
                        rfl

theorem cell23_2224814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2224814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224814 prefixEnd_2224814 := by exact prefixLift 2224814
  have htrace : WordTrace (prefixWord ++ tailWord_2224814) baseStart_2224814 baseEnd_2224814 := by
    simpa [prefixWord, tailWord_2224814, baseEnd_2224814] using wordTrace_append hprefix tailTrace_2224814
  have hstable : (prefixWord ++ tailWord_2224814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224814).length < 2 ^ (prefixWord ++ tailWord_2224814).sum := by decide
  have hdescent : baseEnd_2224814 < baseStart_2224814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224821 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2224821 : Nat := 118140960795 + 2224821 * 2 ^ 59
def prefixEnd_2224821 : Nat := 4983230072969 + 3 ^ 40 * 2224821 * 2
def baseEnd_2224821 : Nat := 1142402543216745111305741

theorem tailTrace_2224821 : CollatzResearch.WordTrace tailWord_2224821 prefixEnd_2224821 1142402543216745111305741 := by
  unfold tailWord_2224821
  simp only [CollatzResearch.WordTrace]
  refine ⟨81145888272860961021018317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54097258848573974014012211 81145888272860961021018317)
  ·
    refine ⟨30429708102322860382881869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81145888272860961021018317 30429708102322860382881869)
    ·
      refine ⟨11411140538371072643580701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30429708102322860382881869 11411140538371072643580701)
      ·
        refine ⟨4279177701889152241342763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11411140538371072643580701 4279177701889152241342763)
        ·
          refine ⟨6418766552833728362014145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279177701889152241342763 6418766552833728362014145)
          ·
            refine ⟨4814074914625296271510609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418766552833728362014145 4814074914625296271510609)
            ·
              refine ⟨3610556185968972203632957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4814074914625296271510609 3610556185968972203632957)
              ·
                refine ⟨1353958569738364576362359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3610556185968972203632957 1353958569738364576362359)
                ·
                  refine ⟨2030937854607546864543539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353958569738364576362359 2030937854607546864543539)
                  ·
                    refine ⟨3046406781911320296815309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2030937854607546864543539 3046406781911320296815309)
                    ·
                      refine ⟨1142402543216745111305741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046406781911320296815309 1142402543216745111305741)
                      ·
                        rfl

theorem cell23_2224821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2224821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224821 prefixEnd_2224821 := by exact prefixLift 2224821
  have htrace : WordTrace (prefixWord ++ tailWord_2224821) baseStart_2224821 baseEnd_2224821 := by
    simpa [prefixWord, tailWord_2224821, baseEnd_2224821] using wordTrace_append hprefix tailTrace_2224821
  have hstable : (prefixWord ++ tailWord_2224821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224821).length < 2 ^ (prefixWord ++ tailWord_2224821).sum := by decide
  have hdescent : baseEnd_2224821 < baseStart_2224821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224830 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2224830 : Nat := 118140960795 + 2224830 * 2 ^ 59
def prefixEnd_2224830 : Nat := 4983230072969 + 3 ^ 40 * 2224830 * 2
def baseEnd_2224830 : Nat := 1142407164542635576093199

theorem tailTrace_2224830 : CollatzResearch.WordTrace tailWord_2224830 prefixEnd_2224830 1142407164542635576093199 := by
  unfold tailWord_2224830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143277066228544444761993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54097477686552237038730629 10143277066228544444761993)
  ·
    refine ⟨7607457799671408333571495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10143277066228544444761993 7607457799671408333571495)
    ·
      refine ⟨11411186699507112500357243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7607457799671408333571495 11411186699507112500357243)
      ·
        refine ⟨17116780049260668750535865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11411186699507112500357243 17116780049260668750535865)
        ·
          refine ⟨12837585036945501562901899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17116780049260668750535865 12837585036945501562901899)
          ·
            refine ⟨19256377555418252344352849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12837585036945501562901899 19256377555418252344352849)
            ·
              refine ⟨14442283166563689258264637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19256377555418252344352849 14442283166563689258264637)
              ·
                refine ⟨5415856187461383471849239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14442283166563689258264637 5415856187461383471849239)
                ·
                  refine ⟨8123784281192075207773859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5415856187461383471849239 8123784281192075207773859)
                  ·
                    refine ⟨12185676421788112811660789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8123784281192075207773859 12185676421788112811660789)
                    ·
                      refine ⟨1142407164542635576093199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12185676421788112811660789 1142407164542635576093199)
                      ·
                        rfl

theorem cell23_2224830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2224830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224830 prefixEnd_2224830 := by exact prefixLift 2224830
  have htrace : WordTrace (prefixWord ++ tailWord_2224830) baseStart_2224830 baseEnd_2224830 := by
    simpa [prefixWord, tailWord_2224830, baseEnd_2224830] using wordTrace_append hprefix tailTrace_2224830
  have hstable : (prefixWord ++ tailWord_2224830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224830).length < 2 ^ (prefixWord ++ tailWord_2224830).sum := by decide
  have hdescent : baseEnd_2224830 < baseStart_2224830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224838 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2224838 : Nat := 118140960795 + 2224838 * 2 ^ 59
def prefixEnd_2224838 : Nat := 4983230072969 + 3 ^ 40 * 2224838 * 2
def baseEnd_2224838 : Nat := 1142411272387871544793163

theorem tailTrace_2224838 : CollatzResearch.WordTrace tailWord_2224838 prefixEnd_2224838 1142411272387871544793163 := by
  unfold tailWord_2224838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535828384806230403887099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54097672209199581949591445 2535828384806230403887099)
  ·
    refine ⟨3803742577209345605830649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2535828384806230403887099 3803742577209345605830649)
    ·
      refine ⟨2852806932907009204372987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3803742577209345605830649 2852806932907009204372987)
      ·
        refine ⟨4279210399360513806559481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852806932907009204372987 4279210399360513806559481)
        ·
          refine ⟨3209407799520385354919611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4279210399360513806559481 3209407799520385354919611)
          ·
            refine ⟨4814111699280578032379417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209407799520385354919611 4814111699280578032379417)
            ·
              refine ⟨3610583774460433524284563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4814111699280578032379417 3610583774460433524284563)
              ·
                refine ⟨5415875661690650286426845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610583774460433524284563 5415875661690650286426845)
                ·
                  refine ⟨2030953373133993857410067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5415875661690650286426845 2030953373133993857410067)
                  ·
                    refine ⟨3046430059700990786115101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2030953373133993857410067 3046430059700990786115101)
                    ·
                      refine ⟨1142411272387871544793163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046430059700990786115101 1142411272387871544793163)
                      ·
                        rfl

theorem cell23_2224838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2224838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224838 prefixEnd_2224838 := by exact prefixLift 2224838
  have htrace : WordTrace (prefixWord ++ tailWord_2224838) baseStart_2224838 baseEnd_2224838 := by
    simpa [prefixWord, tailWord_2224838, baseEnd_2224838] using wordTrace_append hprefix tailTrace_2224838
  have hstable : (prefixWord ++ tailWord_2224838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224838).length < 2 ^ (prefixWord ++ tailWord_2224838).sum := by decide
  have hdescent : baseEnd_2224838 < baseStart_2224838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224843 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 3]
def baseStart_2224843 : Nat := 118140960795 + 2224843 * 2 ^ 59
def prefixEnd_2224843 : Nat := 4983230072969 + 3 ^ 40 * 2224843 * 2
def baseEnd_2224843 : Nat := 1142413839791144025230639

theorem tailTrace_2224843 : CollatzResearch.WordTrace tailWord_2224843 prefixEnd_2224843 1142413839791144025230639 := by
  unfold tailWord_2224843
  simp only [CollatzResearch.WordTrace]
  refine ⟨81146690678781258778319183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54097793785854172518879455 81146690678781258778319183)
  ·
    refine ⟨121720036018171888167478775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81146690678781258778319183 121720036018171888167478775)
    ·
      refine ⟨182580054027257832251218163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121720036018171888167478775 182580054027257832251218163)
      ·
        refine ⟨273870081040886748376827245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182580054027257832251218163 273870081040886748376827245)
        ·
          refine ⟨102701280390332530641310217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273870081040886748376827245 102701280390332530641310217)
          ·
            refine ⟨77025960292749397980982663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102701280390332530641310217 77025960292749397980982663)
            ·
              refine ⟨115538940439124096971473995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77025960292749397980982663 115538940439124096971473995)
              ·
                refine ⟨173308410658686145457210993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115538940439124096971473995 173308410658686145457210993)
                ·
                  refine ⟨129981307994014609092908245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173308410658686145457210993 129981307994014609092908245)
                  ·
                    refine ⟨3046436906109717400615037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129981307994014609092908245 3046436906109717400615037)
                    ·
                      refine ⟨1142413839791144025230639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046436906109717400615037 1142413839791144025230639)
                      ·
                        rfl

theorem cell23_2224843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 3].length) (baseStart_2224843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224843 prefixEnd_2224843 := by exact prefixLift 2224843
  have htrace : WordTrace (prefixWord ++ tailWord_2224843) baseStart_2224843 baseEnd_2224843 := by
    simpa [prefixWord, tailWord_2224843, baseEnd_2224843] using wordTrace_append hprefix tailTrace_2224843
  have hstable : (prefixWord ++ tailWord_2224843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224843).length < 2 ^ (prefixWord ++ tailWord_2224843).sum := by decide
  have hdescent : baseEnd_2224843 < baseStart_2224843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224844 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2224844 : Nat := 118140960795 + 2224844 * 2 ^ 59
def prefixEnd_2224844 : Nat := 4983230072969 + 3 ^ 40 * 2224844 * 2
def baseEnd_2224844 : Nat := 1142414353271798521318135

theorem tailTrace_2224844 : CollatzResearch.WordTrace tailWord_2224844 prefixEnd_2224844 1142414353271798521318135 := by
  unfold tailWord_2224844
  simp only [CollatzResearch.WordTrace]
  refine ⟨40573363575888817974552793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54097818101185090632737057 40573363575888817974552793)
  ·
    refine ⟨30430022681916613480914595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40573363575888817974552793 30430022681916613480914595)
    ·
      refine ⟨45645034022874920221371893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30430022681916613480914595 45645034022874920221371893)
      ·
        refine ⟨4279221939644523770753615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45645034022874920221371893 4279221939644523770753615)
        ·
          refine ⟨6418832909466785656130423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279221939644523770753615 6418832909466785656130423)
          ·
            refine ⟨9628249364200178484195635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418832909466785656130423 9628249364200178484195635)
            ·
              refine ⟨14442374046300267726293453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9628249364200178484195635 14442374046300267726293453)
              ·
                refine ⟨5415890267362600397360045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14442374046300267726293453 5415890267362600397360045)
                ·
                  refine ⟨2030958850260975149010017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5415890267362600397360045 2030958850260975149010017)
                  ·
                    refine ⟨1523219137695731361757513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2030958850260975149010017 1523219137695731361757513)
                    ·
                      refine ⟨1142414353271798521318135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523219137695731361757513 1142414353271798521318135)
                      ·
                        rfl

theorem cell23_2224844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2224844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224844 prefixEnd_2224844 := by exact prefixLift 2224844
  have htrace : WordTrace (prefixWord ++ tailWord_2224844) baseStart_2224844 baseEnd_2224844 := by
    simpa [prefixWord, tailWord_2224844, baseEnd_2224844] using wordTrace_append hprefix tailTrace_2224844
  have hstable : (prefixWord ++ tailWord_2224844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224844).length < 2 ^ (prefixWord ++ tailWord_2224844).sum := by decide
  have hdescent : baseEnd_2224844 < baseStart_2224844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224867 : List Nat := [1, 1, 1, 7, 1, 3, 2, 7]
def baseStart_2224867 : Nat := 118140960795 + 2224867 * 2 ^ 59
def prefixEnd_2224867 : Nat := 4983230072969 + 3 ^ 40 * 2224867 * 2
def baseEnd_2224867 : Nat := 42312080123216738197427

theorem tailTrace_2224867 : CollatzResearch.WordTrace tailWord_2224867 prefixEnd_2224867 42312080123216738197427 := by
  unfold tailWord_2224867
  simp only [CollatzResearch.WordTrace]
  refine ⟨81147566030694310877192855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54098377353796207251461903 81147566030694310877192855)
  ·
    refine ⟨121721349046041466315789283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81147566030694310877192855 121721349046041466315789283)
    ·
      refine ⟨182582023569062199473683925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121721349046041466315789283 182582023569062199473683925)
      ·
        refine ⟨4279266177399895300164467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 182582023569062199473683925 4279266177399895300164467)
        ·
          refine ⟨6418899266099842950246701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279266177399895300164467 6418899266099842950246701)
          ·
            refine ⟨2407087224787441106342513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6418899266099842950246701 2407087224787441106342513)
            ·
              refine ⟨1805315418590580829756885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407087224787441106342513 1805315418590580829756885)
              ·
                refine ⟨42312080123216738197427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1805315418590580829756885 42312080123216738197427)
                ·
                  rfl

theorem cell23_2224867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 7].length) (baseStart_2224867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224867 prefixEnd_2224867 := by exact prefixLift 2224867
  have htrace : WordTrace (prefixWord ++ tailWord_2224867) baseStart_2224867 baseEnd_2224867 := by
    simpa [prefixWord, tailWord_2224867, baseEnd_2224867] using wordTrace_append hprefix tailTrace_2224867
  have hstable : (prefixWord ++ tailWord_2224867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224867).length < 2 ^ (prefixWord ++ tailWord_2224867).sum := by decide
  have hdescent : baseEnd_2224867 < baseStart_2224867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224873 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_2224873 : Nat := 118140960795 + 2224873 * 2 ^ 59
def prefixEnd_2224873 : Nat := 4983230072969 + 3 ^ 40 * 2224873 * 2
def baseEnd_2224873 : Nat := 1142429244210778907855501

theorem tailTrace_2224873 : CollatzResearch.WordTrace tailWord_2224873 prefixEnd_2224873 1142429244210778907855501 := by
  unfold tailWord_2224873
  simp only [CollatzResearch.WordTrace]
  refine ⟨81147784868672573901911273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54098523245781715934607515 81147784868672573901911273)
  ·
    refine ⟨60860838651504430426433455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81147784868672573901911273 60860838651504430426433455)
    ·
      refine ⟨91291257977256645639650183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60860838651504430426433455 91291257977256645639650183)
      ·
        refine ⟨136936886965884968459475275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91291257977256645639650183 136936886965884968459475275)
        ·
          refine ⟨205405330448827452689212913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136936886965884968459475275 205405330448827452689212913)
          ·
            refine ⟨154053997836620589516909685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205405330448827452689212913 154053997836620589516909685)
            ·
              refine ⟨14442562297183180267210283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154053997836620589516909685 14442562297183180267210283)
              ·
                refine ⟨21663843445774770400815425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14442562297183180267210283 21663843445774770400815425)
                ·
                  refine ⟨16247882584331077800611569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21663843445774770400815425 16247882584331077800611569)
                  ·
                    refine ⟨12185911938248308350458677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16247882584331077800611569 12185911938248308350458677)
                    ·
                      refine ⟨1142429244210778907855501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12185911938248308350458677 1142429244210778907855501)
                      ·
                        rfl

theorem cell23_2224873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_2224873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224873 prefixEnd_2224873 := by exact prefixLift 2224873
  have htrace : WordTrace (prefixWord ++ tailWord_2224873) baseStart_2224873 baseEnd_2224873 := by
    simpa [prefixWord, tailWord_2224873, baseEnd_2224873] using wordTrace_append hprefix tailTrace_2224873
  have hstable : (prefixWord ++ tailWord_2224873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224873).length < 2 ^ (prefixWord ++ tailWord_2224873).sum := by decide
  have hdescent : baseEnd_2224873 < baseStart_2224873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224877 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2224877 : Nat := 118140960795 + 2224877 * 2 ^ 59
def prefixEnd_2224877 : Nat := 4983230072969 + 3 ^ 40 * 2224877 * 2
def baseEnd_2224877 : Nat := 1142431298133396892205483

theorem tailTrace_2224877 : CollatzResearch.WordTrace tailWord_2224877 prefixEnd_2224877 1142431298133396892205483 := by
  unfold tailWord_2224877
  simp only [CollatzResearch.WordTrace]
  refine ⟨81147930760658082585056885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54098620507105388390037923 81147930760658082585056885)
  ·
    refine ⟨7607618508811695242349083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81147930760658082585056885 7607618508811695242349083)
    ·
      refine ⟨11411427763217542863523625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7607618508811695242349083 11411427763217542863523625)
      ·
        refine ⟨8558570822413157147642719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11411427763217542863523625 8558570822413157147642719)
        ·
          refine ⟨12837856233619735721464079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558570822413157147642719 12837856233619735721464079)
          ·
            refine ⟨19256784350429603582196119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12837856233619735721464079 19256784350429603582196119)
            ·
              refine ⟨28885176525644405373294179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19256784350429603582196119 28885176525644405373294179)
              ·
                refine ⟨43327764788466608059941269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28885176525644405373294179 43327764788466608059941269)
                ·
                  refine ⟨2030988974459372252809747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43327764788466608059941269 2030988974459372252809747)
                  ·
                    refine ⟨3046483461689058379214621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2030988974459372252809747 3046483461689058379214621)
                    ·
                      refine ⟨1142431298133396892205483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046483461689058379214621 1142431298133396892205483)
                      ·
                        rfl

theorem cell23_2224877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2224877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224877 prefixEnd_2224877 := by exact prefixLift 2224877
  have htrace : WordTrace (prefixWord ++ tailWord_2224877) baseStart_2224877 baseEnd_2224877 := by
    simpa [prefixWord, tailWord_2224877, baseEnd_2224877] using wordTrace_append hprefix tailTrace_2224877
  have hstable : (prefixWord ++ tailWord_2224877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224877).length < 2 ^ (prefixWord ++ tailWord_2224877).sum := by decide
  have hdescent : baseEnd_2224877 < baseStart_2224877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224878 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_2224878 : Nat := 118140960795 + 2224878 * 2 ^ 59
def prefixEnd_2224878 : Nat := 4983230072969 + 3 ^ 40 * 2224878 * 2
def baseEnd_2224878 : Nat := 1142431811614051388292979

theorem tailTrace_2224878 : CollatzResearch.WordTrace tailWord_2224878 prefixEnd_2224878 1142431811614051388292979 := by
  unfold tailWord_2224878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143495904206807469480411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54098644822436306503895525 10143495904206807469480411)
  ·
    refine ⟨15215243856310211204220617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10143495904206807469480411 15215243856310211204220617)
    ·
      refine ⟨11411432892232658403165463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15215243856310211204220617 11411432892232658403165463)
      ·
        refine ⟨17117149338348987604748195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11411432892232658403165463 17117149338348987604748195)
        ·
          refine ⟨25675724007523481407122293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17117149338348987604748195 25675724007523481407122293)
          ·
            refine ⟨2407099125705326381917715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25675724007523481407122293 2407099125705326381917715)
            ·
              refine ⟨3610648688557989572876573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407099125705326381917715 3610648688557989572876573)
              ·
                refine ⟨1353993258209246089828715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3610648688557989572876573 1353993258209246089828715)
                ·
                  refine ⟨2030989887313869134743073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353993258209246089828715 2030989887313869134743073)
                  ·
                    refine ⟨1523242415485401851057305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2030989887313869134743073 1523242415485401851057305)
                    ·
                      refine ⟨1142431811614051388292979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523242415485401851057305 1142431811614051388292979)
                      ·
                        rfl

theorem cell23_2224878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_2224878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224878 prefixEnd_2224878 := by exact prefixLift 2224878
  have htrace : WordTrace (prefixWord ++ tailWord_2224878) baseStart_2224878 baseEnd_2224878 := by
    simpa [prefixWord, tailWord_2224878, baseEnd_2224878] using wordTrace_append hprefix tailTrace_2224878
  have hstable : (prefixWord ++ tailWord_2224878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224878).length < 2 ^ (prefixWord ++ tailWord_2224878).sum := by decide
  have hdescent : baseEnd_2224878 < baseStart_2224878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224883 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4]
def baseStart_2224883 : Nat := 118140960795 + 2224883 * 2 ^ 59
def prefixEnd_2224883 : Nat := 4983230072969 + 3 ^ 40 * 2224883 * 2
def baseEnd_2224883 : Nat := 1142434379017323868730455

theorem tailTrace_2224883 : CollatzResearch.WordTrace tailWord_2224883 prefixEnd_2224883 1142434379017323868730455 := by
  unfold tailWord_2224883
  simp only [CollatzResearch.WordTrace]
  refine ⟨81148149598636345609775303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54098766399090897073183535 81148149598636345609775303)
  ·
    refine ⟨121722224397954518414662955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81148149598636345609775303 121722224397954518414662955)
    ·
      refine ⟨182583336596931777621994433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121722224397954518414662955 182583336596931777621994433)
      ·
        refine ⟨136937502447698833216495825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182583336596931777621994433 136937502447698833216495825)
        ·
          refine ⟨102703126835774124912371869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136937502447698833216495825 102703126835774124912371869)
          ·
            refine ⟨38513672563415296842139451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102703126835774124912371869 38513672563415296842139451)
            ·
              refine ⟨57770508845122945263209177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38513672563415296842139451 57770508845122945263209177)
              ·
                refine ⟨43327881633842208947406883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57770508845122945263209177 43327881633842208947406883)
                ·
                  refine ⟨64991822450763313421110325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43327881633842208947406883 64991822450763313421110325)
                  ·
                    refine ⟨6092983354759060633229093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64991822450763313421110325 6092983354759060633229093)
                    ·
                      refine ⟨1142434379017323868730455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6092983354759060633229093 1142434379017323868730455)
                      ·
                        rfl

theorem cell23_2224883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_2224883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224883 prefixEnd_2224883 := by exact prefixLift 2224883
  have htrace : WordTrace (prefixWord ++ tailWord_2224883) baseStart_2224883 baseEnd_2224883 := by
    simpa [prefixWord, tailWord_2224883, baseEnd_2224883] using wordTrace_append hprefix tailTrace_2224883
  have hstable : (prefixWord ++ tailWord_2224883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224883).length < 2 ^ (prefixWord ++ tailWord_2224883).sum := by decide
  have hdescent : baseEnd_2224883 < baseStart_2224883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224884 : List Nat := [2, 6, 1, 1, 2, 2, 9]
def baseStart_2224884 : Nat := 118140960795 + 2224884 * 2 ^ 59
def prefixEnd_2224884 : Nat := 4983230072969 + 3 ^ 40 * 2224884 * 2
def baseEnd_2224884 : Nat := 14104134475283683516271

theorem tailTrace_2224884 : CollatzResearch.WordTrace tailWord_2224884 prefixEnd_2224884 14104134475283683516271 := by
  unfold tailWord_2224884
  simp only [CollatzResearch.WordTrace]
  refine ⟨40574093035816361390280853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54098790714421815187041137 40574093035816361390280853)
  ·
    refine ⟨1901910611053891940169415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40574093035816361390280853 1901910611053891940169415)
    ·
      refine ⟨2852865916580837910254123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901910611053891940169415 2852865916580837910254123)
      ·
        refine ⟨4279298874871256865381185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852865916580837910254123 4279298874871256865381185)
        ·
          refine ⟨3209474156153442649035889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4279298874871256865381185 3209474156153442649035889)
          ·
            refine ⟨2407105617115081986776917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209474156153442649035889 2407105617115081986776917)
            ·
              refine ⟨14104134475283683516271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2407105617115081986776917 14104134475283683516271)
              ·
                rfl

theorem cell23_2224884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 9].length) (baseStart_2224884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224884 prefixEnd_2224884 := by exact prefixLift 2224884
  have htrace : WordTrace (prefixWord ++ tailWord_2224884) baseStart_2224884 baseEnd_2224884 := by
    simpa [prefixWord, tailWord_2224884, baseEnd_2224884] using wordTrace_append hprefix tailTrace_2224884
  have hstable : (prefixWord ++ tailWord_2224884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224884).length < 2 ^ (prefixWord ++ tailWord_2224884).sum := by decide
  have hdescent : baseEnd_2224884 < baseStart_2224884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224894 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_2224894 : Nat := 118140960795 + 2224894 * 2 ^ 59
def prefixEnd_2224894 : Nat := 4983230072969 + 3 ^ 40 * 2224894 * 2
def baseEnd_2224894 : Nat := 1142440027304523325692905

theorem tailTrace_2224894 : CollatzResearch.WordTrace tailWord_2224894 prefixEnd_2224894 1142440027304523325692905 := by
  unfold tailWord_2224894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143568850199561811053217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54099033867730996325617157 10143568850199561811053217)
  ·
    refine ⟨7607676637649671358289913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10143568850199561811053217 7607676637649671358289913)
    ·
      refine ⟨5705757478237253518717435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7607676637649671358289913 5705757478237253518717435)
      ·
        refine ⟨8558636217355880278076153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5705757478237253518717435 8558636217355880278076153)
        ·
          refine ⟨6418977163016910208557115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8558636217355880278076153 6418977163016910208557115)
          ·
            refine ⟨9628465744525365312835673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418977163016910208557115 9628465744525365312835673)
            ·
              refine ⟨7221349308394023984626755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9628465744525365312835673 7221349308394023984626755)
              ·
                refine ⟨10832023962591035976940133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7221349308394023984626755 10832023962591035976940133)
                ·
                  refine ⟨2031004492985819245676275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10832023962591035976940133 2031004492985819245676275)
                  ·
                    refine ⟨3046506739478728868514413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2031004492985819245676275 3046506739478728868514413)
                    ·
                      refine ⟨1142440027304523325692905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046506739478728868514413 1142440027304523325692905)
                      ·
                        rfl

theorem cell23_2224894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_2224894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224894 prefixEnd_2224894 := by exact prefixLift 2224894
  have htrace : WordTrace (prefixWord ++ tailWord_2224894) baseStart_2224894 baseEnd_2224894 := by
    simpa [prefixWord, tailWord_2224894, baseEnd_2224894] using wordTrace_append hprefix tailTrace_2224894
  have hstable : (prefixWord ++ tailWord_2224894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224894).length < 2 ^ (prefixWord ++ tailWord_2224894).sum := by decide
  have hdescent : baseEnd_2224894 < baseStart_2224894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224900 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2224900 : Nat := 118140960795 + 2224900 * 2 ^ 59
def prefixEnd_2224900 : Nat := 4983230072969 + 3 ^ 40 * 2224900 * 2
def baseEnd_2224900 : Nat := 1142443108188450302217877

theorem tailTrace_2224900 : CollatzResearch.WordTrace tailWord_2224900 prefixEnd_2224900 1142443108188450302217877 := by
  unfold tailWord_2224900
  simp only [CollatzResearch.WordTrace]
  refine ⟨40574384819787378756572077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54099179759716505008762769 40574384819787378756572077)
  ·
    refine ⟨15215394307420267033714529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40574384819787378756572077 15215394307420267033714529)
    ·
      refine ⟨11411545730565200275285897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15215394307420267033714529 11411545730565200275285897)
      ·
        refine ⟨8558659297923900206464423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11411545730565200275285897 8558659297923900206464423)
        ·
          refine ⟨12837988946885850309696635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558659297923900206464423 12837988946885850309696635)
          ·
            refine ⟨19256983420328775464544953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12837988946885850309696635 19256983420328775464544953)
            ·
              refine ⟨14442737565246581598408715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19256983420328775464544953 14442737565246581598408715)
              ·
                refine ⟨21664106347869872397613073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14442737565246581598408715 21664106347869872397613073)
                ·
                  refine ⟨16248079760902404298209805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21664106347869872397613073 16248079760902404298209805)
                  ·
                    refine ⟨6093029910338401611828677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16248079760902404298209805 6093029910338401611828677)
                    ·
                      refine ⟨1142443108188450302217877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6093029910338401611828677 1142443108188450302217877)
                      ·
                        rfl

theorem cell23_2224900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2224900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224900 prefixEnd_2224900 := by exact prefixLift 2224900
  have htrace : WordTrace (prefixWord ++ tailWord_2224900) baseStart_2224900 baseEnd_2224900 := by
    simpa [prefixWord, tailWord_2224900, baseEnd_2224900] using wordTrace_append hprefix tailTrace_2224900
  have hstable : (prefixWord ++ tailWord_2224900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224900).length < 2 ^ (prefixWord ++ tailWord_2224900).sum := by decide
  have hdescent : baseEnd_2224900 < baseStart_2224900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224917 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_2224917 : Nat := 118140960795 + 2224917 * 2 ^ 59
def prefixEnd_2224917 : Nat := 4983230072969 + 3 ^ 40 * 2224917 * 2
def baseEnd_2224917 : Nat := 1142451837359576735705299

theorem tailTrace_2224917 : CollatzResearch.WordTrace tailWord_2224917 prefixEnd_2224917 1142451837359576735705299 := by
  unfold tailWord_2224917
  simp only [CollatzResearch.WordTrace]
  refine ⟨81149389680513169416513005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54099593120342112944342003 81149389680513169416513005)
  ·
    refine ⟨30431021130192438531192377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81149389680513169416513005 30431021130192438531192377)
    ·
      refine ⟨22823265847644328898394283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30431021130192438531192377 22823265847644328898394283)
      ·
        refine ⟨34234898771466493347591425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22823265847644328898394283 34234898771466493347591425)
        ·
          refine ⟨25676174078599870010693569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34234898771466493347591425 25676174078599870010693569)
          ·
            refine ⟨19257130558949902508020177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25676174078599870010693569 19257130558949902508020177)
            ·
              refine ⟨14442847919212426881015133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19257130558949902508020177 14442847919212426881015133)
              ·
                refine ⟨5416067969704660080380675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14442847919212426881015133 5416067969704660080380675)
                ·
                  refine ⟨8124101954556990120571013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5416067969704660080380675 8124101954556990120571013)
                  ·
                    refine ⟨1523269116479435647607065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8124101954556990120571013 1523269116479435647607065)
                    ·
                      refine ⟨1142451837359576735705299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523269116479435647607065 1142451837359576735705299)
                      ·
                        rfl

theorem cell23_2224917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_2224917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224917 prefixEnd_2224917 := by exact prefixLift 2224917
  have htrace : WordTrace (prefixWord ++ tailWord_2224917) baseStart_2224917 baseEnd_2224917 := by
    simpa [prefixWord, tailWord_2224917, baseEnd_2224917] using wordTrace_append hprefix tailTrace_2224917
  have hstable : (prefixWord ++ tailWord_2224917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224917).length < 2 ^ (prefixWord ++ tailWord_2224917).sum := by decide
  have hdescent : baseEnd_2224917 < baseStart_2224917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224943 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_2224943 : Nat := 118140960795 + 2224943 * 2 ^ 59
def prefixEnd_2224943 : Nat := 4983230072969 + 3 ^ 40 * 2224943 * 2
def baseEnd_2224943 : Nat := 1142465187856593633980179

theorem tailTrace_2224943 : CollatzResearch.WordTrace tailWord_2224943 prefixEnd_2224943 1142465187856593633980179 := by
  unfold tailWord_2224943
  simp only [CollatzResearch.WordTrace]
  refine ⟨81150337978418975856959483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54100225318945983904639655 81150337978418975856959483)
  ·
    refine ⟨121725506967628463785439225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81150337978418975856959483 121725506967628463785439225)
    ·
      refine ⟨91294130225721347839079419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121725506967628463785439225 91294130225721347839079419)
      ·
        refine ⟨136941195338582021758619129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91294130225721347839079419 136941195338582021758619129)
        ·
          refine ⟨102705896503936516318964347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136941195338582021758619129 102705896503936516318964347)
          ·
            refine ⟨154058844755904774478446521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102705896503936516318964347 154058844755904774478446521)
            ·
              refine ⟨115544133566928580858834891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154058844755904774478446521 115544133566928580858834891)
              ·
                refine ⟨173316200350392871288252337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115544133566928580858834891 173316200350392871288252337)
                ·
                  refine ⟨129987150262794653466189253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173316200350392871288252337 129987150262794653466189253)
                  ·
                    refine ⟨24372590674273997524910485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129987150262794653466189253 24372590674273997524910485)
                    ·
                      refine ⟨1142465187856593633980179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24372590674273997524910485 1142465187856593633980179)
                      ·
                        rfl

theorem cell23_2224943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_2224943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2224943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2224943 prefixEnd_2224943 := by exact prefixLift 2224943
  have htrace : WordTrace (prefixWord ++ tailWord_2224943) baseStart_2224943 baseEnd_2224943 := by
    simpa [prefixWord, tailWord_2224943, baseEnd_2224943] using wordTrace_append hprefix tailTrace_2224943
  have hstable : (prefixWord ++ tailWord_2224943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224943).length < 2 ^ (prefixWord ++ tailWord_2224943).sum := by decide
  have hdescent : baseEnd_2224943 < baseStart_2224943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225010 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2225010 : Nat := 118140960795 + 2225010 * 2 ^ 59
def prefixEnd_2225010 : Nat := 4983230072969 + 3 ^ 40 * 2225010 * 2
def baseEnd_2225010 : Nat := 1142499591060444871842371

theorem tailTrace_2225010 : CollatzResearch.WordTrace tailWord_2225010 prefixEnd_2225010 1142499591060444871842371 := by
  unfold tailWord_2225010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20288195417294061574912121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54101854446117497533098989 20288195417294061574912121)
  ·
    refine ⟨15216146562970546181184091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20288195417294061574912121 15216146562970546181184091)
    ·
      refine ⟨22824219844455819271776137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15216146562970546181184091 22824219844455819271776137)
      ·
        refine ⟨17118164883341864453832103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22824219844455819271776137 17118164883341864453832103)
        ·
          refine ⟨25677247325012796680748155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17118164883341864453832103 25677247325012796680748155)
          ·
            refine ⟨38515870987519195021122233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25677247325012796680748155 38515870987519195021122233)
            ·
              refine ⟨28886903240639396265841675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38515870987519195021122233 28886903240639396265841675)
              ·
                refine ⟨43330354860959094398762513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28886903240639396265841675 43330354860959094398762513)
                ·
                  refine ⟨32497766145719320799071885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43330354860959094398762513 32497766145719320799071885)
                  ·
                    refine ⟨12186662304644745299651957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32497766145719320799071885 12186662304644745299651957)
                    ·
                      refine ⟨1142499591060444871842371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12186662304644745299651957 1142499591060444871842371)
                      ·
                        rfl

theorem cell23_2225010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2225010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225010 prefixEnd_2225010 := by exact prefixLift 2225010
  have htrace : WordTrace (prefixWord ++ tailWord_2225010) baseStart_2225010 baseEnd_2225010 := by
    simpa [prefixWord, tailWord_2225010, baseEnd_2225010] using wordTrace_append hprefix tailTrace_2225010
  have hstable : (prefixWord ++ tailWord_2225010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225010).length < 2 ^ (prefixWord ++ tailWord_2225010).sum := by decide
  have hdescent : baseEnd_2225010 < baseStart_2225010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225017 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 3, 4]
def baseStart_2225017 : Nat := 118140960795 + 2225017 * 2 ^ 59
def prefixEnd_2225017 : Nat := 4983230072969 + 3 ^ 40 * 2225017 * 2
def baseEnd_2225017 : Nat := 380834395141675448151613

theorem tailTrace_2225017 : CollatzResearch.WordTrace tailWord_2225017 prefixEnd_2225017 380834395141675448151613 := by
  unfold tailWord_2225017
  simp only [CollatzResearch.WordTrace]
  refine ⟨81153036980150886495153305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54102024653433924330102203 81153036980150886495153305)
  ·
    refine ⟨60864777735113164871364979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81153036980150886495153305 60864777735113164871364979)
    ·
      refine ⟨91297166602669747307047469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60864777735113164871364979 91297166602669747307047469)
      ·
        refine ⟨34236437476001155240142801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91297166602669747307047469 34236437476001155240142801)
        ·
          refine ⟨25677328107000866430107101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34236437476001155240142801 25677328107000866430107101)
          ·
            refine ⟨9628998040125324911290163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25677328107000866430107101 9628998040125324911290163)
            ·
              refine ⟨14443497060187987366935245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9628998040125324911290163 14443497060187987366935245)
              ·
                refine ⟨5416311397570495262600717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14443497060187987366935245 5416311397570495262600717)
                ·
                  refine ⟨2031116774088935723475269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5416311397570495262600717 2031116774088935723475269)
                  ·
                    refine ⟨380834395141675448151613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031116774088935723475269 380834395141675448151613)
                    ·
                      rfl

theorem cell23_2225017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_2225017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225017 prefixEnd_2225017 := by exact prefixLift 2225017
  have htrace : WordTrace (prefixWord ++ tailWord_2225017) baseStart_2225017 baseEnd_2225017 := by
    simpa [prefixWord, tailWord_2225017, baseEnd_2225017] using wordTrace_append hprefix tailTrace_2225017
  have hstable : (prefixWord ++ tailWord_2225017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225017).length < 2 ^ (prefixWord ++ tailWord_2225017).sum := by decide
  have hdescent : baseEnd_2225017 < baseStart_2225017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225034 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_2225034 : Nat := 118140960795 + 2225034 * 2 ^ 59
def prefixEnd_2225034 : Nat := 4983230072969 + 3 ^ 40 * 2225034 * 2
def baseEnd_2225034 : Nat := 380837304865384259314087

theorem tailTrace_2225034 : CollatzResearch.WordTrace tailWord_2225034 prefixEnd_2225034 380837304865384259314087 := by
  unfold tailWord_2225034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20288414255272324599630539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54102438014059532265681437 20288414255272324599630539)
  ·
    refine ⟨30432621382908486899445809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20288414255272324599630539 30432621382908486899445809)
    ·
      refine ⟨22824466037181365174584357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30432621382908486899445809 22824466037181365174584357)
      ·
        refine ⟨4279587381971505970234567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22824466037181365174584357 4279587381971505970234567)
        ·
          refine ⟨6419381072957258955351851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279587381971505970234567 6419381072957258955351851)
          ·
            refine ⟨9629071609435888433027777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419381072957258955351851 9629071609435888433027777)
            ·
              refine ⟨7221803707076916324770833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9629071609435888433027777 7221803707076916324770833)
              ·
                refine ⟨5416352780307687243578125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7221803707076916324770833 5416352780307687243578125)
                ·
                  refine ⟨2031132292615382716341797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5416352780307687243578125 2031132292615382716341797)
                  ·
                    refine ⟨380837304865384259314087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031132292615382716341797 380837304865384259314087)
                    ·
                      rfl

theorem cell23_2225034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_2225034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225034 prefixEnd_2225034 := by exact prefixLift 2225034
  have htrace : WordTrace (prefixWord ++ tailWord_2225034) baseStart_2225034 baseEnd_2225034 := by
    simpa [prefixWord, tailWord_2225034, baseEnd_2225034] using wordTrace_append hprefix tailTrace_2225034
  have hstable : (prefixWord ++ tailWord_2225034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225034).length < 2 ^ (prefixWord ++ tailWord_2225034).sum := by decide
  have hdescent : baseEnd_2225034 < baseStart_2225034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225044 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2225044 : Nat := 118140960795 + 2225044 * 2 ^ 59
def prefixEnd_2225044 : Nat := 4983230072969 + 3 ^ 40 * 2225044 * 2
def baseEnd_2225044 : Nat := 1142517049402697738817215

theorem tailTrace_2225044 : CollatzResearch.WordTrace tailWord_2225044 prefixEnd_2225044 1142517049402697738817215 := by
  unfold tailWord_2225044
  simp only [CollatzResearch.WordTrace]
  refine ⟨40577010875526535053193093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54102681167368713404257457 40577010875526535053193093)
  ·
    refine ⟨7608189539161225322473705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40577010875526535053193093 7608189539161225322473705)
    ·
      refine ⟨5706142154370918991855279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7608189539161225322473705 5706142154370918991855279)
      ·
        refine ⟨8559213231556378487782919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5706142154370918991855279 8559213231556378487782919)
        ·
          refine ⟨12838819847334567731674379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559213231556378487782919 12838819847334567731674379)
          ·
            refine ⟨19258229771001851597511569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12838819847334567731674379 19258229771001851597511569)
            ·
              refine ⟨14443672328251388698133677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19258229771001851597511569 14443672328251388698133677)
              ·
                refine ⟨5416377123094270761800129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14443672328251388698133677 5416377123094270761800129)
                ·
                  refine ⟨4062282842320703071350097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5416377123094270761800129 4062282842320703071350097)
                  ·
                    refine ⟨3046712131740527303512573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062282842320703071350097 3046712131740527303512573)
                    ·
                      refine ⟨1142517049402697738817215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046712131740527303512573 1142517049402697738817215)
                      ·
                        rfl

theorem cell23_2225044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2225044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225044 prefixEnd_2225044 := by exact prefixLift 2225044
  have htrace : WordTrace (prefixWord ++ tailWord_2225044) baseStart_2225044 baseEnd_2225044 := by
    simpa [prefixWord, tailWord_2225044, baseEnd_2225044] using wordTrace_append hprefix tailTrace_2225044
  have hstable : (prefixWord ++ tailWord_2225044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225044).length < 2 ^ (prefixWord ++ tailWord_2225044).sum := by decide
  have hdescent : baseEnd_2225044 < baseStart_2225044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225077 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2225077 : Nat := 118140960795 + 2225077 * 2 ^ 59
def prefixEnd_2225077 : Nat := 4983230072969 + 3 ^ 40 * 2225077 * 2
def baseEnd_2225077 : Nat := 380844664754765369901521

theorem tailTrace_2225077 : CollatzResearch.WordTrace tailWord_2225077 prefixEnd_2225077 380844664754765369901521 := by
  unfold tailWord_2225077
  simp only [CollatzResearch.WordTrace]
  refine ⟨81155225359933516742337485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54103483573289011161558323 81155225359933516742337485)
  ·
    refine ⟨30433209509975068778376557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81155225359933516742337485 30433209509975068778376557)
    ·
      refine ⟨11412453566240650791891209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30433209509975068778376557 11412453566240650791891209)
      ·
        refine ⟨8559340174680488093918407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11412453566240650791891209 8559340174680488093918407)
        ·
          refine ⟨12839010262020732140877611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559340174680488093918407 12839010262020732140877611)
          ·
            refine ⟨19258515393031098211316417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12839010262020732140877611 19258515393031098211316417)
            ·
              refine ⟨14443886544773323658487313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19258515393031098211316417 14443886544773323658487313)
              ·
                refine ⟨10832914908579992743865485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14443886544773323658487313 10832914908579992743865485)
                ·
                  refine ⟨4062343090717497278949557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10832914908579992743865485 4062343090717497278949557)
                  ·
                    refine ⟨380844664754765369901521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4062343090717497278949557 380844664754765369901521)
                    ·
                      rfl

theorem cell23_2225077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2225077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225077 prefixEnd_2225077 := by exact prefixLift 2225077
  have htrace : WordTrace (prefixWord ++ tailWord_2225077) baseStart_2225077 baseEnd_2225077 := by
    simpa [prefixWord, tailWord_2225077, baseEnd_2225077] using wordTrace_append hprefix tailTrace_2225077
  have hstable : (prefixWord ++ tailWord_2225077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225077).length < 2 ^ (prefixWord ++ tailWord_2225077).sum := by decide
  have hdescent : baseEnd_2225077 < baseStart_2225077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225125 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2225125 : Nat := 118140960795 + 2225125 * 2 ^ 59
def prefixEnd_2225125 : Nat := 4983230072969 + 3 ^ 40 * 2225125 * 2
def baseEnd_2225125 : Nat := 1142558641335711921904343

theorem tailTrace_2225125 : CollatzResearch.WordTrace tailWord_2225125 prefixEnd_2225125 1142558641335711921904343 := by
  unfold tailWord_2225125
  simp only [CollatzResearch.WordTrace]
  refine ⟨81156976063759620940084829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54104650709173080626723219 81156976063759620940084829)
  ·
    refine ⟨30433866023909857852531811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81156976063759620940084829 30433866023909857852531811)
    ·
      refine ⟨45650799035864786778797717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30433866023909857852531811 45650799035864786778797717)
      ·
        refine ⟨2139881204806161880256143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45650799035864786778797717 2139881204806161880256143)
        ·
          refine ⟨3209821807209242820384215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139881204806161880256143 3209821807209242820384215)
          ·
            refine ⟨4814732710813864230576323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209821807209242820384215 4814732710813864230576323)
            ·
              refine ⟨7222099066220796345864485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814732710813864230576323 7222099066220796345864485)
              ·
                refine ⟨1354143574916399314849591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7222099066220796345864485 1354143574916399314849591)
                ·
                  refine ⟨2031215362374598972274387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354143574916399314849591 2031215362374598972274387)
                  ·
                    refine ⟨3046823043561898458411581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2031215362374598972274387 3046823043561898458411581)
                    ·
                      refine ⟨1142558641335711921904343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046823043561898458411581 1142558641335711921904343)
                      ·
                        rfl

theorem cell23_2225125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2225125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225125 prefixEnd_2225125 := by exact prefixLift 2225125
  have htrace : WordTrace (prefixWord ++ tailWord_2225125) baseStart_2225125 baseEnd_2225125 := by
    simpa [prefixWord, tailWord_2225125, baseEnd_2225125] using wordTrace_append hprefix tailTrace_2225125
  have hstable : (prefixWord ++ tailWord_2225125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225125).length < 2 ^ (prefixWord ++ tailWord_2225125).sum := by decide
  have hdescent : baseEnd_2225125 < baseStart_2225125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225137 : List Nat := [1, 2, 2, 2, 4, 1, 3, 8]
def baseStart_2225137 : Nat := 118140960795 + 2225137 * 2 ^ 59
def prefixEnd_2225137 : Nat := 4983230072969 + 3 ^ 40 * 2225137 * 2
def baseEnd_2225137 : Nat := 42317214929761699072381

theorem tailTrace_2225137 : CollatzResearch.WordTrace tailWord_2225137 prefixEnd_2225137 42317214929761699072381 := by
  unfold tailWord_2225137
  simp only [CollatzResearch.WordTrace]
  refine ⟨81157413739716146989521665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54104942493144097993014443 81157413739716146989521665)
  ·
    refine ⟨60868060304787110242141249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81157413739716146989521665 60868060304787110242141249)
    ·
      refine ⟨45651045228590332681605937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60868060304787110242141249 45651045228590332681605937)
      ·
        refine ⟨34238283921442749511204453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45651045228590332681605937 34238283921442749511204453)
        ·
          refine ⟨6419678235270515533350835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34238283921442749511204453 6419678235270515533350835)
          ·
            refine ⟨9629517352905773300026253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419678235270515533350835 9629517352905773300026253)
            ·
              refine ⟨3611069007339664987509845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9629517352905773300026253 3611069007339664987509845)
              ·
                refine ⟨42317214929761699072381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3611069007339664987509845 42317214929761699072381)
                ·
                  rfl

theorem cell23_2225137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 8].length) (baseStart_2225137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225137 prefixEnd_2225137 := by exact prefixLift 2225137
  have htrace : WordTrace (prefixWord ++ tailWord_2225137) baseStart_2225137 baseEnd_2225137 := by
    simpa [prefixWord, tailWord_2225137, baseEnd_2225137] using wordTrace_append hprefix tailTrace_2225137
  have hstable : (prefixWord ++ tailWord_2225137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225137).length < 2 ^ (prefixWord ++ tailWord_2225137).sum := by decide
  have hdescent : baseEnd_2225137 < baseStart_2225137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225164 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_2225164 : Nat := 118140960795 + 2225164 * 2 ^ 59
def prefixEnd_2225164 : Nat := 4983230072969 + 3 ^ 40 * 2225164 * 2
def baseEnd_2225164 : Nat := 1142578667081237269316663

theorem tailTrace_2225164 : CollatzResearch.WordTrace tailWord_2225164 prefixEnd_2225164 1142578667081237269316663 := by
  unfold tailWord_2225164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40579199255309165300377273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54105599007078887067169697 40579199255309165300377273)
  ·
    refine ⟨30434399441481873975282955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40579199255309165300377273 30434399441481873975282955)
    ·
      refine ⟨45651599162222810962924433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30434399441481873975282955 45651599162222810962924433)
      ·
        refine ⟨34238699371667108222193325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45651599162222810962924433 34238699371667108222193325)
        ·
          refine ⟨12839512264375165583322497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34238699371667108222193325 12839512264375165583322497)
          ·
            refine ⟨9629634198281374187491873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12839512264375165583322497 9629634198281374187491873)
            ·
              refine ⟨7222225648711030640618905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9629634198281374187491873 7222225648711030640618905)
              ·
                refine ⟨5416669236533272980464179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7222225648711030640618905 5416669236533272980464179)
                ·
                  refine ⟨8125003854799909470696269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5416669236533272980464179 8125003854799909470696269)
                  ·
                    refine ⟨3046876445549966051511101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8125003854799909470696269 3046876445549966051511101)
                    ·
                      refine ⟨1142578667081237269316663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3046876445549966051511101 1142578667081237269316663)
                      ·
                        rfl

theorem cell23_2225164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_2225164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225164 prefixEnd_2225164 := by exact prefixLift 2225164
  have htrace : WordTrace (prefixWord ++ tailWord_2225164) baseStart_2225164 baseEnd_2225164 := by
    simpa [prefixWord, tailWord_2225164, baseEnd_2225164] using wordTrace_append hprefix tailTrace_2225164
  have hstable : (prefixWord ++ tailWord_2225164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225164).length < 2 ^ (prefixWord ++ tailWord_2225164).sum := by decide
  have hdescent : baseEnd_2225164 < baseStart_2225164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225207 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_2225207 : Nat := 118140960795 + 2225207 * 2 ^ 59
def prefixEnd_2225207 : Nat := 4983230072969 + 3 ^ 40 * 2225207 * 2
def baseEnd_2225207 : Nat := 1142600746749380601078965

theorem tailTrace_2225207 : CollatzResearch.WordTrace tailWord_2225207 prefixEnd_2225207 1142600746749380601078965 := by
  unfold tailWord_2225207
  simp only [CollatzResearch.WordTrace]
  refine ⟨81159966849462548944569875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54106644566308365963046583 81159966849462548944569875)
  ·
    refine ⟨121739950274193823416854813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81159966849462548944569875 121739950274193823416854813)
    ·
      refine ⟨45652481352822683781320555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121739950274193823416854813 45652481352822683781320555)
      ·
        refine ⟨68478722029234025671980833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45652481352822683781320555 68478722029234025671980833)
        ·
          refine ⟨51359041521925519253985625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68478722029234025671980833 51359041521925519253985625)
          ·
            refine ⟨38519281141444139440489219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51359041521925519253985625 38519281141444139440489219)
            ·
              refine ⟨57778921712166209160733829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38519281141444139440489219 57778921712166209160733829)
              ·
                refine ⟨10833547821031164217637593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57778921712166209160733829 10833547821031164217637593)
                ·
                  refine ⟨8125160865773373163228195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10833547821031164217637593 8125160865773373163228195)
                  ·
                    refine ⟨12187741298660059744842293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8125160865773373163228195 12187741298660059744842293)
                    ·
                      refine ⟨1142600746749380601078965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12187741298660059744842293 1142600746749380601078965)
                      ·
                        rfl

theorem cell23_2225207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_2225207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225207 prefixEnd_2225207 := by exact prefixLift 2225207
  have htrace : WordTrace (prefixWord ++ tailWord_2225207) baseStart_2225207 baseEnd_2225207 := by
    simpa [prefixWord, tailWord_2225207, baseEnd_2225207] using wordTrace_append hprefix tailTrace_2225207
  have hstable : (prefixWord ++ tailWord_2225207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225207).length < 2 ^ (prefixWord ++ tailWord_2225207).sum := by decide
  have hdescent : baseEnd_2225207 < baseStart_2225207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225208 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 1, 3, 2]
def baseStart_2225208 : Nat := 118140960795 + 2225208 * 2 ^ 59
def prefixEnd_2225208 : Nat := 4983230072969 + 3 ^ 40 * 2225208 * 2
def baseEnd_2225208 : Nat := 1142601260230035097166461

theorem tailTrace_2225208 : CollatzResearch.WordTrace tailWord_2225208 prefixEnd_2225208 1142601260230035097166461 := by
  unfold tailWord_2225208
  simp only [CollatzResearch.WordTrace]
  refine ⟨40580001661229463057678139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54106668881639284076904185 40580001661229463057678139)
  ·
    refine ⟨60870002491844194586517209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40580001661229463057678139 60870002491844194586517209)
    ·
      refine ⟨45652501868883145939887907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60870002491844194586517209 45652501868883145939887907)
      ·
        refine ⟨68478752803324718909831861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45652501868883145939887907 68478752803324718909831861)
        ·
          refine ⟨6419883075311692397796737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68478752803324718909831861 6419883075311692397796737)
          ·
            refine ⟨4814912306483769298347553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6419883075311692397796737 4814912306483769298347553)
            ·
              refine ⟨3611184229862826973760665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4814912306483769298347553 3611184229862826973760665)
              ·
                refine ⟨2708388172397120230320499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611184229862826973760665 2708388172397120230320499)
                ·
                  refine ⟨4062582258595680345480749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708388172397120230320499 4062582258595680345480749)
                  ·
                    refine ⟨1523468346973380129555281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4062582258595680345480749 1523468346973380129555281)
                    ·
                      refine ⟨1142601260230035097166461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523468346973380129555281 1142601260230035097166461)
                      ·
                        rfl

theorem cell23_2225208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_2225208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225208 prefixEnd_2225208 := by exact prefixLift 2225208
  have htrace : WordTrace (prefixWord ++ tailWord_2225208) baseStart_2225208 baseEnd_2225208 := by
    simpa [prefixWord, tailWord_2225208, baseEnd_2225208] using wordTrace_append hprefix tailTrace_2225208
  have hstable : (prefixWord ++ tailWord_2225208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225208).length < 2 ^ (prefixWord ++ tailWord_2225208).sum := by decide
  have hdescent : baseEnd_2225208 < baseStart_2225208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225221 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 4, 2, 2]
def baseStart_2225221 : Nat := 118140960795 + 2225221 * 2 ^ 59
def prefixEnd_2225221 : Nat := 4983230072969 + 3 ^ 40 * 2225221 * 2
def baseEnd_2225221 : Nat := 1142607935478543546303901

theorem tailTrace_2225221 : CollatzResearch.WordTrace tailWord_2225221 prefixEnd_2225221 1142607935478543546303901 := by
  unfold tailWord_2225221
  simp only [CollatzResearch.WordTrace]
  refine ⟨81160477471411829335579517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54106984980941219557053011 81160477471411829335579517)
  ·
    refine ⟨30435179051779436000842319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81160477471411829335579517 30435179051779436000842319)
    ·
      refine ⟨45652768577669154001263479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30435179051779436000842319 45652768577669154001263479)
      ·
        refine ⟨68479152866503731001895219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45652768577669154001263479 68479152866503731001895219)
        ·
          refine ⟨102718729299755596502842829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68479152866503731001895219 102718729299755596502842829)
          ·
            refine ⟨38519523487408348688566061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102718729299755596502842829 38519523487408348688566061)
            ·
              refine ⟨14444821307778130758212273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38519523487408348688566061 14444821307778130758212273)
              ·
                refine ⟨10833615980833598068659205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14444821307778130758212273 10833615980833598068659205)
                ·
                  refine ⟨2031302996406299637873601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10833615980833598068659205 2031302996406299637873601)
                  ·
                    refine ⟨1523477247304724728405201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2031302996406299637873601 1523477247304724728405201)
                    ·
                      refine ⟨1142607935478543546303901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523477247304724728405201 1142607935478543546303901)
                      ·
                        rfl

theorem cell23_2225221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_2225221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225221 prefixEnd_2225221 := by exact prefixLift 2225221
  have htrace : WordTrace (prefixWord ++ tailWord_2225221) baseStart_2225221 baseEnd_2225221 := by
    simpa [prefixWord, tailWord_2225221, baseEnd_2225221] using wordTrace_append hprefix tailTrace_2225221
  have hstable : (prefixWord ++ tailWord_2225221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225221).length < 2 ^ (prefixWord ++ tailWord_2225221).sum := by decide
  have hdescent : baseEnd_2225221 < baseStart_2225221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225237 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2225237 : Nat := 118140960795 + 2225237 * 2 ^ 59
def prefixEnd_2225237 : Nat := 4983230072969 + 3 ^ 40 * 2225237 * 2
def baseEnd_2225237 : Nat := 1142616151169015483703827

theorem tailTrace_2225237 : CollatzResearch.WordTrace tailWord_2225237 prefixEnd_2225237 1142616151169015483703827 := by
  unfold tailWord_2225237
  simp only [CollatzResearch.WordTrace]
  refine ⟨81161061039353864068161965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54107374026235909378774643 81161061039353864068161965)
  ·
    refine ⟨30435397889757699025560737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81161061039353864068161965 30435397889757699025560737)
    ·
      refine ⟨22826548417318274269170553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30435397889757699025560737 22826548417318274269170553)
      ·
        refine ⟨17119911312988705701877915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22826548417318274269170553 17119911312988705701877915)
        ·
          refine ⟨25679866969483058552816873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17119911312988705701877915 25679866969483058552816873)
          ·
            refine ⟨19259900227112293914612655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25679866969483058552816873 19259900227112293914612655)
            ·
              refine ⟨28889850340668440871918983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19259900227112293914612655 28889850340668440871918983)
              ·
                refine ⟨43334775511002661307878475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28889850340668440871918983 43334775511002661307878475)
                ·
                  refine ⟨65002163266503991961817713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43334775511002661307878475 65002163266503991961817713)
                  ·
                    refine ⟨48751622449877993971363285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65002163266503991961817713 48751622449877993971363285)
                    ·
                      refine ⟨1142616151169015483703827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48751622449877993971363285 1142616151169015483703827)
                      ·
                        rfl

theorem cell23_2225237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2225237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225237 prefixEnd_2225237 := by exact prefixLift 2225237
  have htrace : WordTrace (prefixWord ++ tailWord_2225237) baseStart_2225237 baseEnd_2225237 := by
    simpa [prefixWord, tailWord_2225237, baseEnd_2225237] using wordTrace_append hprefix tailTrace_2225237
  have hstable : (prefixWord ++ tailWord_2225237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225237).length < 2 ^ (prefixWord ++ tailWord_2225237).sum := by decide
  have hdescent : baseEnd_2225237 < baseStart_2225237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225255 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_2225255 : Nat := 118140960795 + 2225255 * 2 ^ 59
def prefixEnd_2225255 : Nat := 4983230072969 + 3 ^ 40 * 2225255 * 2
def baseEnd_2225255 : Nat := 1142625393820796413278745

theorem tailTrace_2225255 : CollatzResearch.WordTrace tailWord_2225255 prefixEnd_2225255 1142625393820796413278745 := by
  unfold tailWord_2225255
  simp only [CollatzResearch.WordTrace]
  refine ⟨81161717553288653142317219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54107811702192435428211479 81161717553288653142317219)
  ·
    refine ⟨121742576329932979713475829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81161717553288653142317219 121742576329932979713475829)
    ·
      refine ⟨11413366530931216848138359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121742576329932979713475829 11413366530931216848138359)
      ·
        refine ⟨17120049796396825272207539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11413366530931216848138359 17120049796396825272207539)
        ·
          refine ⟨25680074694595237908311309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17120049796396825272207539 25680074694595237908311309)
          ·
            refine ⟨9630028010473214215616741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25680074694595237908311309 9630028010473214215616741)
            ·
              refine ⟨1805630251963727665428139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9630028010473214215616741 1805630251963727665428139)
              ·
                refine ⟨2708445377945591498142209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805630251963727665428139 2708445377945591498142209)
                ·
                  refine ⟨2031334033459193623606657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2708445377945591498142209 2031334033459193623606657)
                  ·
                    refine ⟨1523500525094395217704993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2031334033459193623606657 1523500525094395217704993)
                    ·
                      refine ⟨1142625393820796413278745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523500525094395217704993 1142625393820796413278745)
                      ·
                        rfl

theorem cell23_2225255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_2225255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225255 prefixEnd_2225255 := by exact prefixLift 2225255
  have htrace : WordTrace (prefixWord ++ tailWord_2225255) baseStart_2225255 baseEnd_2225255 := by
    simpa [prefixWord, tailWord_2225255, baseEnd_2225255] using wordTrace_append hprefix tailTrace_2225255
  have hstable : (prefixWord ++ tailWord_2225255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225255).length < 2 ^ (prefixWord ++ tailWord_2225255).sum := by decide
  have hdescent : baseEnd_2225255 < baseStart_2225255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225284 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2225284 : Nat := 118140960795 + 2225284 * 2 ^ 59
def prefixEnd_2225284 : Nat := 4983230072969 + 3 ^ 40 * 2225284 * 2
def baseEnd_2225284 : Nat := 1142640284759776799816111

theorem tailTrace_2225284 : CollatzResearch.WordTrace tailWord_2225284 prefixEnd_2225284 1142640284759776799816111 := by
  unfold tailWord_2225284
  simp only [CollatzResearch.WordTrace]
  refine ⟨40581387635091795547561453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54108516846789060730081937 40581387635091795547561453)
  ·
    refine ⟨15218020363159423330335545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40581387635091795547561453 15218020363159423330335545)
    ·
      refine ⟨11413515272369567497751659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15218020363159423330335545 11413515272369567497751659)
      ·
        refine ⟨17120272908554351246627489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11413515272369567497751659 17120272908554351246627489)
        ·
          refine ⟨12840204681415763434970617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17120272908554351246627489 12840204681415763434970617)
          ·
            refine ⟨9630153511061822576227963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12840204681415763434970617 9630153511061822576227963)
            ·
              refine ⟨14445230266592733864341945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9630153511061822576227963 14445230266592733864341945)
              ·
                refine ⟨10833922699944550398256459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14445230266592733864341945 10833922699944550398256459)
                ·
                  refine ⟨16250884049916825597384689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10833922699944550398256459 16250884049916825597384689)
                  ·
                    refine ⟨12188163037437619198038517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16250884049916825597384689 12188163037437619198038517)
                    ·
                      refine ⟨1142640284759776799816111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12188163037437619198038517 1142640284759776799816111)
                      ·
                        rfl

theorem cell23_2225284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2225284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225284 prefixEnd_2225284 := by exact prefixLift 2225284
  have htrace : WordTrace (prefixWord ++ tailWord_2225284) baseStart_2225284 baseEnd_2225284 := by
    simpa [prefixWord, tailWord_2225284, baseEnd_2225284] using wordTrace_append hprefix tailTrace_2225284
  have hstable : (prefixWord ++ tailWord_2225284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225284).length < 2 ^ (prefixWord ++ tailWord_2225284).sum := by decide
  have hdescent : baseEnd_2225284 < baseStart_2225284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225325 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2225325 : Nat := 118140960795 + 2225325 * 2 ^ 59
def prefixEnd_2225325 : Nat := 4983230072969 + 3 ^ 40 * 2225325 * 2
def baseEnd_2225325 : Nat := 380887112488870379801141

theorem tailTrace_2225325 : CollatzResearch.WordTrace tailWord_2225325 prefixEnd_2225325 380887112488870379801141 := by
  unfold tailWord_2225325
  simp only [CollatzResearch.WordTrace]
  refine ⟨81164270663035055097365429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54109513775356703398243619 81164270663035055097365429)
  ·
    refine ⟨7609150374659536415378009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81164270663035055097365429 7609150374659536415378009)
    ·
      refine ⟨5706862780994652311533507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7609150374659536415378009 5706862780994652311533507)
      ·
        refine ⟨8560294171491978467300261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5706862780994652311533507 8560294171491978467300261)
        ·
          refine ⟨1605055157154745962618799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8560294171491978467300261 1605055157154745962618799)
          ·
            refine ⟨2407582735732118943928199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605055157154745962618799 2407582735732118943928199)
            ·
              refine ⟨3611374103598178415892299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407582735732118943928199 3611374103598178415892299)
              ·
                refine ⟨5417061155397267623838449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3611374103598178415892299 5417061155397267623838449)
                ·
                  refine ⟨4062795866547950717878837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5417061155397267623838449 4062795866547950717878837)
                  ·
                    refine ⟨380887112488870379801141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4062795866547950717878837 380887112488870379801141)
                    ·
                      rfl

theorem cell23_2225325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2225325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225325 prefixEnd_2225325 := by exact prefixLift 2225325
  have htrace : WordTrace (prefixWord ++ tailWord_2225325) baseStart_2225325 baseEnd_2225325 := by
    simpa [prefixWord, tailWord_2225325, baseEnd_2225325] using wordTrace_append hprefix tailTrace_2225325
  have hstable : (prefixWord ++ tailWord_2225325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225325).length < 2 ^ (prefixWord ++ tailWord_2225325).sum := by decide
  have hdescent : baseEnd_2225325 < baseStart_2225325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225331 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 3]
def baseStart_2225331 : Nat := 118140960795 + 2225331 * 2 ^ 59
def prefixEnd_2225331 : Nat := 4983230072969 + 3 ^ 40 * 2225331 * 2
def baseEnd_2225331 : Nat := 1142664418350538115928395

theorem tailTrace_2225331 : CollatzResearch.WordTrace tailWord_2225331 prefixEnd_2225331 1142664418350538115928395 := by
  unfold tailWord_2225331
  simp only [CollatzResearch.WordTrace]
  refine ⟨81164489501013318122083847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54109659667342212081389231 81164489501013318122083847)
  ·
    refine ⟨121746734251519977183125771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81164489501013318122083847 121746734251519977183125771)
    ·
      refine ⟨182620101377279965774688657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121746734251519977183125771 182620101377279965774688657)
      ·
        refine ⟨136965076032959974331016493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182620101377279965774688657 136965076032959974331016493)
        ·
          refine ⟨51361903512359990374131185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136965076032959974331016493 51361903512359990374131185)
          ·
            refine ⟨38521427634269992780598389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51361903512359990374131185 38521427634269992780598389)
            ·
              refine ⟨3611383840712811823181099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38521427634269992780598389 3611383840712811823181099)
              ·
                refine ⟨5417075761069217734771649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3611383840712811823181099 5417075761069217734771649)
                ·
                  refine ⟨4062806820801913301078737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5417075761069217734771649 4062806820801913301078737)
                  ·
                    refine ⟨3047105115601434975809053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4062806820801913301078737 3047105115601434975809053)
                    ·
                      refine ⟨1142664418350538115928395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3047105115601434975809053 1142664418350538115928395)
                      ·
                        rfl

theorem cell23_2225331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_2225331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225331 prefixEnd_2225331 := by exact prefixLift 2225331
  have htrace : WordTrace (prefixWord ++ tailWord_2225331) baseStart_2225331 baseEnd_2225331 := by
    simpa [prefixWord, tailWord_2225331, baseEnd_2225331] using wordTrace_append hprefix tailTrace_2225331
  have hstable : (prefixWord ++ tailWord_2225331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225331).length < 2 ^ (prefixWord ++ tailWord_2225331).sum := by decide
  have hdescent : baseEnd_2225331 < baseStart_2225331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225354 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2225354 : Nat := 118140960795 + 2225354 * 2 ^ 59
def prefixEnd_2225354 : Nat := 4983230072969 + 3 ^ 40 * 2225354 * 2
def baseEnd_2225354 : Nat := 1142676228405591525940789

theorem tailTrace_2225354 : CollatzResearch.WordTrace tailWord_2225354 prefixEnd_2225354 1142676228405591525940789 := by
  unfold tailWord_2225354
  simp only [CollatzResearch.WordTrace]
  refine ⟨20291332094982498262542779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54110218919953328700114077 20291332094982498262542779)
  ·
    refine ⟨30436998142473747393814169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20291332094982498262542779 30436998142473747393814169)
    ·
      refine ⟨22827748606855310545360627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30436998142473747393814169 22827748606855310545360627)
      ·
        refine ⟨34241622910282965818040941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22827748606855310545360627 34241622910282965818040941)
        ·
          refine ⟨12840608591356112181765353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34241622910282965818040941 12840608591356112181765353)
          ·
            refine ⟨9630456443517084136324015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12840608591356112181765353 9630456443517084136324015)
            ·
              refine ⟨14445684665275626204486023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9630456443517084136324015 14445684665275626204486023)
              ·
                refine ⟨21668526997913439306729035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14445684665275626204486023 21668526997913439306729035)
                ·
                  refine ⟨32502790496870158960093553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21668526997913439306729035 32502790496870158960093553)
                  ·
                    refine ⟨24377092872652619220070165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32502790496870158960093553 24377092872652619220070165)
                    ·
                      refine ⟨1142676228405591525940789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24377092872652619220070165 1142676228405591525940789)
                      ·
                        rfl

theorem cell23_2225354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2225354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225354 prefixEnd_2225354 := by exact prefixLift 2225354
  have htrace : WordTrace (prefixWord ++ tailWord_2225354) baseStart_2225354 baseEnd_2225354 := by
    simpa [prefixWord, tailWord_2225354, baseEnd_2225354] using wordTrace_append hprefix tailTrace_2225354
  have hstable : (prefixWord ++ tailWord_2225354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225354).length < 2 ^ (prefixWord ++ tailWord_2225354).sum := by decide
  have hdescent : baseEnd_2225354 < baseStart_2225354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225368 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 6]
def baseStart_2225368 : Nat := 118140960795 + 2225368 * 2 ^ 59
def prefixEnd_2225368 : Nat := 4983230072969 + 3 ^ 40 * 2225368 * 2
def baseEnd_2225368 : Nat := 126964824126083830129525

theorem tailTrace_2225368 : CollatzResearch.WordTrace tailWord_2225368 prefixEnd_2225368 126964824126083830129525 := by
  unfold tailWord_2225368
  simp only [CollatzResearch.WordTrace]
  refine ⟨40582919500939636720590379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54110559334586182294120505 40582919500939636720590379)
  ·
    refine ⟨60874379251409455080885569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40582919500939636720590379 60874379251409455080885569)
    ·
      refine ⟨45655784438557091310664177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60874379251409455080885569 45655784438557091310664177)
      ·
        refine ⟨34241838328917818482998133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45655784438557091310664177 34241838328917818482998133)
        ·
          refine ⟨3210172343336045482781075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34241838328917818482998133 3210172343336045482781075)
          ·
            refine ⟨4815258515004068224171613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3210172343336045482781075 4815258515004068224171613)
            ·
              refine ⟨1805721943126525584064355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4815258515004068224171613 1805721943126525584064355)
              ·
                refine ⟨2708582914689788376096533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805721943126525584064355 2708582914689788376096533)
                ·
                  refine ⟨126964824126083830129525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2708582914689788376096533 126964824126083830129525)
                  ·
                    rfl

theorem cell23_2225368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 6].length) (baseStart_2225368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225368 prefixEnd_2225368 := by exact prefixLift 2225368
  have htrace : WordTrace (prefixWord ++ tailWord_2225368) baseStart_2225368 baseEnd_2225368 := by
    simpa [prefixWord, tailWord_2225368, baseEnd_2225368] using wordTrace_append hprefix tailTrace_2225368
  have hstable : (prefixWord ++ tailWord_2225368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225368).length < 2 ^ (prefixWord ++ tailWord_2225368).sum := by decide
  have hdescent : baseEnd_2225368 < baseStart_2225368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225395 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 1, 1, 3]
def baseStart_2225395 : Nat := 118140960795 + 2225395 * 2 ^ 59
def prefixEnd_2225395 : Nat := 4983230072969 + 3 ^ 40 * 2225395 * 2
def baseEnd_2225395 : Nat := 1142697281112425865528101

theorem tailTrace_2225395 : CollatzResearch.WordTrace tailWord_2225395 prefixEnd_2225395 1142697281112425865528101 := by
  unfold tailWord_2225395
  simp only [CollatzResearch.WordTrace]
  refine ⟨81166823772781457052413639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54111215848520971368275759 81166823772781457052413639)
  ·
    refine ⟨121750235659172185578620459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81166823772781457052413639 121750235659172185578620459)
    ·
      refine ⟨182625353488758278367930689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121750235659172185578620459 182625353488758278367930689)
      ·
        refine ⟨136969015116568708775948017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182625353488758278367930689 136969015116568708775948017)
        ·
          refine ⟨102726761337426531581961013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136969015116568708775948017 102726761337426531581961013)
          ·
            refine ⟨9630633875383737335808845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102726761337426531581961013 9630633875383737335808845)
            ·
              refine ⟨3611487703268901500928317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9630633875383737335808845 3611487703268901500928317)
              ·
                refine ⟨1354307888725838062848119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3611487703268901500928317 1354307888725838062848119)
                ·
                  refine ⟨2031461833088757094272179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354307888725838062848119 2031461833088757094272179)
                  ·
                    refine ⟨3047192749633135641408269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2031461833088757094272179 3047192749633135641408269)
                    ·
                      refine ⟨1142697281112425865528101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3047192749633135641408269 1142697281112425865528101)
                      ·
                        rfl

theorem cell23_2225395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 1, 3].length) (baseStart_2225395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225395 prefixEnd_2225395 := by exact prefixLift 2225395
  have htrace : WordTrace (prefixWord ++ tailWord_2225395) baseStart_2225395 baseEnd_2225395 := by
    simpa [prefixWord, tailWord_2225395, baseEnd_2225395] using wordTrace_append hprefix tailTrace_2225395
  have hstable : (prefixWord ++ tailWord_2225395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225395).length < 2 ^ (prefixWord ++ tailWord_2225395).sum := by decide
  have hdescent : baseEnd_2225395 < baseStart_2225395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225401 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 4]
def baseStart_2225401 : Nat := 118140960795 + 2225401 * 2 ^ 59
def prefixEnd_2225401 : Nat := 4983230072969 + 3 ^ 40 * 2225401 * 2
def baseEnd_2225401 : Nat := 1142700361996352842053073

theorem tailTrace_2225401 : CollatzResearch.WordTrace tailWord_2225401 prefixEnd_2225401 1142700361996352842053073 := by
  unfold tailWord_2225401
  simp only [CollatzResearch.WordTrace]
  refine ⟨81167042610759720077132057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54111361740506480051421371 81167042610759720077132057)
  ·
    refine ⟨60875281958069790057849043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81167042610759720077132057 60875281958069790057849043)
    ·
      refine ⟨91312922937104685086773565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60875281958069790057849043 91312922937104685086773565)
      ·
        refine ⟨34242346101414256907540087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91312922937104685086773565 34242346101414256907540087)
        ·
          refine ⟨51363519152121385361310131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34242346101414256907540087 51363519152121385361310131)
          ·
            refine ⟨77045278728182078041965197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51363519152121385361310131 77045278728182078041965197)
            ·
              refine ⟨28891979523068279265736949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77045278728182078041965197 28891979523068279265736949)
              ·
                refine ⟨2708623080287651181162839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28891979523068279265736949 2708623080287651181162839)
                ·
                  refine ⟨4062934620431476771744259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708623080287651181162839 4062934620431476771744259)
                  ·
                    refine ⟨6094401930647215157616389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062934620431476771744259 6094401930647215157616389)
                    ·
                      refine ⟨1142700361996352842053073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6094401930647215157616389 1142700361996352842053073)
                      ·
                        rfl

theorem cell23_2225401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_2225401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225401 prefixEnd_2225401 := by exact prefixLift 2225401
  have htrace : WordTrace (prefixWord ++ tailWord_2225401) baseStart_2225401 baseEnd_2225401 := by
    simpa [prefixWord, tailWord_2225401, baseEnd_2225401] using wordTrace_append hprefix tailTrace_2225401
  have hstable : (prefixWord ++ tailWord_2225401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225401).length < 2 ^ (prefixWord ++ tailWord_2225401).sum := by decide
  have hdescent : baseEnd_2225401 < baseStart_2225401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225411 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 4, 4]
def baseStart_2225411 : Nat := 118140960795 + 2225411 * 2 ^ 59
def prefixEnd_2225411 : Nat := 4983230072969 + 3 ^ 40 * 2225411 * 2
def baseEnd_2225411 : Nat := 380901832267632600976009

theorem tailTrace_2225411 : CollatzResearch.WordTrace tailWord_2225411 prefixEnd_2225411 380901832267632600976009 := by
  unfold tailWord_2225411
  simp only [CollatzResearch.WordTrace]
  refine ⟨81167407340723491784996087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54111604893815661189997391 81167407340723491784996087)
  ·
    refine ⟨121751111011085237677494131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81167407340723491784996087 121751111011085237677494131)
    ·
      refine ⟨182626666516627856516241197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121751111011085237677494131 182626666516627856516241197)
      ·
        refine ⟨68484999943735446193590449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182626666516627856516241197 68484999943735446193590449)
        ·
          refine ⟨51363749957801584645192837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68484999943735446193590449 51363749957801584645192837)
          ·
            refine ⟨9630703117087797120973657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51363749957801584645192837 9630703117087797120973657)
            ·
              refine ⟨7223027337815847840730243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9630703117087797120973657 7223027337815847840730243)
              ·
                refine ⟨10834541006723771761095365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7223027337815847840730243 10834541006723771761095365)
                ·
                  refine ⟨2031476438760707205205381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10834541006723771761095365 2031476438760707205205381)
                  ·
                    refine ⟨380901832267632600976009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031476438760707205205381 380901832267632600976009)
                    ·
                      rfl

theorem cell23_2225411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 4].length) (baseStart_2225411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225411 prefixEnd_2225411 := by exact prefixLift 2225411
  have htrace : WordTrace (prefixWord ++ tailWord_2225411) baseStart_2225411 baseEnd_2225411 := by
    simpa [prefixWord, tailWord_2225411, baseEnd_2225411] using wordTrace_append hprefix tailTrace_2225411
  have hstable : (prefixWord ++ tailWord_2225411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225411).length < 2 ^ (prefixWord ++ tailWord_2225411).sum := by decide
  have hdescent : baseEnd_2225411 < baseStart_2225411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225431 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2225431 : Nat := 118140960795 + 2225431 * 2 ^ 59
def prefixEnd_2225431 : Nat := 4983230072969 + 3 ^ 40 * 2225431 * 2
def baseEnd_2225431 : Nat := 1142715766415987724677935

theorem tailTrace_2225431 : CollatzResearch.WordTrace tailWord_2225431 prefixEnd_2225431 1142715766415987724677935 := by
  unfold tailWord_2225431
  simp only [CollatzResearch.WordTrace]
  refine ⟨81168136800651035200724147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54112091200434023467149431 81168136800651035200724147)
  ·
    refine ⟨121752205200976552801086221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81168136800651035200724147 121752205200976552801086221)
    ·
      refine ⟨45657076950366207300407333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121752205200976552801086221 45657076950366207300407333)
      ·
        refine ⟨8560701928193663868826375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45657076950366207300407333 8560701928193663868826375)
        ·
          refine ⟨12841052892290495803239563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8560701928193663868826375 12841052892290495803239563)
          ·
            refine ⟨19261579338435743704859345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12841052892290495803239563 19261579338435743704859345)
            ·
              refine ⟨14446184503826807778644509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19261579338435743704859345 14446184503826807778644509)
              ·
                refine ⟨5417319188935052916991691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14446184503826807778644509 5417319188935052916991691)
                ·
                  refine ⟨8125978783402579375487537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5417319188935052916991691 8125978783402579375487537)
                  ·
                    refine ⟨6094484087551934531615653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8125978783402579375487537 6094484087551934531615653)
                    ·
                      refine ⟨1142715766415987724677935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6094484087551934531615653 1142715766415987724677935)
                      ·
                        rfl

theorem cell23_2225431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2225431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225431 prefixEnd_2225431 := by exact prefixLift 2225431
  have htrace : WordTrace (prefixWord ++ tailWord_2225431) baseStart_2225431 baseEnd_2225431 := by
    simpa [prefixWord, tailWord_2225431, baseEnd_2225431] using wordTrace_append hprefix tailTrace_2225431
  have hstable : (prefixWord ++ tailWord_2225431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225431).length < 2 ^ (prefixWord ++ tailWord_2225431).sum := by decide
  have hdescent : baseEnd_2225431 < baseStart_2225431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225448 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2225448 : Nat := 118140960795 + 2225448 * 2 ^ 59
def prefixEnd_2225448 : Nat := 4983230072969 + 3 ^ 40 * 2225448 * 2
def baseEnd_2225448 : Nat := 1142724495587114158165357

theorem tailTrace_2225448 : CollatzResearch.WordTrace tailWord_2225448 prefixEnd_2225448 1142724495587114158165357 := by
  unfold tailWord_2225448
  simp only [CollatzResearch.WordTrace]
  refine ⟨40584378420794723552046499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54112504561059631402728665 40584378420794723552046499)
  ·
    refine ⟨60876567631192085328069749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40584378420794723552046499 60876567631192085328069749)
    ·
      refine ⟨5707178215424257999506539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60876567631192085328069749 5707178215424257999506539)
      ·
        refine ⟨8560767323136386999259809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5707178215424257999506539 8560767323136386999259809)
        ·
          refine ⟨6420575492352290249444857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8560767323136386999259809 6420575492352290249444857)
          ·
            refine ⟨4815431619264217687083643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6420575492352290249444857 4815431619264217687083643)
            ·
              refine ⟨7223147428896326530625465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4815431619264217687083643 7223147428896326530625465)
              ·
                refine ⟨5417360571672244897969099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7223147428896326530625465 5417360571672244897969099)
                ·
                  refine ⟨8126040857508367346953649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5417360571672244897969099 8126040857508367346953649)
                  ·
                    refine ⟨6094530643131275510215237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8126040857508367346953649 6094530643131275510215237)
                    ·
                      refine ⟨1142724495587114158165357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6094530643131275510215237 1142724495587114158165357)
                      ·
                        rfl

theorem cell23_2225448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2225448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225448 prefixEnd_2225448 := by exact prefixLift 2225448
  have htrace : WordTrace (prefixWord ++ tailWord_2225448) baseStart_2225448 baseEnd_2225448 := by
    simpa [prefixWord, tailWord_2225448, baseEnd_2225448] using wordTrace_append hprefix tailTrace_2225448
  have hstable : (prefixWord ++ tailWord_2225448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225448).length < 2 ^ (prefixWord ++ tailWord_2225448).sum := by decide
  have hdescent : baseEnd_2225448 < baseStart_2225448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225512 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2225512 : Nat := 118140960795 + 2225512 * 2 ^ 59
def prefixEnd_2225512 : Nat := 4983230072969 + 3 ^ 40 * 2225512 * 2
def baseEnd_2225512 : Nat := 1142757358349001907765063

theorem tailTrace_2225512 : CollatzResearch.WordTrace tailWord_2225512 prefixEnd_2225512 1142757358349001907765063 := by
  unfold tailWord_2225512
  simp only [CollatzResearch.WordTrace]
  refine ⟨40585545556678793017211395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54114060742238390689615193 40585545556678793017211395)
  ·
    refine ⟨60878318335018189525817093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40585545556678793017211395 60878318335018189525817093)
    ·
      refine ⟨11414684687815910536090705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60878318335018189525817093 11414684687815910536090705)
      ·
        refine ⟨8561013515861932902068029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11414684687815910536090705 8561013515861932902068029)
        ·
          refine ⟨3210380068448224838275511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8561013515861932902068029 3210380068448224838275511)
          ·
            refine ⟨4815570102672337257413267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3210380068448224838275511 4815570102672337257413267)
            ·
              refine ⟨7223355154008505886119901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4815570102672337257413267 7223355154008505886119901)
              ·
                refine ⟨2708758182753189707294963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7223355154008505886119901 2708758182753189707294963)
                ·
                  refine ⟨4063137274129784560942445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708758182753189707294963 4063137274129784560942445)
                  ·
                    refine ⟨1523676477798669210353417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4063137274129784560942445 1523676477798669210353417)
                    ·
                      refine ⟨1142757358349001907765063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523676477798669210353417 1142757358349001907765063)
                      ·
                        rfl

theorem cell23_2225512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2225512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225512 prefixEnd_2225512 := by exact prefixLift 2225512
  have htrace : WordTrace (prefixWord ++ tailWord_2225512) baseStart_2225512 baseEnd_2225512 := by
    simpa [prefixWord, tailWord_2225512, baseEnd_2225512] using wordTrace_append hprefix tailTrace_2225512
  have hstable : (prefixWord ++ tailWord_2225512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225512).length < 2 ^ (prefixWord ++ tailWord_2225512).sum := by decide
  have hdescent : baseEnd_2225512 < baseStart_2225512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225521 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_2225521 : Nat := 118140960795 + 2225521 * 2 ^ 59
def prefixEnd_2225521 : Nat := 4983230072969 + 3 ^ 40 * 2225521 * 2
def baseEnd_2225521 : Nat := 1142761979674892372552521

theorem tailTrace_2225521 : CollatzResearch.WordTrace tailWord_2225521 prefixEnd_2225521 1142761979674892372552521 := by
  unfold tailWord_2225521
  simp only [CollatzResearch.WordTrace]
  refine ⟨81171419370324980571500417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54114279580216653714333611 81171419370324980571500417)
  ·
    refine ⟨60878564527743735428625313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81171419370324980571500417 60878564527743735428625313)
    ·
      refine ⟨45658923395807801571468985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60878564527743735428625313 45658923395807801571468985)
      ·
        refine ⟨34244192546855851178601739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45658923395807801571468985 34244192546855851178601739)
        ·
          refine ⟨51366288820283776767902609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34244192546855851178601739 51366288820283776767902609)
          ·
            refine ⟨38524716615212832575926957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51366288820283776767902609 38524716615212832575926957)
            ·
              refine ⟨14446768730704812215972609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38524716615212832575926957 14446768730704812215972609)
              ·
                refine ⟨10835076548028609161979457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14446768730704812215972609 10835076548028609161979457)
                ·
                  refine ⟨8126307411021456871484593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10835076548028609161979457 8126307411021456871484593)
                  ·
                    refine ⟨6094730558266092653613445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8126307411021456871484593 6094730558266092653613445)
                    ·
                      refine ⟨1142761979674892372552521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6094730558266092653613445 1142761979674892372552521)
                      ·
                        rfl

theorem cell23_2225521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_2225521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225521 prefixEnd_2225521 := by exact prefixLift 2225521
  have htrace : WordTrace (prefixWord ++ tailWord_2225521) baseStart_2225521 baseEnd_2225521 := by
    simpa [prefixWord, tailWord_2225521, baseEnd_2225521] using wordTrace_append hprefix tailTrace_2225521
  have hstable : (prefixWord ++ tailWord_2225521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225521).length < 2 ^ (prefixWord ++ tailWord_2225521).sum := by decide
  have hdescent : baseEnd_2225521 < baseStart_2225521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225531 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 7]
def baseStart_2225531 : Nat := 118140960795 + 2225531 * 2 ^ 59
def prefixEnd_2225531 : Nat := 4983230072969 + 3 ^ 40 * 2225531 * 2
def baseEnd_2225531 : Nat := 126974123831270814825275

theorem tailTrace_2225531 : CollatzResearch.WordTrace tailWord_2225531 prefixEnd_2225531 126974123831270814825275 := by
  unfold tailWord_2225531
  simp only [CollatzResearch.WordTrace]
  refine ⟨81171784100288752279364447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54114522733525834852909631 81171784100288752279364447)
  ·
    refine ⟨121757676150433128419046671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81171784100288752279364447 121757676150433128419046671)
    ·
      refine ⟨182636514225649692628570007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121757676150433128419046671 182636514225649692628570007)
      ·
        refine ⟨273954771338474538942855011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182636514225649692628570007 273954771338474538942855011)
        ·
          refine ⟨410932157007711808414282517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273954771338474538942855011 410932157007711808414282517)
          ·
            refine ⟨19262444859736491019419493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 410932157007711808414282517 19262444859736491019419493)
            ·
              refine ⟨3611708411200592066141155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19262444859736491019419493 3611708411200592066141155)
              ·
                refine ⟨5417562616800888099211733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3611708411200592066141155 5417562616800888099211733)
                ·
                  refine ⟨126974123831270814825275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5417562616800888099211733 126974123831270814825275)
                  ·
                    rfl

theorem cell23_2225531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 7].length) (baseStart_2225531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225531 prefixEnd_2225531 := by exact prefixLift 2225531
  have htrace : WordTrace (prefixWord ++ tailWord_2225531) baseStart_2225531 baseEnd_2225531 := by
    simpa [prefixWord, tailWord_2225531, baseEnd_2225531] using wordTrace_append hprefix tailTrace_2225531
  have hstable : (prefixWord ++ tailWord_2225531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225531).length < 2 ^ (prefixWord ++ tailWord_2225531).sum := by decide
  have hdescent : baseEnd_2225531 < baseStart_2225531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225561 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_2225561 : Nat := 118140960795 + 2225561 * 2 ^ 59
def prefixEnd_2225561 : Nat := 4983230072969 + 3 ^ 40 * 2225561 * 2
def baseEnd_2225561 : Nat := 380927506300357405350779

theorem tailTrace_2225561 : CollatzResearch.WordTrace tailWord_2225561 prefixEnd_2225561 380927506300357405350779 := by
  unfold tailWord_2225561
  simp only [CollatzResearch.WordTrace]
  refine ⟨81172878290180067402956537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54115252193453378268637691 81172878290180067402956537)
  ·
    refine ⟨60879658717635050552217403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81172878290180067402956537 60879658717635050552217403)
    ·
      refine ⟨91319488076452575828326105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60879658717635050552217403 91319488076452575828326105)
      ·
        refine ⟨68489616057339431871244579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91319488076452575828326105 68489616057339431871244579)
        ·
          refine ⟨102734424086009147806866869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68489616057339431871244579 102734424086009147806866869)
          ·
            refine ⟨9631352258063357606893769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102734424086009147806866869 9631352258063357606893769)
            ·
              refine ⟨7223514193547518205170327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9631352258063357606893769 7223514193547518205170327)
              ·
                refine ⟨10835271290321277307755491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7223514193547518205170327 10835271290321277307755491)
                ·
                  refine ⟨16252906935481915961633237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10835271290321277307755491 16252906935481915961633237)
                  ·
                    refine ⟨380927506300357405350779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16252906935481915961633237 380927506300357405350779)
                    ·
                      rfl

theorem cell23_2225561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_2225561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225561 prefixEnd_2225561 := by exact prefixLift 2225561
  have htrace : WordTrace (prefixWord ++ tailWord_2225561) baseStart_2225561 baseEnd_2225561 := by
    simpa [prefixWord, tailWord_2225561, baseEnd_2225561] using wordTrace_append hprefix tailTrace_2225561
  have hstable : (prefixWord ++ tailWord_2225561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225561).length < 2 ^ (prefixWord ++ tailWord_2225561).sum := by decide
  have hdescent : baseEnd_2225561 < baseStart_2225561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225565 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 5]
def baseStart_2225565 : Nat := 118140960795 + 2225565 * 2 ^ 59
def prefixEnd_2225565 : Nat := 4983230072969 + 3 ^ 40 * 2225565 * 2
def baseEnd_2225565 : Nat := 126976063647076688933591

theorem tailTrace_2225565 : CollatzResearch.WordTrace tailWord_2225565 prefixEnd_2225565 126976063647076688933591 := by
  unfold tailWord_2225565
  simp only [CollatzResearch.WordTrace]
  refine ⟨81173024182165576086102149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54115349454777050724068099 81173024182165576086102149)
  ·
    refine ⟨15219942034156045516144153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81173024182165576086102149 15219942034156045516144153)
    ·
      refine ⟨11414956525617034137108115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15219942034156045516144153 11414956525617034137108115)
      ·
        refine ⟨17122434788425551205662173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11414956525617034137108115 17122434788425551205662173)
        ·
          refine ⟨6420913045659581702123315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17122434788425551205662173 6420913045659581702123315)
          ·
            refine ⟨9631369568489372553184973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6420913045659581702123315 9631369568489372553184973)
            ·
              refine ⟨3611763588183514707444365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9631369568489372553184973 3611763588183514707444365)
              ·
                refine ⟨1354411345568818015291637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3611763588183514707444365 1354411345568818015291637)
                ·
                  refine ⟨126976063647076688933591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1354411345568818015291637 126976063647076688933591)
                  ·
                    rfl

theorem cell23_2225565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_2225565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225565 prefixEnd_2225565 := by exact prefixLift 2225565
  have htrace : WordTrace (prefixWord ++ tailWord_2225565) baseStart_2225565 baseEnd_2225565 := by
    simpa [prefixWord, tailWord_2225565, baseEnd_2225565] using wordTrace_append hprefix tailTrace_2225565
  have hstable : (prefixWord ++ tailWord_2225565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225565).length < 2 ^ (prefixWord ++ tailWord_2225565).sum := by decide
  have hdescent : baseEnd_2225565 < baseStart_2225565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225571 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2225571 : Nat := 118140960795 + 2225571 * 2 ^ 59
def prefixEnd_2225571 : Nat := 4983230072969 + 3 ^ 40 * 2225571 * 2
def baseEnd_2225571 : Nat := 1142787653707617176927291

theorem tailTrace_2225571 : CollatzResearch.WordTrace tailWord_2225571 prefixEnd_2225571 1142787653707617176927291 := by
  unfold tailWord_2225571
  simp only [CollatzResearch.WordTrace]
  refine ⟨81173243020143839110820567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54115495346762559407213711 81173243020143839110820567)
  ·
    refine ⟨121759864530215758666230851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81173243020143839110820567 121759864530215758666230851)
    ·
      refine ⟨182639796795323637999346277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121759864530215758666230851 182639796795323637999346277)
      ·
        refine ⟨34244961899123182124877427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182639796795323637999346277 34244961899123182124877427)
        ·
          refine ⟨51367442848684773187316141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34244961899123182124877427 51367442848684773187316141)
          ·
            refine ⟨19262791068256789945243553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51367442848684773187316141 19262791068256789945243553)
            ·
              refine ⟨14447093301192592458932665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19262791068256789945243553 14447093301192592458932665)
              ·
                refine ⟨10835319975894444344199499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14447093301192592458932665 10835319975894444344199499)
                ·
                  refine ⟨16252979963841666516299249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10835319975894444344199499 16252979963841666516299249)
                  ·
                    refine ⟨12189734972881249887224437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16252979963841666516299249 12189734972881249887224437)
                    ·
                      refine ⟨1142787653707617176927291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12189734972881249887224437 1142787653707617176927291)
                      ·
                        rfl

theorem cell23_2225571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2225571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225571 prefixEnd_2225571 := by exact prefixLift 2225571
  have htrace : WordTrace (prefixWord ++ tailWord_2225571) baseStart_2225571 baseEnd_2225571 := by
    simpa [prefixWord, tailWord_2225571, baseEnd_2225571] using wordTrace_append hprefix tailTrace_2225571
  have hstable : (prefixWord ++ tailWord_2225571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225571).length < 2 ^ (prefixWord ++ tailWord_2225571).sum := by decide
  have hdescent : baseEnd_2225571 < baseStart_2225571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225598 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2225598 : Nat := 118140960795 + 2225598 * 2 ^ 59
def prefixEnd_2225598 : Nat := 4983230072969 + 3 ^ 40 * 2225598 * 2
def baseEnd_2225598 : Nat := 1142801517685288571289667

theorem tailTrace_2225598 : CollatzResearch.WordTrace tailWord_2225598 prefixEnd_2225598 1142801517685288571289667 := by
  unfold tailWord_2225598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10146778473880752840256681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54116151860697348481368965 10146778473880752840256681)
  ·
    refine ⟨7610083855410564630192511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10146778473880752840256681 7610083855410564630192511)
    ·
      refine ⟨11415125783115846945288767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610083855410564630192511 11415125783115846945288767)
      ·
        refine ⟨17122688674673770417933151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11415125783115846945288767 17122688674673770417933151)
        ·
          refine ⟨25684033012010655626899727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17122688674673770417933151 25684033012010655626899727)
          ·
            refine ⟨38526049518015983440349591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25684033012010655626899727 38526049518015983440349591)
            ·
              refine ⟨57789074277023975160524387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38526049518015983440349591 57789074277023975160524387)
              ·
                refine ⟨86683611415535962740786581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57789074277023975160524387 86683611415535962740786581)
                ·
                  refine ⟨4063294285103248253474371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86683611415535962740786581 4063294285103248253474371)
                  ·
                    refine ⟨6094941427654872380211557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063294285103248253474371 6094941427654872380211557)
                    ·
                      refine ⟨1142801517685288571289667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6094941427654872380211557 1142801517685288571289667)
                      ·
                        rfl

theorem cell23_2225598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2225598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225598 prefixEnd_2225598 := by exact prefixLift 2225598
  have htrace : WordTrace (prefixWord ++ tailWord_2225598) baseStart_2225598 baseEnd_2225598 := by
    simpa [prefixWord, tailWord_2225598, baseEnd_2225598] using wordTrace_append hprefix tailTrace_2225598
  have hstable : (prefixWord ++ tailWord_2225598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225598).length < 2 ^ (prefixWord ++ tailWord_2225598).sum := by decide
  have hdescent : baseEnd_2225598 < baseStart_2225598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225608 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 5, 4]
def baseStart_2225608 : Nat := 118140960795 + 2225608 * 2 ^ 59
def prefixEnd_2225608 : Nat := 4983230072969 + 3 ^ 40 * 2225608 * 2
def baseEnd_2225608 : Nat := 380935550830611177388207

theorem tailTrace_2225608 : CollatzResearch.WordTrace tailWord_2225608 prefixEnd_2225608 380935550830611177388207 := by
  unfold tailWord_2225608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40587296260504897214958739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54116395014006529619944985 40587296260504897214958739)
  ·
    refine ⟨60880944390757345822438109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40587296260504897214958739 60880944390757345822438109)
    ·
      refine ⟨22830354146534004683414291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60880944390757345822438109 22830354146534004683414291)
      ·
        refine ⟨34245531219801007025121437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22830354146534004683414291 34245531219801007025121437)
        ·
          refine ⟨12842074207425377634420539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34245531219801007025121437 12842074207425377634420539)
          ·
            refine ⟨19263111311138066451630809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12842074207425377634420539 19263111311138066451630809)
            ·
              refine ⟨14447333483353549838723107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19263111311138066451630809 14447333483353549838723107)
              ·
                refine ⟨21671000225030324758084661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14447333483353549838723107 21671000225030324758084661)
                ·
                  refine ⟨2031656271096592946070437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21671000225030324758084661 2031656271096592946070437)
                  ·
                    refine ⟨380935550830611177388207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031656271096592946070437 380935550830611177388207)
                    ·
                      rfl

theorem cell23_2225608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_2225608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225608 prefixEnd_2225608 := by exact prefixLift 2225608
  have htrace : WordTrace (prefixWord ++ tailWord_2225608) baseStart_2225608 baseEnd_2225608 := by
    simpa [prefixWord, tailWord_2225608, baseEnd_2225608] using wordTrace_append hprefix tailTrace_2225608
  have hstable : (prefixWord ++ tailWord_2225608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225608).length < 2 ^ (prefixWord ++ tailWord_2225608).sum := by decide
  have hdescent : baseEnd_2225608 < baseStart_2225608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225611 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4]
def baseStart_2225611 : Nat := 118140960795 + 2225611 * 2 ^ 59
def prefixEnd_2225611 : Nat := 4983230072969 + 3 ^ 40 * 2225611 * 2
def baseEnd_2225611 : Nat := 1142808192933797020427107

theorem tailTrace_2225611 : CollatzResearch.WordTrace tailWord_2225611 prefixEnd_2225611 1142808192933797020427107 := by
  unfold tailWord_2225611
  simp only [CollatzResearch.WordTrace]
  refine ⟨81174701939998925942276687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54116467959999283961517791 81174701939998925942276687)
  ·
    refine ⟨121762052909998388913415031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81174701939998925942276687 121762052909998388913415031)
    ·
      refine ⟨182643079364997583370122547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121762052909998388913415031 182643079364997583370122547)
      ·
        refine ⟨273964619047496375055183821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182643079364997583370122547 273964619047496375055183821)
        ·
          refine ⟨102736732142811140645693933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273964619047496375055183821 102736732142811140645693933)
          ·
            refine ⟨38526274553554177742135225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102736732142811140645693933 38526274553554177742135225)
            ·
              refine ⟨28894705915165633306601419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38526274553554177742135225 28894705915165633306601419)
              ·
                refine ⟨43342058872748449959902129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28894705915165633306601419 43342058872748449959902129)
                ·
                  refine ⟨32506544154561337469926597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43342058872748449959902129 32506544154561337469926597)
                  ·
                    refine ⟨6094977028980250775611237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32506544154561337469926597 6094977028980250775611237)
                    ·
                      refine ⟨1142808192933797020427107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6094977028980250775611237 1142808192933797020427107)
                      ·
                        rfl

theorem cell23_2225611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_2225611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225611 prefixEnd_2225611 := by exact prefixLift 2225611
  have htrace : WordTrace (prefixWord ++ tailWord_2225611) baseStart_2225611 baseEnd_2225611 := by
    simpa [prefixWord, tailWord_2225611, baseEnd_2225611] using wordTrace_append hprefix tailTrace_2225611
  have hstable : (prefixWord ++ tailWord_2225611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225611).length < 2 ^ (prefixWord ++ tailWord_2225611).sum := by decide
  have hdescent : baseEnd_2225611 < baseStart_2225611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225635 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2225635 : Nat := 118140960795 + 2225635 * 2 ^ 59
def prefixEnd_2225635 : Nat := 4983230072969 + 3 ^ 40 * 2225635 * 2
def baseEnd_2225635 : Nat := 1142820516469504926526997

theorem tailTrace_2225635 : CollatzResearch.WordTrace tailWord_2225635 prefixEnd_2225635 1142820516469504926526997 := by
  unfold tailWord_2225635
  simp only [CollatzResearch.WordTrace]
  refine ⟨81175577291911978041150359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54117051527941318694100239 81175577291911978041150359)
  ·
    refine ⟨121763365937867967061725539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81175577291911978041150359 121763365937867967061725539)
    ·
      refine ⟨182645048906801950592588309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121763365937867967061725539 182645048906801950592588309)
      ·
        refine ⟨8561486667506341434027577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 182645048906801950592588309 8561486667506341434027577)
        ·
          refine ⟨6421115000629756075520683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8561486667506341434027577 6421115000629756075520683)
          ·
            refine ⟨9631672500944634113281025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421115000629756075520683 9631672500944634113281025)
            ·
              refine ⟨7223754375708475584960769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9631672500944634113281025 7223754375708475584960769)
              ·
                refine ⟨5417815781781356688720577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7223754375708475584960769 5417815781781356688720577)
                ·
                  refine ⟨4063361836336017516540433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5417815781781356688720577 4063361836336017516540433)
                  ·
                    refine ⟨3047521377252013137405325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4063361836336017516540433 3047521377252013137405325)
                    ·
                      refine ⟨1142820516469504926526997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3047521377252013137405325 1142820516469504926526997)
                      ·
                        rfl

theorem cell23_2225635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2225635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225635 prefixEnd_2225635 := by exact prefixLift 2225635
  have htrace : WordTrace (prefixWord ++ tailWord_2225635) baseStart_2225635 baseEnd_2225635 := by
    simpa [prefixWord, tailWord_2225635, baseEnd_2225635] using wordTrace_append hprefix tailTrace_2225635
  have hstable : (prefixWord ++ tailWord_2225635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225635).length < 2 ^ (prefixWord ++ tailWord_2225635).sum := by decide
  have hdescent : baseEnd_2225635 < baseStart_2225635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225685 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2225685 : Nat := 118140960795 + 2225685 * 2 ^ 59
def prefixEnd_2225685 : Nat := 4983230072969 + 3 ^ 40 * 2225685 * 2
def baseEnd_2225685 : Nat := 380948730167409910300589

theorem tailTrace_2225685 : CollatzResearch.WordTrace tailWord_2225685 prefixEnd_2225685 380948730167409910300589 := by
  unfold tailWord_2225685
  simp only [CollatzResearch.WordTrace]
  refine ⟨81177400941730836580470509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54118267294487224386980339 81177400941730836580470509)
  ·
    refine ⟨30441525353149063717676441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81177400941730836580470509 30441525353149063717676441)
    ·
      refine ⟨22831144014861797788257331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30441525353149063717676441 22831144014861797788257331)
      ·
        refine ⟨34246716022292696682385997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22831144014861797788257331 34246716022292696682385997)
        ·
          refine ⟨12842518508359761255894749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34246716022292696682385997 12842518508359761255894749)
          ·
            refine ⟨4815944440634910470960531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12842518508359761255894749 4815944440634910470960531)
            ·
              refine ⟨7223916660952365706440797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4815944440634910470960531 7223916660952365706440797)
              ·
                refine ⟨2708968747857137139915299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7223916660952365706440797 2708968747857137139915299)
                ·
                  refine ⟨4063453121785705709872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708968747857137139915299 4063453121785705709872949)
                  ·
                    refine ⟨380948730167409910300589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4063453121785705709872949 380948730167409910300589)
                    ·
                      rfl

theorem cell23_2225685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2225685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225685 prefixEnd_2225685 := by exact prefixLift 2225685
  have htrace : WordTrace (prefixWord ++ tailWord_2225685) baseStart_2225685 baseEnd_2225685 := by
    simpa [prefixWord, tailWord_2225685, baseEnd_2225685] using wordTrace_append hprefix tailTrace_2225685
  have hstable : (prefixWord ++ tailWord_2225685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225685).length < 2 ^ (prefixWord ++ tailWord_2225685).sum := by decide
  have hdescent : baseEnd_2225685 < baseStart_2225685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225698 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2225698 : Nat := 118140960795 + 2225698 * 2 ^ 59
def prefixEnd_2225698 : Nat := 4983230072969 + 3 ^ 40 * 2225698 * 2
def baseEnd_2225698 : Nat := 380950955250246060013069

theorem tailTrace_2225698 : CollatzResearch.WordTrace tailWord_2225698 prefixEnd_2225698 380950955250246060013069 := by
  unfold tailWord_2225698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20294468772670934950173437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54118583393789159867129165 20294468772670934950173437)
  ·
    refine ⟨7610425789751600606315039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20294468772670934950173437 7610425789751600606315039)
    ·
      refine ⟨11415638684627400909472559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610425789751600606315039 11415638684627400909472559)
      ·
        refine ⟨17123458026941101364208839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11415638684627400909472559 17123458026941101364208839)
        ·
          refine ⟨25685187040411652046313259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17123458026941101364208839 25685187040411652046313259)
          ·
            refine ⟨38527780560617478069469889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25685187040411652046313259 38527780560617478069469889)
            ·
              refine ⟨28895835420463108552102417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38527780560617478069469889 28895835420463108552102417)
              ·
                refine ⟨21671876565347331414076813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28895835420463108552102417 21671876565347331414076813)
                ·
                  refine ⟨8126953712005249280278805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21671876565347331414076813 8126953712005249280278805)
                  ·
                    refine ⟨380950955250246060013069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8126953712005249280278805 380950955250246060013069)
                    ·
                      rfl

theorem cell23_2225698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2225698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225698 prefixEnd_2225698 := by exact prefixLift 2225698
  have htrace : WordTrace (prefixWord ++ tailWord_2225698) baseStart_2225698 baseEnd_2225698 := by
    simpa [prefixWord, tailWord_2225698, baseEnd_2225698] using wordTrace_append hprefix tailTrace_2225698
  have hstable : (prefixWord ++ tailWord_2225698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225698).length < 2 ^ (prefixWord ++ tailWord_2225698).sum := by decide
  have hdescent : baseEnd_2225698 < baseStart_2225698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225715 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 1, 6]
def baseStart_2225715 : Nat := 118140960795 + 2225715 * 2 ^ 59
def prefixEnd_2225715 : Nat := 4983230072969 + 3 ^ 40 * 2225715 * 2
def baseEnd_2225715 : Nat := 380953864973954871175543

theorem tailTrace_2225715 : CollatzResearch.WordTrace tailWord_2225715 prefixEnd_2225715 380953864973954871175543 := by
  unfold tailWord_2225715
  simp only [CollatzResearch.WordTrace]
  refine ⟨81178495131622151704062599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54118996754414767802708399 81178495131622151704062599)
  ·
    refine ⟨121767742697433227556093899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81178495131622151704062599 121767742697433227556093899)
    ·
      refine ⟨182651614046149841334140849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121767742697433227556093899 182651614046149841334140849)
      ·
        refine ⟨136988710534612381000605637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182651614046149841334140849 136988710534612381000605637)
        ·
          refine ⟨25685383225239821437613557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136988710534612381000605637 25685383225239821437613557)
          ·
            refine ⟨2408004677366233259776271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25685383225239821437613557 2408004677366233259776271)
            ·
              refine ⟨3612007016049349889664407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408004677366233259776271 3612007016049349889664407)
              ·
                refine ⟨5418010524074024834496611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612007016049349889664407 5418010524074024834496611)
                ·
                  refine ⟨8127015786111037251744917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418010524074024834496611 8127015786111037251744917)
                  ·
                    refine ⟨380953864973954871175543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8127015786111037251744917 380953864973954871175543)
                    ·
                      rfl

theorem cell23_2225715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 6].length) (baseStart_2225715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225715 prefixEnd_2225715 := by exact prefixLift 2225715
  have htrace : WordTrace (prefixWord ++ tailWord_2225715) baseStart_2225715 baseEnd_2225715 := by
    simpa [prefixWord, tailWord_2225715, baseEnd_2225715] using wordTrace_append hprefix tailTrace_2225715
  have hstable : (prefixWord ++ tailWord_2225715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225715).length < 2 ^ (prefixWord ++ tailWord_2225715).sum := by decide
  have hdescent : baseEnd_2225715 < baseStart_2225715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225722 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2]
def baseStart_2225722 : Nat := 118140960795 + 2225722 * 2 ^ 59
def prefixEnd_2225722 : Nat := 4983230072969 + 3 ^ 40 * 2225722 * 2
def baseEnd_2225722 : Nat := 1142865189286446086139097

theorem tailTrace_2225722 : CollatzResearch.WordTrace tailWord_2225722 prefixEnd_2225722 1142865189286446086139097 := by
  unfold tailWord_2225722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20294687610649197974891855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54119166961731194599711613 20294687610649197974891855)
  ·
    refine ⟨30442031415973796962337783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20294687610649197974891855 30442031415973796962337783)
    ·
      refine ⟨45663047123960695443506675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30442031415973796962337783 45663047123960695443506675)
      ·
        refine ⟨68494570685941043165260013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45663047123960695443506675 68494570685941043165260013)
        ·
          refine ⟨25685464007227891186972505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68494570685941043165260013 25685464007227891186972505)
          ·
            refine ⟨19264098005420918390229379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25685464007227891186972505 19264098005420918390229379)
            ·
              refine ⟨28896147008131377585344069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19264098005420918390229379 28896147008131377585344069)
              ·
                refine ⟨5418027564024633297252013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28896147008131377585344069 5418027564024633297252013)
                ·
                  refine ⟨2031760336509237486469505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5418027564024633297252013 2031760336509237486469505)
                  ·
                    refine ⟨1523820252381928114852129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2031760336509237486469505 1523820252381928114852129)
                    ·
                      refine ⟨1142865189286446086139097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523820252381928114852129 1142865189286446086139097)
                      ·
                        rfl

theorem cell23_2225722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_2225722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225722 prefixEnd_2225722 := by exact prefixLift 2225722
  have htrace : WordTrace (prefixWord ++ tailWord_2225722) baseStart_2225722 baseEnd_2225722 := by
    simpa [prefixWord, tailWord_2225722, baseEnd_2225722] using wordTrace_append hprefix tailTrace_2225722
  have hstable : (prefixWord ++ tailWord_2225722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225722).length < 2 ^ (prefixWord ++ tailWord_2225722).sum := by decide
  have hdescent : baseEnd_2225722 < baseStart_2225722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225750 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2225750 : Nat := 118140960795 + 2225750 * 2 ^ 59
def prefixEnd_2225750 : Nat := 4983230072969 + 3 ^ 40 * 2225750 * 2
def baseEnd_2225750 : Nat := 1142879566744771976588969

theorem tailTrace_2225750 : CollatzResearch.WordTrace tailWord_2225750 prefixEnd_2225750 1142879566744771976588969 := by
  unfold tailWord_2225750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073735730405959542599169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54119847790996901787724469 5073735730405959542599169)
  ·
    refine ⟨3805301797804469656949377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5073735730405959542599169 3805301797804469656949377)
    ·
      refine ⟨2853976348353352242712033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3805301797804469656949377 2853976348353352242712033)
      ·
        refine ⟨2140482261265014182034025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2853976348353352242712033 2140482261265014182034025)
        ·
          refine ⟨1605361695948760636525519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2140482261265014182034025 1605361695948760636525519)
          ·
            refine ⟨2408042543923140954788279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605361695948760636525519 2408042543923140954788279)
            ·
              refine ⟨3612063815884711432182419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408042543923140954788279 3612063815884711432182419)
              ·
                refine ⟨5418095723827067148273629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612063815884711432182419 5418095723827067148273629)
                ·
                  refine ⟨2031785896435150180602611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5418095723827067148273629 2031785896435150180602611)
                  ·
                    refine ⟨3047678844652725270903917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2031785896435150180602611 3047678844652725270903917)
                    ·
                      refine ⟨1142879566744771976588969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3047678844652725270903917 1142879566744771976588969)
                      ·
                        rfl

theorem cell23_2225750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2225750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225750 prefixEnd_2225750 := by exact prefixLift 2225750
  have htrace : WordTrace (prefixWord ++ tailWord_2225750) baseStart_2225750 baseEnd_2225750 := by
    simpa [prefixWord, tailWord_2225750, baseEnd_2225750] using wordTrace_append hprefix tailTrace_2225750
  have hstable : (prefixWord ++ tailWord_2225750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225750).length < 2 ^ (prefixWord ++ tailWord_2225750).sum := by decide
  have hdescent : baseEnd_2225750 < baseStart_2225750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225756 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_2225756 : Nat := 118140960795 + 2225756 * 2 ^ 59
def prefixEnd_2225756 : Nat := 4983230072969 + 3 ^ 40 * 2225756 * 2
def baseEnd_2225756 : Nat := 1142882647628698953113941

theorem tailTrace_2225756 : CollatzResearch.WordTrace tailWord_2225756 prefixEnd_2225756 1142882647628698953113941 := by
  unfold tailWord_2225756
  simp only [CollatzResearch.WordTrace]
  refine ⟨40589995262236807853152561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54119993682982410470870081 40589995262236807853152561)
  ·
    refine ⟨30442496446677605889864421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40589995262236807853152561 30442496446677605889864421)
    ·
      refine ⟨5707968083752051104349579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30442496446677605889864421 5707968083752051104349579)
      ·
        refine ⟨8561952125628076656524369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5707968083752051104349579 8561952125628076656524369)
        ·
          refine ⟨6421464094221057492393277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8561952125628076656524369 6421464094221057492393277)
          ·
            refine ⟨2408049035332896559647479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6421464094221057492393277 2408049035332896559647479)
            ·
              refine ⟨3612073552999344839471219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408049035332896559647479 3612073552999344839471219)
              ·
                refine ⟨5418110329499017259206829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612073552999344839471219 5418110329499017259206829)
                ·
                  refine ⟨2031791373562131472202561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5418110329499017259206829 2031791373562131472202561)
                  ·
                    refine ⟨1523843530171598604151921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2031791373562131472202561 1523843530171598604151921)
                    ·
                      refine ⟨1142882647628698953113941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523843530171598604151921 1142882647628698953113941)
                      ·
                        rfl

theorem cell23_2225756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_2225756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225756 prefixEnd_2225756 := by exact prefixLift 2225756
  have htrace : WordTrace (prefixWord ++ tailWord_2225756) baseStart_2225756 baseEnd_2225756 := by
    simpa [prefixWord, tailWord_2225756, baseEnd_2225756] using wordTrace_append hprefix tailTrace_2225756
  have hstable : (prefixWord ++ tailWord_2225756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225756).length < 2 ^ (prefixWord ++ tailWord_2225756).sum := by decide
  have hdescent : baseEnd_2225756 < baseStart_2225756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225788 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_2225788 : Nat := 118140960795 + 2225788 * 2 ^ 59
def prefixEnd_2225788 : Nat := 4983230072969 + 3 ^ 40 * 2225788 * 2
def baseEnd_2225788 : Nat := 380966359669880942637931

theorem tailTrace_2225788 : CollatzResearch.WordTrace tailWord_2225788 prefixEnd_2225788 380966359669880942637931 := by
  unfold tailWord_2225788
  simp only [CollatzResearch.WordTrace]
  refine ⟨40590578830178842585735009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54120771773571790114313345 40590578830178842585735009)
  ·
    refine ⟨30442934122634131939301257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40590578830178842585735009 30442934122634131939301257)
    ·
      refine ⟨22832200591975598954475943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30442934122634131939301257 22832200591975598954475943)
      ·
        refine ⟨34248300887963398431713915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22832200591975598954475943 34248300887963398431713915)
        ·
          refine ⟨51372451331945097647570873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34248300887963398431713915 51372451331945097647570873)
          ·
            refine ⟨38529338498958823235678155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51372451331945097647570873 38529338498958823235678155)
            ·
              refine ⟨57794007748438234853517233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38529338498958823235678155 57794007748438234853517233)
              ·
                refine ⟨43345505811328676140137925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57794007748438234853517233 43345505811328676140137925)
                ·
                  refine ⟨8127282339624126776275861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43345505811328676140137925 8127282339624126776275861)
                  ·
                    refine ⟨380966359669880942637931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8127282339624126776275861 380966359669880942637931)
                    ·
                      rfl

theorem cell23_2225788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_2225788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225788 prefixEnd_2225788 := by exact prefixLift 2225788
  have htrace : WordTrace (prefixWord ++ tailWord_2225788) baseStart_2225788 baseEnd_2225788 := by
    simpa [prefixWord, tailWord_2225788, baseEnd_2225788] using wordTrace_append hprefix tailTrace_2225788
  have hstable : (prefixWord ++ tailWord_2225788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225788).length < 2 ^ (prefixWord ++ tailWord_2225788).sum := by decide
  have hdescent : baseEnd_2225788 < baseStart_2225788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225808 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_2225808 : Nat := 118140960795 + 2225808 * 2 ^ 59
def prefixEnd_2225808 : Nat := 4983230072969 + 3 ^ 40 * 2225808 * 2
def baseEnd_2225808 : Nat := 1142909348622732749663701

theorem tailTrace_2225808 : CollatzResearch.WordTrace tailWord_2225808 prefixEnd_2225808 1142909348622732749663701 := by
  unfold tailWord_2225808
  simp only [CollatzResearch.WordTrace]
  refine ⟨40590943560142614293599039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54121258080190152391465385 40590943560142614293599039)
  ·
    refine ⟨60886415340213921440398559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40590943560142614293599039 60886415340213921440398559)
    ·
      refine ⟨91329623010320882160597839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60886415340213921440398559 91329623010320882160597839)
      ·
        refine ⟨136994434515481323240896759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91329623010320882160597839 136994434515481323240896759)
        ·
          refine ⟨205491651773221984861345139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136994434515481323240896759 205491651773221984861345139)
          ·
            refine ⟨308237477659832977292017709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205491651773221984861345139 308237477659832977292017709)
            ·
              refine ⟨115589054122437366484506641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 308237477659832977292017709 115589054122437366484506641)
              ·
                refine ⟨86691790591828024863379981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115589054122437366484506641 86691790591828024863379981)
                ·
                  refine ⟨32509421471935509323767493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86691790591828024863379981 32509421471935509323767493)
                  ·
                    refine ⟨6095516525987907998206405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32509421471935509323767493 6095516525987907998206405)
                    ·
                      refine ⟨1142909348622732749663701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6095516525987907998206405 1142909348622732749663701)
                      ·
                        rfl

theorem cell23_2225808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_2225808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225808 prefixEnd_2225808 := by exact prefixLift 2225808
  have htrace : WordTrace (prefixWord ++ tailWord_2225808) baseStart_2225808 baseEnd_2225808 := by
    simpa [prefixWord, tailWord_2225808, baseEnd_2225808] using wordTrace_append hprefix tailTrace_2225808
  have hstable : (prefixWord ++ tailWord_2225808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225808).length < 2 ^ (prefixWord ++ tailWord_2225808).sum := by decide
  have hdescent : baseEnd_2225808 < baseStart_2225808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225815 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2225815 : Nat := 118140960795 + 2225815 * 2 ^ 59
def prefixEnd_2225815 : Nat := 4983230072969 + 3 ^ 40 * 2225815 * 2
def baseEnd_2225815 : Nat := 1142912942987314222276169

theorem tailTrace_2225815 : CollatzResearch.WordTrace tailWord_2225815 prefixEnd_2225815 1142912942987314222276169 := by
  unfold tailWord_2225815
  simp only [CollatzResearch.WordTrace]
  refine ⟨81182142431259868782702899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54121428287506579188468599 81182142431259868782702899)
  ·
    refine ⟨121773213646889803174054349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81182142431259868782702899 121773213646889803174054349)
    ·
      refine ⟨45664955117583676190270381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121773213646889803174054349 45664955117583676190270381)
      ·
        refine ⟨17124358169093878571351393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45664955117583676190270381 17124358169093878571351393)
        ·
          refine ⟨12843268626820408928513545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17124358169093878571351393 12843268626820408928513545)
          ·
            refine ⟨9632451470115306696385159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12843268626820408928513545 9632451470115306696385159)
            ·
              refine ⟨14448677205172960044577739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9632451470115306696385159 14448677205172960044577739)
              ·
                refine ⟨21673015807759440066866609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14448677205172960044577739 21673015807759440066866609)
                ·
                  refine ⟨16254761855819580050149957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21673015807759440066866609 16254761855819580050149957)
                  ·
                    refine ⟨3047767847966171259403117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16254761855819580050149957 3047767847966171259403117)
                    ·
                      refine ⟨1142912942987314222276169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3047767847966171259403117 1142912942987314222276169)
                      ·
                        rfl

theorem cell23_2225815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2225815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225815 prefixEnd_2225815 := by exact prefixLift 2225815
  have htrace : WordTrace (prefixWord ++ tailWord_2225815) baseStart_2225815 baseEnd_2225815 := by
    simpa [prefixWord, tailWord_2225815, baseEnd_2225815] using wordTrace_append hprefix tailTrace_2225815
  have hstable : (prefixWord ++ tailWord_2225815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225815).length < 2 ^ (prefixWord ++ tailWord_2225815).sum := by decide
  have hdescent : baseEnd_2225815 < baseStart_2225815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225822 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2225822 : Nat := 118140960795 + 2225822 * 2 ^ 59
def prefixEnd_2225822 : Nat := 4983230072969 + 3 ^ 40 * 2225822 * 2
def baseEnd_2225822 : Nat := 380972179117298564962879

theorem tailTrace_2225822 : CollatzResearch.WordTrace tailWord_2225822 prefixEnd_2225822 380972179117298564962879 := by
  unfold tailWord_2225822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147799717779313622275965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54121598494823005985471813 10147799717779313622275965)
  ·
    refine ⟨3805424894167242608353487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10147799717779313622275965 3805424894167242608353487)
    ·
      refine ⟨5708137341250863912530231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3805424894167242608353487 5708137341250863912530231)
      ·
        refine ⟨8562206011876295868795347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5708137341250863912530231 8562206011876295868795347)
        ·
          refine ⟨12843309017814443803193021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8562206011876295868795347 12843309017814443803193021)
          ·
            refine ⟨4816240881680416426197383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12843309017814443803193021 4816240881680416426197383)
            ·
              refine ⟨7224361322520624639296075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816240881680416426197383 7224361322520624639296075)
              ·
                refine ⟨10836541983780936958944113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7224361322520624639296075 10836541983780936958944113)
                ·
                  refine ⟨8127406487835702719208085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10836541983780936958944113 8127406487835702719208085)
                  ·
                    refine ⟨380972179117298564962879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8127406487835702719208085 380972179117298564962879)
                    ·
                      rfl

theorem cell23_2225822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2225822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225822 prefixEnd_2225822 := by exact prefixLift 2225822
  have htrace : WordTrace (prefixWord ++ tailWord_2225822) baseStart_2225822 baseEnd_2225822 := by
    simpa [prefixWord, tailWord_2225822, baseEnd_2225822] using wordTrace_append hprefix tailTrace_2225822
  have hstable : (prefixWord ++ tailWord_2225822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225822).length < 2 ^ (prefixWord ++ tailWord_2225822).sum := by decide
  have hdescent : baseEnd_2225822 < baseStart_2225822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225825 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2225825 : Nat := 118140960795 + 2225825 * 2 ^ 59
def prefixEnd_2225825 : Nat := 4983230072969 + 3 ^ 40 * 2225825 * 2
def baseEnd_2225825 : Nat := 1142918077793859183151123

theorem tailTrace_2225825 : CollatzResearch.WordTrace tailWord_2225825 prefixEnd_2225825 1142918077793859183151123 := by
  unfold tailWord_2225825
  simp only [CollatzResearch.WordTrace]
  refine ⟨81182507161223640490566929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54121671440815760327044619 81182507161223640490566929)
  ·
    refine ⟨60886880370917730367925197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81182507161223640490566929 60886880370917730367925197)
    ·
      refine ⟨22832580139094148887971949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60886880370917730367925197 22832580139094148887971949)
      ·
        refine ⟨8562217552160305832989481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22832580139094148887971949 8562217552160305832989481)
        ·
          refine ⟨6421663164120229374742111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8562217552160305832989481 6421663164120229374742111)
          ·
            refine ⟨9632494746180344062113167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421663164120229374742111 9632494746180344062113167)
            ·
              refine ⟨14448742119270516093169751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9632494746180344062113167 14448742119270516093169751)
              ·
                refine ⟨21673113178905774139754627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14448742119270516093169751 21673113178905774139754627)
                ·
                  refine ⟨32509669768358661209631941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21673113178905774139754627 32509669768358661209631941)
                  ·
                    refine ⟨6095563081567248976805989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32509669768358661209631941 6095563081567248976805989)
                    ·
                      refine ⟨1142918077793859183151123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6095563081567248976805989 1142918077793859183151123)
                      ·
                        rfl

theorem cell23_2225825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2225825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225825 prefixEnd_2225825 := by exact prefixLift 2225825
  have htrace : WordTrace (prefixWord ++ tailWord_2225825) baseStart_2225825 baseEnd_2225825 := by
    simpa [prefixWord, tailWord_2225825, baseEnd_2225825] using wordTrace_append hprefix tailTrace_2225825
  have hstable : (prefixWord ++ tailWord_2225825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225825).length < 2 ^ (prefixWord ++ tailWord_2225825).sum := by decide
  have hdescent : baseEnd_2225825 < baseStart_2225825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225829 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 2, 2, 2]
def baseStart_2225829 : Nat := 118140960795 + 2225829 * 2 ^ 59
def prefixEnd_2225829 : Nat := 4983230072969 + 3 ^ 40 * 2225829 * 2
def baseEnd_2225829 : Nat := 1142920131716477167501105

theorem tailTrace_2225829 : CollatzResearch.WordTrace tailWord_2225829 prefixEnd_2225829 1142920131716477167501105 := by
  unfold tailWord_2225829
  simp only [CollatzResearch.WordTrace]
  refine ⟨81182653053209149173712541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54121768702139432782475027 81182653053209149173712541)
  ·
    refine ⟨30443494894953430940142203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81182653053209149173712541 30443494894953430940142203)
    ·
      refine ⟨45665242342430146410213305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30443494894953430940142203 45665242342430146410213305)
      ·
        refine ⟨34248931756822609807659979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45665242342430146410213305 34248931756822609807659979)
        ·
          refine ⟨51373397635233914711489969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34248931756822609807659979 51373397635233914711489969)
          ·
            refine ⟨38530048226425436033617477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51373397635233914711489969 38530048226425436033617477)
            ·
              refine ⟨7224384042454769256303277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38530048226425436033617477 7224384042454769256303277)
              ·
                refine ⟨2709144015920538471113729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7224384042454769256303277 2709144015920538471113729)
                ·
                  refine ⟨2031858011940403853335297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709144015920538471113729 2031858011940403853335297)
                  ·
                    refine ⟨1523893508955302890001473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2031858011940403853335297 1523893508955302890001473)
                    ·
                      refine ⟨1142920131716477167501105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523893508955302890001473 1142920131716477167501105)
                      ·
                        rfl

theorem cell23_2225829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_2225829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225829 prefixEnd_2225829 := by exact prefixLift 2225829
  have htrace : WordTrace (prefixWord ++ tailWord_2225829) baseStart_2225829 baseEnd_2225829 := by
    simpa [prefixWord, tailWord_2225829, baseEnd_2225829] using wordTrace_append hprefix tailTrace_2225829
  have hstable : (prefixWord ++ tailWord_2225829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225829).length < 2 ^ (prefixWord ++ tailWord_2225829).sum := by decide
  have hdescent : baseEnd_2225829 < baseStart_2225829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225846 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2225846 : Nat := 118140960795 + 2225846 * 2 ^ 59
def prefixEnd_2225846 : Nat := 4983230072969 + 3 ^ 40 * 2225846 * 2
def baseEnd_2225846 : Nat := 1142928860887603600988527

theorem tailTrace_2225846 : CollatzResearch.WordTrace tailWord_2225846 prefixEnd_2225846 1142928860887603600988527 := by
  unfold tailWord_2225846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073954568384222567317587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54122182062765040718054261 5073954568384222567317587)
  ·
    refine ⟨7610931852576333850976381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5073954568384222567317587 7610931852576333850976381)
    ·
      refine ⟨2854099444716125194116143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7610931852576333850976381 2854099444716125194116143)
      ·
        refine ⟨4281149167074187791174215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854099444716125194116143 4281149167074187791174215)
        ·
          refine ⟨6421723750611281686761323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281149167074187791174215 6421723750611281686761323)
          ·
            refine ⟨9632585625916922530141985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6421723750611281686761323 9632585625916922530141985)
            ·
              refine ⟨7224439219437691897606489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9632585625916922530141985 7224439219437691897606489)
              ·
                refine ⟨5418329414578268923204867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224439219437691897606489 5418329414578268923204867)
                ·
                  refine ⟨8127494121867403384807301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418329414578268923204867 8127494121867403384807301)
                  ·
                    refine ⟨1523905147850138134651369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8127494121867403384807301 1523905147850138134651369)
                    ·
                      refine ⟨1142928860887603600988527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1523905147850138134651369 1142928860887603600988527)
                      ·
                        rfl

theorem cell23_2225846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2225846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225846 prefixEnd_2225846 := by exact prefixLift 2225846
  have htrace : WordTrace (prefixWord ++ tailWord_2225846) baseStart_2225846 baseEnd_2225846 := by
    simpa [prefixWord, tailWord_2225846, baseEnd_2225846] using wordTrace_append hprefix tailTrace_2225846
  have hstable : (prefixWord ++ tailWord_2225846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225846).length < 2 ^ (prefixWord ++ tailWord_2225846).sum := by decide
  have hdescent : baseEnd_2225846 < baseStart_2225846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225852 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 5]
def baseStart_2225852 : Nat := 118140960795 + 2225852 * 2 ^ 59
def prefixEnd_2225852 : Nat := 4983230072969 + 3 ^ 40 * 2225852 * 2
def baseEnd_2225852 : Nat := 126992437974614508612611

theorem tailTrace_2225852 : CollatzResearch.WordTrace tailWord_2225852 prefixEnd_2225852 126992437974614508612611 := by
  unfold tailWord_2225852
  simp only [CollatzResearch.WordTrace]
  refine ⟨40591745966062912050899905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54122327954750549401199873 40591745966062912050899905)
  ·
    refine ⟨30443809474547184038174929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40591745966062912050899905 30443809474547184038174929)
    ·
      refine ⟨22832857105910388028631197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30443809474547184038174929 22832857105910388028631197)
      ·
        refine ⟨8562321414716395510736699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22832857105910388028631197 8562321414716395510736699)
        ·
          refine ⟨12843482122074593266105049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8562321414716395510736699 12843482122074593266105049)
          ·
            refine ⟨9632611591555944949578787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12843482122074593266105049 9632611591555944949578787)
            ·
              refine ⟨14448917387333917424368181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9632611591555944949578787 14448917387333917424368181)
              ·
                refine ⟨1354586005062554758534517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14448917387333917424368181 1354586005062554758534517)
                ·
                  refine ⟨126992437974614508612611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1354586005062554758534517 126992437974614508612611)
                  ·
                    rfl

theorem cell23_2225852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_2225852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225852 prefixEnd_2225852 := by exact prefixLift 2225852
  have htrace : WordTrace (prefixWord ++ tailWord_2225852) baseStart_2225852 baseEnd_2225852 := by
    simpa [prefixWord, tailWord_2225852, baseEnd_2225852] using wordTrace_append hprefix tailTrace_2225852
  have hstable : (prefixWord ++ tailWord_2225852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225852).length < 2 ^ (prefixWord ++ tailWord_2225852).sum := by decide
  have hdescent : baseEnd_2225852 < baseStart_2225852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225869 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2225869 : Nat := 118140960795 + 2225869 * 2 ^ 59
def prefixEnd_2225869 : Nat := 4983230072969 + 3 ^ 40 * 2225869 * 2
def baseEnd_2225869 : Nat := 126993407882517445666769

theorem tailTrace_2225869 : CollatzResearch.WordTrace tailWord_2225869 prefixEnd_2225869 126993407882517445666769 := by
  unfold tailWord_2225869
  simp only [CollatzResearch.WordTrace]
  refine ⟨81184111973064236005168661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54122741315376157336779107 81184111973064236005168661)
  ·
    refine ⟨3805505248737386062742281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81184111973064236005168661 3805505248737386062742281)
    ·
      refine ⟨2854128936553039547056711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3805505248737386062742281 2854128936553039547056711)
      ·
        refine ⟨4281193404829559320585067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854128936553039547056711 4281193404829559320585067)
        ·
          refine ⟨6421790107244338980877601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281193404829559320585067 6421790107244338980877601)
          ·
            refine ⟨4816342580433254235658201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6421790107244338980877601 4816342580433254235658201)
            ·
              refine ⟨3612256935324940676743651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4816342580433254235658201 3612256935324940676743651)
              ·
                refine ⟨5418385402987411015115477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612256935324940676743651 5418385402987411015115477)
                ·
                  refine ⟨126993407882517445666769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5418385402987411015115477 126993407882517445666769)
                  ·
                    rfl

theorem cell23_2225869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2225869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225869 prefixEnd_2225869 := by exact prefixLift 2225869
  have htrace : WordTrace (prefixWord ++ tailWord_2225869) baseStart_2225869 baseEnd_2225869 := by
    simpa [prefixWord, tailWord_2225869, baseEnd_2225869] using wordTrace_append hprefix tailTrace_2225869
  have hstable : (prefixWord ++ tailWord_2225869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225869).length < 2 ^ (prefixWord ++ tailWord_2225869).sum := by decide
  have hdescent : baseEnd_2225869 < baseStart_2225869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225902 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2225902 : Nat := 118140960795 + 2225902 * 2 ^ 59
def prefixEnd_2225902 : Nat := 4983230072969 + 3 ^ 40 * 2225902 * 2
def baseEnd_2225902 : Nat := 1142957615804255381888269

theorem tailTrace_2225902 : CollatzResearch.WordTrace tailWord_2225902 prefixEnd_2225902 1142957615804255381888269 := by
  unfold tailWord_2225902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10148164447743085330139995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54123543721296455094079973 10148164447743085330139995)
  ·
    refine ⟨15222246671614627995209993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10148164447743085330139995 15222246671614627995209993)
    ·
      refine ⟨11416685003710970996407495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15222246671614627995209993 11416685003710970996407495)
      ·
        refine ⟨17125027505566456494611243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11416685003710970996407495 17125027505566456494611243)
        ·
          refine ⟨25687541258349684741916865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17125027505566456494611243 25687541258349684741916865)
          ·
            refine ⟨19265655943762263556437649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25687541258349684741916865 19265655943762263556437649)
            ·
              refine ⟨14449241957821697667328237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19265655943762263556437649 14449241957821697667328237)
              ·
                refine ⟨5418465734183136625248089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14449241957821697667328237 5418465734183136625248089)
                ·
                  refine ⟨4063849300637352468936067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418465734183136625248089 4063849300637352468936067)
                  ·
                    refine ⟨6095773950956028703404101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4063849300637352468936067 6095773950956028703404101)
                    ·
                      refine ⟨1142957615804255381888269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6095773950956028703404101 1142957615804255381888269)
                      ·
                        rfl

theorem cell23_2225902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2225902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225902 prefixEnd_2225902 := by exact prefixLift 2225902
  have htrace : WordTrace (prefixWord ++ tailWord_2225902) baseStart_2225902 baseEnd_2225902 := by
    simpa [prefixWord, tailWord_2225902, baseEnd_2225902] using wordTrace_append hprefix tailTrace_2225902
  have hstable : (prefixWord ++ tailWord_2225902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225902).length < 2 ^ (prefixWord ++ tailWord_2225902).sum := by decide
  have hdescent : baseEnd_2225902 < baseStart_2225902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225935 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_2225935 : Nat := 118140960795 + 2225935 * 2 ^ 59
def prefixEnd_2225935 : Nat := 4983230072969 + 3 ^ 40 * 2225935 * 2
def baseEnd_2225935 : Nat := 1142974560665853752775617

theorem tailTrace_2225935 : CollatzResearch.WordTrace tailWord_2225935 prefixEnd_2225935 1142974560665853752775617 := by
  unfold tailWord_2225935
  simp only [CollatzResearch.WordTrace]
  refine ⟨81186519190825129277071259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54124346127216752851380839 81186519190825129277071259)
  ·
    refine ⟨121779778786237693915606889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81186519190825129277071259 121779778786237693915606889)
    ·
      refine ⟨91334834089678270436705167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121779778786237693915606889 91334834089678270436705167)
      ·
        refine ⟨137002251134517405655057751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91334834089678270436705167 137002251134517405655057751)
        ·
          refine ⟨205503376701776108482586627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137002251134517405655057751 205503376701776108482586627)
          ·
            refine ⟨308255065052664162723879941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205503376701776108482586627 308255065052664162723879941)
            ·
              refine ⟨57797824697374530510727489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 308255065052664162723879941 57797824697374530510727489)
              ·
                refine ⟨43348368523030897883045617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57797824697374530510727489 43348368523030897883045617)
                ·
                  refine ⟨32511276392273173412284213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43348368523030897883045617 32511276392273173412284213)
                  ·
                    refine ⟨3047932161775610007401645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32511276392273173412284213 3047932161775610007401645)
                    ·
                      refine ⟨1142974560665853752775617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3047932161775610007401645 1142974560665853752775617)
                      ·
                        rfl

theorem cell23_2225935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_2225935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225935 prefixEnd_2225935 := by exact prefixLift 2225935
  have htrace : WordTrace (prefixWord ++ tailWord_2225935) baseStart_2225935 baseEnd_2225935 := by
    simpa [prefixWord, tailWord_2225935, baseEnd_2225935] using wordTrace_append hprefix tailTrace_2225935
  have hstable : (prefixWord ++ tailWord_2225935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225935).length < 2 ^ (prefixWord ++ tailWord_2225935).sum := by decide
  have hdescent : baseEnd_2225935 < baseStart_2225935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225992 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_2225992 : Nat := 118140960795 + 2225992 * 2 ^ 59
def prefixEnd_2225992 : Nat := 4983230072969 + 3 ^ 40 * 2225992 * 2
def baseEnd_2225992 : Nat := 1143003829063160029762855

theorem tailTrace_2225992 : CollatzResearch.WordTrace tailWord_2225992 prefixEnd_2225992 1143003829063160029762855 := by
  unfold tailWord_2225992
  simp only [CollatzResearch.WordTrace]
  refine ⟨40594299075809314005948115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54125732101079085341264153 40594299075809314005948115)
  ·
    refine ⟨60891448613713971008922173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40594299075809314005948115 60891448613713971008922173)
    ·
      refine ⟨22834293230142739128345815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60891448613713971008922173 22834293230142739128345815)
      ·
        refine ⟨34251439845214108692518723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22834293230142739128345815 34251439845214108692518723)
        ·
          refine ⟨51377159767821163038778085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34251439845214108692518723 51377159767821163038778085)
          ·
            refine ⟨9633217456466468069770891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51377159767821163038778085 9633217456466468069770891)
            ·
              refine ⟨14449826184699702104656337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633217456466468069770891 14449826184699702104656337)
              ·
                refine ⟨10837369638524776578492253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14449826184699702104656337 10837369638524776578492253)
                ·
                  refine ⟨4064013614446791216934595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10837369638524776578492253 4064013614446791216934595)
                  ·
                    refine ⟨6096020421670186825401893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4064013614446791216934595 6096020421670186825401893)
                    ·
                      refine ⟨1143003829063160029762855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6096020421670186825401893 1143003829063160029762855)
                      ·
                        rfl

theorem cell23_2225992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_2225992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2225992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2225992 prefixEnd_2225992 := by exact prefixLift 2225992
  have htrace : WordTrace (prefixWord ++ tailWord_2225992) baseStart_2225992 baseEnd_2225992 := by
    simpa [prefixWord, tailWord_2225992, baseEnd_2225992] using wordTrace_append hprefix tailTrace_2225992
  have hstable : (prefixWord ++ tailWord_2225992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225992).length < 2 ^ (prefixWord ++ tailWord_2225992).sum := by decide
  have hdescent : baseEnd_2225992 < baseStart_2225992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226002 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2226002 : Nat := 118140960795 + 2226002 * 2 ^ 59
def prefixEnd_2226002 : Nat := 4983230072969 + 3 ^ 40 * 2226002 * 2
def baseEnd_2226002 : Nat := 381002987956568330212603

theorem tailTrace_2226002 : CollatzResearch.WordTrace tailWord_2226002 prefixEnd_2226002 381002987956568330212603 := by
  unfold tailWord_2226002
  simp only [CollatzResearch.WordTrace]
  refine ⟨20297240720395599929940065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54125975254388266479840173 20297240720395599929940065)
  ·
    refine ⟨15222930540296699947455049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20297240720395599929940065 15222930540296699947455049)
    ·
      refine ⟨11417197905222524960591287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15222930540296699947455049 11417197905222524960591287)
      ·
        refine ⟨17125796857833787440886931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11417197905222524960591287 17125796857833787440886931)
        ·
          refine ⟨25688695286750681161330397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17125796857833787440886931 25688695286750681161330397)
          ·
            refine ⟨9633260732531505435498899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25688695286750681161330397 9633260732531505435498899)
            ·
              refine ⟨14449891098797258153248349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633260732531505435498899 14449891098797258153248349)
              ·
                refine ⟨5418709162048971807468131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14449891098797258153248349 5418709162048971807468131)
                ·
                  refine ⟨8128063743073457711202197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418709162048971807468131 8128063743073457711202197)
                  ·
                    refine ⟨381002987956568330212603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8128063743073457711202197 381002987956568330212603)
                    ·
                      rfl

theorem cell23_2226002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2226002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226002 prefixEnd_2226002 := by exact prefixLift 2226002
  have htrace : WordTrace (prefixWord ++ tailWord_2226002) baseStart_2226002 baseEnd_2226002 := by
    simpa [prefixWord, tailWord_2226002, baseEnd_2226002] using wordTrace_append hprefix tailTrace_2226002
  have hstable : (prefixWord ++ tailWord_2226002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226002).length < 2 ^ (prefixWord ++ tailWord_2226002).sum := by decide
  have hdescent : baseEnd_2226002 < baseStart_2226002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226035 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_2226035 : Nat := 118140960795 + 2226035 * 2 ^ 59
def prefixEnd_2226035 : Nat := 4983230072969 + 3 ^ 40 * 2226035 * 2
def baseEnd_2226035 : Nat := 1143025908731303361525157

theorem tailTrace_2226035 : CollatzResearch.WordTrace tailWord_2226035 prefixEnd_2226035 1143025908731303361525157 := by
  unfold tailWord_2226035
  simp only [CollatzResearch.WordTrace]
  refine ⟨81190166490462846355711559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54126777660308564237141039 81190166490462846355711559)
  ·
    refine ⟨121785249735694269533567339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81190166490462846355711559 121785249735694269533567339)
    ·
      refine ⟨182677874603541404300351009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121785249735694269533567339 182677874603541404300351009)
      ·
        refine ⟨137008405952656053225263257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182677874603541404300351009 137008405952656053225263257)
        ·
          refine ⟨102756304464492039918947443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137008405952656053225263257 102756304464492039918947443)
          ·
            refine ⟨154134456696738059878421165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102756304464492039918947443 154134456696738059878421165)
            ·
              refine ⟨57800421261276772454407937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154134456696738059878421165 57800421261276772454407937)
              ·
                refine ⟨43350315945957579340805953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57800421261276772454407937 43350315945957579340805953)
                ·
                  refine ⟨32512736959468184505604465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43350315945957579340805953 32512736959468184505604465)
                  ·
                    refine ⟨24384552719601138379203349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32512736959468184505604465 24384552719601138379203349)
                    ·
                      refine ⟨1143025908731303361525157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24384552719601138379203349 1143025908731303361525157)
                      ·
                        rfl

theorem cell23_2226035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_2226035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226035 prefixEnd_2226035 := by exact prefixLift 2226035
  have htrace : WordTrace (prefixWord ++ tailWord_2226035) baseStart_2226035 baseEnd_2226035 := by
    simpa [prefixWord, tailWord_2226035, baseEnd_2226035] using wordTrace_append hprefix tailTrace_2226035
  have hstable : (prefixWord ++ tailWord_2226035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226035).length < 2 ^ (prefixWord ++ tailWord_2226035).sum := by decide
  have hdescent : baseEnd_2226035 < baseStart_2226035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226042 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_2226042 : Nat := 118140960795 + 2226042 * 2 ^ 59
def prefixEnd_2226042 : Nat := 4983230072969 + 3 ^ 40 * 2226042 * 2
def baseEnd_2226042 : Nat := 1143029503095884834137625

theorem tailTrace_2226042 : CollatzResearch.WordTrace tailWord_2226042 prefixEnd_2226042 1143029503095884834137625 := by
  unfold tailWord_2226042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20297605450359371637804095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54126947867624991034144253 20297605450359371637804095)
  ·
    refine ⟨30446408175539057456706143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20297605450359371637804095 30446408175539057456706143)
    ·
      refine ⟨45669612263308586185059215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30446408175539057456706143 45669612263308586185059215)
      ·
        refine ⟨68504418394962879277588823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45669612263308586185059215 68504418394962879277588823)
        ·
          refine ⟨102756627592444318916383235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68504418394962879277588823 102756627592444318916383235)
          ·
            refine ⟨154134941388666478374574853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102756627592444318916383235 154134941388666478374574853)
            ·
              refine ⟨28900301510374964695232785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154134941388666478374574853 28900301510374964695232785)
              ·
                refine ⟨21675226132781223521424589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28900301510374964695232785 21675226132781223521424589)
                ·
                  refine ⟨8128209799792958820534221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21675226132781223521424589 8128209799792958820534221)
                  ·
                    refine ⟨3048078674922359557700333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8128209799792958820534221 3048078674922359557700333)
                    ·
                      refine ⟨1143029503095884834137625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3048078674922359557700333 1143029503095884834137625)
                      ·
                        rfl

theorem cell23_2226042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_2226042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226042 prefixEnd_2226042 := by exact prefixLift 2226042
  have htrace : WordTrace (prefixWord ++ tailWord_2226042) baseStart_2226042 baseEnd_2226042 := by
    simpa [prefixWord, tailWord_2226042, baseEnd_2226042] using wordTrace_append hprefix tailTrace_2226042
  have hstable : (prefixWord ++ tailWord_2226042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226042).length < 2 ^ (prefixWord ++ tailWord_2226042).sum := by decide
  have hdescent : baseEnd_2226042 < baseStart_2226042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226046 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2226046 : Nat := 118140960795 + 2226046 * 2 ^ 59
def prefixEnd_2226046 : Nat := 4983230072969 + 3 ^ 40 * 2226046 * 2
def baseEnd_2226046 : Nat := 1143031557018502818487607

theorem tailTrace_2226046 : CollatzResearch.WordTrace tailWord_2226046 prefixEnd_2226046 1143031557018502818487607 := by
  unfold tailWord_2226046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10148820961677874404295249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54127045128948663489574661 10148820961677874404295249)
  ·
    refine ⟨7611615721258405803221437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10148820961677874404295249 7611615721258405803221437)
    ·
      refine ⟨2854355895471902176208039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7611615721258405803221437 2854355895471902176208039)
      ·
        refine ⟨4281533843207853264312059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854355895471902176208039 4281533843207853264312059)
        ·
          refine ⟨6422300764811779896468089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281533843207853264312059 6422300764811779896468089)
          ·
            refine ⟨4816725573608834922351067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6422300764811779896468089 4816725573608834922351067)
            ·
              refine ⟨7225088360413252383526601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816725573608834922351067 7225088360413252383526601)
              ·
                refine ⟨5418816270309939287644951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7225088360413252383526601 5418816270309939287644951)
                ·
                  refine ⟨8128224405464908931467427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418816270309939287644951 8128224405464908931467427)
                  ·
                    refine ⟨12192336608197363397201141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8128224405464908931467427 12192336608197363397201141)
                    ·
                      refine ⟨1143031557018502818487607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12192336608197363397201141 1143031557018502818487607)
                      ·
                        rfl

theorem cell23_2226046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2226046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226046 prefixEnd_2226046 := by exact prefixLift 2226046
  have htrace : WordTrace (prefixWord ++ tailWord_2226046) baseStart_2226046 baseEnd_2226046 := by
    simpa [prefixWord, tailWord_2226046, baseEnd_2226046] using wordTrace_append hprefix tailTrace_2226046
  have hstable : (prefixWord ++ tailWord_2226046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226046).length < 2 ^ (prefixWord ++ tailWord_2226046).sum := by decide
  have hdescent : baseEnd_2226046 < baseStart_2226046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226056 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2226056 : Nat := 118140960795 + 2226056 * 2 ^ 59
def prefixEnd_2226056 : Nat := 4983230072969 + 3 ^ 40 * 2226056 * 2
def baseEnd_2226056 : Nat := 1143036691825047779362561

theorem tailTrace_2226056 : CollatzResearch.WordTrace tailWord_2226056 prefixEnd_2226056 1143036691825047779362561 := by
  unfold tailWord_2226056
  simp only [CollatzResearch.WordTrace]
  refine ⟨40595466211693383471113011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54127288282257844628150681 40595466211693383471113011)
  ·
    refine ⟨60893199317540075206669517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40595466211693383471113011 60893199317540075206669517)
    ·
      refine ⟨22834949744077528202501069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60893199317540075206669517 22834949744077528202501069)
      ·
        refine ⟨8563106154029073075937901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22834949744077528202501069 8563106154029073075937901)
        ·
          refine ⟨3211164807760902403476713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8563106154029073075937901 3211164807760902403476713)
          ·
            refine ⟨2408373605820676802607535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3211164807760902403476713 2408373605820676802607535)
            ·
              refine ⟨3612560408731015203911303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408373605820676802607535 3612560408731015203911303)
              ·
                refine ⟨5418840613096522805866955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612560408731015203911303 5418840613096522805866955)
                ·
                  refine ⟨8128260919644784208800433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418840613096522805866955 8128260919644784208800433)
                  ·
                    refine ⟨6096195689733588156600325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8128260919644784208800433 6096195689733588156600325)
                    ·
                      refine ⟨1143036691825047779362561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6096195689733588156600325 1143036691825047779362561)
                      ·
                        rfl

theorem cell23_2226056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2226056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226056 prefixEnd_2226056 := by exact prefixLift 2226056
  have htrace : WordTrace (prefixWord ++ tailWord_2226056) baseStart_2226056 baseEnd_2226056 := by
    simpa [prefixWord, tailWord_2226056, baseEnd_2226056] using wordTrace_append hprefix tailTrace_2226056
  have hstable : (prefixWord ++ tailWord_2226056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226056).length < 2 ^ (prefixWord ++ tailWord_2226056).sum := by decide
  have hdescent : baseEnd_2226056 < baseStart_2226056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226066 : List Nat := [3, 2, 3, 2, 1, 3, 2, 7]
def baseStart_2226066 : Nat := 118140960795 + 2226066 * 2 ^ 59
def prefixEnd_2226066 : Nat := 4983230072969 + 3 ^ 40 * 2226066 * 2
def baseEnd_2226066 : Nat := 42334882467836768156945

theorem tailTrace_2226066 : CollatzResearch.WordTrace tailWord_2226066 prefixEnd_2226066 42334882467836768156945 := by
  unfold tailWord_2226066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20297824288337634662522513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54127531435567025766726701 20297824288337634662522513)
  ·
    refine ⟨15223368216253225996891885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20297824288337634662522513 15223368216253225996891885)
    ·
      refine ⟨5708763081094959748834457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15223368216253225996891885 5708763081094959748834457)
      ·
        refine ⟨4281572310821219811625843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5708763081094959748834457 4281572310821219811625843)
        ·
          refine ⟨6422358466231829717438765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281572310821219811625843 6422358466231829717438765)
          ·
            refine ⟨2408384424836936144039537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6422358466231829717438765 2408384424836936144039537)
            ·
              refine ⟨1806288318627702108029653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408384424836936144039537 1806288318627702108029653)
              ·
                refine ⟨42334882467836768156945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1806288318627702108029653 42334882467836768156945)
                ·
                  rfl

theorem cell23_2226066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_2226066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226066 prefixEnd_2226066 := by exact prefixLift 2226066
  have htrace : WordTrace (prefixWord ++ tailWord_2226066) baseStart_2226066 baseEnd_2226066 := by
    simpa [prefixWord, tailWord_2226066, baseEnd_2226066] using wordTrace_append hprefix tailTrace_2226066
  have hstable : (prefixWord ++ tailWord_2226066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226066).length < 2 ^ (prefixWord ++ tailWord_2226066).sum := by decide
  have hdescent : baseEnd_2226066 < baseStart_2226066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226076 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2226076 : Nat := 118140960795 + 2226076 * 2 ^ 59
def prefixEnd_2226076 : Nat := 4983230072969 + 3 ^ 40 * 2226076 * 2
def baseEnd_2226076 : Nat := 1143046961438137701112469

theorem tailTrace_2226076 : CollatzResearch.WordTrace tailWord_2226076 prefixEnd_2226076 1143046961438137701112469 := by
  unfold tailWord_2226076
  simp only [CollatzResearch.WordTrace]
  refine ⟨40595830941657155178977041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54127774588876206905302721 40595830941657155178977041)
  ·
    refine ⟨30446873206242866384232781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40595830941657155178977041 30446873206242866384232781)
    ·
      refine ⟨11417577452341074894087293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30446873206242866384232781 11417577452341074894087293)
      ·
        refine ⟨4281591544627903085282735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11417577452341074894087293 4281591544627903085282735)
        ·
          refine ⟨6422387316941854627924103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281591544627903085282735 6422387316941854627924103)
          ·
            refine ⟨9633580975412781941886155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6422387316941854627924103 9633580975412781941886155)
            ·
              refine ⟨14450371463119172912829233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9633580975412781941886155 14450371463119172912829233)
              ·
                refine ⟨10837778597339379684621925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14450371463119172912829233 10837778597339379684621925)
                ·
                  refine ⟨2032083487001133690866611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10837778597339379684621925 2032083487001133690866611)
                  ·
                    refine ⟨3048125230501700536299917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032083487001133690866611 3048125230501700536299917)
                    ·
                      refine ⟨1143046961438137701112469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3048125230501700536299917 1143046961438137701112469)
                      ·
                        rfl

theorem cell23_2226076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2226076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226076 prefixEnd_2226076 := by exact prefixLift 2226076
  have htrace : WordTrace (prefixWord ++ tailWord_2226076) baseStart_2226076 baseEnd_2226076 := by
    simpa [prefixWord, tailWord_2226076, baseEnd_2226076] using wordTrace_append hprefix tailTrace_2226076
  have hstable : (prefixWord ++ tailWord_2226076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226076).length < 2 ^ (prefixWord ++ tailWord_2226076).sum := by decide
  have hdescent : baseEnd_2226076 < baseStart_2226076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226094 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2226094 : Nat := 118140960795 + 2226094 * 2 ^ 59
def prefixEnd_2226094 : Nat := 4983230072969 + 3 ^ 40 * 2226094 * 2
def baseEnd_2226094 : Nat := 1143056204089918630687387

theorem tailTrace_2226094 : CollatzResearch.WordTrace tailWord_2226094 prefixEnd_2226094 1143056204089918630687387 := by
  unfold tailWord_2226094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149039799656137429013667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54128212264832732954739557 10149039799656137429013667)
  ·
    refine ⟨15223559699484206143520501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10149039799656137429013667 15223559699484206143520501)
    ·
      refine ⟨1427208721826644325955047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15223559699484206143520501 1427208721826644325955047)
      ·
        refine ⟨2140813082739966488932571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1427208721826644325955047 2140813082739966488932571)
        ·
          refine ⟨3211219624109949733398857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140813082739966488932571 3211219624109949733398857)
          ·
            refine ⟨2408414718082462300049143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3211219624109949733398857 2408414718082462300049143)
            ·
              refine ⟨3612622077123693450073715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408414718082462300049143 3612622077123693450073715)
              ·
                refine ⟨5418933115685540175110573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612622077123693450073715 5418933115685540175110573)
                ·
                  refine ⟨2032099918382077565666465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5418933115685540175110573 2032099918382077565666465)
                  ·
                    refine ⟨1524074938786558174249849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2032099918382077565666465 1524074938786558174249849)
                    ·
                      refine ⟨1143056204089918630687387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524074938786558174249849 1143056204089918630687387)
                      ·
                        rfl

theorem cell23_2226094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2226094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226094 prefixEnd_2226094 := by exact prefixLift 2226094
  have htrace : WordTrace (prefixWord ++ tailWord_2226094) baseStart_2226094 baseEnd_2226094 := by
    simpa [prefixWord, tailWord_2226094, baseEnd_2226094] using wordTrace_append hprefix tailTrace_2226094
  have hstable : (prefixWord ++ tailWord_2226094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226094).length < 2 ^ (prefixWord ++ tailWord_2226094).sum := by decide
  have hdescent : baseEnd_2226094 < baseStart_2226094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226110 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_2226110 : Nat := 118140960795 + 2226110 * 2 ^ 59
def prefixEnd_2226110 : Nat := 4983230072969 + 3 ^ 40 * 2226110 * 2
def baseEnd_2226110 : Nat := 1143064419780390568087313

theorem tailTrace_2226110 : CollatzResearch.WordTrace tailWord_2226110 prefixEnd_2226110 1143064419780390568087313 := by
  unfold tailWord_2226110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149112745648891770586473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54128601310127422776461189 10149112745648891770586473)
  ·
    refine ⟨7611834559236668827939855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10149112745648891770586473 7611834559236668827939855)
    ·
      refine ⟨11417751838855003241909783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7611834559236668827939855 11417751838855003241909783)
      ·
        refine ⟨17126627758282504862864675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11417751838855003241909783 17126627758282504862864675)
        ·
          refine ⟨25689941637423757294297013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17126627758282504862864675 25689941637423757294297013)
          ·
            refine ⟨2408432028508477246340345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25689941637423757294297013 2408432028508477246340345)
            ·
              refine ⟨1806324021381357934755259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408432028508477246340345 1806324021381357934755259)
              ·
                refine ⟨2709486032072036902132889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806324021381357934755259 2709486032072036902132889)
                ·
                  refine ⟨2032114524054027676599667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709486032072036902132889 2032114524054027676599667)
                  ·
                    refine ⟨3048171786081041514899501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032114524054027676599667 3048171786081041514899501)
                    ·
                      refine ⟨1143064419780390568087313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3048171786081041514899501 1143064419780390568087313)
                      ·
                        rfl

theorem cell23_2226110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_2226110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226110 prefixEnd_2226110 := by exact prefixLift 2226110
  have htrace : WordTrace (prefixWord ++ tailWord_2226110) baseStart_2226110 baseEnd_2226110 := by
    simpa [prefixWord, tailWord_2226110, baseEnd_2226110] using wordTrace_append hprefix tailTrace_2226110
  have hstable : (prefixWord ++ tailWord_2226110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226110).length < 2 ^ (prefixWord ++ tailWord_2226110).sum := by decide
  have hdescent : baseEnd_2226110 < baseStart_2226110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226112 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_2226112 : Nat := 118140960795 + 2226112 * 2 ^ 59
def prefixEnd_2226112 : Nat := 4983230072969 + 3 ^ 40 * 2226112 * 2
def baseEnd_2226112 : Nat := 1143065446741699560262303

theorem tailTrace_2226112 : CollatzResearch.WordTrace tailWord_2226112 prefixEnd_2226112 1143065446741699560262303 := by
  unfold tailWord_2226112
  simp only [CollatzResearch.WordTrace]
  refine ⟨40596487455591944253132295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54128649940789259004176393 40596487455591944253132295)
  ·
    refine ⟨60894731183387916379698443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40596487455591944253132295 60894731183387916379698443)
    ·
      refine ⟨91342096775081874569547665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60894731183387916379698443 91342096775081874569547665)
      ·
        refine ⟨68506572581311405927160749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91342096775081874569547665 68506572581311405927160749)
        ·
          refine ⟨25689964717991777222685281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68506572581311405927160749 25689964717991777222685281)
          ·
            refine ⟨19267473538493832917013961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25689964717991777222685281 19267473538493832917013961)
            ·
              refine ⟨14450605153870374687760471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19267473538493832917013961 14450605153870374687760471)
              ·
                refine ⟨21675907730805562031640707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14450605153870374687760471 21675907730805562031640707)
                ·
                  refine ⟨32513861596208343047461061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21675907730805562031640707 32513861596208343047461061)
                  ·
                    refine ⟨6096349049289064321398949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32513861596208343047461061 6096349049289064321398949)
                    ·
                      refine ⟨1143065446741699560262303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6096349049289064321398949 1143065446741699560262303)
                      ·
                        rfl

theorem cell23_2226112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_2226112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226112 prefixEnd_2226112 := by exact prefixLift 2226112
  have htrace : WordTrace (prefixWord ++ tailWord_2226112) baseStart_2226112 baseEnd_2226112 := by
    simpa [prefixWord, tailWord_2226112, baseEnd_2226112] using wordTrace_append hprefix tailTrace_2226112
  have hstable : (prefixWord ++ tailWord_2226112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226112).length < 2 ^ (prefixWord ++ tailWord_2226112).sum := by decide
  have hdescent : baseEnd_2226112 < baseStart_2226112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226122 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_2226122 : Nat := 118140960795 + 2226122 * 2 ^ 59
def prefixEnd_2226122 : Nat := 4983230072969 + 3 ^ 40 * 2226122 * 2
def baseEnd_2226122 : Nat := 127007842394249391237473

theorem tailTrace_2226122 : CollatzResearch.WordTrace tailWord_2226122 prefixEnd_2226122 127007842394249391237473 := by
  unfold tailWord_2226122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298334910286915053532155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54128893094098440142752413 20298334910286915053532155)
  ·
    refine ⟨30447502365430372580298233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20298334910286915053532155 30447502365430372580298233)
    ·
      refine ⟨22835626774072779435223675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30447502365430372580298233 22835626774072779435223675)
      ·
        refine ⟨34253440161109169152835513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22835626774072779435223675 34253440161109169152835513)
        ·
          refine ⟨25690080120831876864626635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34253440161109169152835513 25690080120831876864626635)
          ·
            refine ⟨38535120181247815296939953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25690080120831876864626635 38535120181247815296939953)
            ·
              refine ⟨28901340135935861472704965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38535120181247815296939953 28901340135935861472704965)
              ·
                refine ⟨5419001275487974026132181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28901340135935861472704965 5419001275487974026132181)
                ·
                  refine ⟨127007842394249391237473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5419001275487974026132181 127007842394249391237473)
                  ·
                    rfl

theorem cell23_2226122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_2226122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226122 prefixEnd_2226122 := by exact prefixLift 2226122
  have htrace : WordTrace (prefixWord ++ tailWord_2226122) baseStart_2226122 baseEnd_2226122 := by
    simpa [prefixWord, tailWord_2226122, baseEnd_2226122] using wordTrace_append hprefix tailTrace_2226122
  have hstable : (prefixWord ++ tailWord_2226122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226122).length < 2 ^ (prefixWord ++ tailWord_2226122).sum := by decide
  have hdescent : baseEnd_2226122 < baseStart_2226122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226152 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2226152 : Nat := 118140960795 + 2226152 * 2 ^ 59
def prefixEnd_2226152 : Nat := 4983230072969 + 3 ^ 40 * 2226152 * 2
def baseEnd_2226152 : Nat := 381028661989293134587373

theorem tailTrace_2226152 : CollatzResearch.WordTrace tailWord_2226152 prefixEnd_2226152 381028661989293134587373 := by
  unfold tailWord_2226152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40597216915519487668860355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54129622554025983558480473 40597216915519487668860355)
  ·
    refine ⟨60895825373279231503290533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40597216915519487668860355 60895825373279231503290533)
    ·
      refine ⟨11417967257489855906866975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60895825373279231503290533 11417967257489855906866975)
      ·
        refine ⟨17126950886234783860300463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11417967257489855906866975 17126950886234783860300463)
        ·
          refine ⟨25690426329352175790450695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17126950886234783860300463 25690426329352175790450695)
          ·
            refine ⟨38535639494028263685676043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25690426329352175790450695 38535639494028263685676043)
            ·
              refine ⟨57803459241042395528514065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38535639494028263685676043 57803459241042395528514065)
              ·
                refine ⟨43352594430781796646385549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57803459241042395528514065 43352594430781796646385549)
                ·
                  refine ⟨16257222911543173742394581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43352594430781796646385549 16257222911543173742394581)
                  ·
                    refine ⟨381028661989293134587373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16257222911543173742394581 381028661989293134587373)
                    ·
                      rfl

theorem cell23_2226152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2226152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226152 prefixEnd_2226152 := by exact prefixLift 2226152
  have htrace : WordTrace (prefixWord ++ tailWord_2226152) baseStart_2226152 baseEnd_2226152 := by
    simpa [prefixWord, tailWord_2226152, baseEnd_2226152] using wordTrace_append hprefix tailTrace_2226152
  have hstable : (prefixWord ++ tailWord_2226152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226152).length < 2 ^ (prefixWord ++ tailWord_2226152).sum := by decide
  have hdescent : baseEnd_2226152 < baseStart_2226152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226159 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 7, 2]
def baseStart_2226159 : Nat := 118140960795 + 2226159 * 2 ^ 59
def prefixEnd_2226159 : Nat := 4983230072969 + 3 ^ 40 * 2226159 * 2
def baseEnd_2226159 : Nat := 1143089580332460876374587

theorem tailTrace_2226159 : CollatzResearch.WordTrace tailWord_2226159 prefixEnd_2226159 1143089580332460876374587 := by
  unfold tailWord_2226159
  simp only [CollatzResearch.WordTrace]
  refine ⟨81194689142013615533225531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54129792761342410355483687 81194689142013615533225531)
  ·
    refine ⟨121792033713020423299838297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81194689142013615533225531 121792033713020423299838297)
    ·
      refine ⟨91344025284765317474878723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121792033713020423299838297 91344025284765317474878723)
      ·
        refine ⟨137016037927147976212318085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91344025284765317474878723 137016037927147976212318085)
        ·
          refine ⟨25690507111340245539809641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137016037927147976212318085 25690507111340245539809641)
          ·
            refine ⟨19267880333505184154857231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25690507111340245539809641 19267880333505184154857231)
            ·
              refine ⟨28901820500257776232285847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19267880333505184154857231 28901820500257776232285847)
              ·
                refine ⟨43352730750386664348428771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28901820500257776232285847 43352730750386664348428771)
                ·
                  refine ⟨65029096125579996522643157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43352730750386664348428771 65029096125579996522643157)
                  ·
                    refine ⟨1524119440443281168499449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65029096125579996522643157 1524119440443281168499449)
                    ·
                      refine ⟨1143089580332460876374587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524119440443281168499449 1143089580332460876374587)
                      ·
                        rfl

theorem cell23_2226159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7, 2].length) (baseStart_2226159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226159 prefixEnd_2226159 := by exact prefixLift 2226159
  have htrace : WordTrace (prefixWord ++ tailWord_2226159) baseStart_2226159 baseEnd_2226159 := by
    simpa [prefixWord, tailWord_2226159, baseEnd_2226159] using wordTrace_append hprefix tailTrace_2226159
  have hstable : (prefixWord ++ tailWord_2226159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226159).length < 2 ^ (prefixWord ++ tailWord_2226159).sum := by decide
  have hdescent : baseEnd_2226159 < baseStart_2226159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226229 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 6]
def baseStart_2226229 : Nat := 118140960795 + 2226229 * 2 ^ 59
def prefixEnd_2226229 : Nat := 4983230072969 + 3 ^ 40 * 2226229 * 2
def baseEnd_2226229 : Nat := 127013947108697289166585

theorem tailTrace_2226229 : CollatzResearch.WordTrace tailWord_2226229 prefixEnd_2226229 127013947108697289166585 := by
  unfold tailWord_2226229
  simp only [CollatzResearch.WordTrace]
  refine ⟨81197242251760017488273741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54131494834506678325515827 81197242251760017488273741)
  ·
    refine ⟨30448965844410006558102653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81197242251760017488273741 30448965844410006558102653)
    ·
      refine ⟨11418362191653752459288495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30448965844410006558102653 11418362191653752459288495)
      ·
        refine ⟨17127543287480628688932743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11418362191653752459288495 17127543287480628688932743)
        ·
          refine ⟨25691314931220943033399115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17127543287480628688932743 25691314931220943033399115)
          ·
            refine ⟨38536972396831414550098673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25691314931220943033399115 38536972396831414550098673)
            ·
              refine ⟨28902729297623560912574005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38536972396831414550098673 28902729297623560912574005)
              ·
                refine ⟨2709630871652208835553813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28902729297623560912574005 2709630871652208835553813)
                ·
                  refine ⟨127013947108697289166585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2709630871652208835553813 127013947108697289166585)
                  ·
                    rfl

theorem cell23_2226229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_2226229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226229 prefixEnd_2226229 := by exact prefixLift 2226229
  have htrace : WordTrace (prefixWord ++ tailWord_2226229) baseStart_2226229 baseEnd_2226229 := by
    simpa [prefixWord, tailWord_2226229, baseEnd_2226229] using wordTrace_append hprefix tailTrace_2226229
  have hstable : (prefixWord ++ tailWord_2226229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226229).length < 2 ^ (prefixWord ++ tailWord_2226229).sum := by decide
  have hdescent : baseEnd_2226229 < baseStart_2226229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226246 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_2226246 : Nat := 118140960795 + 2226246 * 2 ^ 59
def prefixEnd_2226246 : Nat := 4983230072969 + 3 ^ 40 * 2226246 * 2
def baseEnd_2226246 : Nat := 127014917016600226220743

theorem tailTrace_2226246 : CollatzResearch.WordTrace tailWord_2226246 prefixEnd_2226246 127014917016600226220743 := by
  unfold tailWord_2226246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537433196646825918488831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54131908195132286261095061 2537433196646825918488831)
  ·
    refine ⟨3806149794970238877733247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2537433196646825918488831 3806149794970238877733247)
    ·
      refine ⟨5709224692455358316599871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3806149794970238877733247 5709224692455358316599871)
      ·
        refine ⟨8563837038683037474899807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709224692455358316599871 8563837038683037474899807)
        ·
          refine ⟨12845755558024556212349711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8563837038683037474899807 12845755558024556212349711)
          ·
            refine ⟨19268633337036834318524567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12845755558024556212349711 19268633337036834318524567)
            ·
              refine ⟨28902950005555251477786851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19268633337036834318524567 28902950005555251477786851)
              ·
                refine ⟨43354425008332877216680277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28902950005555251477786851 43354425008332877216680277)
                ·
                  refine ⟨127014917016600226220743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43354425008332877216680277 127014917016600226220743)
                  ·
                    rfl

theorem cell23_2226246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_2226246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226246 prefixEnd_2226246 := by exact prefixLift 2226246
  have htrace : WordTrace (prefixWord ++ tailWord_2226246) baseStart_2226246 baseEnd_2226246 := by
    simpa [prefixWord, tailWord_2226246, baseEnd_2226246] using wordTrace_append hprefix tailTrace_2226246
  have hstable : (prefixWord ++ tailWord_2226246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226246).length < 2 ^ (prefixWord ++ tailWord_2226246).sum := by decide
  have hdescent : baseEnd_2226246 < baseStart_2226246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226289 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_2226289 : Nat := 118140960795 + 2226289 * 2 ^ 59
def prefixEnd_2226289 : Nat := 4983230072969 + 3 ^ 40 * 2226289 * 2
def baseEnd_2226289 : Nat := 381052110939181789249663

theorem tailTrace_2226289 : CollatzResearch.WordTrace tailWord_2226289 prefixEnd_2226289 381052110939181789249663 := by
  unfold tailWord_2226289
  simp only [CollatzResearch.WordTrace]
  refine ⟨81199430631542647735457921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54132953754361765156971947 81199430631542647735457921)
  ·
    refine ⟨60899572973656985801593441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81199430631542647735457921 60899572973656985801593441)
    ·
      refine ⟨45674679730242739351195081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60899572973656985801593441 45674679730242739351195081)
      ·
        refine ⟨34256009797682054513396311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45674679730242739351195081 34256009797682054513396311)
        ·
          refine ⟨51384014696523081770094467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34256009797682054513396311 51384014696523081770094467)
          ·
            refine ⟨77076022044784622655141701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51384014696523081770094467 77076022044784622655141701)
            ·
              refine ⟨14451754133397116747839069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77076022044784622655141701 14451754133397116747839069)
              ·
                refine ⟨5419407800023918780439651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14451754133397116747839069 5419407800023918780439651)
                ·
                  refine ⟨8129111700035878170659477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5419407800023918780439651 8129111700035878170659477)
                  ·
                    refine ⟨381052110939181789249663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8129111700035878170659477 381052110939181789249663)
                    ·
                      rfl

theorem cell23_2226289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_2226289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226289 prefixEnd_2226289 := by exact prefixLift 2226289
  have htrace : WordTrace (prefixWord ++ tailWord_2226289) baseStart_2226289 baseEnd_2226289 := by
    simpa [prefixWord, tailWord_2226289, baseEnd_2226289] using wordTrace_append hprefix tailTrace_2226289
  have hstable : (prefixWord ++ tailWord_2226289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226289).length < 2 ^ (prefixWord ++ tailWord_2226289).sum := by decide
  have hdescent : baseEnd_2226289 < baseStart_2226289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226313 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 1, 1, 4]
def baseStart_2226313 : Nat := 118140960795 + 2226313 * 2 ^ 59
def prefixEnd_2226313 : Nat := 4983230072969 + 3 ^ 40 * 2226313 * 2
def baseEnd_2226313 : Nat := 1143168656353253273848879

theorem tailTrace_2226313 : CollatzResearch.WordTrace tailWord_2226313 prefixEnd_2226313 1143168656353253273848879 := by
  unfold tailWord_2226313
  simp only [CollatzResearch.WordTrace]
  refine ⟨81200305983455699834331593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54133537322303799889554395 81200305983455699834331593)
  ·
    refine ⟨60900229487591774875748695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81200305983455699834331593 60900229487591774875748695)
    ·
      refine ⟨91350344231387662313623043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60900229487591774875748695 91350344231387662313623043)
      ·
        refine ⟨137025516347081493470434565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91350344231387662313623043 137025516347081493470434565)
        ·
          refine ⟨25692284315077780025706481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137025516347081493470434565 25692284315077780025706481)
          ·
            refine ⟨19269213236308335019279861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25692284315077780025706481 19269213236308335019279861)
            ·
              refine ⟨1806488740903906408057487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19269213236308335019279861 1806488740903906408057487)
              ·
                refine ⟨2709733111355859612086231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806488740903906408057487 2709733111355859612086231)
                ·
                  refine ⟨4064599667033789418129347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709733111355859612086231 4064599667033789418129347)
                  ·
                    refine ⟨6096899500550684127194021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4064599667033789418129347 6096899500550684127194021)
                    ·
                      refine ⟨1143168656353253273848879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6096899500550684127194021 1143168656353253273848879)
                      ·
                        rfl

theorem cell23_2226313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 1, 4].length) (baseStart_2226313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226313 prefixEnd_2226313 := by exact prefixLift 2226313
  have htrace : WordTrace (prefixWord ++ tailWord_2226313) baseStart_2226313 baseEnd_2226313 := by
    simpa [prefixWord, tailWord_2226313, baseEnd_2226313] using wordTrace_append hprefix tailTrace_2226313
  have hstable : (prefixWord ++ tailWord_2226313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226313).length < 2 ^ (prefixWord ++ tailWord_2226313).sum := by decide
  have hdescent : baseEnd_2226313 < baseStart_2226313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226324 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2226324 : Nat := 118140960795 + 2226324 * 2 ^ 59
def prefixEnd_2226324 : Nat := 4983230072969 + 3 ^ 40 * 2226324 * 2
def baseEnd_2226324 : Nat := 1143174304640452730811329

theorem tailTrace_2226324 : CollatzResearch.WordTrace tailWord_2226324 prefixEnd_2226324 1143174304640452730811329 := by
  unfold tailWord_2226324
  simp only [CollatzResearch.WordTrace]
  refine ⟨40600353593207924356491013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54133804790943899141988017 40600353593207924356491013)
  ·
    refine ⟨7612566298726485816842065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40600353593207924356491013 7612566298726485816842065)
    ·
      refine ⟨5709424724044864362631549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7612566298726485816842065 5709424724044864362631549)
      ·
        refine ⟨2141034271516824135986831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5709424724044864362631549 2141034271516824135986831)
        ·
          refine ⟨3211551407275236203980247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141034271516824135986831 3211551407275236203980247)
          ·
            refine ⟨4817327110912854305970371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3211551407275236203980247 4817327110912854305970371)
            ·
              refine ⟨7225990666369281458955557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4817327110912854305970371 7225990666369281458955557)
              ·
                refine ⟨1354873249944240273554167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7225990666369281458955557 1354873249944240273554167)
                ·
                  refine ⟨2032309874916360410331251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354873249944240273554167 2032309874916360410331251)
                  ·
                    refine ⟨3048464812374540615496877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032309874916360410331251 3048464812374540615496877)
                    ·
                      refine ⟨1143174304640452730811329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3048464812374540615496877 1143174304640452730811329)
                      ·
                        rfl

theorem cell23_2226324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2226324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226324 prefixEnd_2226324 := by exact prefixLift 2226324
  have htrace : WordTrace (prefixWord ++ tailWord_2226324) baseStart_2226324 baseEnd_2226324 := by
    simpa [prefixWord, tailWord_2226324, baseEnd_2226324] using wordTrace_append hprefix tailTrace_2226324
  have hstable : (prefixWord ++ tailWord_2226324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226324).length < 2 ^ (prefixWord ++ tailWord_2226324).sum := by decide
  have hdescent : baseEnd_2226324 < baseStart_2226324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226336 : List Nat := [2, 1, 1, 4, 2, 4, 1, 8]
def baseStart_2226336 : Nat := 118140960795 + 2226336 * 2 ^ 59
def prefixEnd_2226336 : Nat := 4983230072969 + 3 ^ 40 * 2226336 * 2
def baseEnd_2226336 : Nat := 42340017274381729031899

theorem tailTrace_2226336 : CollatzResearch.WordTrace tailWord_2226336 prefixEnd_2226336 42340017274381729031899 := by
  unfold tailWord_2226336
  simp only [CollatzResearch.WordTrace]
  refine ⟨40600572431186187381209431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54134096574914916508279241 40600572431186187381209431)
  ·
    refine ⟨60900858646779281071814147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40600572431186187381209431 60900858646779281071814147)
    ·
      refine ⟨91351287970168921607721221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60900858646779281071814147 91351287970168921607721221)
      ·
        refine ⟨17128366494406672801447729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91351287970168921607721221 17128366494406672801447729)
        ·
          refine ⟨12846274870805004601085797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17128366494406672801447729 12846274870805004601085797)
          ·
            refine ⟨2408676538275938362703587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12846274870805004601085797 2408676538275938362703587)
            ·
              refine ⟨3613014807413907544055381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408676538275938362703587 3613014807413907544055381)
              ·
                refine ⟨42340017274381729031899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3613014807413907544055381 42340017274381729031899)
                ·
                  rfl

theorem cell23_2226336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 8].length) (baseStart_2226336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226336 prefixEnd_2226336 := by exact prefixLift 2226336
  have htrace : WordTrace (prefixWord ++ tailWord_2226336) baseStart_2226336 baseEnd_2226336 := by
    simpa [prefixWord, tailWord_2226336, baseEnd_2226336] using wordTrace_append hprefix tailTrace_2226336
  have hstable : (prefixWord ++ tailWord_2226336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226336).length < 2 ^ (prefixWord ++ tailWord_2226336).sum := by decide
  have hdescent : baseEnd_2226336 < baseStart_2226336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226353 : List Nat := [1, 2, 2, 5, 2, 1, 3, 7]
def baseStart_2226353 : Nat := 118140960795 + 2226353 * 2 ^ 59
def prefixEnd_2226353 : Nat := 4983230072969 + 3 ^ 40 * 2226353 * 2
def baseEnd_2226353 : Nat := 42340340577016041383285

theorem tailTrace_2226353 : CollatzResearch.WordTrace tailWord_2226353 prefixEnd_2226353 42340340577016041383285 := by
  unfold tailWord_2226353
  simp only [CollatzResearch.WordTrace]
  refine ⟨81201764903310786665787713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54134509935540524443858475 81201764903310786665787713)
  ·
    refine ⟨60901323677483089999340785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81201764903310786665787713 60901323677483089999340785)
    ·
      refine ⟨45675992758112317499505589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60901323677483089999340785 45675992758112317499505589)
      ·
        refine ⟨4282124321073029765578649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45675992758112317499505589 4282124321073029765578649)
        ·
          refine ⟨3211593240804772324183987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4282124321073029765578649 3211593240804772324183987)
          ·
            refine ⟨4817389861207158486275981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3211593240804772324183987 4817389861207158486275981)
            ·
              refine ⟨1806521197952684432353493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4817389861207158486275981 1806521197952684432353493)
              ·
                refine ⟨42340340577016041383285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1806521197952684432353493 42340340577016041383285)
                ·
                  rfl

theorem cell23_2226353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 7].length) (baseStart_2226353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226353 prefixEnd_2226353 := by exact prefixLift 2226353
  have htrace : WordTrace (prefixWord ++ tailWord_2226353) baseStart_2226353 baseEnd_2226353 := by
    simpa [prefixWord, tailWord_2226353, baseEnd_2226353] using wordTrace_append hprefix tailTrace_2226353
  have hstable : (prefixWord ++ tailWord_2226353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226353).length < 2 ^ (prefixWord ++ tailWord_2226353).sum := by decide
  have hdescent : baseEnd_2226353 < baseStart_2226353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226364 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_2226364 : Nat := 118140960795 + 2226364 * 2 ^ 59
def prefixEnd_2226364 : Nat := 4983230072969 + 3 ^ 40 * 2226364 * 2
def baseEnd_2226364 : Nat := 1143194843866632574311145

theorem tailTrace_2226364 : CollatzResearch.WordTrace tailWord_2226364 prefixEnd_2226364 1143194843866632574311145 := by
  unfold tailWord_2226364
  simp only [CollatzResearch.WordTrace]
  refine ⟨40601083053135467772219073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54134777404180623696292097 40601083053135467772219073)
  ·
    refine ⟨30450812289851600829164305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40601083053135467772219073 30450812289851600829164305)
    ·
      refine ⟨22838109217388700621873229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30450812289851600829164305 22838109217388700621873229)
      ·
        refine ⟨8564290956520762733202461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22838109217388700621873229 8564290956520762733202461)
        ·
          refine ⟨3211609108695286024950923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8564290956520762733202461 3211609108695286024950923)
          ·
            refine ⟨4817413663042929037426385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3211609108695286024950923 4817413663042929037426385)
            ·
              refine ⟨3613060247282196778069789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4817413663042929037426385 3613060247282196778069789)
              ·
                refine ⟨1354897592730823791776171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3613060247282196778069789 1354897592730823791776171)
                ·
                  refine ⟨2032346389096235687664257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354897592730823791776171 2032346389096235687664257)
                  ·
                    refine ⟨1524259791822176765748193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2032346389096235687664257 1524259791822176765748193)
                    ·
                      refine ⟨1143194843866632574311145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524259791822176765748193 1143194843866632574311145)
                      ·
                        rfl

theorem cell23_2226364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_2226364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226364 prefixEnd_2226364 := by exact prefixLift 2226364
  have htrace : WordTrace (prefixWord ++ tailWord_2226364) baseStart_2226364 baseEnd_2226364 := by
    simpa [prefixWord, tailWord_2226364, baseEnd_2226364] using wordTrace_append hprefix tailTrace_2226364
  have hstable : (prefixWord ++ tailWord_2226364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226364).length < 2 ^ (prefixWord ++ tailWord_2226364).sum := by decide
  have hdescent : baseEnd_2226364 < baseStart_2226364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226379 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 4, 6]
def baseStart_2226379 : Nat := 118140960795 + 2226379 * 2 ^ 59
def prefixEnd_2226379 : Nat := 4983230072969 + 3 ^ 40 * 2226379 * 2
def baseEnd_2226379 : Nat := 381067515358816671874525

theorem tailTrace_2226379 : CollatzResearch.WordTrace tailWord_2226379 prefixEnd_2226379 381067515358816671874525 := by
  unfold tailWord_2226379
  simp only [CollatzResearch.WordTrace]
  refine ⟨81202713201216593106234191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54135142134144395404156127 81202713201216593106234191)
  ·
    refine ⟨121804069801824889659351287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81202713201216593106234191 121804069801824889659351287)
    ·
      refine ⟨182706104702737334489026931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121804069801824889659351287 182706104702737334489026931)
      ·
        refine ⟨274059157054106001733540397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182706104702737334489026931 274059157054106001733540397)
        ·
          refine ⟨102772183895289750650077649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274059157054106001733540397 102772183895289750650077649)
          ·
            refine ⟨77079137921467312987558237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102772183895289750650077649 77079137921467312987558237)
            ·
              refine ⟨28904676720550242370334339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77079137921467312987558237 28904676720550242370334339)
              ·
                refine ⟨43357015080825363555501509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28904676720550242370334339 43357015080825363555501509)
                ·
                  refine ⟨8129440327654755666656533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43357015080825363555501509 8129440327654755666656533)
                  ·
                    refine ⟨381067515358816671874525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8129440327654755666656533 381067515358816671874525)
                    ·
                      rfl

theorem cell23_2226379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_2226379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226379 prefixEnd_2226379 := by exact prefixLift 2226379
  have htrace : WordTrace (prefixWord ++ tailWord_2226379) baseStart_2226379 baseEnd_2226379 := by
    simpa [prefixWord, tailWord_2226379, baseEnd_2226379] using wordTrace_append hprefix tailTrace_2226379
  have hstable : (prefixWord ++ tailWord_2226379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226379).length < 2 ^ (prefixWord ++ tailWord_2226379).sum := by decide
  have hdescent : baseEnd_2226379 < baseStart_2226379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226407 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2226407 : Nat := 118140960795 + 2226407 * 2 ^ 59
def prefixEnd_2226407 : Nat := 4983230072969 + 3 ^ 40 * 2226407 * 2
def baseEnd_2226407 : Nat := 1143216923534775906073447

theorem tailTrace_2226407 : CollatzResearch.WordTrace tailWord_2226407 prefixEnd_2226407 1143216923534775906073447 := by
  unfold tailWord_2226407
  simp only [CollatzResearch.WordTrace]
  refine ⟨81203734445115153888253475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54135822963410102592168983 81203734445115153888253475)
  ·
    refine ⟨121805601667672730832380213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81203734445115153888253475 121805601667672730832380213)
    ·
      refine ⟨11419275156344318515535645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121805601667672730832380213 11419275156344318515535645)
      ·
        refine ⟨4282228183629119443325867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11419275156344318515535645 4282228183629119443325867)
        ·
          refine ⟨6423342275443679164988801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282228183629119443325867 6423342275443679164988801)
          ·
            refine ⟨4817506706582759373741601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6423342275443679164988801 4817506706582759373741601)
            ·
              refine ⟨3613130029937069530306201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4817506706582759373741601 3613130029937069530306201)
              ·
                refine ⟨2709847522452802147729651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3613130029937069530306201 2709847522452802147729651)
                ·
                  refine ⟨4064771283679203221594477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709847522452802147729651 4064771283679203221594477)
                  ·
                    refine ⟨1524289231379701208097929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4064771283679203221594477 1524289231379701208097929)
                    ·
                      refine ⟨1143216923534775906073447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524289231379701208097929 1143216923534775906073447)
                      ·
                        rfl

theorem cell23_2226407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2226407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226407 prefixEnd_2226407 := by exact prefixLift 2226407
  have htrace : WordTrace (prefixWord ++ tailWord_2226407) baseStart_2226407 baseEnd_2226407 := by
    simpa [prefixWord, tailWord_2226407, baseEnd_2226407] using wordTrace_append hprefix tailTrace_2226407
  have hstable : (prefixWord ++ tailWord_2226407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226407).length < 2 ^ (prefixWord ++ tailWord_2226407).sum := by decide
  have hdescent : baseEnd_2226407 < baseStart_2226407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226456 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_2226456 : Nat := 118140960795 + 2226456 * 2 ^ 59
def prefixEnd_2226456 : Nat := 4983230072969 + 3 ^ 40 * 2226456 * 2
def baseEnd_2226456 : Nat := 381080694695615404786907

theorem tailTrace_2226456 : CollatzResearch.WordTrace tailWord_2226456 prefixEnd_2226456 381080694695615404786907 := by
  unfold tailWord_2226456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40602760810968817628393611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54137014414625090171191481 40602760810968817628393611)
  ·
    refine ⟨60904141216453226442590417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40602760810968817628393611 60904141216453226442590417)
    ·
      refine ⟨45678105912339919831942813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60904141216453226442590417 45678105912339919831942813)
      ·
        refine ⟨17129289717127469936978555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45678105912339919831942813 17129289717127469936978555)
        ·
          refine ⟨25693934575691204905467833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17129289717127469936978555 25693934575691204905467833)
          ·
            refine ⟨19270450931768403679100875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25693934575691204905467833 19270450931768403679100875)
            ·
              refine ⟨28905676397652605518651313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19270450931768403679100875 28905676397652605518651313)
              ·
                refine ⟨21679257298239454138988485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28905676397652605518651313 21679257298239454138988485)
                ·
                  refine ⟨4064860743419897651060341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21679257298239454138988485 4064860743419897651060341)
                  ·
                    refine ⟨381080694695615404786907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4064860743419897651060341 381080694695615404786907)
                    ·
                      rfl

theorem cell23_2226456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_2226456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226456 prefixEnd_2226456 := by exact prefixLift 2226456
  have htrace : WordTrace (prefixWord ++ tailWord_2226456) baseStart_2226456 baseEnd_2226456 := by
    simpa [prefixWord, tailWord_2226456, baseEnd_2226456] using wordTrace_append hprefix tailTrace_2226456
  have hstable : (prefixWord ++ tailWord_2226456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226456).length < 2 ^ (prefixWord ++ tailWord_2226456).sum := by decide
  have hdescent : baseEnd_2226456 < baseStart_2226456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226476 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_2226476 : Nat := 118140960795 + 2226476 * 2 ^ 59
def prefixEnd_2226476 : Nat := 4983230072969 + 3 ^ 40 * 2226476 * 2
def baseEnd_2226476 : Nat := 1143252353699936136110629

theorem tailTrace_2226476 : CollatzResearch.WordTrace tailWord_2226476 prefixEnd_2226476 1143252353699936136110629 := by
  unfold tailWord_2226476
  simp only [CollatzResearch.WordTrace]
  refine ⟨40603125540932589336257641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54137500721243452448343521 40603125540932589336257641)
  ·
    refine ⟨30452344155699442002193231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40603125540932589336257641 30452344155699442002193231)
    ·
      refine ⟨45678516233549163003289847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30452344155699442002193231 45678516233549163003289847)
      ·
        refine ⟨68517774350323744504934771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45678516233549163003289847 68517774350323744504934771)
        ·
          refine ⟨102776661525485616757402157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68517774350323744504934771 102776661525485616757402157)
          ·
            refine ⟨38541248072057106284025809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102776661525485616757402157 38541248072057106284025809)
            ·
              refine ⟨28905936054042829713019357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38541248072057106284025809 28905936054042829713019357)
              ·
                refine ⟨10839726020266061142382259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28905936054042829713019357 10839726020266061142382259)
                ·
                  refine ⟨16259589030399091713573389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10839726020266061142382259 16259589030399091713573389)
                  ·
                    refine ⟨6097345886399659392590021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16259589030399091713573389 6097345886399659392590021)
                    ·
                      refine ⟨1143252353699936136110629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6097345886399659392590021 1143252353699936136110629)
                      ·
                        rfl

theorem cell23_2226476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_2226476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226476 prefixEnd_2226476 := by exact prefixLift 2226476
  have htrace : WordTrace (prefixWord ++ tailWord_2226476) baseStart_2226476 baseEnd_2226476 := by
    simpa [prefixWord, tailWord_2226476, baseEnd_2226476] using wordTrace_append hprefix tailTrace_2226476
  have hstable : (prefixWord ++ tailWord_2226476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226476).length < 2 ^ (prefixWord ++ tailWord_2226476).sum := by decide
  have hdescent : baseEnd_2226476 < baseStart_2226476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226503 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 3, 4]
def baseStart_2226503 : Nat := 118140960795 + 2226503 * 2 ^ 59
def prefixEnd_2226503 : Nat := 4983230072969 + 3 ^ 40 * 2226503 * 2
def baseEnd_2226503 : Nat := 381088739225869176824335

theorem tailTrace_2226503 : CollatzResearch.WordTrace tailWord_2226503 prefixEnd_2226503 381088739225869176824335 := by
  unfold tailWord_2226503
  simp only [CollatzResearch.WordTrace]
  refine ⟨81207235852767362283748163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54138157235178241522498775 81207235852767362283748163)
  ·
    refine ⟨121810853779151043425622245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81207235852767362283748163 121810853779151043425622245)
    ·
      refine ⟨22839535083590820642304171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121810853779151043425622245 22839535083590820642304171)
      ·
        refine ⟨34259302625386230963456257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22839535083590820642304171 34259302625386230963456257)
        ·
          refine ⟨25694476969039673222592193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34259302625386230963456257 25694476969039673222592193)
          ·
            refine ⟨19270857726779754916944145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25694476969039673222592193 19270857726779754916944145)
            ·
              refine ⟨14453143295084816187708109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19270857726779754916944145 14453143295084816187708109)
              ·
                refine ⟨5419928735656806070390541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14453143295084816187708109 5419928735656806070390541)
                ·
                  refine ⟨2032473275871302276396453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5419928735656806070390541 2032473275871302276396453)
                  ·
                    refine ⟨381088739225869176824335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2032473275871302276396453 381088739225869176824335)
                    ·
                      rfl

theorem cell23_2226503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_2226503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226503 prefixEnd_2226503 := by exact prefixLift 2226503
  have htrace : WordTrace (prefixWord ++ tailWord_2226503) baseStart_2226503 baseEnd_2226503 := by
    simpa [prefixWord, tailWord_2226503, baseEnd_2226503] using wordTrace_append hprefix tailTrace_2226503
  have hstable : (prefixWord ++ tailWord_2226503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226503).length < 2 ^ (prefixWord ++ tailWord_2226503).sum := by decide
  have hdescent : baseEnd_2226503 < baseStart_2226503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226506 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2226506 : Nat := 118140960795 + 2226506 * 2 ^ 59
def prefixEnd_2226506 : Nat := 4983230072969 + 3 ^ 40 * 2226506 * 2
def baseEnd_2226506 : Nat := 1143267758119571018735491

theorem tailTrace_2226506 : CollatzResearch.WordTrace tailWord_2226506 prefixEnd_2226506 1143267758119571018735491 := by
  unfold tailWord_2226506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20301836317939123449026843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54138230181170995864071581 20301836317939123449026843)
  ·
    refine ⟨30452754476908685173540265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20301836317939123449026843 30452754476908685173540265)
    ·
      refine ⟨22839565857681513880155199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30452754476908685173540265 22839565857681513880155199)
      ·
        refine ⟨34259348786522270820232799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22839565857681513880155199 34259348786522270820232799)
        ·
          refine ⟨51389023179783406230349199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34259348786522270820232799 51389023179783406230349199)
          ·
            refine ⟨77083534769675109345523799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51389023179783406230349199 77083534769675109345523799)
            ·
              refine ⟨115625302154512664018285699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77083534769675109345523799 115625302154512664018285699)
              ·
                refine ⟨173437953231768996027428549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115625302154512664018285699 173437953231768996027428549)
                ·
                  refine ⟨32519616230956686755142853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173437953231768996027428549 32519616230956686755142853)
                  ·
                    refine ⟨6097428043304378766589285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32519616230956686755142853 6097428043304378766589285)
                    ·
                      refine ⟨1143267758119571018735491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6097428043304378766589285 1143267758119571018735491)
                      ·
                        rfl

theorem cell23_2226506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2226506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226506 prefixEnd_2226506 := by exact prefixLift 2226506
  have htrace : WordTrace (prefixWord ++ tailWord_2226506) baseStart_2226506 baseEnd_2226506 := by
    simpa [prefixWord, tailWord_2226506, baseEnd_2226506] using wordTrace_append hprefix tailTrace_2226506
  have hstable : (prefixWord ++ tailWord_2226506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226506).length < 2 ^ (prefixWord ++ tailWord_2226506).sum := by decide
  have hdescent : baseEnd_2226506 < baseStart_2226506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226524 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2226524 : Nat := 118140960795 + 2226524 * 2 ^ 59
def prefixEnd_2226524 : Nat := 4983230072969 + 3 ^ 40 * 2226524 * 2
def baseEnd_2226524 : Nat := 381092333590450649436803

theorem tailTrace_2226524 : CollatzResearch.WordTrace tailWord_2226524 prefixEnd_2226524 381092333590450649436803 := by
  unfold tailWord_2226524
  simp only [CollatzResearch.WordTrace]
  refine ⟨40604000892845641435131313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54138667857127521913508417 40604000892845641435131313)
  ·
    refine ⟨30453000669634231076348485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40604000892845641435131313 30453000669634231076348485)
    ·
      refine ⟨5709937625556418326815341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30453000669634231076348485 5709937625556418326815341)
      ·
        refine ⟨2141226609583656872555753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5709937625556418326815341 2141226609583656872555753)
        ·
          refine ⟨1605919957187742654416815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2141226609583656872555753 1605919957187742654416815)
          ·
            refine ⟨2408879935781613981625223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605919957187742654416815 2408879935781613981625223)
            ·
              refine ⟨3613319903672420972437835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408879935781613981625223 3613319903672420972437835)
              ·
                refine ⟨5419979855508631458656753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613319903672420972437835 5419979855508631458656753)
                ·
                  refine ⟨4064984891631473593992565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5419979855508631458656753 4064984891631473593992565)
                  ·
                    refine ⟨381092333590450649436803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4064984891631473593992565 381092333590450649436803)
                    ·
                      rfl

theorem cell23_2226524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2226524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226524 prefixEnd_2226524 := by exact prefixLift 2226524
  have htrace : WordTrace (prefixWord ++ tailWord_2226524) baseStart_2226524 baseEnd_2226524 := by
    simpa [prefixWord, tailWord_2226524, baseEnd_2226524] using wordTrace_append hprefix tailTrace_2226524
  have hstable : (prefixWord ++ tailWord_2226524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226524).length < 2 ^ (prefixWord ++ tailWord_2226524).sum := by decide
  have hdescent : baseEnd_2226524 < baseStart_2226524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226530 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2226530 : Nat := 118140960795 + 2226530 * 2 ^ 59
def prefixEnd_2226530 : Nat := 4983230072969 + 3 ^ 40 * 2226530 * 2
def baseEnd_2226530 : Nat := 1143280081655278924835381

theorem tailTrace_2226530 : CollatzResearch.WordTrace tailWord_2226530 prefixEnd_2226530 1143280081655278924835381 := by
  unfold tailWord_2226530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20302055155917386473745261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54138813749113030596654029 20302055155917386473745261)
  ·
    refine ⟨7613270683469019927654473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20302055155917386473745261 7613270683469019927654473)
    ·
      refine ⟨5709953012601764945740855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7613270683469019927654473 5709953012601764945740855)
      ·
        refine ⟨8564929518902647418611283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709953012601764945740855 8564929518902647418611283)
        ·
          refine ⟨12847394278353971127916925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564929518902647418611283 12847394278353971127916925)
          ·
            refine ⟨4817772854382739172968847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12847394278353971127916925 4817772854382739172968847)
            ·
              refine ⟨7226659281574108759453271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4817772854382739172968847 7226659281574108759453271)
              ·
                refine ⟨10839988922361163139179907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7226659281574108759453271 10839988922361163139179907)
                ·
                  refine ⟨16259983383541744708769861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10839988922361163139179907 16259983383541744708769861)
                  ·
                    refine ⟨3048746884414077132894349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16259983383541744708769861 3048746884414077132894349)
                    ·
                      refine ⟨1143280081655278924835381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3048746884414077132894349 1143280081655278924835381)
                      ·
                        rfl

theorem cell23_2226530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2226530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226530 prefixEnd_2226530 := by exact prefixLift 2226530
  have htrace : WordTrace (prefixWord ++ tailWord_2226530) baseStart_2226530 baseEnd_2226530 := by
    simpa [prefixWord, tailWord_2226530, baseEnd_2226530] using wordTrace_append hprefix tailTrace_2226530
  have hstable : (prefixWord ++ tailWord_2226530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226530).length < 2 ^ (prefixWord ++ tailWord_2226530).sum := by decide
  have hdescent : baseEnd_2226530 < baseStart_2226530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226556 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2226556 : Nat := 118140960795 + 2226556 * 2 ^ 59
def prefixEnd_2226556 : Nat := 4983230072969 + 3 ^ 40 * 2226556 * 2
def baseEnd_2226556 : Nat := 1143293432152295823110261

theorem tailTrace_2226556 : CollatzResearch.WordTrace tailWord_2226556 prefixEnd_2226556 1143293432152295823110261 := by
  unfold tailWord_2226556
  simp only [CollatzResearch.WordTrace]
  refine ⟨40604584460787676167713761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54139445947716901556951681 40604584460787676167713761)
  ·
    refine ⟨30453438345590757125785321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40604584460787676167713761 30453438345590757125785321)
    ·
      refine ⟨22840078759193067844338991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30453438345590757125785321 22840078759193067844338991)
      ·
        refine ⟨34260118138789601766508487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22840078759193067844338991 34260118138789601766508487)
        ·
          refine ⟨51390177208184402649762731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34260118138789601766508487 51390177208184402649762731)
          ·
            refine ⟨77085265812276603974644097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51390177208184402649762731 77085265812276603974644097)
            ·
              refine ⟨57813949359207452980983073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77085265812276603974644097 57813949359207452980983073)
              ·
                refine ⟨43360462019405589735737305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57813949359207452980983073 43360462019405589735737305)
                ·
                  refine ⟨32520346514554192301802979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43360462019405589735737305 32520346514554192301802979)
                  ·
                    refine ⟨48780519771831288452704469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32520346514554192301802979 48780519771831288452704469)
                    ·
                      refine ⟨1143293432152295823110261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48780519771831288452704469 1143293432152295823110261)
                      ·
                        rfl

theorem cell23_2226556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2226556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226556 prefixEnd_2226556 := by exact prefixLift 2226556
  have htrace : WordTrace (prefixWord ++ tailWord_2226556) baseStart_2226556 baseEnd_2226556 := by
    simpa [prefixWord, tailWord_2226556, baseEnd_2226556] using wordTrace_append hprefix tailTrace_2226556
  have hstable : (prefixWord ++ tailWord_2226556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226556).length < 2 ^ (prefixWord ++ tailWord_2226556).sum := by decide
  have hdescent : baseEnd_2226556 < baseStart_2226556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226576 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_2226576 : Nat := 118140960795 + 2226576 * 2 ^ 59
def prefixEnd_2226576 : Nat := 4983230072969 + 3 ^ 40 * 2226576 * 2
def baseEnd_2226576 : Nat := 381101233921795248286723

theorem tailTrace_2226576 : CollatzResearch.WordTrace tailWord_2226576 prefixEnd_2226576 381101233921795248286723 := by
  unfold tailWord_2226576
  simp only [CollatzResearch.WordTrace]
  refine ⟨40604949190751447875577791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54139932254335263834103721 40604949190751447875577791)
  ·
    refine ⟨60907423786127171813366687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40604949190751447875577791 60907423786127171813366687)
    ·
      refine ⟨91361135679190757720050031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60907423786127171813366687 91361135679190757720050031)
      ·
        refine ⟨137041703518786136580075047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91361135679190757720050031 137041703518786136580075047)
        ·
          refine ⟨205562555278179204870112571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137041703518786136580075047 205562555278179204870112571)
          ·
            refine ⟨308343832917268807305168857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205562555278179204870112571 308343832917268807305168857)
            ·
              refine ⟨231257874687951605478876643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308343832917268807305168857 231257874687951605478876643)
              ·
                refine ⟨346886812031927408218314965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231257874687951605478876643 346886812031927408218314965)
                ·
                  refine ⟨8130159656998298630116757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 346886812031927408218314965 8130159656998298630116757)
                  ·
                    refine ⟨381101233921795248286723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8130159656998298630116757 381101233921795248286723)
                    ·
                      rfl

theorem cell23_2226576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_2226576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226576 prefixEnd_2226576 := by exact prefixLift 2226576
  have htrace : WordTrace (prefixWord ++ tailWord_2226576) baseStart_2226576 baseEnd_2226576 := by
    simpa [prefixWord, tailWord_2226576, baseEnd_2226576] using wordTrace_append hprefix tailTrace_2226576
  have hstable : (prefixWord ++ tailWord_2226576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226576).length < 2 ^ (prefixWord ++ tailWord_2226576).sum := by decide
  have hdescent : baseEnd_2226576 < baseStart_2226576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226583 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2226583 : Nat := 118140960795 + 2226583 * 2 ^ 59
def prefixEnd_2226583 : Nat := 4983230072969 + 3 ^ 40 * 2226583 * 2
def baseEnd_2226583 : Nat := 1143307296129967217472637

theorem tailTrace_2226583 : CollatzResearch.WordTrace tailWord_2226583 prefixEnd_2226583 1143307296129967217472637 := by
  unfold tailWord_2226583
  simp only [CollatzResearch.WordTrace]
  refine ⟨81210153692477535946660403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54140102461651690631106935 81210153692477535946660403)
  ·
    refine ⟨121815230538716303919990605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81210153692477535946660403 121815230538716303919990605)
    ·
      refine ⟨45680711452018613969996477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121815230538716303919990605 45680711452018613969996477)
      ·
        refine ⟨17130266794506980238748679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45680711452018613969996477 17130266794506980238748679)
        ·
          refine ⟨25695400191760470358123019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17130266794506980238748679 25695400191760470358123019)
          ·
            refine ⟨38543100287640705537184529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25695400191760470358123019 38543100287640705537184529)
            ·
              refine ⟨28907325215730529152888397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38543100287640705537184529 28907325215730529152888397)
              ·
                refine ⟨10840246955898948432333149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28907325215730529152888397 10840246955898948432333149)
                ·
                  refine ⟨4065092608462105662124931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10840246955898948432333149 4065092608462105662124931)
                  ·
                    refine ⟨6097638912693158493187397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4065092608462105662124931 6097638912693158493187397)
                    ·
                      refine ⟨1143307296129967217472637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6097638912693158493187397 1143307296129967217472637)
                      ·
                        rfl

theorem cell23_2226583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2226583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226583 prefixEnd_2226583 := by exact prefixLift 2226583
  have htrace : WordTrace (prefixWord ++ tailWord_2226583) baseStart_2226583 baseEnd_2226583 := by
    simpa [prefixWord, tailWord_2226583, baseEnd_2226583] using wordTrace_append hprefix tailTrace_2226583
  have hstable : (prefixWord ++ tailWord_2226583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226583).length < 2 ^ (prefixWord ++ tailWord_2226583).sum := by decide
  have hdescent : baseEnd_2226583 < baseStart_2226583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226610 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_2226610 : Nat := 118140960795 + 2226610 * 2 ^ 59
def prefixEnd_2226610 : Nat := 4983230072969 + 3 ^ 40 * 2226610 * 2
def baseEnd_2226610 : Nat := 381107053369212870611671

theorem tailTrace_2226610 : CollatzResearch.WordTrace tailWord_2226610 prefixEnd_2226610 381107053369212870611671 := by
  unfold tailWord_2226610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20302784615844929889473321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54140758975586479705262189 20302784615844929889473321)
  ·
    refine ⟨15227088461883697417104991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20302784615844929889473321 15227088461883697417104991)
    ·
      refine ⟨22840632692825546125657487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15227088461883697417104991 22840632692825546125657487)
      ·
        refine ⟨34260949039238319188486231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22840632692825546125657487 34260949039238319188486231)
        ·
          refine ⟨51391423558857478782729347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34260949039238319188486231 51391423558857478782729347)
          ·
            refine ⟨77087135338286218174094021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51391423558857478782729347 77087135338286218174094021)
            ·
              refine ⟨14453837875928665907642629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77087135338286218174094021 14453837875928665907642629)
              ·
                refine ⟨2710094601736624857682993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14453837875928665907642629 2710094601736624857682993)
                ·
                  refine ⟨2032570951302468643262245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710094601736624857682993 2032570951302468643262245)
                  ·
                    refine ⟨381107053369212870611671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2032570951302468643262245 381107053369212870611671)
                    ·
                      rfl

theorem cell23_2226610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_2226610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226610 prefixEnd_2226610 := by exact prefixLift 2226610
  have htrace : WordTrace (prefixWord ++ tailWord_2226610) baseStart_2226610 baseEnd_2226610 := by
    simpa [prefixWord, tailWord_2226610, baseEnd_2226610] using wordTrace_append hprefix tailTrace_2226610
  have hstable : (prefixWord ++ tailWord_2226610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226610).length < 2 ^ (prefixWord ++ tailWord_2226610).sum := by decide
  have hdescent : baseEnd_2226610 < baseStart_2226610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226620 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2226620 : Nat := 118140960795 + 2226620 * 2 ^ 59
def prefixEnd_2226620 : Nat := 4983230072969 + 3 ^ 40 * 2226620 * 2
def baseEnd_2226620 : Nat := 1143326294914183572709967

theorem tailTrace_2226620 : CollatzResearch.WordTrace tailWord_2226620 prefixEnd_2226620 1143326294914183572709967 := by
  unfold tailWord_2226620
  simp only [CollatzResearch.WordTrace]
  refine ⟨40605751596671745632878657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54141002128895660843838209 40605751596671745632878657)
  ·
    refine ⟨30454313697503809224658993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40605751596671745632878657 30454313697503809224658993)
    ·
      refine ⟨22840735273127856918494245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30454313697503809224658993 22840735273127856918494245)
      ·
        refine ⟨4282637863711473172217671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22840735273127856918494245 4282637863711473172217671)
        ·
          refine ⟨6423956795567209758326507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282637863711473172217671 6423956795567209758326507)
          ·
            refine ⟨9635935193350814637489761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423956795567209758326507 9635935193350814637489761)
            ·
              refine ⟨7226951395013110978117321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9635935193350814637489761 7226951395013110978117321)
              ·
                refine ⟨5420213546259833233587991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7226951395013110978117321 5420213546259833233587991)
                ·
                  refine ⟨8130320319389749850381987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420213546259833233587991 8130320319389749850381987)
                  ·
                    refine ⟨12195480479084624775572981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8130320319389749850381987 12195480479084624775572981)
                    ·
                      refine ⟨1143326294914183572709967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12195480479084624775572981 1143326294914183572709967)
                      ·
                        rfl

theorem cell23_2226620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2226620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226620 prefixEnd_2226620 := by exact prefixLift 2226620
  have htrace : WordTrace (prefixWord ++ tailWord_2226620) baseStart_2226620 baseEnd_2226620 := by
    simpa [prefixWord, tailWord_2226620, baseEnd_2226620] using wordTrace_append hprefix tailTrace_2226620
  have hstable : (prefixWord ++ tailWord_2226620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226620).length < 2 ^ (prefixWord ++ tailWord_2226620).sum := by decide
  have hdescent : baseEnd_2226620 < baseStart_2226620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226650 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_2226650 : Nat := 118140960795 + 2226650 * 2 ^ 59
def prefixEnd_2226650 : Nat := 4983230072969 + 3 ^ 40 * 2226650 * 2
def baseEnd_2226650 : Nat := 1143341699333818455334829

theorem tailTrace_2226650 : CollatzResearch.WordTrace tailWord_2226650 prefixEnd_2226650 1143341699333818455334829 := by
  unfold tailWord_2226650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303149345808701597337351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54141731588823204259566269 20303149345808701597337351)
  ·
    refine ⟨30454724018713052396006027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20303149345808701597337351 30454724018713052396006027)
    ·
      refine ⟨45682086028069578594009041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30454724018713052396006027 45682086028069578594009041)
      ·
        refine ⟨34261564521052183945506781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45682086028069578594009041 34261564521052183945506781)
        ·
          refine ⟨12848086695394568979565043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34261564521052183945506781 12848086695394568979565043)
          ·
            refine ⟨19272130043091853469347565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12848086695394568979565043 19272130043091853469347565)
            ·
              refine ⟨7227048766159445051005337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19272130043091853469347565 7227048766159445051005337)
              ·
                refine ⟨5420286574619583788254003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7227048766159445051005337 5420286574619583788254003)
                ·
                  refine ⟨8130429861929375682381005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420286574619583788254003 8130429861929375682381005)
                  ·
                    refine ⟨3048911198223515880892877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8130429861929375682381005 3048911198223515880892877)
                    ·
                      refine ⟨1143341699333818455334829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3048911198223515880892877 1143341699333818455334829)
                      ·
                        rfl

theorem cell23_2226650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_2226650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226650 prefixEnd_2226650 := by exact prefixLift 2226650
  have htrace : WordTrace (prefixWord ++ tailWord_2226650) baseStart_2226650 baseEnd_2226650 := by
    simpa [prefixWord, tailWord_2226650, baseEnd_2226650] using wordTrace_append hprefix tailTrace_2226650
  have hstable : (prefixWord ++ tailWord_2226650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226650).length < 2 ^ (prefixWord ++ tailWord_2226650).sum := by decide
  have hdescent : baseEnd_2226650 < baseStart_2226650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226667 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 3]
def baseStart_2226667 : Nat := 118140960795 + 2226667 * 2 ^ 59
def prefixEnd_2226667 : Nat := 4983230072969 + 3 ^ 40 * 2226667 * 2
def baseEnd_2226667 : Nat := 1143350428504944888822251

theorem tailTrace_2226667 : CollatzResearch.WordTrace tailWord_2226667 prefixEnd_2226667 1143350428504944888822251 := by
  unfold tailWord_2226667
  simp only [CollatzResearch.WordTrace]
  refine ⟨81213217424173218292718255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54142144949448812195145503 81213217424173218292718255)
  ·
    refine ⟨121819826136259827439077383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81213217424173218292718255 121819826136259827439077383)
    ·
      refine ⟨182729739204389741158616075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121819826136259827439077383 182729739204389741158616075)
      ·
        refine ⟨274094608806584611737924113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182729739204389741158616075 274094608806584611737924113)
        ·
          refine ⟨205570956604938458803443085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274094608806584611737924113 205570956604938458803443085)
          ·
            refine ⟨77089108726851922051291157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205570956604938458803443085 77089108726851922051291157)
            ·
              refine ⟨3613551971571183846154273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77089108726851922051291157 3613551971571183846154273)
              ·
                refine ⟨2710163978678387884615705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3613551971571183846154273 2710163978678387884615705)
                ·
                  refine ⟨2032622984008790913461779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710163978678387884615705 2032622984008790913461779)
                  ·
                    refine ⟨3048934476013186370192669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032622984008790913461779 3048934476013186370192669)
                    ·
                      refine ⟨1143350428504944888822251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3048934476013186370192669 1143350428504944888822251)
                      ·
                        rfl

theorem cell23_2226667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 3].length) (baseStart_2226667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226667 prefixEnd_2226667 := by exact prefixLift 2226667
  have htrace : WordTrace (prefixWord ++ tailWord_2226667) baseStart_2226667 baseEnd_2226667 := by
    simpa [prefixWord, tailWord_2226667, baseEnd_2226667] using wordTrace_append hprefix tailTrace_2226667
  have hstable : (prefixWord ++ tailWord_2226667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226667).length < 2 ^ (prefixWord ++ tailWord_2226667).sum := by decide
  have hdescent : baseEnd_2226667 < baseStart_2226667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226673 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_2226673 : Nat := 118140960795 + 2226673 * 2 ^ 59
def prefixEnd_2226673 : Nat := 4983230072969 + 3 ^ 40 * 2226673 * 2
def baseEnd_2226673 : Nat := 1143353509388871865347223

theorem tailTrace_2226673 : CollatzResearch.WordTrace tailWord_2226673 prefixEnd_2226673 1143353509388871865347223 := by
  unfold tailWord_2226673
  simp only [CollatzResearch.WordTrace]
  refine ⟨81213436262151481317436673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54142290841434320878291115 81213436262151481317436673)
  ·
    refine ⟨60910077196613610988077505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81213436262151481317436673 60910077196613610988077505)
    ·
      refine ⟨45682557897460208241058129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60910077196613610988077505 45682557897460208241058129)
      ·
        refine ⟨34261918423095156180793597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45682557897460208241058129 34261918423095156180793597)
        ·
          refine ⟨12848219408660683567797599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34261918423095156180793597 12848219408660683567797599)
          ·
            refine ⟨19272329112991025351696399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12848219408660683567797599 19272329112991025351696399)
            ·
              refine ⟨28908493669486538027544599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19272329112991025351696399 28908493669486538027544599)
              ·
                refine ⟨43362740504229807041316899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28908493669486538027544599 43362740504229807041316899)
                ·
                  refine ⟨65044110756344710561975349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43362740504229807041316899 65044110756344710561975349)
                  ·
                    refine ⟨6097885383407316615185189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65044110756344710561975349 6097885383407316615185189)
                    ·
                      refine ⟨1143353509388871865347223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6097885383407316615185189 1143353509388871865347223)
                      ·
                        rfl

theorem cell23_2226673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_2226673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226673 prefixEnd_2226673 := by exact prefixLift 2226673
  have htrace : WordTrace (prefixWord ++ tailWord_2226673) baseStart_2226673 baseEnd_2226673 := by
    simpa [prefixWord, tailWord_2226673, baseEnd_2226673] using wordTrace_append hprefix tailTrace_2226673
  have hstable : (prefixWord ++ tailWord_2226673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226673).length < 2 ^ (prefixWord ++ tailWord_2226673).sum := by decide
  have hdescent : baseEnd_2226673 < baseStart_2226673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226693 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_2226693 : Nat := 118140960795 + 2226693 * 2 ^ 59
def prefixEnd_2226693 : Nat := 4983230072969 + 3 ^ 40 * 2226693 * 2
def baseEnd_2226693 : Nat := 1143363779001961787097131

theorem tailTrace_2226693 : CollatzResearch.WordTrace tailWord_2226693 prefixEnd_2226693 1143363779001961787097131 := by
  unfold tailWord_2226693
  simp only [CollatzResearch.WordTrace]
  refine ⟨81214165722079024733164733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54142777148052683155443155 81214165722079024733164733)
  ·
    refine ⟨30455312145779634274936775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81214165722079024733164733 30455312145779634274936775)
    ·
      refine ⟨45682968218669451412405163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30455312145779634274936775 45682968218669451412405163)
      ·
        refine ⟨68524452328004177118607745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45682968218669451412405163 68524452328004177118607745)
        ·
          refine ⟨51393339246003132838955809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68524452328004177118607745 51393339246003132838955809)
          ·
            refine ⟨38545004434502349629216857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51393339246003132838955809 38545004434502349629216857)
            ·
              refine ⟨28908753325876762221912643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38545004434502349629216857 28908753325876762221912643)
              ·
                refine ⟨43363129988815143332868965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28908753325876762221912643 43363129988815143332868965)
                ·
                  refine ⟨8130586872902839374912931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43363129988815143332868965 8130586872902839374912931)
                  ·
                    refine ⟨12195880309354259062369397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8130586872902839374912931 12195880309354259062369397)
                    ·
                      refine ⟨1143363779001961787097131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12195880309354259062369397 1143363779001961787097131)
                      ·
                        rfl

theorem cell23_2226693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_2226693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226693 prefixEnd_2226693 := by exact prefixLift 2226693
  have htrace : WordTrace (prefixWord ++ tailWord_2226693) baseStart_2226693 baseEnd_2226693 := by
    simpa [prefixWord, tailWord_2226693, baseEnd_2226693] using wordTrace_append hprefix tailTrace_2226693
  have hstable : (prefixWord ++ tailWord_2226693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226693).length < 2 ^ (prefixWord ++ tailWord_2226693).sum := by decide
  have hdescent : baseEnd_2226693 < baseStart_2226693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226703 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_2226703 : Nat := 118140960795 + 2226703 * 2 ^ 59
def prefixEnd_2226703 : Nat := 4983230072969 + 3 ^ 40 * 2226703 * 2
def baseEnd_2226703 : Nat := 1143368913808506747972085

theorem tailTrace_2226703 : CollatzResearch.WordTrace tailWord_2226703 prefixEnd_2226703 1143368913808506747972085 := by
  unfold tailWord_2226703
  simp only [CollatzResearch.WordTrace]
  refine ⟨81214530452042796441028763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54143020301361864294019175 81214530452042796441028763)
  ·
    refine ⟨121821795678064194661543145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81214530452042796441028763 121821795678064194661543145)
    ·
      refine ⟨91366346758548145996157359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121821795678064194661543145 91366346758548145996157359)
      ·
        refine ⟨137049520137822218994236039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91366346758548145996157359 137049520137822218994236039)
        ·
          refine ⟨205574280206733328491354059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137049520137822218994236039 205574280206733328491354059)
          ·
            refine ⟨308361420310099992737031089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205574280206733328491354059 308361420310099992737031089)
            ·
              refine ⟨231271065232574994552773317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308361420310099992737031089 231271065232574994552773317)
              ·
                refine ⟨43363324731107811478644997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231271065232574994552773317 43363324731107811478644997)
                ·
                  refine ⟨8130623387082714652245937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43363324731107811478644997 8130623387082714652245937)
                  ·
                    refine ⟨6097967540312035989184453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8130623387082714652245937 6097967540312035989184453)
                    ·
                      refine ⟨1143368913808506747972085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6097967540312035989184453 1143368913808506747972085)
                      ·
                        rfl

theorem cell23_2226703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_2226703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226703 prefixEnd_2226703 := by exact prefixLift 2226703
  have htrace : WordTrace (prefixWord ++ tailWord_2226703) baseStart_2226703 baseEnd_2226703 := by
    simpa [prefixWord, tailWord_2226703, baseEnd_2226703] using wordTrace_append hprefix tailTrace_2226703
  have hstable : (prefixWord ++ tailWord_2226703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226703).length < 2 ^ (prefixWord ++ tailWord_2226703).sum := by decide
  have hdescent : baseEnd_2226703 < baseStart_2226703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226707 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 4, 2, 2]
def baseStart_2226707 : Nat := 118140960795 + 2226707 * 2 ^ 59
def prefixEnd_2226707 : Nat := 4983230072969 + 3 ^ 40 * 2226707 * 2
def baseEnd_2226707 : Nat := 1143370967731124732322067

theorem tailTrace_2226707 : CollatzResearch.WordTrace tailWord_2226707 prefixEnd_2226707 1143370967731124732322067 := by
  unfold tailWord_2226707
  simp only [CollatzResearch.WordTrace]
  refine ⟨81214676344028305124174375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54143117562685536749449583 81214676344028305124174375)
  ·
    refine ⟨121822014516042457686261563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81214676344028305124174375 121822014516042457686261563)
    ·
      refine ⟨182733021774063686529392345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121822014516042457686261563 182733021774063686529392345)
      ·
        refine ⟨137049766330547764897044259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182733021774063686529392345 137049766330547764897044259)
        ·
          refine ⟨205574649495821647345566389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137049766330547764897044259 205574649495821647345566389)
          ·
            refine ⟨19272623390233279438646849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 205574649495821647345566389 19272623390233279438646849)
            ·
              refine ⟨14454467542674959578985137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19272623390233279438646849 14454467542674959578985137)
              ·
                refine ⟨10840850657006219684238853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14454467542674959578985137 10840850657006219684238853)
                ·
                  refine ⟨2032659498188666190794785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10840850657006219684238853 2032659498188666190794785)
                  ·
                    refine ⟨1524494623641499643096089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2032659498188666190794785 1524494623641499643096089)
                    ·
                      refine ⟨1143370967731124732322067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524494623641499643096089 1143370967731124732322067)
                      ·
                        rfl

theorem cell23_2226707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 2, 2].length) (baseStart_2226707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226707 prefixEnd_2226707 := by exact prefixLift 2226707
  have htrace : WordTrace (prefixWord ++ tailWord_2226707) baseStart_2226707 baseEnd_2226707 := by
    simpa [prefixWord, tailWord_2226707, baseEnd_2226707] using wordTrace_append hprefix tailTrace_2226707
  have hstable : (prefixWord ++ tailWord_2226707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226707).length < 2 ^ (prefixWord ++ tailWord_2226707).sum := by decide
  have hdescent : baseEnd_2226707 < baseStart_2226707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226711 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2226711 : Nat := 118140960795 + 2226711 * 2 ^ 59
def prefixEnd_2226711 : Nat := 4983230072969 + 3 ^ 40 * 2226711 * 2
def baseEnd_2226711 : Nat := 1143373021653742716672049

theorem tailTrace_2226711 : CollatzResearch.WordTrace tailWord_2226711 prefixEnd_2226711 1143373021653742716672049 := by
  unfold tailWord_2226711
  simp only [CollatzResearch.WordTrace]
  refine ⟨81214822236013813807319987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54143214824009209204879991 81214822236013813807319987)
  ·
    refine ⟨121822233354020720710979981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81214822236013813807319987 121822233354020720710979981)
    ·
      refine ⟨45683337507757770266617493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121822233354020720710979981 45683337507757770266617493)
      ·
        refine ⟨2141406445676145481247695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45683337507757770266617493 2141406445676145481247695)
        ·
          refine ⟨3212109668514218221871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141406445676145481247695 3212109668514218221871543)
          ·
            refine ⟨4818164502771327332807315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212109668514218221871543 4818164502771327332807315)
            ·
              refine ⟨7227246754156990999210973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818164502771327332807315 7227246754156990999210973)
              ·
                refine ⟨2710217532808871624704115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7227246754156990999210973 2710217532808871624704115)
                ·
                  refine ⟨4065326299213307437056173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710217532808871624704115 4065326299213307437056173)
                  ·
                    refine ⟨1524497362204990288896065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4065326299213307437056173 1524497362204990288896065)
                    ·
                      refine ⟨1143373021653742716672049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524497362204990288896065 1143373021653742716672049)
                      ·
                        rfl

theorem cell23_2226711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2226711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226711 prefixEnd_2226711 := by exact prefixLift 2226711
  have htrace : WordTrace (prefixWord ++ tailWord_2226711) baseStart_2226711 baseEnd_2226711 := by
    simpa [prefixWord, tailWord_2226711, baseEnd_2226711] using wordTrace_append hprefix tailTrace_2226711
  have hstable : (prefixWord ++ tailWord_2226711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226711).length < 2 ^ (prefixWord ++ tailWord_2226711).sum := by decide
  have hdescent : baseEnd_2226711 < baseStart_2226711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226730 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_2226730 : Nat := 118140960795 + 2226730 * 2 ^ 59
def prefixEnd_2226730 : Nat := 4983230072969 + 3 ^ 40 * 2226730 * 2
def baseEnd_2226730 : Nat := 127042530865130904703829

theorem tailTrace_2226730 : CollatzResearch.WordTrace tailWord_2226730 prefixEnd_2226730 127042530865130904703829 := by
  unfold tailWord_2226730
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303878805736245013065411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54143676815296653368174429 20303878805736245013065411)
  ·
    refine ⟨30455818208604367519598117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20303878805736245013065411 30455818208604367519598117)
    ·
      refine ⟨5710465914113318909924647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30455818208604367519598117 5710465914113318909924647)
      ·
        refine ⟨8565698871169978364886971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710465914113318909924647 8565698871169978364886971)
        ·
          refine ⟨12848548306754967547330457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8565698871169978364886971 12848548306754967547330457)
          ·
            refine ⟨9636411230066225660497843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12848548306754967547330457 9636411230066225660497843)
            ·
              refine ⟨14454616845099338490746765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9636411230066225660497843 14454616845099338490746765)
              ·
                refine ⟨5420481316912251934030037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14454616845099338490746765 5420481316912251934030037)
                ·
                  refine ⟨127042530865130904703829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5420481316912251934030037 127042530865130904703829)
                  ·
                    rfl

theorem cell23_2226730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_2226730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226730 prefixEnd_2226730 := by exact prefixLift 2226730
  have htrace : WordTrace (prefixWord ++ tailWord_2226730) baseStart_2226730 baseEnd_2226730 := by
    simpa [prefixWord, tailWord_2226730, baseEnd_2226730] using wordTrace_append hprefix tailTrace_2226730
  have hstable : (prefixWord ++ tailWord_2226730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226730).length < 2 ^ (prefixWord ++ tailWord_2226730).sum := by decide
  have hdescent : baseEnd_2226730 < baseStart_2226730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226741 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_2226741 : Nat := 118140960795 + 2226741 * 2 ^ 59
def prefixEnd_2226741 : Nat := 4983230072969 + 3 ^ 40 * 2226741 * 2
def baseEnd_2226741 : Nat := 1143388426073377599296911

theorem tailTrace_2226741 : CollatzResearch.WordTrace tailWord_2226741 prefixEnd_2226741 1143388426073377599296911 := by
  unfold tailWord_2226741
  simp only [CollatzResearch.WordTrace]
  refine ⟨81215916425905128930912077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54143944283936752620608051 81215916425905128930912077)
  ·
    refine ⟨30455968659714423349092029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81215916425905128930912077 30455968659714423349092029)
    ·
      refine ⟨11420988247392908755909511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30455968659714423349092029 11420988247392908755909511)
      ·
        refine ⟨17131482371089363133864267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11420988247392908755909511 17131482371089363133864267)
        ·
          refine ⟨25697223556634044700796401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17131482371089363133864267 25697223556634044700796401)
          ·
            refine ⟨19272917667475533525597301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25697223556634044700796401 19272917667475533525597301)
            ·
              refine ⟨1806836031325831268024747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19272917667475533525597301 1806836031325831268024747)
              ·
                refine ⟨2710254046988746902037121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806836031325831268024747 2710254046988746902037121)
                ·
                  refine ⟨2032690535241560176527841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710254046988746902037121 2032690535241560176527841)
                  ·
                    refine ⟨1524517901431170132395881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2032690535241560176527841 1524517901431170132395881)
                    ·
                      refine ⟨1143388426073377599296911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524517901431170132395881 1143388426073377599296911)
                      ·
                        rfl

theorem cell23_2226741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_2226741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226741 prefixEnd_2226741 := by exact prefixLift 2226741
  have htrace : WordTrace (prefixWord ++ tailWord_2226741) baseStart_2226741 baseEnd_2226741 := by
    simpa [prefixWord, tailWord_2226741, baseEnd_2226741] using wordTrace_append hprefix tailTrace_2226741
  have hstable : (prefixWord ++ tailWord_2226741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226741).length < 2 ^ (prefixWord ++ tailWord_2226741).sum := by decide
  have hdescent : baseEnd_2226741 < baseStart_2226741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226743 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 3, 7]
def baseStart_2226743 : Nat := 118140960795 + 2226743 * 2 ^ 59
def prefixEnd_2226743 : Nat := 4983230072969 + 3 ^ 40 * 2226743 * 2
def baseEnd_2226743 : Nat := 381129817678228863823967

theorem tailTrace_2226743 : CollatzResearch.WordTrace tailWord_2226743 prefixEnd_2226743 381129817678228863823967 := by
  unfold tailWord_2226743
  simp only [CollatzResearch.WordTrace]
  refine ⟨81215989371897883272484883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54143992914598588848323255 81215989371897883272484883)
  ·
    refine ⟨121823984057846824908727325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81215989371897883272484883 121823984057846824908727325)
    ·
      refine ⟨45683994021692559340772747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121823984057846824908727325 45683994021692559340772747)
      ·
        refine ⟨68525991032538839011159121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45683994021692559340772747 68525991032538839011159121)
        ·
          refine ⟨51394493274404129258369341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68525991032538839011159121 51394493274404129258369341)
          ·
            refine ⟨19272934977901548471888503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51394493274404129258369341 19272934977901548471888503)
            ·
              refine ⟨28909402466852322707832755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19272934977901548471888503 28909402466852322707832755)
              ·
                refine ⟨43364103700278484061749133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28909402466852322707832755 43364103700278484061749133)
                ·
                  refine ⟨16261538887604431523155925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43364103700278484061749133 16261538887604431523155925)
                  ·
                    refine ⟨381129817678228863823967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16261538887604431523155925 381129817678228863823967)
                    ·
                      rfl

theorem cell23_2226743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_2226743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226743 prefixEnd_2226743 := by exact prefixLift 2226743
  have htrace : WordTrace (prefixWord ++ tailWord_2226743) baseStart_2226743 baseEnd_2226743 := by
    simpa [prefixWord, tailWord_2226743, baseEnd_2226743] using wordTrace_append hprefix tailTrace_2226743
  have hstable : (prefixWord ++ tailWord_2226743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226743).length < 2 ^ (prefixWord ++ tailWord_2226743).sum := by decide
  have hdescent : baseEnd_2226743 < baseStart_2226743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226770 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2226770 : Nat := 118140960795 + 2226770 * 2 ^ 59
def prefixEnd_2226770 : Nat := 4983230072969 + 3 ^ 40 * 2226770 * 2
def baseEnd_2226770 : Nat := 1143403317012357985834277

theorem tailTrace_2226770 : CollatzResearch.WordTrace tailWord_2226770 prefixEnd_2226770 1143403317012357985834277 := by
  unfold tailWord_2226770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304243535700016720929441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54144649428533377922478509 20304243535700016720929441)
  ·
    refine ⟨15228182651775012540697081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20304243535700016720929441 15228182651775012540697081)
    ·
      refine ⟨11421136988831259405522811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15228182651775012540697081 11421136988831259405522811)
      ·
        refine ⟨17131705483246889108284217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11421136988831259405522811 17131705483246889108284217)
        ·
          refine ⟨12848779112435166831213163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17131705483246889108284217 12848779112435166831213163)
          ·
            refine ⟨19273168668652750246819745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12848779112435166831213163 19273168668652750246819745)
            ·
              refine ⟨14454876501489562685114809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19273168668652750246819745 14454876501489562685114809)
              ·
                refine ⟨10841157376117172013836107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14454876501489562685114809 10841157376117172013836107)
                ·
                  refine ⟨16261736064175758020754161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10841157376117172013836107 16261736064175758020754161)
                  ·
                    refine ⟨12196302048131818515565621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16261736064175758020754161 12196302048131818515565621)
                    ·
                      refine ⟨1143403317012357985834277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12196302048131818515565621 1143403317012357985834277)
                      ·
                        rfl

theorem cell23_2226770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2226770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226770 prefixEnd_2226770 := by exact prefixLift 2226770
  have htrace : WordTrace (prefixWord ++ tailWord_2226770) baseStart_2226770 baseEnd_2226770 := by
    simpa [prefixWord, tailWord_2226770, baseEnd_2226770] using wordTrace_append hprefix tailTrace_2226770
  have hstable : (prefixWord ++ tailWord_2226770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226770).length < 2 ^ (prefixWord ++ tailWord_2226770).sum := by decide
  have hdescent : baseEnd_2226770 < baseStart_2226770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226803 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 10]
def baseStart_2226803 : Nat := 118140960795 + 2226803 * 2 ^ 59
def prefixEnd_2226803 : Nat := 4983230072969 + 3 ^ 40 * 2226803 * 2
def baseEnd_2226803 : Nat := 127046695763772928524625

theorem tailTrace_2226803 : CollatzResearch.WordTrace tailWord_2226803 prefixEnd_2226803 127046695763772928524625 := by
  unfold tailWord_2226803
  simp only [CollatzResearch.WordTrace]
  refine ⟨81218177751680513519669063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54145451834453675679779375 81218177751680513519669063)
  ·
    refine ⟨121827266627520770279503595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81218177751680513519669063 121827266627520770279503595)
    ·
      refine ⟨182740899941281155419255393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121827266627520770279503595 182740899941281155419255393)
      ·
        refine ⟨137055674955960866564441545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182740899941281155419255393 137055674955960866564441545)
        ·
          refine ⟨102791756216970649923331159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137055674955960866564441545 102791756216970649923331159)
          ·
            refine ⟨154187634325455974884996739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102791756216970649923331159 154187634325455974884996739)
            ·
              refine ⟨231281451488183962327495109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154187634325455974884996739 231281451488183962327495109)
              ·
                refine ⟨43365272154034492936405333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231281451488183962327495109 43365272154034492936405333)
                ·
                  refine ⟨127046695763772928524625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43365272154034492936405333 127046695763772928524625)
                  ·
                    rfl

theorem cell23_2226803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 10].length) (baseStart_2226803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226803 prefixEnd_2226803 := by exact prefixLift 2226803
  have htrace : WordTrace (prefixWord ++ tailWord_2226803) baseStart_2226803 baseEnd_2226803 := by
    simpa [prefixWord, tailWord_2226803, baseEnd_2226803] using wordTrace_append hprefix tailTrace_2226803
  have hstable : (prefixWord ++ tailWord_2226803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226803).length < 2 ^ (prefixWord ++ tailWord_2226803).sum := by decide
  have hdescent : baseEnd_2226803 < baseStart_2226803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226834 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2226834 : Nat := 118140960795 + 2226834 * 2 ^ 59
def prefixEnd_2226834 : Nat := 4983230072969 + 3 ^ 40 * 2226834 * 2
def baseEnd_2226834 : Nat := 1143436179774245735433983

theorem tailTrace_2226834 : CollatzResearch.WordTrace tailWord_2226834 prefixEnd_2226834 1143436179774245735433983 := by
  unfold tailWord_2226834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304827103642051453511889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54146205609712137209365037 20304827103642051453511889)
  ·
    refine ⟨15228620327731538590133917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20304827103642051453511889 15228620327731538590133917)
    ·
      refine ⟨5710732622899326971300219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15228620327731538590133917 5710732622899326971300219)
      ·
        refine ⟨8566098934348990456950329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710732622899326971300219 8566098934348990456950329)
        ·
          refine ⟨6424574200761742842712747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8566098934348990456950329 6424574200761742842712747)
          ·
            refine ⟨9636861301142614264069121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6424574200761742842712747 9636861301142614264069121)
            ·
              refine ⟨7227645975856960698051841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9636861301142614264069121 7227645975856960698051841)
              ·
                refine ⟨5420734481892720523538881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7227645975856960698051841 5420734481892720523538881)
                ·
                  refine ⟨4065550861419540392654161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5420734481892720523538881 4065550861419540392654161)
                  ·
                    refine ⟨3049163146064655294490621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4065550861419540392654161 3049163146064655294490621)
                    ·
                      refine ⟨1143436179774245735433983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049163146064655294490621 1143436179774245735433983)
                      ·
                        rfl

theorem cell23_2226834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2226834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226834 prefixEnd_2226834 := by exact prefixLift 2226834
  have htrace : WordTrace (prefixWord ++ tailWord_2226834) baseStart_2226834 baseEnd_2226834 := by
    simpa [prefixWord, tailWord_2226834, baseEnd_2226834] using wordTrace_append hprefix tailTrace_2226834
  have hstable : (prefixWord ++ tailWord_2226834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226834).length < 2 ^ (prefixWord ++ tailWord_2226834).sum := by decide
  have hdescent : baseEnd_2226834 < baseStart_2226834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226840 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2226840 : Nat := 118140960795 + 2226840 * 2 ^ 59
def prefixEnd_2226840 : Nat := 4983230072969 + 3 ^ 40 * 2226840 * 2
def baseEnd_2226840 : Nat := 1143439260658172711958955

theorem tailTrace_2226840 : CollatzResearch.WordTrace tailWord_2226840 prefixEnd_2226840 1143439260658172711958955 := by
  unfold tailWord_2226840
  simp only [CollatzResearch.WordTrace]
  refine ⟨40609763626273234419382987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54146351501697645892510649 40609763626273234419382987)
  ·
    refine ⟨60914645439409851629074481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40609763626273234419382987 60914645439409851629074481)
    ·
      refine ⟨45685984079557388721805861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60914645439409851629074481 45685984079557388721805861)
      ·
        refine ⟨8566122014917010385338599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45685984079557388721805861 8566122014917010385338599)
        ·
          refine ⟨12849183022375515578007899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8566122014917010385338599 12849183022375515578007899)
          ·
            refine ⟨19273774533563273367011849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12849183022375515578007899 19273774533563273367011849)
            ·
              refine ⟨14455330900172455025258887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19273774533563273367011849 14455330900172455025258887)
              ·
                refine ⟨21682996350258682537888331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14455330900172455025258887 21682996350258682537888331)
                ·
                  refine ⟨32524494525388023806832497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21682996350258682537888331 32524494525388023806832497)
                  ·
                    refine ⟨24393370894041017855124373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32524494525388023806832497 24393370894041017855124373)
                    ·
                      refine ⟨1143439260658172711958955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24393370894041017855124373 1143439260658172711958955)
                      ·
                        rfl

theorem cell23_2226840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2226840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226840 prefixEnd_2226840 := by exact prefixLift 2226840
  have htrace : WordTrace (prefixWord ++ tailWord_2226840) baseStart_2226840 baseEnd_2226840 := by
    simpa [prefixWord, tailWord_2226840, baseEnd_2226840] using wordTrace_append hprefix tailTrace_2226840
  have hstable : (prefixWord ++ tailWord_2226840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226840).length < 2 ^ (prefixWord ++ tailWord_2226840).sum := by decide
  have hdescent : baseEnd_2226840 < baseStart_2226840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226857 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 6, 3, 2]
def baseStart_2226857 : Nat := 118140960795 + 2226857 * 2 ^ 59
def prefixEnd_2226857 : Nat := 4983230072969 + 3 ^ 40 * 2226857 * 2
def baseEnd_2226857 : Nat := 1143447989829299145446377

theorem tailTrace_2226857 : CollatzResearch.WordTrace tailWord_2226857 prefixEnd_2226857 1143447989829299145446377 := by
  unfold tailWord_2226857
  simp only [CollatzResearch.WordTrace]
  refine ⟨81220147293484880742134825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54146764862323253828089883 81220147293484880742134825)
  ·
    refine ⟨60915110470113660556601119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81220147293484880742134825 60915110470113660556601119)
    ·
      refine ⟨91372665705170490834901679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60915110470113660556601119 91372665705170490834901679)
      ·
        refine ⟨137058998557755736252352519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91372665705170490834901679 137058998557755736252352519)
        ·
          refine ⟨205588497836633604378528779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137058998557755736252352519 205588497836633604378528779)
          ·
            refine ⟨308382746754950406567793169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205588497836633604378528779 308382746754950406567793169)
            ·
              refine ⟨231287060066212804925844877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308382746754950406567793169 231287060066212804925844877)
              ·
                refine ⟨86732647524829801847191829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231287060066212804925844877 86732647524829801847191829)
                ·
                  refine ⟨4065592852726396961587117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86732647524829801847191829 4065592852726396961587117)
                  ·
                    refine ⟨1524597319772398860595169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4065592852726396961587117 1524597319772398860595169)
                    ·
                      refine ⟨1143447989829299145446377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524597319772398860595169 1143447989829299145446377)
                      ·
                        rfl

theorem cell23_2226857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 3, 2].length) (baseStart_2226857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226857 prefixEnd_2226857 := by exact prefixLift 2226857
  have htrace : WordTrace (prefixWord ++ tailWord_2226857) baseStart_2226857 baseEnd_2226857 := by
    simpa [prefixWord, tailWord_2226857, baseEnd_2226857] using wordTrace_append hprefix tailTrace_2226857
  have hstable : (prefixWord ++ tailWord_2226857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226857).length < 2 ^ (prefixWord ++ tailWord_2226857).sum := by decide
  have hdescent : baseEnd_2226857 < baseStart_2226857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226884 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2226884 : Nat := 118140960795 + 2226884 * 2 ^ 59
def prefixEnd_2226884 : Nat := 4983230072969 + 3 ^ 40 * 2226884 * 2
def baseEnd_2226884 : Nat := 381153951268990179936251

theorem tailTrace_2226884 : CollatzResearch.WordTrace tailWord_2226884 prefixEnd_2226884 381153951268990179936251 := by
  unfold tailWord_2226884
  simp only [CollatzResearch.WordTrace]
  refine ⟨40610566032193532176683853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54147421376258042902245137 40610566032193532176683853)
  ·
    refine ⟨15228962262072574566256445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40610566032193532176683853 15228962262072574566256445)
    ·
      refine ⟨5710860848277215462346167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15228962262072574566256445 5710860848277215462346167)
      ·
        refine ⟨8566291272415823193519251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710860848277215462346167 8566291272415823193519251)
        ·
          refine ⟨12849436908623734790278877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8566291272415823193519251 12849436908623734790278877)
          ·
            refine ⟨4818538840733900546354579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12849436908623734790278877 4818538840733900546354579)
            ·
              refine ⟨7227808261100850819531869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818538840733900546354579 7227808261100850819531869)
              ·
                refine ⟨2710428097912819057324451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7227808261100850819531869 2710428097912819057324451)
                ·
                  refine ⟨4065642146869228585986677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710428097912819057324451 4065642146869228585986677)
                  ·
                    refine ⟨381153951268990179936251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4065642146869228585986677 381153951268990179936251)
                    ·
                      rfl

theorem cell23_2226884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2226884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226884 prefixEnd_2226884 := by exact prefixLift 2226884
  have htrace : WordTrace (prefixWord ++ tailWord_2226884) baseStart_2226884 baseEnd_2226884 := by
    simpa [prefixWord, tailWord_2226884, baseEnd_2226884] using wordTrace_append hprefix tailTrace_2226884
  have hstable : (prefixWord ++ tailWord_2226884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226884).length < 2 ^ (prefixWord ++ tailWord_2226884).sum := by decide
  have hdescent : baseEnd_2226884 < baseStart_2226884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226897 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 4, 4]
def baseStart_2226897 : Nat := 118140960795 + 2226897 * 2 ^ 59
def prefixEnd_2226897 : Nat := 4983230072969 + 3 ^ 40 * 2226897 * 2
def baseEnd_2226897 : Nat := 381156176351826329648731

theorem tailTrace_2226897 : CollatzResearch.WordTrace tailWord_2226897 prefixEnd_2226897 381156176351826329648731 := by
  unfold tailWord_2226897
  simp only [CollatzResearch.WordTrace]
  refine ⟨81221606213339967573590945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54147737475559978382393963 81221606213339967573590945)
  ·
    refine ⟨60916204660004975680193209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81221606213339967573590945 60916204660004975680193209)
    ·
      refine ⟨45687153495003731760144907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60916204660004975680193209 45687153495003731760144907)
      ·
        refine ⟨68530730242505597640217361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45687153495003731760144907 68530730242505597640217361)
        ·
          refine ⟨51398047681879198230163021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68530730242505597640217361 51398047681879198230163021)
          ·
            refine ⟨19274267880704699336311133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51398047681879198230163021 19274267880704699336311133)
            ·
              refine ⟨7227850455264262251116675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19274267880704699336311133 7227850455264262251116675)
              ·
                refine ⟨10841775682896393376675013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227850455264262251116675 10841775682896393376675013)
                ·
                  refine ⟨2032832940543073758126565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10841775682896393376675013 2032832940543073758126565)
                  ·
                    refine ⟨381156176351826329648731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2032832940543073758126565 381156176351826329648731)
                    ·
                      rfl

theorem cell23_2226897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_2226897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226897 prefixEnd_2226897 := by exact prefixLift 2226897
  have htrace : WordTrace (prefixWord ++ tailWord_2226897) baseStart_2226897 baseEnd_2226897 := by
    simpa [prefixWord, tailWord_2226897, baseEnd_2226897] using wordTrace_append hprefix tailTrace_2226897
  have hstable : (prefixWord ++ tailWord_2226897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226897).length < 2 ^ (prefixWord ++ tailWord_2226897).sum := by decide
  have hdescent : baseEnd_2226897 < baseStart_2226897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226917 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2226917 : Nat := 118140960795 + 2226917 * 2 ^ 59
def prefixEnd_2226917 : Nat := 4983230072969 + 3 ^ 40 * 2226917 * 2
def baseEnd_2226917 : Nat := 1143478798668568910696101

theorem tailTrace_2226917 : CollatzResearch.WordTrace tailWord_2226917 prefixEnd_2226917 1143478798668568910696101 := by
  unfold tailWord_2226917
  simp only [CollatzResearch.WordTrace]
  refine ⟨81222335673267510989319005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54148223782178340659546003 81222335673267510989319005)
  ·
    refine ⟨30458375877475316620994627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81222335673267510989319005 30458375877475316620994627)
    ·
      refine ⟨45687563816212974931491941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30458375877475316620994627 45687563816212974931491941)
      ·
        refine ⟨8566418215539932799654739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45687563816212974931491941 8566418215539932799654739)
        ·
          refine ⟨12849627323309899199482109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8566418215539932799654739 12849627323309899199482109)
          ·
            refine ⟨4818610246241212199805791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12849627323309899199482109 4818610246241212199805791)
            ·
              refine ⟨7227915369361818299708687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818610246241212199805791 7227915369361818299708687)
              ·
                refine ⟨10841873054042727449563031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227915369361818299708687 10841873054042727449563031)
                ·
                  refine ⟨16262809581064091174344547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10841873054042727449563031 16262809581064091174344547)
                  ·
                    refine ⟨24394214371596136761516821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16262809581064091174344547 24394214371596136761516821)
                    ·
                      refine ⟨1143478798668568910696101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24394214371596136761516821 1143478798668568910696101)
                      ·
                        rfl

theorem cell23_2226917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2226917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226917 prefixEnd_2226917 := by exact prefixLift 2226917
  have htrace : WordTrace (prefixWord ++ tailWord_2226917) baseStart_2226917 baseEnd_2226917 := by
    simpa [prefixWord, tailWord_2226917, baseEnd_2226917] using wordTrace_append hprefix tailTrace_2226917
  have hstable : (prefixWord ++ tailWord_2226917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226917).length < 2 ^ (prefixWord ++ tailWord_2226917).sum := by decide
  have hdescent : baseEnd_2226917 < baseStart_2226917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226927 : List Nat := [1, 1, 2, 1, 5, 2, 4, 7]
def baseStart_2226927 : Nat := 118140960795 + 2226927 * 2 ^ 59
def prefixEnd_2226927 : Nat := 4983230072969 + 3 ^ 40 * 2226927 * 2
def baseEnd_2226927 : Nat := 42351256795374587835965

theorem tailTrace_2226927 : CollatzResearch.WordTrace tailWord_2226927 prefixEnd_2226927 42351256795374587835965 := by
  unfold tailWord_2226927
  simp only [CollatzResearch.WordTrace]
  refine ⟨81222700403231282697183035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54148466935487521798122023 81222700403231282697183035)
  ·
    refine ⟨121834050604846924045774553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81222700403231282697183035 121834050604846924045774553)
    ·
      refine ⟨91375537953635193034330915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121834050604846924045774553 91375537953635193034330915)
      ·
        refine ⟨137063306930452789551496373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91375537953635193034330915 137063306930452789551496373)
        ·
          refine ⟨12849685024729949020452785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137063306930452789551496373 12849685024729949020452785)
          ·
            refine ⟨9637263768547461765339589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12849685024729949020452785 9637263768547461765339589)
            ·
              refine ⟨1806986956602649081001173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9637263768547461765339589 1806986956602649081001173)
              ·
                refine ⟨42351256795374587835965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1806986956602649081001173 42351256795374587835965)
                ·
                  rfl

theorem cell23_2226927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 7].length) (baseStart_2226927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226927 prefixEnd_2226927 := by exact prefixLift 2226927
  have htrace : WordTrace (prefixWord ++ tailWord_2226927) baseStart_2226927 baseEnd_2226927 := by
    simpa [prefixWord, tailWord_2226927, baseEnd_2226927] using wordTrace_append hprefix tailTrace_2226927
  have hstable : (prefixWord ++ tailWord_2226927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226927).length < 2 ^ (prefixWord ++ tailWord_2226927).sum := by decide
  have hdescent : baseEnd_2226927 < baseStart_2226927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226937 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_2226937 : Nat := 118140960795 + 2226937 * 2 ^ 59
def prefixEnd_2226937 : Nat := 4983230072969 + 3 ^ 40 * 2226937 * 2
def baseEnd_2226937 : Nat := 1143489068281658832446009

theorem tailTrace_2226937 : CollatzResearch.WordTrace tailWord_2226937 prefixEnd_2226937 1143489068281658832446009 := by
  unfold tailWord_2226937
  simp only [CollatzResearch.WordTrace]
  refine ⟨81223065133195054405047065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54148710088796702936698043 81223065133195054405047065)
  ·
    refine ⟨60917298849896290803785299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81223065133195054405047065 60917298849896290803785299)
    ·
      refine ⟨91375948274844436205677949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60917298849896290803785299 91375948274844436205677949)
      ·
        refine ⟨34265980603066663577129231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91375948274844436205677949 34265980603066663577129231)
        ·
          refine ⟨51398970904599995365693847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34265980603066663577129231 51398970904599995365693847)
          ·
            refine ⟨77098456356899993048540771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51398970904599995365693847 77098456356899993048540771)
            ·
              refine ⟨115647684535349989572811157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77098456356899993048540771 115647684535349989572811157)
              ·
                refine ⟨5420985212594530761225523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115647684535349989572811157 5420985212594530761225523)
                ·
                  refine ⟨8131477818891796141838285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420985212594530761225523 8131477818891796141838285)
                  ·
                    refine ⟨3049304182084423553189357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8131477818891796141838285 3049304182084423553189357)
                    ·
                      refine ⟨1143489068281658832446009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049304182084423553189357 1143489068281658832446009)
                      ·
                        rfl

theorem cell23_2226937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_2226937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226937 prefixEnd_2226937 := by exact prefixLift 2226937
  have htrace : WordTrace (prefixWord ++ tailWord_2226937) baseStart_2226937 baseEnd_2226937 := by
    simpa [prefixWord, tailWord_2226937, baseEnd_2226937] using wordTrace_append hprefix tailTrace_2226937
  have hstable : (prefixWord ++ tailWord_2226937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226937).length < 2 ^ (prefixWord ++ tailWord_2226937).sum := by decide
  have hdescent : baseEnd_2226937 < baseStart_2226937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226938 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2]
def baseStart_2226938 : Nat := 118140960795 + 2226938 * 2 ^ 59
def prefixEnd_2226938 : Nat := 4983230072969 + 3 ^ 40 * 2226938 * 2
def baseEnd_2226938 : Nat := 1143489581762313328533505

theorem tailTrace_2226938 : CollatzResearch.WordTrace tailWord_2226938 prefixEnd_2226938 1143489581762313328533505 := by
  unfold tailWord_2226938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20305775401547857893958367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54148734404127621050555645 20305775401547857893958367)
  ·
    refine ⟨30458663102321786840937551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20305775401547857893958367 30458663102321786840937551)
    ·
      refine ⟨45687994653482680261406327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30458663102321786840937551 45687994653482680261406327)
      ·
        refine ⟨68531991980224020392109491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45687994653482680261406327 68531991980224020392109491)
        ·
          refine ⟨102797987970336030588164237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68531991980224020392109491 102797987970336030588164237)
          ·
            refine ⟨38549245488876011470561589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102797987970336030588164237 38549245488876011470561589)
            ·
              refine ⟨3613991764582126075365149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38549245488876011470561589 3613991764582126075365149)
              ·
                refine ⟨1355246911718297278261931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3613991764582126075365149 1355246911718297278261931)
                ·
                  refine ⟨2032870367577445917392897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355246911718297278261931 2032870367577445917392897)
                  ·
                    refine ⟨1524652775683084438044673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2032870367577445917392897 1524652775683084438044673)
                    ·
                      refine ⟨1143489581762313328533505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524652775683084438044673 1143489581762313328533505)
                      ·
                        rfl

theorem cell23_2226938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_2226938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226938 prefixEnd_2226938 := by exact prefixLift 2226938
  have htrace : WordTrace (prefixWord ++ tailWord_2226938) baseStart_2226938 baseEnd_2226938 := by
    simpa [prefixWord, tailWord_2226938, baseEnd_2226938] using wordTrace_append hprefix tailTrace_2226938
  have hstable : (prefixWord ++ tailWord_2226938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226938).length < 2 ^ (prefixWord ++ tailWord_2226938).sum := by decide
  have hdescent : baseEnd_2226938 < baseStart_2226938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226954 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2226954 : Nat := 118140960795 + 2226954 * 2 ^ 59
def prefixEnd_2226954 : Nat := 4983230072969 + 3 ^ 40 * 2226954 * 2
def baseEnd_2226954 : Nat := 1143497797452785265933431

theorem tailTrace_2226954 : CollatzResearch.WordTrace tailWord_2226954 prefixEnd_2226954 1143497797452785265933431 := by
  unfold tailWord_2226954
  simp only [CollatzResearch.WordTrace]
  refine ⟨20305921293533366577103979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54149123449422310872277277 20305921293533366577103979)
  ·
    refine ⟨30458881940300049865655969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20305921293533366577103979 30458881940300049865655969)
    ·
      refine ⟨22844161455225037399241977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30458881940300049865655969 22844161455225037399241977)
      ·
        refine ⟨17133121091418778049431483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22844161455225037399241977 17133121091418778049431483)
        ·
          refine ⟨25699681637128167074147225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17133121091418778049431483 25699681637128167074147225)
          ·
            refine ⟨19274761227846125305610419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25699681637128167074147225 19274761227846125305610419)
            ·
              refine ⟨28912141841769187958415629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19274761227846125305610419 28912141841769187958415629)
              ·
                refine ⟨10842053190663445484405861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28912141841769187958415629 10842053190663445484405861)
                ·
                  refine ⟨2032884973249396028326099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10842053190663445484405861 2032884973249396028326099)
                  ·
                    refine ⟨3049327459874094042489149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032884973249396028326099 3049327459874094042489149)
                    ·
                      refine ⟨1143497797452785265933431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049327459874094042489149 1143497797452785265933431)
                      ·
                        rfl

theorem cell23_2226954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2226954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2226954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2226954 prefixEnd_2226954 := by exact prefixLift 2226954
  have htrace : WordTrace (prefixWord ++ tailWord_2226954) baseStart_2226954 baseEnd_2226954 := by
    simpa [prefixWord, tailWord_2226954, baseEnd_2226954] using wordTrace_append hprefix tailTrace_2226954
  have hstable : (prefixWord ++ tailWord_2226954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226954).length < 2 ^ (prefixWord ++ tailWord_2226954).sum := by decide
  have hdescent : baseEnd_2226954 < baseStart_2226954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227021 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_2227021 : Nat := 118140960795 + 2227021 * 2 ^ 59
def prefixEnd_2227021 : Nat := 4983230072969 + 3 ^ 40 * 2227021 * 2
def baseEnd_2227021 : Nat := 381177400218878834598541

theorem tailTrace_2227021 : CollatzResearch.WordTrace tailWord_2227021 prefixEnd_2227021 381177400218878834598541 := by
  unfold tailWord_2227021
  simp only [CollatzResearch.WordTrace]
  refine ⟨81226128864890736751104917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54150752576593824500736611 81226128864890736751104917)
  ·
    refine ⟨3807474790541753285208043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81226128864890736751104917 3807474790541753285208043)
    ·
      refine ⟨5711212185812629927812065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807474790541753285208043 5711212185812629927812065)
      ·
        refine ⟨4283409139359472445859049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5711212185812629927812065 4283409139359472445859049)
        ·
          refine ⟨3212556854519604334394287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4283409139359472445859049 3212556854519604334394287)
          ·
            refine ⟨4818835281779406501591431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212556854519604334394287 4818835281779406501591431)
            ·
              refine ⟨7228252922669109752387147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818835281779406501591431 7228252922669109752387147)
              ·
                refine ⟨10842379384003664628580721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7228252922669109752387147 10842379384003664628580721)
                ·
                  refine ⟨8131784538002748471435541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10842379384003664628580721 8131784538002748471435541)
                  ·
                    refine ⟨381177400218878834598541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8131784538002748471435541 381177400218878834598541)
                    ·
                      rfl

theorem cell23_2227021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_2227021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227021 prefixEnd_2227021 := by exact prefixLift 2227021
  have htrace : WordTrace (prefixWord ++ tailWord_2227021) baseStart_2227021 baseEnd_2227021 := by
    simpa [prefixWord, tailWord_2227021, baseEnd_2227021] using wordTrace_append hprefix tailTrace_2227021
  have hstable : (prefixWord ++ tailWord_2227021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227021).length < 2 ^ (prefixWord ++ tailWord_2227021).sum := by decide
  have hdescent : baseEnd_2227021 < baseStart_2227021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227028 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_2227028 : Nat := 118140960795 + 2227028 * 2 ^ 59
def prefixEnd_2227028 : Nat := 4983230072969 + 3 ^ 40 * 2227028 * 2
def baseEnd_2227028 : Nat := 1143535795021217976408091

theorem tailTrace_2227028 : CollatzResearch.WordTrace tailWord_2227028 prefixEnd_2227028 1143535795021217976408091 := by
  unfold tailWord_2227028
  simp only [CollatzResearch.WordTrace]
  refine ⟨40613192087932688473304869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54150922783910251297739825 40613192087932688473304869)
  ·
    refine ⟨7614973516487379088744663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40613192087932688473304869 7614973516487379088744663)
    ·
      refine ⟨11422460274731068633116995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7614973516487379088744663 11422460274731068633116995)
      ·
        refine ⟨17133690412096602949675493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11422460274731068633116995 17133690412096602949675493)
        ·
          refine ⟨3212566952268113053064155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17133690412096602949675493 3212566952268113053064155)
          ·
            refine ⟨4818850428402169579596233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212566952268113053064155 4818850428402169579596233)
            ·
              refine ⟨3614137821301627184697175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4818850428402169579596233 3614137821301627184697175)
              ·
                refine ⟨5421206731952440777045763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614137821301627184697175 5421206731952440777045763)
                ·
                  refine ⟨8131810097928661165568645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421206731952440777045763 8131810097928661165568645)
                  ·
                    refine ⟨1524714393361623968544121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8131810097928661165568645 1524714393361623968544121)
                    ·
                      refine ⟨1143535795021217976408091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524714393361623968544121 1143535795021217976408091)
                      ·
                        rfl

theorem cell23_2227028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_2227028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227028 prefixEnd_2227028 := by exact prefixLift 2227028
  have htrace : WordTrace (prefixWord ++ tailWord_2227028) baseStart_2227028 baseEnd_2227028 := by
    simpa [prefixWord, tailWord_2227028, baseEnd_2227028] using wordTrace_append hprefix tailTrace_2227028
  have hstable : (prefixWord ++ tailWord_2227028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227028).length < 2 ^ (prefixWord ++ tailWord_2227028).sum := by decide
  have hdescent : baseEnd_2227028 < baseStart_2227028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227062 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2227062 : Nat := 118140960795 + 2227062 * 2 ^ 59
def prefixEnd_2227062 : Nat := 4983230072969 + 3 ^ 40 * 2227062 * 2
def baseEnd_2227062 : Nat := 1143553253363470843382935

theorem tailTrace_2227062 : CollatzResearch.WordTrace tailWord_2227062 prefixEnd_2227062 1143553253363470843382935 := by
  unfold tailWord_2227062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5076726516108887547084215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54151749505161467168898293 5076726516108887547084215)
  ·
    refine ⟨7615089774163331320626323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5076726516108887547084215 7615089774163331320626323)
    ·
      refine ⟨11422634661244996980939485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7615089774163331320626323 11422634661244996980939485)
      ·
        refine ⟨4283487997966873867852307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11422634661244996980939485 4283487997966873867852307)
        ·
          refine ⟨6425231996950310801778461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283487997966873867852307 6425231996950310801778461)
          ·
            refine ⟨2409461998856366550666923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6425231996950310801778461 2409461998856366550666923)
            ·
              refine ⟨3614192998284549826000385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409461998856366550666923 3614192998284549826000385)
              ·
                refine ⟨2710644748713412369500289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3614192998284549826000385 2710644748713412369500289)
                ·
                  refine ⟨2032983561535059277125217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710644748713412369500289 2032983561535059277125217)
                  ·
                    refine ⟨1524737671151294457843913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2032983561535059277125217 1524737671151294457843913)
                    ·
                      refine ⟨1143553253363470843382935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524737671151294457843913 1143553253363470843382935)
                      ·
                        rfl

theorem cell23_2227062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2227062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227062 prefixEnd_2227062 := by exact prefixLift 2227062
  have htrace : WordTrace (prefixWord ++ tailWord_2227062) baseStart_2227062 baseEnd_2227062 := by
    simpa [prefixWord, tailWord_2227062, baseEnd_2227062] using wordTrace_append hprefix tailTrace_2227062
  have hstable : (prefixWord ++ tailWord_2227062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227062).length < 2 ^ (prefixWord ++ tailWord_2227062).sum := by decide
  have hdescent : baseEnd_2227062 < baseStart_2227062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227097 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_2227097 : Nat := 118140960795 + 2227097 * 2 ^ 59
def prefixEnd_2227097 : Nat := 4983230072969 + 3 ^ 40 * 2227097 * 2
def baseEnd_2227097 : Nat := 1143571225186378206445273

theorem tailTrace_2227097 : CollatzResearch.WordTrace tailWord_2227097 prefixEnd_2227097 1143571225186378206445273 := by
  unfold tailWord_2227097
  simp only [CollatzResearch.WordTrace]
  refine ⟨81228900812615401730871545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54152600541743601153914363 81228900812615401730871545)
  ·
    refine ⟨60921675609461551298153659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81228900812615401730871545 60921675609461551298153659)
    ·
      refine ⟨91382513414192326947230489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60921675609461551298153659 91382513414192326947230489)
      ·
        refine ⟨68536885060644245210422867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91382513414192326947230489 68536885060644245210422867)
        ·
          refine ⟨102805327590966367815634301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68536885060644245210422867 102805327590966367815634301)
          ·
            refine ⟨38551997846612387930862863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102805327590966367815634301 38551997846612387930862863)
            ·
              refine ⟨57827996769918581896294295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38551997846612387930862863 57827996769918581896294295)
              ·
                refine ⟨86741995154877872844441443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57827996769918581896294295 86741995154877872844441443)
                ·
                  refine ⟨130112992732316809266662165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86741995154877872844441443 130112992732316809266662165)
                  ·
                    refine ⟨6099046534327350434374789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130112992732316809266662165 6099046534327350434374789)
                    ·
                      refine ⟨1143571225186378206445273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6099046534327350434374789 1143571225186378206445273)
                      ·
                        rfl

theorem cell23_2227097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_2227097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227097 prefixEnd_2227097 := by exact prefixLift 2227097
  have htrace : WordTrace (prefixWord ++ tailWord_2227097) baseStart_2227097 baseEnd_2227097 := by
    simpa [prefixWord, tailWord_2227097, baseEnd_2227097] using wordTrace_append hprefix tailTrace_2227097
  have hstable : (prefixWord ++ tailWord_2227097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227097).length < 2 ^ (prefixWord ++ tailWord_2227097).sum := by decide
  have hdescent : baseEnd_2227097 < baseStart_2227097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227104 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2227104 : Nat := 118140960795 + 2227104 * 2 ^ 59
def prefixEnd_2227104 : Nat := 4983230072969 + 3 ^ 40 * 2227104 * 2
def baseEnd_2227104 : Nat := 1143574819550959679057741

theorem tailTrace_2227104 : CollatzResearch.WordTrace tailWord_2227104 prefixEnd_2227104 1143574819550959679057741 := by
  unfold tailWord_2227104
  simp only [CollatzResearch.WordTrace]
  refine ⟨40614578061795020963188183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54152770749060027950917577 40614578061795020963188183)
  ·
    refine ⟨60921867092692531444782275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40614578061795020963188183 60921867092692531444782275)
    ·
      refine ⟨91382800639038797167173413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60921867092692531444782275 91382800639038797167173413)
      ·
        refine ⟨17134275119819774468845015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91382800639038797167173413 17134275119819774468845015)
        ·
          refine ⟨25701412679729661703267523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17134275119819774468845015 25701412679729661703267523)
          ·
            refine ⟨38552119019594492554901285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25701412679729661703267523 38552119019594492554901285)
            ·
              refine ⟨7228522316173967354043991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38552119019594492554901285 7228522316173967354043991)
              ·
                refine ⟨10842783474260951031065987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7228522316173967354043991 10842783474260951031065987)
                ·
                  refine ⟨16264175211391426546598981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10842783474260951031065987 16264175211391426546598981)
                  ·
                    refine ⟨3049532852135892477487309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16264175211391426546598981 3049532852135892477487309)
                    ·
                      refine ⟨1143574819550959679057741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049532852135892477487309 1143574819550959679057741)
                      ·
                        rfl

theorem cell23_2227104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2227104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227104 prefixEnd_2227104 := by exact prefixLift 2227104
  have htrace : WordTrace (prefixWord ++ tailWord_2227104) baseStart_2227104 baseEnd_2227104 := by
    simpa [prefixWord, tailWord_2227104, baseEnd_2227104] using wordTrace_append hprefix tailTrace_2227104
  have hstable : (prefixWord ++ tailWord_2227104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227104).length < 2 ^ (prefixWord ++ tailWord_2227104).sum := by decide
  have hdescent : baseEnd_2227104 < baseStart_2227104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227107 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 8]
def baseStart_2227107 : Nat := 118140960795 + 2227107 * 2 ^ 59
def prefixEnd_2227107 : Nat := 4983230072969 + 3 ^ 40 * 2227107 * 2
def baseEnd_2227107 : Nat := 127064039999213685257803

theorem tailTrace_2227107 : CollatzResearch.WordTrace tailWord_2227107 prefixEnd_2227107 127064039999213685257803 := by
  unfold tailWord_2227107
  simp only [CollatzResearch.WordTrace]
  refine ⟨81229265542579173438735575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54152843695052782292490383 81229265542579173438735575)
  ·
    refine ⟨121843898313868760158103363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81229265542579173438735575 121843898313868760158103363)
    ·
      refine ⟨182765847470803140237155045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121843898313868760158103363 182765847470803140237155045)
      ·
        refine ⟨34268596400775588794466571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182765847470803140237155045 34268596400775588794466571)
        ·
          refine ⟨51402894601163383191699857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34268596400775588794466571 51402894601163383191699857)
          ·
            refine ⟨38552170950872537393774893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51402894601163383191699857 38552170950872537393774893)
            ·
              refine ⟨14457064106577201522665585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38552170950872537393774893 14457064106577201522665585)
              ·
                refine ⟨10842798079932901141999189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14457064106577201522665585 10842798079932901141999189)
                ·
                  refine ⟨127064039999213685257803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10842798079932901141999189 127064039999213685257803)
                  ·
                    rfl

theorem cell23_2227107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 8].length) (baseStart_2227107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227107 prefixEnd_2227107 := by exact prefixLift 2227107
  have htrace : WordTrace (prefixWord ++ tailWord_2227107) baseStart_2227107 baseEnd_2227107 := by
    simpa [prefixWord, tailWord_2227107, baseEnd_2227107] using wordTrace_append hprefix tailTrace_2227107
  have hstable : (prefixWord ++ tailWord_2227107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227107).length < 2 ^ (prefixWord ++ tailWord_2227107).sum := by decide
  have hdescent : baseEnd_2227107 < baseStart_2227107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227127 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_2227127 : Nat := 118140960795 + 2227127 * 2 ^ 59
def prefixEnd_2227127 : Nat := 4983230072969 + 3 ^ 40 * 2227127 * 2
def baseEnd_2227127 : Nat := 1143586629606013089070135

theorem tailTrace_2227127 : CollatzResearch.WordTrace tailWord_2227127 prefixEnd_2227127 1143586629606013089070135 := by
  unfold tailWord_2227127
  simp only [CollatzResearch.WordTrace]
  refine ⟨81229995002506716854463635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54153330001671144569642423 81229995002506716854463635)
  ·
    refine ⟨121844992503760075281695453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81229995002506716854463635 121844992503760075281695453)
    ·
      refine ⟨45691872188910028230635795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121844992503760075281695453 45691872188910028230635795)
      ·
        refine ⟨68537808283365042345953693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45691872188910028230635795 68537808283365042345953693)
        ·
          refine ⟨25701678106261890879732635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68537808283365042345953693 25701678106261890879732635)
          ·
            refine ⟨38552517159392836319598953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25701678106261890879732635 38552517159392836319598953)
            ·
              refine ⟨28914387869544627239699215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38552517159392836319598953 28914387869544627239699215)
              ·
                refine ⟨43371581804316940859548823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28914387869544627239699215 43371581804316940859548823)
                ·
                  refine ⟨65057372706475411289323235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43371581804316940859548823 65057372706475411289323235)
                  ·
                    refine ⟨97586059059713116933984853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65057372706475411289323235 97586059059713116933984853)
                    ·
                      refine ⟨1143586629606013089070135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 97586059059713116933984853 1143586629606013089070135)
                      ·
                        rfl

theorem cell23_2227127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_2227127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227127 prefixEnd_2227127 := by exact prefixLift 2227127
  have htrace : WordTrace (prefixWord ++ tailWord_2227127) baseStart_2227127 baseEnd_2227127 := by
    simpa [prefixWord, tailWord_2227127, baseEnd_2227127] using wordTrace_append hprefix tailTrace_2227127
  have hstable : (prefixWord ++ tailWord_2227127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227127).length < 2 ^ (prefixWord ++ tailWord_2227127).sum := by decide
  have hdescent : baseEnd_2227127 < baseStart_2227127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227178 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_2227178 : Nat := 118140960795 + 2227178 * 2 ^ 59
def prefixEnd_2227178 : Nat := 4983230072969 + 3 ^ 40 * 2227178 * 2
def baseEnd_2227178 : Nat := 1143612817119392389532401

theorem tailTrace_2227178 : CollatzResearch.WordTrace tailWord_2227178 prefixEnd_2227178 1143612817119392389532401 := by
  unfold tailWord_2227178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20307963781330488141142547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54154570083547968376380125 20307963781330488141142547)
  ·
    refine ⟨30461945671995732211713821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20307963781330488141142547 30461945671995732211713821)
    ·
      refine ⟨11423229626998399579392683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30461945671995732211713821 11423229626998399579392683)
      ·
        refine ⟨17134844440497599369089025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11423229626998399579392683 17134844440497599369089025)
        ·
          refine ⟨12851133330373199526816769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17134844440497599369089025 12851133330373199526816769)
          ·
            refine ⟨9638349997779899645112577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12851133330373199526816769 9638349997779899645112577)
            ·
              refine ⟨7228762498334924733834433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9638349997779899645112577 7228762498334924733834433)
              ·
                refine ⟨5421571873751193550375825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228762498334924733834433 5421571873751193550375825)
                ·
                  refine ⟨4066178905313395162781869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5421571873751193550375825 4066178905313395162781869)
                  ·
                    refine ⟨1524817089492523186043201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4066178905313395162781869 1524817089492523186043201)
                    ·
                      refine ⟨1143612817119392389532401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524817089492523186043201 1143612817119392389532401)
                      ·
                        rfl

theorem cell23_2227178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_2227178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227178 prefixEnd_2227178 := by exact prefixLift 2227178
  have htrace : WordTrace (prefixWord ++ tailWord_2227178) baseStart_2227178 baseEnd_2227178 := by
    simpa [prefixWord, tailWord_2227178, baseEnd_2227178] using wordTrace_append hprefix tailTrace_2227178
  have hstable : (prefixWord ++ tailWord_2227178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227178).length < 2 ^ (prefixWord ++ tailWord_2227178).sum := by decide
  have hdescent : baseEnd_2227178 < baseStart_2227178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227185 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 1, 1, 3]
def baseStart_2227185 : Nat := 118140960795 + 2227185 * 2 ^ 59
def prefixEnd_2227185 : Nat := 4983230072969 + 3 ^ 40 * 2227185 * 2
def baseEnd_2227185 : Nat := 1143616411483973862144869

theorem tailTrace_2227185 : CollatzResearch.WordTrace tailWord_2227185 prefixEnd_2227185 1143616411483973862144869 := by
  unfold tailWord_2227185
  simp only [CollatzResearch.WordTrace]
  refine ⟨81232110436296592760075009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54154740290864395173383339 81232110436296592760075009)
  ·
    refine ⟨60924082827222444570056257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81232110436296592760075009 60924082827222444570056257)
    ·
      refine ⟨45693062120416833427542193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60924082827222444570056257 45693062120416833427542193)
      ·
        refine ⟨34269796590312625070656645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45693062120416833427542193 34269796590312625070656645)
        ·
          refine ⟨6425586860683617200748121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34269796590312625070656645 6425586860683617200748121)
          ·
            refine ⟨4819190145512712900561091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6425586860683617200748121 4819190145512712900561091)
            ·
              refine ⟨7228785218269069350841637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819190145512712900561091 7228785218269069350841637)
              ·
                refine ⟨1355397228425450503282807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7228785218269069350841637 1355397228425450503282807)
                ·
                  refine ⟨2033095842638175754924211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355397228425450503282807 2033095842638175754924211)
                  ·
                    refine ⟨3049643763957263632386317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2033095842638175754924211 3049643763957263632386317)
                    ·
                      refine ⟨1143616411483973862144869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049643763957263632386317 1143616411483973862144869)
                      ·
                        rfl

theorem cell23_2227185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_2227185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227185 prefixEnd_2227185 := by exact prefixLift 2227185
  have htrace : WordTrace (prefixWord ++ tailWord_2227185) baseStart_2227185 baseEnd_2227185 := by
    simpa [prefixWord, tailWord_2227185, baseEnd_2227185] using wordTrace_append hprefix tailTrace_2227185
  have hstable : (prefixWord ++ tailWord_2227185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227185).length < 2 ^ (prefixWord ++ tailWord_2227185).sum := by decide
  have hdescent : baseEnd_2227185 < baseStart_2227185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227194 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_2227194 : Nat := 118140960795 + 2227194 * 2 ^ 59
def prefixEnd_2227194 : Nat := 4983230072969 + 3 ^ 40 * 2227194 * 2
def baseEnd_2227194 : Nat := 1143621032809864326932327

theorem tailTrace_2227194 : CollatzResearch.WordTrace tailWord_2227194 prefixEnd_2227194 1143621032809864326932327 := by
  unfold tailWord_2227194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308109673315996824288159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54154959128842658198101757 20308109673315996824288159)
  ·
    refine ⟨30462164509973995236432239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20308109673315996824288159 30462164509973995236432239)
    ·
      refine ⟨45693246764960992854648359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30462164509973995236432239 45693246764960992854648359)
      ·
        refine ⟨68539870147441489281972539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45693246764960992854648359 68539870147441489281972539)
        ·
          refine ⟨102809805221162233922958809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68539870147441489281972539 102809805221162233922958809)
          ·
            refine ⟨77107353915871675442219107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102809805221162233922958809 77107353915871675442219107)
            ·
              refine ⟨115661030873807513163328661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77107353915871675442219107 115661030873807513163328661)
              ·
                refine ⟨5421610822209727179531031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115661030873807513163328661 5421610822209727179531031)
                ·
                  refine ⟨8132416233314590769296547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421610822209727179531031 8132416233314590769296547)
                  ·
                    refine ⟨12198624349971886153944821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8132416233314590769296547 12198624349971886153944821)
                    ·
                      refine ⟨1143621032809864326932327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12198624349971886153944821 1143621032809864326932327)
                      ·
                        rfl

theorem cell23_2227194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_2227194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227194 prefixEnd_2227194 := by exact prefixLift 2227194
  have htrace : WordTrace (prefixWord ++ tailWord_2227194) baseStart_2227194 baseEnd_2227194 := by
    simpa [prefixWord, tailWord_2227194, baseEnd_2227194] using wordTrace_append hprefix tailTrace_2227194
  have hstable : (prefixWord ++ tailWord_2227194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227194).length < 2 ^ (prefixWord ++ tailWord_2227194).sum := by decide
  have hdescent : baseEnd_2227194 < baseStart_2227194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227201 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2227201 : Nat := 118140960795 + 2227201 * 2 ^ 59
def prefixEnd_2227201 : Nat := 4983230072969 + 3 ^ 40 * 2227201 * 2
def baseEnd_2227201 : Nat := 381208209058148599848265

theorem tailTrace_2227201 : CollatzResearch.WordTrace tailWord_2227201 prefixEnd_2227201 381208209058148599848265 := by
  unfold tailWord_2227201
  simp only [CollatzResearch.WordTrace]
  refine ⟨81232694004238627492657457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54155129336159084995104971 81232694004238627492657457)
  ·
    refine ⟨60924520503178970619493093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81232694004238627492657457 60924520503178970619493093)
    ·
      refine ⟨11423347594346056991154955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60924520503178970619493093 11423347594346056991154955)
      ·
        refine ⟨17135021391519085486732433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11423347594346056991154955 17135021391519085486732433)
        ·
          refine ⟨12851266043639314115049325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17135021391519085486732433 12851266043639314115049325)
          ·
            refine ⟨4819224766364742793143497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12851266043639314115049325 4819224766364742793143497)
            ·
              refine ⟨3614418574773557094857623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4819224766364742793143497 3614418574773557094857623)
              ·
                refine ⟨5421627862160335642286435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614418574773557094857623 5421627862160335642286435)
                ·
                  refine ⟨8132441793240503463429653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421627862160335642286435 8132441793240503463429653)
                  ·
                    refine ⟨381208209058148599848265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8132441793240503463429653 381208209058148599848265)
                    ·
                      rfl

theorem cell23_2227201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2227201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227201 prefixEnd_2227201 := by exact prefixLift 2227201
  have htrace : WordTrace (prefixWord ++ tailWord_2227201) baseStart_2227201 baseEnd_2227201 := by
    simpa [prefixWord, tailWord_2227201, baseEnd_2227201] using wordTrace_append hprefix tailTrace_2227201
  have hstable : (prefixWord ++ tailWord_2227201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227201).length < 2 ^ (prefixWord ++ tailWord_2227201).sum := by decide
  have hdescent : baseEnd_2227201 < baseStart_2227201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227202 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2227202 : Nat := 118140960795 + 2227202 * 2 ^ 59
def prefixEnd_2227202 : Nat := 4983230072969 + 3 ^ 40 * 2227202 * 2
def baseEnd_2227202 : Nat := 1143625140655100295632291

theorem tailTrace_2227202 : CollatzResearch.WordTrace tailWord_2227202 prefixEnd_2227202 1143625140655100295632291 := by
  unfold tailWord_2227202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308182619308751165860965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54155153651490003108962573 20308182619308751165860965)
  ·
    refine ⟨3807784241120390843598931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20308182619308751165860965 3807784241120390843598931)
    ·
      refine ⟨5711676361680586265398397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807784241120390843598931 5711676361680586265398397)
      ·
        refine ⟨2141878635630219849524399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5711676361680586265398397 2141878635630219849524399)
        ·
          refine ⟨3212817953445329774286599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141878635630219849524399 3212817953445329774286599)
          ·
            refine ⟨4819226930167994661429899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212817953445329774286599 4819226930167994661429899)
            ·
              refine ⟨7228840395251991992144849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819226930167994661429899 7228840395251991992144849)
              ·
                refine ⟨5421630296438993994108637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228840395251991992144849 5421630296438993994108637)
                ·
                  refine ⟨2033111361164622747790739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5421630296438993994108637 2033111361164622747790739)
                  ·
                    refine ⟨3049667041746934121686109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2033111361164622747790739 3049667041746934121686109)
                    ·
                      refine ⟨1143625140655100295632291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049667041746934121686109 1143625140655100295632291)
                      ·
                        rfl

theorem cell23_2227202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2227202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227202 prefixEnd_2227202 := by exact prefixLift 2227202
  have htrace : WordTrace (prefixWord ++ tailWord_2227202) baseStart_2227202 baseEnd_2227202 := by
    simpa [prefixWord, tailWord_2227202, baseEnd_2227202] using wordTrace_append hprefix tailTrace_2227202
  have hstable : (prefixWord ++ tailWord_2227202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227202).length < 2 ^ (prefixWord ++ tailWord_2227202).sum := by decide
  have hdescent : baseEnd_2227202 < baseStart_2227202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227208 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_2227208 : Nat := 118140960795 + 2227208 * 2 ^ 59
def prefixEnd_2227208 : Nat := 4983230072969 + 3 ^ 40 * 2227208 * 2
def baseEnd_2227208 : Nat := 1143628221539027272157263

theorem tailTrace_2227208 : CollatzResearch.WordTrace tailWord_2227208 prefixEnd_2227208 1143628221539027272157263 := by
  unfold tailWord_2227208
  simp only [CollatzResearch.WordTrace]
  refine ⟨40616474657606633844081139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54155299543475511792108185 40616474657606633844081139)
  ·
    refine ⟨60924711986409950766121709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40616474657606633844081139 60924711986409950766121709)
    ·
      refine ⟨22846766994903731537295641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60924711986409950766121709 22846766994903731537295641)
      ·
        refine ⟨17135075246177798652971731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22846766994903731537295641 17135075246177798652971731)
        ·
          refine ⟨25702612869266697979457597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17135075246177798652971731 25702612869266697979457597)
          ·
            refine ⟨9638479825975011742296599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25702612869266697979457597 9638479825975011742296599)
            ·
              refine ⟨14457719738962517613444899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9638479825975011742296599 14457719738962517613444899)
              ·
                refine ⟨21686579608443776420167349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14457719738962517613444899 21686579608443776420167349)
                ·
                  refine ⟨2033116838291604039390689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21686579608443776420167349 2033116838291604039390689)
                  ·
                    refine ⟨1524837628718703029543017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2033116838291604039390689 1524837628718703029543017)
                    ·
                      refine ⟨1143628221539027272157263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524837628718703029543017 1143628221539027272157263)
                      ·
                        rfl

theorem cell23_2227208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_2227208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227208 prefixEnd_2227208 := by exact prefixLift 2227208
  have htrace : WordTrace (prefixWord ++ tailWord_2227208) baseStart_2227208 baseEnd_2227208 := by
    simpa [prefixWord, tailWord_2227208, baseEnd_2227208] using wordTrace_append hprefix tailTrace_2227208
  have hstable : (prefixWord ++ tailWord_2227208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227208).length < 2 ^ (prefixWord ++ tailWord_2227208).sum := by decide
  have hdescent : baseEnd_2227208 < baseStart_2227208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227211 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 3]
def baseStart_2227211 : Nat := 118140960795 + 2227211 * 2 ^ 59
def prefixEnd_2227211 : Nat := 4983230072969 + 3 ^ 40 * 2227211 * 2
def baseEnd_2227211 : Nat := 1143629761980990760419749

theorem tailTrace_2227211 : CollatzResearch.WordTrace tailWord_2227211 prefixEnd_2227211 1143629761980990760419749 := by
  unfold tailWord_2227211
  simp only [CollatzResearch.WordTrace]
  refine ⟨81233058734202399200521487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54155372489468266133680991 81233058734202399200521487)
  ·
    refine ⟨121849588101303598800782231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81233058734202399200521487 121849588101303598800782231)
    ·
      refine ⟨182774382151955398201173347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121849588101303598800782231 182774382151955398201173347)
      ·
        refine ⟨274161573227933097301760021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182774382151955398201173347 274161573227933097301760021)
        ·
          refine ⟨12851323745059363936020001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 274161573227933097301760021 12851323745059363936020001)
          ·
            refine ⟨9638492808794522952015001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12851323745059363936020001 9638492808794522952015001)
            ·
              refine ⟨7228869606595892214011251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9638492808794522952015001 7228869606595892214011251)
              ·
                refine ⟨10843304409893838321016877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7228869606595892214011251 10843304409893838321016877)
                ·
                  refine ⟨4066239153710189370381329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10843304409893838321016877 4066239153710189370381329)
                  ·
                    refine ⟨3049679365282642027785997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4066239153710189370381329 3049679365282642027785997)
                    ·
                      refine ⟨1143629761980990760419749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049679365282642027785997 1143629761980990760419749)
                      ·
                        rfl

theorem cell23_2227211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 3].length) (baseStart_2227211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227211 prefixEnd_2227211 := by exact prefixLift 2227211
  have htrace : WordTrace (prefixWord ++ tailWord_2227211) baseStart_2227211 baseEnd_2227211 := by
    simpa [prefixWord, tailWord_2227211, baseEnd_2227211] using wordTrace_append hprefix tailTrace_2227211
  have hstable : (prefixWord ++ tailWord_2227211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227211).length < 2 ^ (prefixWord ++ tailWord_2227211).sum := by decide
  have hdescent : baseEnd_2227211 < baseStart_2227211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227221 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2227221 : Nat := 118140960795 + 2227221 * 2 ^ 59
def prefixEnd_2227221 : Nat := 4983230072969 + 3 ^ 40 * 2227221 * 2
def baseEnd_2227221 : Nat := 1143634896787535721294703

theorem tailTrace_2227221 : CollatzResearch.WordTrace tailWord_2227221 prefixEnd_2227221 1143634896787535721294703 := by
  unfold tailWord_2227221
  simp only [CollatzResearch.WordTrace]
  refine ⟨81233423464166170908385517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54155615642777447272257011 81233423464166170908385517)
  ·
    refine ⟨30462533799062314090644569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81233423464166170908385517 30462533799062314090644569)
    ·
      refine ⟨22846900349296735567983427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30462533799062314090644569 22846900349296735567983427)
      ·
        refine ⟨34270350523945103351975141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22846900349296735567983427 34270350523945103351975141)
        ·
          refine ⟨6425690723239706878495339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34270350523945103351975141 6425690723239706878495339)
          ·
            refine ⟨9638536084859560317743009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6425690723239706878495339 9638536084859560317743009)
            ·
              refine ⟨7228902063644670238307257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9638536084859560317743009 7228902063644670238307257)
              ·
                refine ⟨5421676547733502678730443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228902063644670238307257 5421676547733502678730443)
                ·
                  refine ⟨8132514821600254018095665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421676547733502678730443 8132514821600254018095665)
                  ·
                    refine ⟨6099386116200190513571749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8132514821600254018095665 6099386116200190513571749)
                    ·
                      refine ⟨1143634896787535721294703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6099386116200190513571749 1143634896787535721294703)
                      ·
                        rfl

theorem cell23_2227221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2227221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227221 prefixEnd_2227221 := by exact prefixLift 2227221
  have htrace : WordTrace (prefixWord ++ tailWord_2227221) baseStart_2227221 baseEnd_2227221 := by
    simpa [prefixWord, tailWord_2227221, baseEnd_2227221] using wordTrace_append hprefix tailTrace_2227221
  have hstable : (prefixWord ++ tailWord_2227221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227221).length < 2 ^ (prefixWord ++ tailWord_2227221).sum := by decide
  have hdescent : baseEnd_2227221 < baseStart_2227221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227225 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 1, 2, 2]
def baseStart_2227225 : Nat := 118140960795 + 2227225 * 2 ^ 59
def prefixEnd_2227225 : Nat := 4983230072969 + 3 ^ 40 * 2227225 * 2
def baseEnd_2227225 : Nat := 1143636950710153705644685

theorem tailTrace_2227225 : CollatzResearch.WordTrace tailWord_2227225 prefixEnd_2227225 1143636950710153705644685 := by
  unfold tailWord_2227225
  simp only [CollatzResearch.WordTrace]
  refine ⟨81233569356151679591531129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54155712904101119727687419 81233569356151679591531129)
  ·
    refine ⟨60925177017113759693648347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81233569356151679591531129 60925177017113759693648347)
    ·
      refine ⟨91387765525670639540472521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60925177017113759693648347 91387765525670639540472521)
      ·
        refine ⟨68540824144252979655354391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91387765525670639540472521 68540824144252979655354391)
        ·
          refine ⟨102811236216379469483031587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68540824144252979655354391 102811236216379469483031587)
          ·
            refine ⟨154216854324569204224547381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102811236216379469483031587 154216854324569204224547381)
            ·
              refine ⟨14457830092928362896051317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154216854324569204224547381 14457830092928362896051317)
              ·
                refine ⟨1355421571212034021504811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14457830092928362896051317 1355421571212034021504811)
                ·
                  refine ⟨2033132356818051032257217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355421571212034021504811 2033132356818051032257217)
                  ·
                    refine ⟨1524849267613538274192913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2033132356818051032257217 1524849267613538274192913)
                    ·
                      refine ⟨1143636950710153705644685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524849267613538274192913 1143636950710153705644685)
                      ·
                        rfl

theorem cell23_2227225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_2227225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227225 prefixEnd_2227225 := by exact prefixLift 2227225
  have htrace : WordTrace (prefixWord ++ tailWord_2227225) baseStart_2227225 baseEnd_2227225 := by
    simpa [prefixWord, tailWord_2227225, baseEnd_2227225] using wordTrace_append hprefix tailTrace_2227225
  have hstable : (prefixWord ++ tailWord_2227225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227225).length < 2 ^ (prefixWord ++ tailWord_2227225).sum := by decide
  have hdescent : baseEnd_2227225 < baseStart_2227225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227242 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2227242 : Nat := 118140960795 + 2227242 * 2 ^ 59
def prefixEnd_2227242 : Nat := 4983230072969 + 3 ^ 40 * 2227242 * 2
def baseEnd_2227242 : Nat := 1143645679881280139132107

theorem tailTrace_2227242 : CollatzResearch.WordTrace tailWord_2227242 prefixEnd_2227242 1143645679881280139132107 := by
  unfold tailWord_2227242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308547349272522873724995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54156126264726727663266653 20308547349272522873724995)
  ·
    refine ⟨30462821023908784310587493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20308547349272522873724995 30462821023908784310587493)
    ·
      refine ⟨5711778941982897058235155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30462821023908784310587493 5711778941982897058235155)
      ·
        refine ⟨8567668412974345587352733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5711778941982897058235155 8567668412974345587352733)
        ·
          refine ⟨3212875654865379595257275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8567668412974345587352733 3212875654865379595257275)
          ·
            refine ⟨4819313482298069392885913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212875654865379595257275 4819313482298069392885913)
            ·
              refine ⟨3614485111723552044664435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4819313482298069392885913 3614485111723552044664435)
              ·
                refine ⟨5421727667585328066996653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614485111723552044664435 5421727667585328066996653)
                ·
                  refine ⟨2033147875344498025123745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5421727667585328066996653 2033147875344498025123745)
                  ·
                    refine ⟨1524860906508373518842809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2033147875344498025123745 1524860906508373518842809)
                    ·
                      refine ⟨1143645679881280139132107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1524860906508373518842809 1143645679881280139132107)
                      ·
                        rfl

theorem cell23_2227242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2227242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227242 prefixEnd_2227242 := by exact prefixLift 2227242
  have htrace : WordTrace (prefixWord ++ tailWord_2227242) baseStart_2227242 baseEnd_2227242 := by
    simpa [prefixWord, tailWord_2227242, baseEnd_2227242] using wordTrace_append hprefix tailTrace_2227242
  have hstable : (prefixWord ++ tailWord_2227242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227242).length < 2 ^ (prefixWord ++ tailWord_2227242).sum := by decide
  have hdescent : baseEnd_2227242 < baseStart_2227242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227252 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2227252 : Nat := 118140960795 + 2227252 * 2 ^ 59
def prefixEnd_2227252 : Nat := 4983230072969 + 3 ^ 40 * 2227252 * 2
def baseEnd_2227252 : Nat := 381216938229275033335687

theorem tailTrace_2227252 : CollatzResearch.WordTrace tailWord_2227252 prefixEnd_2227252 381216938229275033335687 := by
  unfold tailWord_2227252
  simp only [CollatzResearch.WordTrace]
  refine ⟨40617277063526931601382005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54156369418035908801842673 40617277063526931601382005)
  ·
    refine ⟨3807869724705649837629563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40617277063526931601382005 3807869724705649837629563)
    ·
      refine ⟨5711804587058474756444345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807869724705649837629563 5711804587058474756444345)
      ·
        refine ⟨4283853440293856067333259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5711804587058474756444345 4283853440293856067333259)
        ·
          refine ⟨6425780160440784100999889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283853440293856067333259 6425780160440784100999889)
          ·
            refine ⟨4819335120330588075749917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6425780160440784100999889 4819335120330588075749917)
            ·
              refine ⟨1807250670123970528406219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4819335120330588075749917 1807250670123970528406219)
              ·
                refine ⟨2710876005185955792609329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807250670123970528406219 2710876005185955792609329)
                ·
                  refine ⟨2033157003889466844456997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710876005185955792609329 2033157003889466844456997)
                  ·
                    refine ⟨381216938229275033335687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033157003889466844456997 381216938229275033335687)
                    ·
                      rfl

theorem cell23_2227252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2227252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227252 prefixEnd_2227252 := by exact prefixLift 2227252
  have htrace : WordTrace (prefixWord ++ tailWord_2227252) baseStart_2227252 baseEnd_2227252 := by
    simpa [prefixWord, tailWord_2227252, baseEnd_2227252] using wordTrace_append hprefix tailTrace_2227252
  have hstable : (prefixWord ++ tailWord_2227252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227252).length < 2 ^ (prefixWord ++ tailWord_2227252).sum := by decide
  have hdescent : baseEnd_2227252 < baseStart_2227252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227258 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_2227258 : Nat := 118140960795 + 2227258 * 2 ^ 59
def prefixEnd_2227258 : Nat := 4983230072969 + 3 ^ 40 * 2227258 * 2
def baseEnd_2227258 : Nat := 1143653895571752076532033

theorem tailTrace_2227258 : CollatzResearch.WordTrace tailWord_2227258 prefixEnd_2227258 1143653895571752076532033 := by
  unfold tailWord_2227258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308693241258031556870607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54156515310021417484988285 20308693241258031556870607)
  ·
    refine ⟨30463039861887047335305911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20308693241258031556870607 30463039861887047335305911)
    ·
      refine ⟨45694559792830571002958867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30463039861887047335305911 45694559792830571002958867)
      ·
        refine ⟨68541839689245856504438301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45694559792830571002958867 68541839689245856504438301)
        ·
          refine ⟨25703189883467196189164363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68541839689245856504438301 25703189883467196189164363)
          ·
            refine ⟨38554784825200794283746545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25703189883467196189164363 38554784825200794283746545)
            ·
              refine ⟨28916088618900595712809909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38554784825200794283746545 28916088618900595712809909)
              ·
                refine ⟨2710883308021930848075929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28916088618900595712809909 2710883308021930848075929)
                ·
                  refine ⟨2033162481016448136056947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710883308021930848075929 2033162481016448136056947)
                  ·
                    refine ⟨3049743721524672204085421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2033162481016448136056947 3049743721524672204085421)
                    ·
                      refine ⟨1143653895571752076532033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049743721524672204085421 1143653895571752076532033)
                      ·
                        rfl

theorem cell23_2227258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_2227258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227258 prefixEnd_2227258 := by exact prefixLift 2227258
  have htrace : WordTrace (prefixWord ++ tailWord_2227258) baseStart_2227258 baseEnd_2227258 := by
    simpa [prefixWord, tailWord_2227258, baseEnd_2227258] using wordTrace_append hprefix tailTrace_2227258
  have hstable : (prefixWord ++ tailWord_2227258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227258).length < 2 ^ (prefixWord ++ tailWord_2227258).sum := by decide
  have hdescent : baseEnd_2227258 < baseStart_2227258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227265 : List Nat := [1, 2, 5, 1, 4, 1, 2, 7]
def baseStart_2227265 : Nat := 118140960795 + 2227265 * 2 ^ 59
def prefixEnd_2227265 : Nat := 4983230072969 + 3 ^ 40 * 2227265 * 2
def baseEnd_2227265 : Nat := 42357684812456798116463

theorem tailTrace_2227265 : CollatzResearch.WordTrace tailWord_2227265 prefixEnd_2227265 42357684812456798116463 := by
  unfold tailWord_2227265
  simp only [CollatzResearch.WordTrace]
  refine ⟨81235028276006766422987249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54156685517337844281991499 81235028276006766422987249)
  ·
    refine ⟨60926271207005074817240437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81235028276006766422987249 60926271207005074817240437)
    ·
      refine ⟨5711837925656725764116291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60926271207005074817240437 5711837925656725764116291)
      ·
        refine ⟨8567756888485088646174437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5711837925656725764116291 8567756888485088646174437)
        ·
          refine ⟨1606454416590954121157707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8567756888485088646174437 1606454416590954121157707)
          ·
            refine ⟨2409681624886431181736561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606454416590954121157707 2409681624886431181736561)
            ·
              refine ⟨1807261218664823386302421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409681624886431181736561 1807261218664823386302421)
              ·
                refine ⟨42357684812456798116463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1807261218664823386302421 42357684812456798116463)
                ·
                  rfl

theorem cell23_2227265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 7].length) (baseStart_2227265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227265 prefixEnd_2227265 := by exact prefixLift 2227265
  have htrace : WordTrace (prefixWord ++ tailWord_2227265) baseStart_2227265 baseEnd_2227265 := by
    simpa [prefixWord, tailWord_2227265, baseEnd_2227265] using wordTrace_append hprefix tailTrace_2227265
  have hstable : (prefixWord ++ tailWord_2227265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227265).length < 2 ^ (prefixWord ++ tailWord_2227265).sum := by decide
  have hdescent : baseEnd_2227265 < baseStart_2227265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227274 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_2227274 : Nat := 118140960795 + 2227274 * 2 ^ 59
def prefixEnd_2227274 : Nat := 4983230072969 + 3 ^ 40 * 2227274 * 2
def baseEnd_2227274 : Nat := 381220703754074671310653

theorem tailTrace_2227274 : CollatzResearch.WordTrace tailWord_2227274 prefixEnd_2227274 381220703754074671310653 := by
  unfold tailWord_2227274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308839133243540240016219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54156904355316107306709917 20308839133243540240016219)
  ·
    refine ⟨30463258699865310360024329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20308839133243540240016219 30463258699865310360024329)
    ·
      refine ⟨22847444024898982770018247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30463258699865310360024329 22847444024898982770018247)
      ·
        refine ⟨34271166037348474155027371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22847444024898982770018247 34271166037348474155027371)
        ·
          refine ⟨51406749056022711232541057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34271166037348474155027371 51406749056022711232541057)
          ·
            refine ⟨38555061792017033424405793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51406749056022711232541057 38555061792017033424405793)
            ·
              refine ⟨28916296344012775068304345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38555061792017033424405793 28916296344012775068304345)
              ·
                refine ⟨21687222258009581301228259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28916296344012775068304345 21687222258009581301228259)
                ·
                  refine ⟨32530833387014371951842389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21687222258009581301228259 32530833387014371951842389)
                  ·
                    refine ⟨381220703754074671310653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32530833387014371951842389 381220703754074671310653)
                    ·
                      rfl

theorem cell23_2227274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_2227274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227274 prefixEnd_2227274 := by exact prefixLift 2227274
  have htrace : WordTrace (prefixWord ++ tailWord_2227274) baseStart_2227274 baseEnd_2227274 := by
    simpa [prefixWord, tailWord_2227274, baseEnd_2227274] using wordTrace_append hprefix tailTrace_2227274
  have hstable : (prefixWord ++ tailWord_2227274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227274).length < 2 ^ (prefixWord ++ tailWord_2227274).sum := by decide
  have hdescent : baseEnd_2227274 < baseStart_2227274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227301 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_2227301 : Nat := 118140960795 + 2227301 * 2 ^ 59
def prefixEnd_2227301 : Nat := 4983230072969 + 3 ^ 40 * 2227301 * 2
def baseEnd_2227301 : Nat := 1143675975239895408294335

theorem tailTrace_2227301 : CollatzResearch.WordTrace tailWord_2227301 prefixEnd_2227301 1143675975239895408294335 := by
  unfold tailWord_2227301
  simp only [CollatzResearch.WordTrace]
  refine ⟨81236341303876344571297757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54157560869250896380865171 81236341303876344571297757)
  ·
    refine ⟨30463627988953629214236659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81236341303876344571297757 30463627988953629214236659)
    ·
      refine ⟨45695441983430443821354989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30463627988953629214236659 45695441983430443821354989)
      ·
        refine ⟨17135790743786416433008121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45695441983430443821354989 17135790743786416433008121)
        ·
          refine ⟨12851843057839812324756091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17135790743786416433008121 12851843057839812324756091)
          ·
            refine ⟨19277764586759718487134137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12851843057839812324756091 19277764586759718487134137)
            ·
              refine ⟨14458323440069788865350603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19277764586759718487134137 14458323440069788865350603)
              ·
                refine ⟨21687485160104683298025905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14458323440069788865350603 21687485160104683298025905)
                ·
                  refine ⟨16265613870078512473519429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21687485160104683298025905 16265613870078512473519429)
                  ·
                    refine ⟨3049802600639721088784893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16265613870078512473519429 3049802600639721088784893)
                    ·
                      refine ⟨1143675975239895408294335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3049802600639721088784893 1143675975239895408294335)
                      ·
                        rfl

theorem cell23_2227301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_2227301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227301 prefixEnd_2227301 := by exact prefixLift 2227301
  have htrace : WordTrace (prefixWord ++ tailWord_2227301) baseStart_2227301 baseEnd_2227301 := by
    simpa [prefixWord, tailWord_2227301, baseEnd_2227301] using wordTrace_append hprefix tailTrace_2227301
  have hstable : (prefixWord ++ tailWord_2227301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227301).length < 2 ^ (prefixWord ++ tailWord_2227301).sum := by decide
  have hdescent : baseEnd_2227301 < baseStart_2227301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227338 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_2227338 : Nat := 118140960795 + 2227338 * 2 ^ 59
def prefixEnd_2227338 : Nat := 4983230072969 + 3 ^ 40 * 2227338 * 2
def baseEnd_2227338 : Nat := 127077219336012418170185

theorem tailTrace_2227338 : CollatzResearch.WordTrace tailWord_2227338 prefixEnd_2227338 127077219336012418170185 := by
  unfold tailWord_2227338
  simp only [CollatzResearch.WordTrace]
  refine ⟨20309422701185574972598667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54158460536494866593596445 20309422701185574972598667)
  ·
    refine ⟨30464134051778362458898001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20309422701185574972598667 30464134051778362458898001)
    ·
      refine ⟨22848100538833771844173501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30464134051778362458898001 22848100538833771844173501)
      ·
        refine ⟨8568037702062664441565063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22848100538833771844173501 8568037702062664441565063)
        ·
          refine ⟨12852056553093996662347595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568037702062664441565063 12852056553093996662347595)
          ·
            refine ⟨19278084829640994993521393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12852056553093996662347595 19278084829640994993521393)
            ·
              refine ⟨14458563622230746245141045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19278084829640994993521393 14458563622230746245141045)
              ·
                refine ⟨1355490339584132460481973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14458563622230746245141045 1355490339584132460481973)
                ·
                  refine ⟨127077219336012418170185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355490339584132460481973 127077219336012418170185)
                  ·
                    rfl

theorem cell23_2227338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_2227338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227338 prefixEnd_2227338 := by exact prefixLift 2227338
  have htrace : WordTrace (prefixWord ++ tailWord_2227338) baseStart_2227338 baseEnd_2227338 := by
    simpa [prefixWord, tailWord_2227338, baseEnd_2227338] using wordTrace_append hprefix tailTrace_2227338
  have hstable : (prefixWord ++ tailWord_2227338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227338).length < 2 ^ (prefixWord ++ tailWord_2227338).sum := by decide
  have hdescent : baseEnd_2227338 < baseStart_2227338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227361 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2227361 : Nat := 118140960795 + 2227361 * 2 ^ 59
def prefixEnd_2227361 : Nat := 4983230072969 + 3 ^ 40 * 2227361 * 2
def baseEnd_2227361 : Nat := 1143706784079165173544059

theorem tailTrace_2227361 : CollatzResearch.WordTrace tailWord_2227361 prefixEnd_2227361 1143706784079165173544059 := by
  unfold tailWord_2227361
  simp only [CollatzResearch.WordTrace]
  refine ⟨81238529683658974818481937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54159019789105983212321291 81238529683658974818481937)
  ·
    refine ⟨60928897262744231113861453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81238529683658974818481937 60928897262744231113861453)
    ·
      refine ⟨22848336473529086667698045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60928897262744231113861453 22848336473529086667698045)
      ·
        refine ⟨8568126177573407500386767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22848336473529086667698045 8568126177573407500386767)
        ·
          refine ⟨12852189266360111250580151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568126177573407500386767 12852189266360111250580151)
          ·
            refine ⟨19278283899540166875870227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12852189266360111250580151 19278283899540166875870227)
            ·
              refine ⟨28917425849310250313805341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19278283899540166875870227 28917425849310250313805341)
              ·
                refine ⟨10844034693491343867677003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28917425849310250313805341 10844034693491343867677003)
                ·
                  refine ⟨16266052040237015801515505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10844034693491343867677003 16266052040237015801515505)
                  ·
                    refine ⟨12199539030177761851136629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16266052040237015801515505 12199539030177761851136629)
                    ·
                      refine ⟨1143706784079165173544059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12199539030177761851136629 1143706784079165173544059)
                      ·
                        rfl

theorem cell23_2227361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2227361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227361 prefixEnd_2227361 := by exact prefixLift 2227361
  have htrace : WordTrace (prefixWord ++ tailWord_2227361) baseStart_2227361 baseEnd_2227361 := by
    simpa [prefixWord, tailWord_2227361, baseEnd_2227361] using wordTrace_append hprefix tailTrace_2227361
  have hstable : (prefixWord ++ tailWord_2227361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227361).length < 2 ^ (prefixWord ++ tailWord_2227361).sum := by decide
  have hdescent : baseEnd_2227361 < baseStart_2227361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227388 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2227388 : Nat := 118140960795 + 2227388 * 2 ^ 59
def prefixEnd_2227388 : Nat := 4983230072969 + 3 ^ 40 * 2227388 * 2
def baseEnd_2227388 : Nat := 1143720648056836567906435

theorem tailTrace_2227388 : CollatzResearch.WordTrace tailWord_2227388 prefixEnd_2227388 1143720648056836567906435 := by
  unfold tailWord_2227388
  simp only [CollatzResearch.WordTrace]
  refine ⟨40619757227280579214857409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54159676303040772286476545 40619757227280579214857409)
  ·
    refine ⟨30464817920460434411143057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40619757227280579214857409 30464817920460434411143057)
    ·
      refine ⟨22848613440345325808357293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30464817920460434411143057 22848613440345325808357293)
      ·
        refine ⟨8568230040129497178133985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22848613440345325808357293 8568230040129497178133985)
        ·
          refine ⟨6426172530097122883600489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8568230040129497178133985 6426172530097122883600489)
          ·
            refine ⟨4819629397572842162700367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6426172530097122883600489 4819629397572842162700367)
            ·
              refine ⟨7229444096359263244050551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819629397572842162700367 7229444096359263244050551)
              ·
                refine ⟨10844166144538894866075827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7229444096359263244050551 10844166144538894866075827)
                ·
                  refine ⟨16266249216808342299113741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10844166144538894866075827 16266249216808342299113741)
                  ·
                    refine ⟨6099843456303128362167653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16266249216808342299113741 6099843456303128362167653)
                    ·
                      refine ⟨1143720648056836567906435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6099843456303128362167653 1143720648056836567906435)
                      ·
                        rfl

theorem cell23_2227388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2227388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227388 prefixEnd_2227388 := by exact prefixLift 2227388
  have htrace : WordTrace (prefixWord ++ tailWord_2227388) baseStart_2227388 baseEnd_2227388 := by
    simpa [prefixWord, tailWord_2227388, baseEnd_2227388] using wordTrace_append hprefix tailTrace_2227388
  have hstable : (prefixWord ++ tailWord_2227388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227388).length < 2 ^ (prefixWord ++ tailWord_2227388).sum := by decide
  have hdescent : baseEnd_2227388 < baseStart_2227388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227415 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 1, 4]
def baseStart_2227415 : Nat := 118140960795 + 2227415 * 2 ^ 59
def prefixEnd_2227415 : Nat := 4983230072969 + 3 ^ 40 * 2227415 * 2
def baseEnd_2227415 : Nat := 381244837344835987422937

theorem tailTrace_2227415 : CollatzResearch.WordTrace tailWord_2227415 prefixEnd_2227415 381244837344835987422937 := by
  unfold tailWord_2227415
  simp only [CollatzResearch.WordTrace]
  refine ⟨81240499225463342040947699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54160332816975561360631799 81240499225463342040947699)
  ·
    refine ⟨121860748838195013061421549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81240499225463342040947699 121860748838195013061421549)
    ·
      refine ⟨45697780814323129898033081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121860748838195013061421549 45697780814323129898033081)
      ·
        refine ⟨34273335610742347423524811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45697780814323129898033081 34273335610742347423524811)
        ·
          refine ⟨51410003416113521135287217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34273335610742347423524811 51410003416113521135287217)
          ·
            refine ⟨38557502562085140851465413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51410003416113521135287217 38557502562085140851465413)
            ·
              refine ⟨7229531730390963909649765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38557502562085140851465413 7229531730390963909649765)
              ·
                refine ⟨1355537199448305733059331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7229531730390963909649765 1355537199448305733059331)
                ·
                  refine ⟨2033305799172458599588997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355537199448305733059331 2033305799172458599588997)
                  ·
                    refine ⟨381244837344835987422937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033305799172458599588997 381244837344835987422937)
                    ·
                      rfl

theorem cell23_2227415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_2227415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227415 prefixEnd_2227415 := by exact prefixLift 2227415
  have htrace : WordTrace (prefixWord ++ tailWord_2227415) baseStart_2227415 baseEnd_2227415 := by
    simpa [prefixWord, tailWord_2227415, baseEnd_2227415] using wordTrace_append hprefix tailTrace_2227415
  have hstable : (prefixWord ++ tailWord_2227415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227415).length < 2 ^ (prefixWord ++ tailWord_2227415).sum := by decide
  have hdescent : baseEnd_2227415 < baseStart_2227415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227465 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 2, 3, 2]
def baseStart_2227465 : Nat := 118140960795 + 2227465 * 2 ^ 59
def prefixEnd_2227465 : Nat := 4983230072969 + 3 ^ 40 * 2227465 * 2
def baseEnd_2227465 : Nat := 1143760186067232766643581

theorem tailTrace_2227465 : CollatzResearch.WordTrace tailWord_2227465 prefixEnd_2227465 1143760186067232766643581 := by
  unfold tailWord_2227465
  simp only [CollatzResearch.WordTrace]
  refine ⟨81242322875282200580267849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54161548583521467053511899 81242322875282200580267849)
  ·
    refine ⟨60931742156461650435200887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81242322875282200580267849 60931742156461650435200887)
    ·
      refine ⟨91397613234692475652801331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60931742156461650435200887 91397613234692475652801331)
      ·
        refine ⟨137096419852038713479201997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91397613234692475652801331 137096419852038713479201997)
        ·
          refine ⟨51411157444514517554700749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137096419852038713479201997 51411157444514517554700749)
          ·
            refine ⟨19279184041692944083012781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51411157444514517554700749 19279184041692944083012781)
            ·
              refine ⟨7229694015634854031129793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19279184041692944083012781 7229694015634854031129793)
              ·
                refine ⟨5422270511726140523347345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7229694015634854031129793 5422270511726140523347345)
                ·
                  refine ⟨4066702883794605392510509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422270511726140523347345 4066702883794605392510509)
                  ·
                    refine ⟨1525013581422977022191441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4066702883794605392510509 1525013581422977022191441)
                    ·
                      refine ⟨1143760186067232766643581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525013581422977022191441 1143760186067232766643581)
                      ·
                        rfl

theorem cell23_2227465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 3, 2].length) (baseStart_2227465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227465 prefixEnd_2227465 := by exact prefixLift 2227465
  have htrace : WordTrace (prefixWord ++ tailWord_2227465) baseStart_2227465 baseEnd_2227465 := by
    simpa [prefixWord, tailWord_2227465, baseEnd_2227465] using wordTrace_append hprefix tailTrace_2227465
  have hstable : (prefixWord ++ tailWord_2227465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227465).length < 2 ^ (prefixWord ++ tailWord_2227465).sum := by decide
  have hdescent : baseEnd_2227465 < baseStart_2227465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227528 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_2227528 : Nat := 118140960795 + 2227528 * 2 ^ 59
def prefixEnd_2227528 : Nat := 4983230072969 + 3 ^ 40 * 2227528 * 2
def baseEnd_2227528 : Nat := 1143792535348466020155791

theorem tailTrace_2227528 : CollatzResearch.WordTrace tailWord_2227528 prefixEnd_2227528 1143792535348466020155791 := by
  unfold tailWord_2227528
  simp only [CollatzResearch.WordTrace]
  refine ⟨40622310337026981169905619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54163080449369308226540825 40622310337026981169905619)
  ·
    refine ⟨60933465505540471754858429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40622310337026981169905619 60933465505540471754858429)
    ·
      refine ⟨22850049564577676908071911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60933465505540471754858429 22850049564577676908071911)
      ·
        refine ⟨34275074346866515362107867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22850049564577676908071911 34275074346866515362107867)
        ·
          refine ⟨51412611520299773043161801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34275074346866515362107867 51412611520299773043161801)
          ·
            refine ⟨38559458640224829782371351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51412611520299773043161801 38559458640224829782371351)
            ·
              refine ⟨57839187960337244673557027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38559458640224829782371351 57839187960337244673557027)
              ·
                refine ⟨86758781940505867010335541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57839187960337244673557027 86758781940505867010335541)
                ·
                  refine ⟨8133635806922425032218957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86758781940505867010335541 8133635806922425032218957)
                  ·
                    refine ⟨3050113427595909387082109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8133635806922425032218957 3050113427595909387082109)
                    ·
                      refine ⟨1143792535348466020155791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3050113427595909387082109 1143792535348466020155791)
                      ·
                        rfl

theorem cell23_2227528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_2227528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227528 prefixEnd_2227528 := by exact prefixLift 2227528
  have htrace : WordTrace (prefixWord ++ tailWord_2227528) baseStart_2227528 baseEnd_2227528 := by
    simpa [prefixWord, tailWord_2227528, baseEnd_2227528] using wordTrace_append hprefix tailTrace_2227528
  have hstable : (prefixWord ++ tailWord_2227528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227528).length < 2 ^ (prefixWord ++ tailWord_2227528).sum := by decide
  have hdescent : baseEnd_2227528 < baseStart_2227528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227648 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2227648 : Nat := 118140960795 + 2227648 * 2 ^ 59
def prefixEnd_2227648 : Nat := 4983230072969 + 3 ^ 40 * 2227648 * 2
def baseEnd_2227648 : Nat := 1143854153027005550655239

theorem tailTrace_2227648 : CollatzResearch.WordTrace tailWord_2227648 prefixEnd_2227648 1143854153027005550655239 := by
  unfold tailWord_2227648
  simp only [CollatzResearch.WordTrace]
  refine ⟨40624498716809611417089799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54165998289079481889453065 40624498716809611417089799)
  ·
    refine ⟨60936748075214417125634699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40624498716809611417089799 60936748075214417125634699)
    ·
      refine ⟨91405122112821625688452049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60936748075214417125634699 91405122112821625688452049)
      ·
        refine ⟨68553841584616219266339037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91405122112821625688452049 68553841584616219266339037)
        ·
          refine ⟨25707690594231082224877139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68553841584616219266339037 25707690594231082224877139)
          ·
            refine ⟨38561535891346623337315709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25707690594231082224877139 38561535891346623337315709)
            ·
              refine ⟨14460575959254983751493391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38561535891346623337315709 14460575959254983751493391)
              ·
                refine ⟨21690863938882475627240087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14460575959254983751493391 21690863938882475627240087)
                ·
                  refine ⟨32536295908323713440860131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21690863938882475627240087 32536295908323713440860131)
                  ·
                    refine ⟨48804443862485570161290197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32536295908323713440860131 48804443862485570161290197)
                    ·
                      refine ⟨1143854153027005550655239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48804443862485570161290197 1143854153027005550655239)
                      ·
                        rfl

theorem cell23_2227648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2227648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227648 prefixEnd_2227648 := by exact prefixLift 2227648
  have htrace : WordTrace (prefixWord ++ tailWord_2227648) baseStart_2227648 baseEnd_2227648 := by
    simpa [prefixWord, tailWord_2227648, baseEnd_2227648] using wordTrace_append hprefix tailTrace_2227648
  have hstable : (prefixWord ++ tailWord_2227648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227648).length < 2 ^ (prefixWord ++ tailWord_2227648).sum := by decide
  have hdescent : baseEnd_2227648 < baseStart_2227648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227693 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2227693 : Nat := 118140960795 + 2227693 * 2 ^ 59
def prefixEnd_2227693 : Nat := 4983230072969 + 3 ^ 40 * 2227693 * 2
def baseEnd_2227693 : Nat := 127097473295161986065837

theorem tailTrace_2227693 : CollatzResearch.WordTrace tailWord_2227693 prefixEnd_2227693 127097473295161986065837 := by
  unfold tailWord_2227693
  simp only [CollatzResearch.WordTrace]
  refine ⟨81250638718456195519567733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54167092478970797013045155 81250638718456195519567733)
  ·
    refine ⟨7617247379855268329959475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81250638718456195519567733 7617247379855268329959475)
    ·
      refine ⟨11425871069782902494939213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7617247379855268329959475 11425871069782902494939213)
      ·
        refine ⟨4284701651168588435602205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11425871069782902494939213 4284701651168588435602205)
        ·
          refine ⟨1606763119188220663350827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4284701651168588435602205 1606763119188220663350827)
          ·
            refine ⟨2410144678782330995026241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606763119188220663350827 2410144678782330995026241)
            ·
              refine ⟨1807608509086748246269681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410144678782330995026241 1807608509086748246269681)
              ·
                refine ⟨1355706381815061184702261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1807608509086748246269681 1355706381815061184702261)
                ·
                  refine ⟨127097473295161986065837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355706381815061184702261 127097473295161986065837)
                  ·
                    rfl

theorem cell23_2227693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2227693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227693 prefixEnd_2227693 := by exact prefixLift 2227693
  have htrace : WordTrace (prefixWord ++ tailWord_2227693) baseStart_2227693 baseEnd_2227693 := by
    simpa [prefixWord, tailWord_2227693, baseEnd_2227693] using wordTrace_append hprefix tailTrace_2227693
  have hstable : (prefixWord ++ tailWord_2227693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227693).length < 2 ^ (prefixWord ++ tailWord_2227693).sum := by decide
  have hdescent : baseEnd_2227693 < baseStart_2227693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227726 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_2227726 : Nat := 118140960795 + 2227726 * 2 ^ 59
def prefixEnd_2227726 : Nat := 4983230072969 + 3 ^ 40 * 2227726 * 2
def baseEnd_2227726 : Nat := 1143894204518056245479881

theorem tailTrace_2227726 : CollatzResearch.WordTrace tailWord_2227726 prefixEnd_2227726 1143894204518056245479881 := by
  unfold tailWord_2227726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10156480290917080269439879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54167894884891094770346021 10156480290917080269439879)
  ·
    refine ⟨15234720436375620404159819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10156480290917080269439879 15234720436375620404159819)
    ·
      refine ⟨22852080654563430606239729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15234720436375620404159819 22852080654563430606239729)
      ·
        refine ⟨17139060490922572954679797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22852080654563430606239729 17139060490922572954679797)
        ·
          refine ⟨1606786921023991214501231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17139060490922572954679797 1606786921023991214501231)
          ·
            refine ⟨2410180381535986821751847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606786921023991214501231 2410180381535986821751847)
            ·
              refine ⟨3615270572303980232627771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410180381535986821751847 3615270572303980232627771)
              ·
                refine ⟨5422905858455970348941657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615270572303980232627771 5422905858455970348941657)
                ·
                  refine ⟨4067179393841977761706243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422905858455970348941657 4067179393841977761706243)
                  ·
                    refine ⟨6100769090762966642559365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4067179393841977761706243 6100769090762966642559365)
                    ·
                      refine ⟨1143894204518056245479881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6100769090762966642559365 1143894204518056245479881)
                      ·
                        rfl

theorem cell23_2227726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_2227726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227726 prefixEnd_2227726 := by exact prefixLift 2227726
  have htrace : WordTrace (prefixWord ++ tailWord_2227726) baseStart_2227726 baseEnd_2227726 := by
    simpa [prefixWord, tailWord_2227726, baseEnd_2227726] using wordTrace_append hprefix tailTrace_2227726
  have hstable : (prefixWord ++ tailWord_2227726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227726).length < 2 ^ (prefixWord ++ tailWord_2227726).sum := by decide
  have hdescent : baseEnd_2227726 < baseStart_2227726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227736 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 1, 4]
def baseStart_2227736 : Nat := 118140960795 + 2227736 * 2 ^ 59
def prefixEnd_2227736 : Nat := 4983230072969 + 3 ^ 40 * 2227736 * 2
def baseEnd_2227736 : Nat := 381299779774867068784945

theorem tailTrace_2227736 : CollatzResearch.WordTrace tailWord_2227736 prefixEnd_2227736 381299779774867068784945 := by
  unfold tailWord_2227736
  simp only [CollatzResearch.WordTrace]
  refine ⟨40626103528650206931691531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54168138038200275908922041 40626103528650206931691531)
  ·
    refine ⟨60939155292975310397537297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40626103528650206931691531 60939155292975310397537297)
    ·
      refine ⟨45704366469731482798152973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60939155292975310397537297 45704366469731482798152973)
      ·
        refine ⟨17139137426149306049307365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45704366469731482798152973 17139137426149306049307365)
        ·
          refine ⟨3213588267402994884245131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17139137426149306049307365 3213588267402994884245131)
          ·
            refine ⟨4820382401104492326367697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3213588267402994884245131 4820382401104492326367697)
            ·
              refine ⟨3615286800828369244775773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4820382401104492326367697 3615286800828369244775773)
              ·
                refine ⟨1355732550310638466790915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3615286800828369244775773 1355732550310638466790915)
                ·
                  refine ⟨2033598825465957700186373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355732550310638466790915 2033598825465957700186373)
                  ·
                    refine ⟨381299779774867068784945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033598825465957700186373 381299779774867068784945)
                    ·
                      rfl

theorem cell23_2227736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_2227736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227736 prefixEnd_2227736 := by exact prefixLift 2227736
  have htrace : WordTrace (prefixWord ++ tailWord_2227736) baseStart_2227736 baseEnd_2227736 := by
    simpa [prefixWord, tailWord_2227736, baseEnd_2227736] using wordTrace_append hprefix tailTrace_2227736
  have hstable : (prefixWord ++ tailWord_2227736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227736).length < 2 ^ (prefixWord ++ tailWord_2227736).sum := by decide
  have hdescent : baseEnd_2227736 < baseStart_2227736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227766 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_2227766 : Nat := 118140960795 + 2227766 * 2 ^ 59
def prefixEnd_2227766 : Nat := 4983230072969 + 3 ^ 40 * 2227766 * 2
def baseEnd_2227766 : Nat := 127101638193804009886633

theorem tailTrace_2227766 : CollatzResearch.WordTrace tailWord_2227766 prefixEnd_2227766 127101638193804009886633 := by
  unfold tailWord_2227766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078331327949483061685947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54168867498127819324650101 5078331327949483061685947)
  ·
    refine ⟨7617496991924224592528921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5078331327949483061685947 7617496991924224592528921)
    ·
      refine ⟨5713122743943168444396691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7617496991924224592528921 5713122743943168444396691)
      ·
        refine ⟨8569684115914752666595037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5713122743943168444396691 8569684115914752666595037)
        ·
          refine ⟨3213631543468032249973139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8569684115914752666595037 3213631543468032249973139)
          ·
            refine ⟨4820447315202048374959709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3213631543468032249973139 4820447315202048374959709)
            ·
              refine ⟨1807667743200768140609891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4820447315202048374959709 1807667743200768140609891)
              ·
                refine ⟨2711501614801152210914837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807667743200768140609891 2711501614801152210914837)
                ·
                  refine ⟨127101638193804009886633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2711501614801152210914837 127101638193804009886633)
                  ·
                    rfl

theorem cell23_2227766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_2227766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227766 prefixEnd_2227766 := by exact prefixLift 2227766
  have htrace : WordTrace (prefixWord ++ tailWord_2227766) baseStart_2227766 baseEnd_2227766 := by
    simpa [prefixWord, tailWord_2227766, baseEnd_2227766] using wordTrace_append hprefix tailTrace_2227766
  have hstable : (prefixWord ++ tailWord_2227766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227766).length < 2 ^ (prefixWord ++ tailWord_2227766).sum := by decide
  have hdescent : baseEnd_2227766 < baseStart_2227766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227785 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_2227785 : Nat := 118140960795 + 2227785 * 2 ^ 59
def prefixEnd_2227785 : Nat := 4983230072969 + 3 ^ 40 * 2227785 * 2
def baseEnd_2227785 : Nat := 1143924499876671514642109

theorem tailTrace_2227785 : CollatzResearch.WordTrace tailWord_2227785 prefixEnd_2227785 1143924499876671514642109 := by
  unfold tailWord_2227785
  simp only [CollatzResearch.WordTrace]
  refine ⟨81253994234122895231916809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54169329489415263487944539 81253994234122895231916809)
  ·
    refine ⟨60940495675592171423937607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81253994234122895231916809 60940495675592171423937607)
    ·
      refine ⟨91410743513388257135906411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60940495675592171423937607 91410743513388257135906411)
      ·
        refine ⟨137116115270082385703859617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91410743513388257135906411 137116115270082385703859617)
        ·
          refine ⟨102837086452561789277894713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137116115270082385703859617 102837086452561789277894713)
          ·
            refine ⟨77127814839421341958421035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102837086452561789277894713 77127814839421341958421035)
            ·
              refine ⟨115691722259132012937631553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77127814839421341958421035 115691722259132012937631553)
              ·
                refine ⟨86768791694349009703223665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115691722259132012937631553 86768791694349009703223665)
                ·
                  refine ⟨65076593770761757277417749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86768791694349009703223665 65076593770761757277417749)
                  ·
                    refine ⟨3050465333004457372378957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65076593770761757277417749 3050465333004457372378957)
                    ·
                      refine ⟨1143924499876671514642109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3050465333004457372378957 1143924499876671514642109)
                      ·
                        rfl

theorem cell23_2227785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_2227785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227785 prefixEnd_2227785 := by exact prefixLift 2227785
  have htrace : WordTrace (prefixWord ++ tailWord_2227785) baseStart_2227785 baseEnd_2227785 := by
    simpa [prefixWord, tailWord_2227785, baseEnd_2227785] using wordTrace_append hprefix tailTrace_2227785
  have hstable : (prefixWord ++ tailWord_2227785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227785).length < 2 ^ (prefixWord ++ tailWord_2227785).sum := by decide
  have hdescent : baseEnd_2227785 < baseStart_2227785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227826 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_2227826 : Nat := 118140960795 + 2227826 * 2 ^ 59
def prefixEnd_2227826 : Nat := 4983230072969 + 3 ^ 40 * 2227826 * 2
def baseEnd_2227826 : Nat := 381315184194501951409807

theorem tailTrace_2227826 : CollatzResearch.WordTrace tailWord_2227826 prefixEnd_2227826 381315184194501951409807 := by
  unfold tailWord_2227826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20313872406743589808539833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54170326417982906156106221 20313872406743589808539833)
  ·
    refine ⟨15235404305057692356404875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20313872406743589808539833 15235404305057692356404875)
    ·
      refine ⟨22853106457586538534607313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15235404305057692356404875 22853106457586538534607313)
      ·
        refine ⟨17139829843189903900955485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22853106457586538534607313 17139829843189903900955485)
        ·
          refine ⟨6427436191196213962858307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17139829843189903900955485 6427436191196213962858307)
          ·
            refine ⟨9641154286794320944287461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6427436191196213962858307 9641154286794320944287461)
            ·
              refine ⟨1807716428773935177053899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9641154286794320944287461 1807716428773935177053899)
              ·
                refine ⟨2711574643160902765580849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807716428773935177053899 2711574643160902765580849)
                ·
                  refine ⟨2033680982370677074185637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2711574643160902765580849 2033680982370677074185637)
                  ·
                    refine ⟨381315184194501951409807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033680982370677074185637 381315184194501951409807)
                    ·
                      rfl

theorem cell23_2227826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_2227826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227826 prefixEnd_2227826 := by exact prefixLift 2227826
  have htrace : WordTrace (prefixWord ++ tailWord_2227826) baseStart_2227826 baseEnd_2227826 := by
    simpa [prefixWord, tailWord_2227826, baseEnd_2227826] using wordTrace_append hprefix tailTrace_2227826
  have hstable : (prefixWord ++ tailWord_2227826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227826).length < 2 ^ (prefixWord ++ tailWord_2227826).sum := by decide
  have hdescent : baseEnd_2227826 < baseStart_2227826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227855 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_2227855 : Nat := 118140960795 + 2227855 * 2 ^ 59
def prefixEnd_2227855 : Nat := 4983230072969 + 3 ^ 40 * 2227855 * 2
def baseEnd_2227855 : Nat := 1143960443522486240766787

theorem tailTrace_2227855 : CollatzResearch.WordTrace tailWord_2227855 prefixEnd_2227855 1143960443522486240766787 := by
  unfold tailWord_2227855
  simp only [CollatzResearch.WordTrace]
  refine ⟨81256547343869297186965019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54171031562579531457976679 81256547343869297186965019)
  ·
    refine ⟨121884821015803945780447529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81256547343869297186965019 121884821015803945780447529)
    ·
      refine ⟨91413615761852959335335647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121884821015803945780447529 91413615761852959335335647)
      ·
        refine ⟨137120423642779439003003471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91413615761852959335335647 137120423642779439003003471)
        ·
          refine ⟨205680635464169158504505207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137120423642779439003003471 205680635464169158504505207)
          ·
            refine ⟨308520953196253737756757811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205680635464169158504505207 308520953196253737756757811)
            ·
              refine ⟨462781429794380606635136717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308520953196253737756757811 462781429794380606635136717)
              ·
                refine ⟨173543036172892727488176269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462781429794380606635136717 173543036172892727488176269)
                ·
                  refine ⟨65078638564834772808066101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173543036172892727488176269 65078638564834772808066101)
                  ·
                    refine ⟨6101122365453259950756197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65078638564834772808066101 6101122365453259950756197)
                    ·
                      refine ⟨1143960443522486240766787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6101122365453259950756197 1143960443522486240766787)
                      ·
                        rfl

theorem cell23_2227855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_2227855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227855 prefixEnd_2227855 := by exact prefixLift 2227855
  have htrace : WordTrace (prefixWord ++ tailWord_2227855) baseStart_2227855 baseEnd_2227855 := by
    simpa [prefixWord, tailWord_2227855, baseEnd_2227855] using wordTrace_append hprefix tailTrace_2227855
  have hstable : (prefixWord ++ tailWord_2227855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227855).length < 2 ^ (prefixWord ++ tailWord_2227855).sum := by decide
  have hdescent : baseEnd_2227855 < baseStart_2227855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227872 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2227872 : Nat := 118140960795 + 2227872 * 2 ^ 59
def prefixEnd_2227872 : Nat := 4983230072969 + 3 ^ 40 * 2227872 * 2
def baseEnd_2227872 : Nat := 1143969172693612674254209

theorem tailTrace_2227872 : CollatzResearch.WordTrace tailWord_2227872 prefixEnd_2227872 1143969172693612674254209 := by
  unfold tailWord_2227872
  simp only [CollatzResearch.WordTrace]
  refine ⟨40628583692403854545166935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54171444923205139393555913 40628583692403854545166935)
  ·
    refine ⟨60942875538605781817750403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40628583692403854545166935 60942875538605781817750403)
    ·
      refine ⟨91414313307908672726625605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60942875538605781817750403 91414313307908672726625605)
      ·
        refine ⟨17140183745232876136242301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91414313307908672726625605 17140183745232876136242301)
        ·
          refine ⟨6427568904462328551090863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17140183745232876136242301 6427568904462328551090863)
          ·
            refine ⟨9641353356693492826636295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6427568904462328551090863 9641353356693492826636295)
            ·
              refine ⟨14462030035040239239954443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9641353356693492826636295 14462030035040239239954443)
              ·
                refine ⟨21693045052560358859931665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14462030035040239239954443 21693045052560358859931665)
                ·
                  refine ⟨16269783789420269144948749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21693045052560358859931665 16269783789420269144948749)
                  ·
                    refine ⟨6101168921032600929355781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16269783789420269144948749 6101168921032600929355781)
                    ·
                      refine ⟨1143969172693612674254209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6101168921032600929355781 1143969172693612674254209)
                      ·
                        rfl

theorem cell23_2227872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2227872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227872 prefixEnd_2227872 := by exact prefixLift 2227872
  have htrace : WordTrace (prefixWord ++ tailWord_2227872) baseStart_2227872 baseEnd_2227872 := by
    simpa [prefixWord, tailWord_2227872, baseEnd_2227872] using wordTrace_append hprefix tailTrace_2227872
  have hstable : (prefixWord ++ tailWord_2227872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227872).length < 2 ^ (prefixWord ++ tailWord_2227872).sum := by decide
  have hdescent : baseEnd_2227872 < baseStart_2227872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227929 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 5]
def baseStart_2227929 : Nat := 118140960795 + 2227929 * 2 ^ 59
def prefixEnd_2227929 : Nat := 4983230072969 + 3 ^ 40 * 2227929 * 2
def baseEnd_2227929 : Nat := 127110937898990994582383

theorem tailTrace_2227929 : CollatzResearch.WordTrace tailWord_2227929 prefixEnd_2227929 127110937898990994582383 := by
  unfold tailWord_2227929
  simp only [CollatzResearch.WordTrace]
  refine ⟨81259246345601207825158841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54172830897067471883439227 81259246345601207825158841)
  ·
    refine ⟨60944434759200905868869131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81259246345601207825158841 60944434759200905868869131)
    ·
      refine ⟨91416652138801358803303697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60944434759200905868869131 91416652138801358803303697)
      ·
        refine ⟨68562489104101019102477773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91416652138801358803303697 68562489104101019102477773)
        ·
          refine ⟨25710933414037882163429165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68562489104101019102477773 25710933414037882163429165)
          ·
            refine ⟨9641600030264205811285937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25710933414037882163429165 9641600030264205811285937)
            ·
              refine ⟨7231200022698154358464453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9641600030264205811285937 7231200022698154358464453)
              ·
                refine ⟨1355850004255903942212085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7231200022698154358464453 1355850004255903942212085)
                ·
                  refine ⟨127110937898990994582383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355850004255903942212085 127110937898990994582383)
                  ·
                    rfl

theorem cell23_2227929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 5].length) (baseStart_2227929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227929 prefixEnd_2227929 := by exact prefixLift 2227929
  have htrace : WordTrace (prefixWord ++ tailWord_2227929) baseStart_2227929 baseEnd_2227929 := by
    simpa [prefixWord, tailWord_2227929, baseEnd_2227929] using wordTrace_append hprefix tailTrace_2227929
  have hstable : (prefixWord ++ tailWord_2227929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227929).length < 2 ^ (prefixWord ++ tailWord_2227929).sum := by decide
  have hdescent : baseEnd_2227929 < baseStart_2227929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227979 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 4, 4, 2]
def baseStart_2227979 : Nat := 118140960795 + 2227979 * 2 ^ 59
def prefixEnd_2227979 : Nat := 4983230072969 + 3 ^ 40 * 2227979 * 2
def baseEnd_2227979 : Nat := 1144024115123643755616217

theorem tailTrace_2227979 : CollatzResearch.WordTrace tailWord_2227979 prefixEnd_2227979 1144024115123643755616217 := by
  unfold tailWord_2227979
  simp only [CollatzResearch.WordTrace]
  refine ⟨81261069995420066364478991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54174046663613377576319327 81261069995420066364478991)
  ·
    refine ⟨121891604993130099546718487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81261069995420066364478991 121891604993130099546718487)
    ·
      refine ⟨182837407489695149320077731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121891604993130099546718487 182837407489695149320077731)
      ·
        refine ⟨274256111234542723980116597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182837407489695149320077731 274256111234542723980116597)
        ·
          refine ⟨25711510428238380373135931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 274256111234542723980116597 25711510428238380373135931)
          ·
            refine ⟨38567265642357570559703897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25711510428238380373135931 38567265642357570559703897)
            ·
              refine ⟨28925449231768177919777923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38567265642357570559703897 28925449231768177919777923)
              ·
                refine ⟨43388173847652266879666885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28925449231768177919777923 43388173847652266879666885)
                ·
                  refine ⟨8135282596434800039937541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43388173847652266879666885 8135282596434800039937541)
                  ·
                    refine ⟨1525365486831525007488289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8135282596434800039937541 1525365486831525007488289)
                    ·
                      refine ⟨1144024115123643755616217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525365486831525007488289 1144024115123643755616217)
                      ·
                        rfl

theorem cell23_2227979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4, 2].length) (baseStart_2227979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227979 prefixEnd_2227979 := by exact prefixLift 2227979
  have htrace : WordTrace (prefixWord ++ tailWord_2227979) baseStart_2227979 baseEnd_2227979 := by
    simpa [prefixWord, tailWord_2227979, baseEnd_2227979] using wordTrace_append hprefix tailTrace_2227979
  have hstable : (prefixWord ++ tailWord_2227979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227979).length < 2 ^ (prefixWord ++ tailWord_2227979).sum := by decide
  have hdescent : baseEnd_2227979 < baseStart_2227979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227986 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2227986 : Nat := 118140960795 + 2227986 * 2 ^ 59
def prefixEnd_2227986 : Nat := 4983230072969 + 3 ^ 40 * 2227986 * 2
def baseEnd_2227986 : Nat := 1144027709488225228228685

theorem tailTrace_2227986 : CollatzResearch.WordTrace tailWord_2227986 prefixEnd_2227986 1144027709488225228228685 := by
  unfold tailWord_2227986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315331326598676639995953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54174216870929804373322541 20315331326598676639995953)
  ·
    refine ⟨15236498494949007479996965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20315331326598676639995953 15236498494949007479996965)
    ·
      refine ⟨2856843467802938902499431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15236498494949007479996965 2856843467802938902499431)
      ·
        refine ⟨4285265201704408353749147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856843467802938902499431 4285265201704408353749147)
        ·
          refine ⟨6427897802556612530623721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285265201704408353749147 6427897802556612530623721)
          ·
            refine ⟨4820923351917459397967791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6427897802556612530623721 4820923351917459397967791)
            ·
              refine ⟨7231385027876189096951687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4820923351917459397967791 7231385027876189096951687)
              ·
                refine ⟨10847077541814283645427531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7231385027876189096951687 10847077541814283645427531)
                ·
                  refine ⟨16270616312721425468141297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10847077541814283645427531 16270616312721425468141297)
                  ·
                    refine ⟨12202962234541069101105973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16270616312721425468141297 12202962234541069101105973)
                    ·
                      refine ⟨1144027709488225228228685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12202962234541069101105973 1144027709488225228228685)
                      ·
                        rfl

theorem cell23_2227986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2227986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227986 prefixEnd_2227986 := by exact prefixLift 2227986
  have htrace : WordTrace (prefixWord ++ tailWord_2227986) baseStart_2227986 baseEnd_2227986 := by
    simpa [prefixWord, tailWord_2227986, baseEnd_2227986] using wordTrace_append hprefix tailTrace_2227986
  have hstable : (prefixWord ++ tailWord_2227986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227986).length < 2 ^ (prefixWord ++ tailWord_2227986).sum := by decide
  have hdescent : baseEnd_2227986 < baseStart_2227986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227992 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2227992 : Nat := 118140960795 + 2227992 * 2 ^ 59
def prefixEnd_2227992 : Nat := 4983230072969 + 3 ^ 40 * 2227992 * 2
def baseEnd_2227992 : Nat := 1144030790372152204753657

theorem tailTrace_2227992 : CollatzResearch.WordTrace tailWord_2227992 prefixEnd_2227992 1144030790372152204753657 := by
  unfold tailWord_2227992
  simp only [CollatzResearch.WordTrace]
  refine ⟨40630772072186484792351115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54174362762915313056468153 40630772072186484792351115)
  ·
    refine ⟨60946158108279727188526673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40630772072186484792351115 60946158108279727188526673)
    ·
      refine ⟨45709618581209795391395005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60946158108279727188526673 45709618581209795391395005)
      ·
        refine ⟨17141106967953673271773127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45709618581209795391395005 17141106967953673271773127)
        ·
          refine ⟨25711660451930509907659691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17141106967953673271773127 25711660451930509907659691)
          ·
            refine ⟨38567490677895764861489537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25711660451930509907659691 38567490677895764861489537)
            ·
              refine ⟨28925618008421823646117153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38567490677895764861489537 28925618008421823646117153)
              ·
                refine ⟨21694213506316367734587865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28925618008421823646117153 21694213506316367734587865)
                ·
                  refine ⟨16270660129737275800940899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21694213506316367734587865 16270660129737275800940899)
                  ·
                    refine ⟨24405990194605913701411349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16270660129737275800940899 24405990194605913701411349)
                    ·
                      refine ⟨1144030790372152204753657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24405990194605913701411349 1144030790372152204753657)
                      ·
                        rfl

theorem cell23_2227992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2227992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227992 prefixEnd_2227992 := by exact prefixLift 2227992
  have htrace : WordTrace (prefixWord ++ tailWord_2227992) baseStart_2227992 baseEnd_2227992 := by
    simpa [prefixWord, tailWord_2227992, baseEnd_2227992] using wordTrace_append hprefix tailTrace_2227992
  have hstable : (prefixWord ++ tailWord_2227992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227992).length < 2 ^ (prefixWord ++ tailWord_2227992).sum := by decide
  have hdescent : baseEnd_2227992 < baseStart_2227992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227999 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_2227999 : Nat := 118140960795 + 2227999 * 2 ^ 59
def prefixEnd_2227999 : Nat := 4983230072969 + 3 ^ 40 * 2227999 * 2
def baseEnd_2227999 : Nat := 1144034384736733677366125

theorem tailTrace_2227999 : CollatzResearch.WordTrace tailWord_2227999 prefixEnd_2227999 1144034384736733677366125 := by
  unfold tailWord_2227999
  simp only [CollatzResearch.WordTrace]
  refine ⟨81261799455347609780207051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54174532970231739853471367 81261799455347609780207051)
  ·
    refine ⟨121892699183021414670310577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81261799455347609780207051 121892699183021414670310577)
    ·
      refine ⟨91419524387266061002732933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121892699183021414670310577 91419524387266061002732933)
      ·
        refine ⟨17141160822612386438012425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91419524387266061002732933 17141160822612386438012425)
        ·
          refine ⟨12855870616959289828509319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17141160822612386438012425 12855870616959289828509319)
          ·
            refine ⟨19283805925438934742763979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12855870616959289828509319 19283805925438934742763979)
            ·
              refine ⟨28925708888158402114145969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19283805925438934742763979 28925708888158402114145969)
              ·
                refine ⟨21694281666118801585609477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28925708888158402114145969 21694281666118801585609477)
                ·
                  refine ⟨4067677812397275297301777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21694281666118801585609477 4067677812397275297301777)
                  ·
                    refine ⟨3050758359297956472976333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4067677812397275297301777 3050758359297956472976333)
                    ·
                      refine ⟨1144034384736733677366125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3050758359297956472976333 1144034384736733677366125)
                      ·
                        rfl

theorem cell23_2227999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_2227999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2227999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2227999 prefixEnd_2227999 := by exact prefixLift 2227999
  have htrace : WordTrace (prefixWord ++ tailWord_2227999) baseStart_2227999 baseEnd_2227999 := by
    simpa [prefixWord, tailWord_2227999, baseEnd_2227999] using wordTrace_append hprefix tailTrace_2227999
  have hstable : (prefixWord ++ tailWord_2227999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227999).length < 2 ^ (prefixWord ++ tailWord_2227999).sum := by decide
  have hdescent : baseEnd_2227999 < baseStart_2227999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228040 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 1, 4]
def baseStart_2228040 : Nat := 118140960795 + 2228040 * 2 ^ 59
def prefixEnd_2228040 : Nat := 4983230072969 + 3 ^ 40 * 2228040 * 2
def baseEnd_2228040 : Nat := 381351812481189338984479

theorem tailTrace_2228040 : CollatzResearch.WordTrace tailWord_2228040 prefixEnd_2228040 381351812481189338984479 := by
  unfold tailWord_2228040
  simp only [CollatzResearch.WordTrace]
  refine ⟨40631647424099536891224787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54175529898799382521633049 40631647424099536891224787)
  ·
    refine ⟨60947471136149305336837181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40631647424099536891224787 60947471136149305336837181)
    ·
      refine ⟨22855301676055989501313943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60947471136149305336837181 22855301676055989501313943)
      ·
        refine ⟨34282952514083984251970915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22855301676055989501313943 34282952514083984251970915)
        ·
          refine ⟨51424428771125976377956373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34282952514083984251970915 51424428771125976377956373)
          ·
            refine ⟨2410520098646530142716705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51424428771125976377956373 2410520098646530142716705)
            ·
              refine ⟨1807890073984897607037529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410520098646530142716705 1807890073984897607037529)
              ·
                refine ⟨1355917555488673205278147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1807890073984897607037529 1355917555488673205278147)
                ·
                  refine ⟨2033876333233009807917221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355917555488673205278147 2033876333233009807917221)
                  ·
                    refine ⟨381351812481189338984479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033876333233009807917221 381351812481189338984479)
                    ·
                      rfl

theorem cell23_2228040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_2228040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228040 prefixEnd_2228040 := by exact prefixLift 2228040
  have htrace : WordTrace (prefixWord ++ tailWord_2228040) baseStart_2228040 baseEnd_2228040 := by
    simpa [prefixWord, tailWord_2228040, baseEnd_2228040] using wordTrace_append hprefix tailTrace_2228040
  have hstable : (prefixWord ++ tailWord_2228040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228040).length < 2 ^ (prefixWord ++ tailWord_2228040).sum := by decide
  have hdescent : baseEnd_2228040 < baseStart_2228040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228049 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_2228049 : Nat := 118140960795 + 2228049 * 2 ^ 59
def prefixEnd_2228049 : Nat := 4983230072969 + 3 ^ 40 * 2228049 * 2
def baseEnd_2228049 : Nat := 381353352923152827246965

theorem tailTrace_2228049 : CollatzResearch.WordTrace tailWord_2228049 prefixEnd_2228049 381353352923152827246965 := by
  unfold tailWord_2228049
  simp only [CollatzResearch.WordTrace]
  refine ⟨81263623105166468319527201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54175748736777645546351467 81263623105166468319527201)
  ·
    refine ⟨60947717328874851239645401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81263623105166468319527201 60947717328874851239645401)
    ·
      refine ⟨45710787996656138429734051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60947717328874851239645401 45710787996656138429734051)
      ·
        refine ⟨68566181994984207644601077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45710787996656138429734051 68566181994984207644601077)
        ·
          refine ⟨6428079562029769466681351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68566181994984207644601077 6428079562029769466681351)
          ·
            refine ⟨9642119343044654200022027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6428079562029769466681351 9642119343044654200022027)
            ·
              refine ⟨14463179014566981300033041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9642119343044654200022027 14463179014566981300033041)
              ·
                refine ⟨10847384260925235975024781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14463179014566981300033041 10847384260925235975024781)
                ·
                  refine ⟨4067769097846963490634293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10847384260925235975024781 4067769097846963490634293)
                  ·
                    refine ⟨381353352923152827246965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4067769097846963490634293 381353352923152827246965)
                    ·
                      rfl

theorem cell23_2228049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_2228049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228049 prefixEnd_2228049 := by exact prefixLift 2228049
  have htrace : WordTrace (prefixWord ++ tailWord_2228049) baseStart_2228049 baseEnd_2228049 := by
    simpa [prefixWord, tailWord_2228049, baseEnd_2228049] using wordTrace_append hprefix tailTrace_2228049
  have hstable : (prefixWord ++ tailWord_2228049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228049).length < 2 ^ (prefixWord ++ tailWord_2228049).sum := by decide
  have hdescent : baseEnd_2228049 < baseStart_2228049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228066 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2228066 : Nat := 118140960795 + 2228066 * 2 ^ 59
def prefixEnd_2228066 : Nat := 4983230072969 + 3 ^ 40 * 2228066 * 2
def baseEnd_2228066 : Nat := 381356262646861638409439

theorem tailTrace_2228066 : CollatzResearch.WordTrace tailWord_2228066 prefixEnd_2228066 381356262646861638409439 := by
  unfold tailWord_2228066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20316060786526220055724013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54176162097403253481930701 20316060786526220055724013)
  ·
    refine ⟨7618522794947332520896505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20316060786526220055724013 7618522794947332520896505)
    ·
      refine ⟨5713892096210499390672379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7618522794947332520896505 5713892096210499390672379)
      ·
        refine ⟨8570838144315749086008569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5713892096210499390672379 8570838144315749086008569)
        ·
          refine ⟨6428128608236811814506427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8570838144315749086008569 6428128608236811814506427)
          ·
            refine ⟨9642192912355217721759641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6428128608236811814506427 9642192912355217721759641)
            ·
              refine ⟨7231644684266413291319731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9642192912355217721759641 7231644684266413291319731)
              ·
                refine ⟨10847467026399619936979597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7231644684266413291319731 10847467026399619936979597)
                ·
                  refine ⟨4067800134899857476367349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10847467026399619936979597 4067800134899857476367349)
                  ·
                    refine ⟨381356262646861638409439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4067800134899857476367349 381356262646861638409439)
                    ·
                      rfl

theorem cell23_2228066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2228066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228066 prefixEnd_2228066 := by exact prefixLift 2228066
  have htrace : WordTrace (prefixWord ++ tailWord_2228066) baseStart_2228066 baseEnd_2228066 := by
    simpa [prefixWord, tailWord_2228066, baseEnd_2228066] using wordTrace_append hprefix tailTrace_2228066
  have hstable : (prefixWord ++ tailWord_2228066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228066).length < 2 ^ (prefixWord ++ tailWord_2228066).sum := by decide
  have hdescent : baseEnd_2228066 < baseStart_2228066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228089 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2228089 : Nat := 118140960795 + 2228089 * 2 ^ 59
def prefixEnd_2228089 : Nat := 4983230072969 + 3 ^ 40 * 2228089 * 2
def baseEnd_2228089 : Nat := 1144080597995638325240711

theorem tailTrace_2228089 : CollatzResearch.WordTrace tailWord_2228089 prefixEnd_2228089 1144080597995638325240711 := by
  unfold tailWord_2228089
  simp only [CollatzResearch.WordTrace]
  refine ⟨81265082025021555150983321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54176721350014370100655547 81265082025021555150983321)
  ·
    refine ⟨60948811518766166363237491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81265082025021555150983321 60948811518766166363237491)
    ·
      refine ⟨91423217278149249544856237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60948811518766166363237491 91423217278149249544856237)
      ·
        refine ⟨34283706479305968579321089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91423217278149249544856237 34283706479305968579321089)
        ·
          refine ⟨25712779859479476434490817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34283706479305968579321089 25712779859479476434490817)
          ·
            refine ⟨19284584894609607325868113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25712779859479476434490817 19284584894609607325868113)
            ·
              refine ⟨14463438670957205494401085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19284584894609607325868113 14463438670957205494401085)
              ·
                refine ⟨5423789501608952060400407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14463438670957205494401085 5423789501608952060400407)
                ·
                  refine ⟨8135684252413428090600611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5423789501608952060400407 8135684252413428090600611)
                  ·
                    refine ⟨12203526378620142135900917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8135684252413428090600611 12203526378620142135900917)
                    ·
                      refine ⟨1144080597995638325240711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12203526378620142135900917 1144080597995638325240711)
                      ·
                        rfl

theorem cell23_2228089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2228089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228089 prefixEnd_2228089 := by exact prefixLift 2228089
  have htrace : WordTrace (prefixWord ++ tailWord_2228089) baseStart_2228089 baseEnd_2228089 := by
    simpa [prefixWord, tailWord_2228089, baseEnd_2228089] using wordTrace_append hprefix tailTrace_2228089
  have hstable : (prefixWord ++ tailWord_2228089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228089).length < 2 ^ (prefixWord ++ tailWord_2228089).sum := by decide
  have hdescent : baseEnd_2228089 < baseStart_2228089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228116 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2228116 : Nat := 118140960795 + 2228116 * 2 ^ 59
def prefixEnd_2228116 : Nat := 4983230072969 + 3 ^ 40 * 2228116 * 2
def baseEnd_2228116 : Nat := 1144094461973309719603087

theorem tailTrace_2228116 : CollatzResearch.WordTrace tailWord_2228116 prefixEnd_2228116 1144094461973309719603087 := by
  unfold tailWord_2228116
  simp only [CollatzResearch.WordTrace]
  refine ⟨40633033397961869381108101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54177377863949159174810801 40633033397961869381108101)
  ·
    refine ⟨7618693762117850508957769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40633033397961869381108101 7618693762117850508957769)
    ·
      refine ⟨5714020321588387881718327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7618693762117850508957769 5714020321588387881718327)
      ·
        refine ⟨8571030482382581822577491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714020321588387881718327 8571030482382581822577491)
        ·
          refine ⟨12856545723573872733866237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8571030482382581822577491 12856545723573872733866237)
          ·
            refine ⟨4821204646340202275199839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12856545723573872733866237 4821204646340202275199839)
            ·
              refine ⟨7231806969510303412799759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821204646340202275199839 7231806969510303412799759)
              ·
                refine ⟨10847710454265455119199639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7231806969510303412799759 10847710454265455119199639)
                ·
                  refine ⟨16271565681398182678799459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10847710454265455119199639 16271565681398182678799459)
                  ·
                    refine ⟨24407348522097274018199189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16271565681398182678799459 24407348522097274018199189)
                    ·
                      refine ⟨1144094461973309719603087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24407348522097274018199189 1144094461973309719603087)
                      ·
                        rfl

theorem cell23_2228116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2228116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228116 prefixEnd_2228116 := by exact prefixLift 2228116
  have htrace : WordTrace (prefixWord ++ tailWord_2228116) baseStart_2228116 baseEnd_2228116 := by
    simpa [prefixWord, tailWord_2228116, baseEnd_2228116] using wordTrace_append hprefix tailTrace_2228116
  have hstable : (prefixWord ++ tailWord_2228116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228116).length < 2 ^ (prefixWord ++ tailWord_2228116).sum := by decide
  have hdescent : baseEnd_2228116 < baseStart_2228116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228120 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2228120 : Nat := 118140960795 + 2228120 * 2 ^ 59
def prefixEnd_2228120 : Nat := 4983230072969 + 3 ^ 40 * 2228120 * 2
def baseEnd_2228120 : Nat := 1144096515895927703953069

theorem tailTrace_2228120 : CollatzResearch.WordTrace tailWord_2228120 prefixEnd_2228120 1144096515895927703953069 := by
  unfold tailWord_2228120
  simp only [CollatzResearch.WordTrace]
  refine ⟨40633106343954623722680907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54177475125272831630241209 40633106343954623722680907)
  ·
    refine ⟨60949659515931935584021361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40633106343954623722680907 60949659515931935584021361)
    ·
      refine ⟨45712244636948951688016021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60949659515931935584021361 45712244636948951688016021)
      ·
        refine ⟨2142761467356982110375751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45712244636948951688016021 2142761467356982110375751)
        ·
          refine ⟨3214142201035473165563627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142761467356982110375751 3214142201035473165563627)
          ·
            refine ⟨4821213301553209748345441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214142201035473165563627 4821213301553209748345441)
            ·
              refine ⟨3615909976164907311259081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4821213301553209748345441 3615909976164907311259081)
              ·
                refine ⟨2711932482123680483444311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3615909976164907311259081 2711932482123680483444311)
                ·
                  refine ⟨4067898723185520725166467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2711932482123680483444311 4067898723185520725166467)
                  ·
                    refine ⟨6101848084778281087749701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4067898723185520725166467 6101848084778281087749701)
                    ·
                      refine ⟨1144096515895927703953069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6101848084778281087749701 1144096515895927703953069)
                      ·
                        rfl

theorem cell23_2228120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2228120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228120 prefixEnd_2228120 := by exact prefixLift 2228120
  have htrace : WordTrace (prefixWord ++ tailWord_2228120) baseStart_2228120 baseEnd_2228120 := by
    simpa [prefixWord, tailWord_2228120, baseEnd_2228120] using wordTrace_append hprefix tailTrace_2228120
  have hstable : (prefixWord ++ tailWord_2228120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228120).length < 2 ^ (prefixWord ++ tailWord_2228120).sum := by decide
  have hdescent : baseEnd_2228120 < baseStart_2228120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228153 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2228153 : Nat := 118140960795 + 2228153 * 2 ^ 59
def prefixEnd_2228153 : Nat := 4983230072969 + 3 ^ 40 * 2228153 * 2
def baseEnd_2228153 : Nat := 1144113460757526074840417

theorem tailTrace_2228153 : CollatzResearch.WordTrace tailWord_2228153 prefixEnd_2228153 1144113460757526074840417 := by
  unfold tailWord_2228153
  simp only [CollatzResearch.WordTrace]
  refine ⟨81267416296789694081313113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54178277531193129387542075 81267416296789694081313113)
  ·
    refine ⟨60950562222592270560984835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81267416296789694081313113 60950562222592270560984835)
    ·
      refine ⟨91425843333888405841477253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60950562222592270560984835 91425843333888405841477253)
      ·
        refine ⟨17142345625104076095276985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91425843333888405841477253 17142345625104076095276985)
        ·
          refine ⟨12856759218828057071457739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17142345625104076095276985 12856759218828057071457739)
          ·
            refine ⟨19285138828242085607186609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12856759218828057071457739 19285138828242085607186609)
            ·
              refine ⟨14463854121181564205389957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19285138828242085607186609 14463854121181564205389957)
              ·
                refine ⟨2711972647721543288510617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14463854121181564205389957 2711972647721543288510617)
                ·
                  refine ⟨2033979485791157466382963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2711972647721543288510617 2033979485791157466382963)
                  ·
                    refine ⟨3050969228686736199574445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2033979485791157466382963 3050969228686736199574445)
                    ·
                      refine ⟨1144113460757526074840417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3050969228686736199574445 1144113460757526074840417)
                      ·
                        rfl

theorem cell23_2228153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2228153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228153 prefixEnd_2228153 := by exact prefixLift 2228153
  have htrace : WordTrace (prefixWord ++ tailWord_2228153) baseStart_2228153 baseEnd_2228153 := by
    simpa [prefixWord, tailWord_2228153, baseEnd_2228153] using wordTrace_append hprefix tailTrace_2228153
  have hstable : (prefixWord ++ tailWord_2228153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228153).length < 2 ^ (prefixWord ++ tailWord_2228153).sum := by decide
  have hdescent : baseEnd_2228153 < baseStart_2228153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228159 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_2228159 : Nat := 118140960795 + 2228159 * 2 ^ 59
def prefixEnd_2228159 : Nat := 4983230072969 + 3 ^ 40 * 2228159 * 2
def baseEnd_2228159 : Nat := 1144116541641453051365389

theorem tailTrace_2228159 : CollatzResearch.WordTrace tailWord_2228159 prefixEnd_2228159 1144116541641453051365389 := by
  unfold tailWord_2228159
  simp only [CollatzResearch.WordTrace]
  refine ⟨81267635134767957106031531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54178423423178638070687687 81267635134767957106031531)
  ·
    refine ⟨121901452702151935659047297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81267635134767957106031531 121901452702151935659047297)
    ·
      refine ⟨91426089526613951744285473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121901452702151935659047297 91426089526613951744285473)
      ·
        refine ⟨68569567144960463808214105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91426089526613951744285473 68569567144960463808214105)
        ·
          refine ⟨51427175358720347856160579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68569567144960463808214105 51427175358720347856160579)
          ·
            refine ⟨77140763038080521784240869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51427175358720347856160579 77140763038080521784240869)
            ·
              refine ⟨14463893069640097834545163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77140763038080521784240869 14463893069640097834545163)
              ·
                refine ⟨21695839604460146751817745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14463893069640097834545163 21695839604460146751817745)
                ·
                  refine ⟨16271879703345110063863309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21695839604460146751817745 16271879703345110063863309)
                  ·
                    refine ⟨6101954888754416273948741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16271879703345110063863309 6101954888754416273948741)
                    ·
                      refine ⟨1144116541641453051365389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6101954888754416273948741 1144116541641453051365389)
                      ·
                        rfl

theorem cell23_2228159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_2228159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228159 prefixEnd_2228159 := by exact prefixLift 2228159
  have htrace : WordTrace (prefixWord ++ tailWord_2228159) baseStart_2228159 baseEnd_2228159 := by
    simpa [prefixWord, tailWord_2228159, baseEnd_2228159] using wordTrace_append hprefix tailTrace_2228159
  have hstable : (prefixWord ++ tailWord_2228159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228159).length < 2 ^ (prefixWord ++ tailWord_2228159).sum := by decide
  have hdescent : baseEnd_2228159 < baseStart_2228159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228170 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_2228170 : Nat := 118140960795 + 2228170 * 2 ^ 59
def prefixEnd_2228170 : Nat := 4983230072969 + 3 ^ 40 * 2228170 * 2
def baseEnd_2228170 : Nat := 1144122189928652508327839

theorem tailTrace_2228170 : CollatzResearch.WordTrace tailWord_2228170 prefixEnd_2228170 1144122189928652508327839 := by
  unfold tailWord_2228170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317009084432026496170491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54178690891818737323121309 20317009084432026496170491)
  ·
    refine ⟨30475513626648039744255737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20317009084432026496170491 30475513626648039744255737)
    ·
      refine ⟨22856635219986029808191803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30475513626648039744255737 22856635219986029808191803)
      ·
        refine ⟨34284952829979044712287705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22856635219986029808191803 34284952829979044712287705)
        ·
          refine ⟨25713714622484283534215779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34284952829979044712287705 25713714622484283534215779)
          ·
            refine ⟨38570571933726425301323669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25713714622484283534215779 38570571933726425301323669)
            ·
              refine ⟨1807995559393426185999547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38570571933726425301323669 1807995559393426185999547)
              ·
                refine ⟨2711993339090139278999321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807995559393426185999547 2711993339090139278999321)
                ·
                  refine ⟨2033995004317604459249491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2711993339090139278999321 2033995004317604459249491)
                  ·
                    refine ⟨3050992506476406688874237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2033995004317604459249491 3050992506476406688874237)
                    ·
                      refine ⟨1144122189928652508327839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3050992506476406688874237 1144122189928652508327839)
                      ·
                        rfl

theorem cell23_2228170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_2228170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228170 prefixEnd_2228170 := by exact prefixLift 2228170
  have htrace : WordTrace (prefixWord ++ tailWord_2228170) baseStart_2228170 baseEnd_2228170 := by
    simpa [prefixWord, tailWord_2228170, baseEnd_2228170] using wordTrace_append hprefix tailTrace_2228170
  have hstable : (prefixWord ++ tailWord_2228170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228170).length < 2 ^ (prefixWord ++ tailWord_2228170).sum := by decide
  have hdescent : baseEnd_2228170 < baseStart_2228170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228193 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_2228193 : Nat := 118140960795 + 2228193 * 2 ^ 59
def prefixEnd_2228193 : Nat := 4983230072969 + 3 ^ 40 * 2228193 * 2
def baseEnd_2228193 : Nat := 1144133999983705918340233

theorem tailTrace_2228193 : CollatzResearch.WordTrace tailWord_2228193 prefixEnd_2228193 1144133999983705918340233 := by
  unfold tailWord_2228193
  simp only [CollatzResearch.WordTrace]
  refine ⟨81268875216644780912769233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54179250144429853941846155 81268875216644780912769233)
  ·
    refine ⟨60951656412483585684576925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81268875216644780912769233 60951656412483585684576925)
    ·
      refine ⟨22856871154681344631716347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60951656412483585684576925 22856871154681344631716347)
      ·
        refine ⟨34285306732022016947574521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22856871154681344631716347 34285306732022016947574521)
        ·
          refine ⟨25713980049016512710680891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34285306732022016947574521 25713980049016512710680891)
          ·
            refine ⟨38570970073524769066021337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25713980049016512710680891 38570970073524769066021337)
            ·
              refine ⟨28928227555143576799516003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38570970073524769066021337 28928227555143576799516003)
              ·
                refine ⟨43392341332715365199274005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28928227555143576799516003 43392341332715365199274005)
                ·
                  refine ⟨2034015999971032743715969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43392341332715365199274005 2034015999971032743715969)
                  ·
                    refine ⟨1525511999978274557786977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2034015999971032743715969 1525511999978274557786977)
                    ·
                      refine ⟨1144133999983705918340233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525511999978274557786977 1144133999983705918340233)
                      ·
                        rfl

theorem cell23_2228193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_2228193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228193 prefixEnd_2228193 := by exact prefixLift 2228193
  have htrace : WordTrace (prefixWord ++ tailWord_2228193) baseStart_2228193 baseEnd_2228193 := by
    simpa [prefixWord, tailWord_2228193, baseEnd_2228193] using wordTrace_append hprefix tailTrace_2228193
  have hstable : (prefixWord ++ tailWord_2228193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228193).length < 2 ^ (prefixWord ++ tailWord_2228193).sum := by decide
  have hdescent : baseEnd_2228193 < baseStart_2228193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228327 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 1, 4]
def baseStart_2228327 : Nat := 118140960795 + 2228327 * 2 ^ 59
def prefixEnd_2228327 : Nat := 4983230072969 + 3 ^ 40 * 2228327 * 2
def baseEnd_2228327 : Nat := 381400935463802798021539

theorem tailTrace_2228327 : CollatzResearch.WordTrace tailWord_2228327 prefixEnd_2228327 381400935463802798021539 := by
  unfold tailWord_2228327
  simp only [CollatzResearch.WordTrace]
  refine ⟨81273762598159321798147235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54182508398772881198764823 81273762598159321798147235)
  ·
    refine ⟨121910643897238982697220853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81273762598159321798147235 121910643897238982697220853)
    ·
      refine ⟨11429122865366154627864455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121910643897238982697220853 11429122865366154627864455)
      ·
        refine ⟨17143684298049231941796683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11429122865366154627864455 17143684298049231941796683)
        ·
          refine ⟨25715526447073847912695025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17143684298049231941796683 25715526447073847912695025)
          ·
            refine ⟨19286644835305385934521269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25715526447073847912695025 19286644835305385934521269)
            ·
              refine ⟨1808122953309879931361369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19286644835305385934521269 1808122953309879931361369)
              ·
                refine ⟨1356092214982409948521027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808122953309879931361369 1356092214982409948521027)
                ·
                  refine ⟨2034138322473614922781541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356092214982409948521027 2034138322473614922781541)
                  ·
                    refine ⟨381400935463802798021539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034138322473614922781541 381400935463802798021539)
                    ·
                      rfl

theorem cell23_2228327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_2228327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228327 prefixEnd_2228327 := by exact prefixLift 2228327
  have htrace : WordTrace (prefixWord ++ tailWord_2228327) baseStart_2228327 baseEnd_2228327 := by
    simpa [prefixWord, tailWord_2228327, baseEnd_2228327] using wordTrace_append hprefix tailTrace_2228327
  have hstable : (prefixWord ++ tailWord_2228327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228327).length < 2 ^ (prefixWord ++ tailWord_2228327).sum := by decide
  have hdescent : baseEnd_2228327 < baseStart_2228327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228384 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 1, 1, 3]
def baseStart_2228384 : Nat := 118140960795 + 2228384 * 2 ^ 59
def prefixEnd_2228384 : Nat := 4983230072969 + 3 ^ 40 * 2228384 * 2
def baseEnd_2228384 : Nat := 1144232074788714671051855

theorem tailTrace_2228384 : CollatzResearch.WordTrace tailWord_2228384 prefixEnd_2228384 1144232074788714671051855 := by
  unfold tailWord_2228384
  simp only [CollatzResearch.WordTrace]
  refine ⟨40637920779476410266486103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54183894372635213688648137 40637920779476410266486103)
  ·
    refine ⟨60956881169214615399729155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40637920779476410266486103 60956881169214615399729155)
    ·
      refine ⟨91435321753821923099593733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60956881169214615399729155 91435321753821923099593733)
      ·
        refine ⟨17144122828841610581173825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91435321753821923099593733 17144122828841610581173825)
        ·
          refine ⟨12858092121631207935880369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17144122828841610581173825 12858092121631207935880369)
          ·
            refine ⟨9643569091223405951910277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12858092121631207935880369 9643569091223405951910277)
            ·
              refine ⟨1808169204604388615983177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9643569091223405951910277 1808169204604388615983177)
              ·
                refine ⟨1356126903453291461987383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808169204604388615983177 1356126903453291461987383)
                ·
                  refine ⟨2034190355179937192981075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356126903453291461987383 2034190355179937192981075)
                  ·
                    refine ⟨3051285532769905789471613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2034190355179937192981075 3051285532769905789471613)
                    ·
                      refine ⟨1144232074788714671051855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3051285532769905789471613 1144232074788714671051855)
                      ·
                        rfl

theorem cell23_2228384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_2228384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228384 prefixEnd_2228384 := by exact prefixLift 2228384
  have htrace : WordTrace (prefixWord ++ tailWord_2228384) baseStart_2228384 baseEnd_2228384 := by
    simpa [prefixWord, tailWord_2228384, baseEnd_2228384] using wordTrace_append hprefix tailTrace_2228384
  have hstable : (prefixWord ++ tailWord_2228384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228384).length < 2 ^ (prefixWord ++ tailWord_2228384).sum := by decide
  have hdescent : baseEnd_2228384 < baseStart_2228384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228407 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 3, 2, 2]
def baseStart_2228407 : Nat := 118140960795 + 2228407 * 2 ^ 59
def prefixEnd_2228407 : Nat := 4983230072969 + 3 ^ 40 * 2228407 * 2
def baseEnd_2228407 : Nat := 1144243884843768081064249

theorem tailTrace_2228407 : CollatzResearch.WordTrace tailWord_2228407 prefixEnd_2228407 1144243884843768081064249 := by
  unfold tailWord_2228407
  simp only [CollatzResearch.WordTrace]
  refine ⟨81276680437869495461059475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54184453625246330307372983 81276680437869495461059475)
  ·
    refine ⟨121915020656804243191589213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81276680437869495461059475 121915020656804243191589213)
    ·
      refine ⟨45718132746301591196845955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121915020656804243191589213 45718132746301591196845955)
      ·
        refine ⟨68577199119452386795268933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45718132746301591196845955 68577199119452386795268933)
        ·
          refine ⟨12858224834897322524112925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68577199119452386795268933 12858224834897322524112925)
          ·
            refine ⟨4821834313086495946542347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12858224834897322524112925 4821834313086495946542347)
            ·
              refine ⟨7232751469629743919813521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821834313086495946542347 7232751469629743919813521)
              ·
                refine ⟨5424563602222307939860141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7232751469629743919813521 5424563602222307939860141)
                ·
                  refine ⟨2034211350833365477447553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5424563602222307939860141 2034211350833365477447553)
                  ·
                    refine ⟨1525658513125024108085665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2034211350833365477447553 1525658513125024108085665)
                    ·
                      refine ⟨1144243884843768081064249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525658513125024108085665 1144243884843768081064249)
                      ·
                        rfl

theorem cell23_2228407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_2228407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228407 prefixEnd_2228407 := by exact prefixLift 2228407
  have htrace : WordTrace (prefixWord ++ tailWord_2228407) baseStart_2228407 baseEnd_2228407 := by
    simpa [prefixWord, tailWord_2228407, baseEnd_2228407] using wordTrace_append hprefix tailTrace_2228407
  have hstable : (prefixWord ++ tailWord_2228407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228407).length < 2 ^ (prefixWord ++ tailWord_2228407).sum := by decide
  have hdescent : baseEnd_2228407 < baseStart_2228407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228418 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2228418 : Nat := 118140960795 + 2228418 * 2 ^ 59
def prefixEnd_2228418 : Nat := 4983230072969 + 3 ^ 40 * 2228418 * 2
def baseEnd_2228418 : Nat := 1144249533130967538026699

theorem tailTrace_2228418 : CollatzResearch.WordTrace tailWord_2228418 prefixEnd_2228418 1144249533130967538026699 := by
  unfold tailWord_2228418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20319270410207411084927477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54184721093886429559806605 20319270410207411084927477)
  ·
    refine ⟨1904931600956944789211951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20319270410207411084927477 1904931600956944789211951)
    ·
      refine ⟨2857397401435417183817927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1904931600956944789211951 2857397401435417183817927)
      ·
        refine ⟨4286096102153125775726891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857397401435417183817927 4286096102153125775726891)
        ·
          refine ⟨6429144153229688663590337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286096102153125775726891 6429144153229688663590337)
          ·
            refine ⟨4821858114922266497692753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6429144153229688663590337 4821858114922266497692753)
            ·
              refine ⟨3616393586191699873269565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4821858114922266497692753 3616393586191699873269565)
              ·
                refine ⟨1356147594821887452476087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616393586191699873269565 1356147594821887452476087)
                ·
                  refine ⟨2034221392232831178714131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356147594821887452476087 2034221392232831178714131)
                  ·
                    refine ⟨3051332088349246768071197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2034221392232831178714131 3051332088349246768071197)
                    ·
                      refine ⟨1144249533130967538026699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3051332088349246768071197 1144249533130967538026699)
                      ·
                        rfl

theorem cell23_2228418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2228418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228418 prefixEnd_2228418 := by exact prefixLift 2228418
  have htrace : WordTrace (prefixWord ++ tailWord_2228418) baseStart_2228418 baseEnd_2228418 := by
    simpa [prefixWord, tailWord_2228418, baseEnd_2228418] using wordTrace_append hprefix tailTrace_2228418
  have hstable : (prefixWord ++ tailWord_2228418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228418).length < 2 ^ (prefixWord ++ tailWord_2228418).sum := by decide
  have hdescent : baseEnd_2228418 < baseStart_2228418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228420 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2228420 : Nat := 118140960795 + 2228420 * 2 ^ 59
def prefixEnd_2228420 : Nat := 4983230072969 + 3 ^ 40 * 2228420 * 2
def baseEnd_2228420 : Nat := 1144250560092276530201689

theorem tailTrace_2228420 : CollatzResearch.WordTrace tailWord_2228420 prefixEnd_2228420 1144250560092276530201689 := by
  unfold tailWord_2228420
  simp only [CollatzResearch.WordTrace]
  refine ⟨40638577293411199340641357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54184769724548265787521809 40638577293411199340641357)
  ·
    refine ⟨15239466485029199752740509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40638577293411199340641357 15239466485029199752740509)
    ·
      refine ⟨5714799931885949907277691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15239466485029199752740509 5714799931885949907277691)
      ·
        refine ⟨8572199897828924860916537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714799931885949907277691 8572199897828924860916537)
        ·
          refine ⟨6429149923371693645687403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8572199897828924860916537 6429149923371693645687403)
          ·
            refine ⟨9643724885057540468531105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6429149923371693645687403 9643724885057540468531105)
            ·
              refine ⟨7232793663793155351398329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9643724885057540468531105 7232793663793155351398329)
              ·
                refine ⟨5424595247844866513548747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7232793663793155351398329 5424595247844866513548747)
                ·
                  refine ⟨8136892871767299770323121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5424595247844866513548747 8136892871767299770323121)
                  ·
                    refine ⟨6102669653825474827742341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8136892871767299770323121 6102669653825474827742341)
                    ·
                      refine ⟨1144250560092276530201689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6102669653825474827742341 1144250560092276530201689)
                      ·
                        rfl

theorem cell23_2228420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2228420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228420 prefixEnd_2228420 := by exact prefixLift 2228420
  have htrace : WordTrace (prefixWord ++ tailWord_2228420) baseStart_2228420 baseEnd_2228420 := by
    simpa [prefixWord, tailWord_2228420, baseEnd_2228420] using wordTrace_append hprefix tailTrace_2228420
  have hstable : (prefixWord ++ tailWord_2228420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228420).length < 2 ^ (prefixWord ++ tailWord_2228420).sum := by decide
  have hdescent : baseEnd_2228420 < baseStart_2228420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228467 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 1, 3, 2]
def baseStart_2228467 : Nat := 118140960795 + 2228467 * 2 ^ 59
def prefixEnd_2228467 : Nat := 4983230072969 + 3 ^ 40 * 2228467 * 2
def baseEnd_2228467 : Nat := 1144274693683037846313973

theorem tailTrace_2228467 : CollatzResearch.WordTrace tailWord_2228467 prefixEnd_2228467 1144274693683037846313973 := by
  unfold tailWord_2228467
  simp only [CollatzResearch.WordTrace]
  refine ⟨81278868817652125708243655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54185912545101417138829103 81278868817652125708243655)
  ·
    refine ⟨121918303226478188562365483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81278868817652125708243655 121918303226478188562365483)
    ·
      refine ⟨182877454839717282843548225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121918303226478188562365483 182877454839717282843548225)
      ·
        refine ⟨137158091129787962132661169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182877454839717282843548225 137158091129787962132661169)
        ·
          refine ⟨102868568347340971599495877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137158091129787962132661169 102868568347340971599495877)
          ·
            refine ⟨19287856565126432174905477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102868568347340971599495877 19287856565126432174905477)
            ·
              refine ⟨3616473105961206032794777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19287856565126432174905477 3616473105961206032794777)
              ·
                refine ⟨2712354829470904524596083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616473105961206032794777 2712354829470904524596083)
                ·
                  refine ⟨4068532244206356786894125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2712354829470904524596083 4068532244206356786894125)
                  ·
                    refine ⟨1525699591577383795085297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4068532244206356786894125 1525699591577383795085297)
                    ·
                      refine ⟨1144274693683037846313973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525699591577383795085297 1144274693683037846313973)
                      ·
                        rfl

theorem cell23_2228467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 3, 2].length) (baseStart_2228467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228467 prefixEnd_2228467 := by exact prefixLift 2228467
  have htrace : WordTrace (prefixWord ++ tailWord_2228467) baseStart_2228467 baseEnd_2228467 := by
    simpa [prefixWord, tailWord_2228467, baseEnd_2228467] using wordTrace_append hprefix tailTrace_2228467
  have hstable : (prefixWord ++ tailWord_2228467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228467).length < 2 ^ (prefixWord ++ tailWord_2228467).sum := by decide
  have hdescent : baseEnd_2228467 < baseStart_2228467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228480 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 1, 4, 2]
def baseStart_2228480 : Nat := 118140960795 + 2228480 * 2 ^ 59
def prefixEnd_2228480 : Nat := 4983230072969 + 3 ^ 40 * 2228480 * 2
def baseEnd_2228480 : Nat := 1144281368931546295451413

theorem tailTrace_2228480 : CollatzResearch.WordTrace tailWord_2228480 prefixEnd_2228480 1144281368931546295451413 := by
  unfold tailWord_2228480
  simp only [CollatzResearch.WordTrace]
  refine ⟨40639671483302514464233447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54186228644403352618977929 40639671483302514464233447)
  ·
    refine ⟨60959507224953771696350171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40639671483302514464233447 60959507224953771696350171)
    ·
      refine ⟨91439260837430657544525257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60959507224953771696350171 91439260837430657544525257)
      ·
        refine ⟨68579445628072993158393943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91439260837430657544525257 68579445628072993158393943)
        ·
          refine ⟨102869168442109489737590915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68579445628072993158393943 102869168442109489737590915)
          ·
            refine ⟨154303752663164234606386373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102869168442109489737590915 154303752663164234606386373)
            ·
              refine ⟨28931953624343293988697445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154303752663164234606386373 28931953624343293988697445)
              ·
                refine ⟨5424741304564367622880771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28931953624343293988697445 5424741304564367622880771)
                ·
                  refine ⟨8137111956846551434321157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5424741304564367622880771 8137111956846551434321157)
                  ·
                    refine ⟨1525708491908728393935217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8137111956846551434321157 1525708491908728393935217)
                    ·
                      refine ⟨1144281368931546295451413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525708491908728393935217 1144281368931546295451413)
                      ·
                        rfl

theorem cell23_2228480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_2228480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228480 prefixEnd_2228480 := by exact prefixLift 2228480
  have htrace : WordTrace (prefixWord ++ tailWord_2228480) baseStart_2228480 baseEnd_2228480 := by
    simpa [prefixWord, tailWord_2228480, baseEnd_2228480] using wordTrace_append hprefix tailTrace_2228480
  have hstable : (prefixWord ++ tailWord_2228480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228480).length < 2 ^ (prefixWord ++ tailWord_2228480).sum := by decide
  have hdescent : baseEnd_2228480 < baseStart_2228480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228483 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5]
def baseStart_2228483 : Nat := 118140960795 + 2228483 * 2 ^ 59
def prefixEnd_2228483 : Nat := 4983230072969 + 3 ^ 40 * 2228483 * 2
def baseEnd_2228483 : Nat := 1144282909373509783713899

theorem tailTrace_2228483 : CollatzResearch.WordTrace tailWord_2228483 prefixEnd_2228483 1144282909373509783713899 := by
  unfold tailWord_2228483
  simp only [CollatzResearch.WordTrace]
  refine ⟨81279452385594160440826103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54186301590396106960550735 81279452385594160440826103)
  ·
    refine ⟨121919178578391240661239155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81279452385594160440826103 121919178578391240661239155)
    ·
      refine ⟨182878767867586860991858733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121919178578391240661239155 182878767867586860991858733)
      ·
        refine ⟨68579537950345072871947025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182878767867586860991858733 68579537950345072871947025)
        ·
          refine ⟨51434653462758804653960269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68579537950345072871947025 51434653462758804653960269)
          ·
            refine ⟨19287995048534551745235101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51434653462758804653960269 19287995048534551745235101)
            ·
              refine ⟨7232998143200456904463163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19287995048534551745235101 7232998143200456904463163)
              ·
                refine ⟨10849497214800685356694745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7232998143200456904463163 10849497214800685356694745)
                ·
                  refine ⟨8137122911100514017521059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10849497214800685356694745 8137122911100514017521059)
                  ·
                    refine ⟨12205684366650771026281589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8137122911100514017521059 12205684366650771026281589)
                    ·
                      refine ⟨1144282909373509783713899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12205684366650771026281589 1144282909373509783713899)
                      ·
                        rfl

theorem cell23_2228483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_2228483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228483 prefixEnd_2228483 := by exact prefixLift 2228483
  have htrace : WordTrace (prefixWord ++ tailWord_2228483) baseStart_2228483 baseEnd_2228483 := by
    simpa [prefixWord, tailWord_2228483, baseEnd_2228483] using wordTrace_append hprefix tailTrace_2228483
  have hstable : (prefixWord ++ tailWord_2228483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228483).length < 2 ^ (prefixWord ++ tailWord_2228483).sum := by decide
  have hdescent : baseEnd_2228483 < baseStart_2228483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228497 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 4, 2, 2]
def baseStart_2228497 : Nat := 118140960795 + 2228497 * 2 ^ 59
def prefixEnd_2228497 : Nat := 4983230072969 + 3 ^ 40 * 2228497 * 2
def baseEnd_2228497 : Nat := 1144290098102672728938835

theorem tailTrace_2228497 : CollatzResearch.WordTrace tailWord_2228497 prefixEnd_2228497 1144290098102672728938835 := by
  unfold tailWord_2228497
  simp only [CollatzResearch.WordTrace]
  refine ⟨81279963007543440831835745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54186642005028960554557163 81279963007543440831835745)
  ·
    refine ⟨60959972255657580623876809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81279963007543440831835745 60959972255657580623876809)
    ·
      refine ⟨45719979191743185467907607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60959972255657580623876809 45719979191743185467907607)
      ·
        refine ⟨68579968787614778201861411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45719979191743185467907607 68579968787614778201861411)
        ·
          refine ⟨102869953181422167302792117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68579968787614778201861411 102869953181422167302792117)
          ·
            refine ⟨9644058110758328184636761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102869953181422167302792117 9644058110758328184636761)
            ·
              refine ⟨7233043583068746138477571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9644058110758328184636761 7233043583068746138477571)
              ·
                refine ⟨10849565374603119207716357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7233043583068746138477571 10849565374603119207716357)
                ·
                  refine ⟨2034293507738084851446817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10849565374603119207716357 2034293507738084851446817)
                  ·
                    refine ⟨1525720130803563638585113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2034293507738084851446817 1525720130803563638585113)
                    ·
                      refine ⟨1144290098102672728938835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1525720130803563638585113 1144290098102672728938835)
                      ·
                        rfl

theorem cell23_2228497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_2228497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2228497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2228497 prefixEnd_2228497 := by exact prefixLift 2228497
  have htrace : WordTrace (prefixWord ++ tailWord_2228497) baseStart_2228497 baseEnd_2228497 := by
    simpa [prefixWord, tailWord_2228497, baseEnd_2228497] using wordTrace_append hprefix tailTrace_2228497
  have hstable : (prefixWord ++ tailWord_2228497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228497).length < 2 ^ (prefixWord ++ tailWord_2228497).sum := by decide
  have hdescent : baseEnd_2228497 < baseStart_2228497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
