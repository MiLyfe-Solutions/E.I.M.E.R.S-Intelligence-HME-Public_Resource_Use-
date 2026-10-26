import V185TrunkScan23Chunk0515

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3051320 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 1, 2, 3]
def baseStart_3051320 : Nat := 118140960795 + 3051320 * 2 ^ 59
def prefixEnd_3051320 : Nat := 4983230072969 + 3 ^ 40 * 3051320 * 2
def baseEnd_3051320 : Nat := 1566793790677106930167241

theorem tailTrace_3051320 : CollatzResearch.WordTrace tailWord_3051320 prefixEnd_3051320 1566793790677106930167241 := by
  unfold tailWord_3051320
  simp only [CollatzResearch.WordTrace]
  refine ⟨55645391652798119406155707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74193855537064159208207609 55645391652798119406155707)
  ·
    refine ⟨83468087479197179109233561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55645391652798119406155707 83468087479197179109233561)
    ·
      refine ⟨62601065609397884331925171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83468087479197179109233561 62601065609397884331925171)
      ·
        refine ⟨93901598414096826497887757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62601065609397884331925171 93901598414096826497887757)
        ·
          refine ⟨35213099405286309936707909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93901598414096826497887757 35213099405286309936707909)
          ·
            refine ⟨6602456138491183113132733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35213099405286309936707909 6602456138491183113132733)
            ·
              refine ⟨2475921051934193667424775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6602456138491183113132733 2475921051934193667424775)
              ·
                refine ⟨3713881577901290501137163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475921051934193667424775 3713881577901290501137163)
                ·
                  refine ⟨5570822366851935751705745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713881577901290501137163 5570822366851935751705745)
                  ·
                    refine ⟨4178116775138951813779309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570822366851935751705745 4178116775138951813779309)
                    ·
                      refine ⟨1566793790677106930167241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4178116775138951813779309 1566793790677106930167241)
                      ·
                        rfl

theorem cell23_3051320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_3051320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051320 prefixEnd_3051320 := by exact prefixLift 3051320
  have htrace : WordTrace (prefixWord ++ tailWord_3051320) baseStart_3051320 baseEnd_3051320 := by
    simpa [prefixWord, tailWord_3051320, baseEnd_3051320] using wordTrace_append hprefix tailTrace_3051320
  have hstable : (prefixWord ++ tailWord_3051320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051320).length < 2 ^ (prefixWord ++ tailWord_3051320).sum := by decide
  have hdescent : baseEnd_3051320 < baseStart_3051320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051379 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 11]
def baseStart_3051379 : Nat := 118140960795 + 3051379 * 2 ^ 59
def prefixEnd_3051379 : Nat := 4983230072969 + 3 ^ 40 * 3051379 * 2
def baseEnd_3051379 : Nat := 174091565115080244369941

theorem tailTrace_3051379 : CollatzResearch.WordTrace tailWord_3051379 prefixEnd_3051379 174091565115080244369941 := by
  unfold tailWord_3051379
  simp only [CollatzResearch.WordTrace]
  refine ⟨111292935212382491888709191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74195290141588327925806127 111292935212382491888709191)
  ·
    refine ⟨166939402818573737833063787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111292935212382491888709191 166939402818573737833063787)
    ·
      refine ⟨250409104227860606749595681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166939402818573737833063787 250409104227860606749595681)
      ·
        refine ⟨187806828170895455062196761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250409104227860606749595681 187806828170895455062196761)
        ·
          refine ⟨140855121128171591296647571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187806828170895455062196761 140855121128171591296647571)
          ·
            refine ⟨211282681692257386944971357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140855121128171591296647571 211282681692257386944971357)
            ·
              refine ⟨79231005634596520104364259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211282681692257386944971357 79231005634596520104364259)
              ·
                refine ⟨118846508451894780156546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79231005634596520104364259 118846508451894780156546389)
                ·
                  refine ⟨174091565115080244369941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 118846508451894780156546389 174091565115080244369941)
                  ·
                    rfl

theorem cell23_3051379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 11].length) (baseStart_3051379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051379 prefixEnd_3051379 := by exact prefixLift 3051379
  have htrace : WordTrace (prefixWord ++ tailWord_3051379) baseStart_3051379 baseEnd_3051379 := by
    simpa [prefixWord, tailWord_3051379, baseEnd_3051379] using wordTrace_append hprefix tailTrace_3051379
  have hstable : (prefixWord ++ tailWord_3051379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051379).length < 2 ^ (prefixWord ++ tailWord_3051379).sum := by decide
  have hdescent : baseEnd_3051379 < baseStart_3051379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051386 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_3051386 : Nat := 118140960795 + 3051386 * 2 ^ 59
def prefixEnd_3051386 : Nat := 4983230072969 + 3 ^ 40 * 3051386 * 2
def baseEnd_3051386 : Nat := 1566827680400303671941937

theorem tailTrace_3051386 : CollatzResearch.WordTrace tailWord_3051386 prefixEnd_3051386 1566827680400303671941937 := by
  unfold tailWord_3051386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27823297630839283021053503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74195460348904754722809341 27823297630839283021053503)
  ·
    refine ⟨41734946446258924531580255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27823297630839283021053503 41734946446258924531580255)
    ·
      refine ⟨62602419669388386797370383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41734946446258924531580255 62602419669388386797370383)
      ·
        refine ⟨93903629504082580196055575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62602419669388386797370383 93903629504082580196055575)
        ·
          refine ⟨140855444256123870294083363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93903629504082580196055575 140855444256123870294083363)
          ·
            refine ⟨211283166384185805441125045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140855444256123870294083363 211283166384185805441125045)
            ·
              refine ⟨19807796848517419260105473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211283166384185805441125045 19807796848517419260105473)
              ·
                refine ⟨14855847636388064445079105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19807796848517419260105473 14855847636388064445079105)
                ·
                  refine ⟨11141885727291048333809329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14855847636388064445079105 11141885727291048333809329)
                  ·
                    refine ⟨8356414295468286250356997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11141885727291048333809329 8356414295468286250356997)
                    ·
                      refine ⟨1566827680400303671941937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8356414295468286250356997 1566827680400303671941937)
                      ·
                        rfl

theorem cell23_3051386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_3051386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051386 prefixEnd_3051386 := by exact prefixLift 3051386
  have htrace : WordTrace (prefixWord ++ tailWord_3051386) baseStart_3051386 baseEnd_3051386 := by
    simpa [prefixWord, tailWord_3051386, baseEnd_3051386] using wordTrace_append hprefix tailTrace_3051386
  have hstable : (prefixWord ++ tailWord_3051386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051386).length < 2 ^ (prefixWord ++ tailWord_3051386).sum := by decide
  have hdescent : baseEnd_3051386 < baseStart_3051386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051396 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 7]
def baseStart_3051396 : Nat := 118140960795 + 3051396 * 2 ^ 59
def prefixEnd_3051396 : Nat := 4983230072969 + 3 ^ 40 * 3051396 * 2
def baseEnd_3051396 : Nat := 174092535022983181424099

theorem tailTrace_3051396 : CollatzResearch.WordTrace tailWord_3051396 prefixEnd_3051396 174092535022983181424099 := by
  unfold tailWord_3051396
  simp only [CollatzResearch.WordTrace]
  refine ⟨55646777626660451896039021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74195703502213935861385361 55646777626660451896039021)
  ·
    refine ⟨20867541609997669461014633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55646777626660451896039021 20867541609997669461014633)
    ·
      refine ⟨15650656207498252095760975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20867541609997669461014633 15650656207498252095760975)
      ·
        refine ⟨23475984311247378143641463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15650656207498252095760975 23475984311247378143641463)
        ·
          refine ⟨35213976466871067215462195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23475984311247378143641463 35213976466871067215462195)
          ·
            refine ⟨52820964700306600823193293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35213976466871067215462195 52820964700306600823193293)
            ·
              refine ⟨19807861762614975308697485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52820964700306600823193293 19807861762614975308697485)
              ·
                refine ⟨7427948160980615740761557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19807861762614975308697485 7427948160980615740761557)
                ·
                  refine ⟨174092535022983181424099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7427948160980615740761557 174092535022983181424099)
                  ·
                    rfl

theorem cell23_3051396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_3051396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051396 prefixEnd_3051396 := by exact prefixLift 3051396
  have htrace : WordTrace (prefixWord ++ tailWord_3051396) baseStart_3051396 baseEnd_3051396 := by
    simpa [prefixWord, tailWord_3051396, baseEnd_3051396] using wordTrace_append hprefix tailTrace_3051396
  have hstable : (prefixWord ++ tailWord_3051396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051396).length < 2 ^ (prefixWord ++ tailWord_3051396).sum := by decide
  have hdescent : baseEnd_3051396 < baseStart_3051396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051453 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3051453 : Nat := 118140960795 + 3051453 * 2 ^ 59
def prefixEnd_3051453 : Nat := 4983230072969 + 3 ^ 40 * 3051453 * 2
def baseEnd_3051453 : Nat := 1566862083604154909804129

theorem tailTrace_3051453 : CollatzResearch.WordTrace tailWord_3051453 prefixEnd_3051453 1566862083604154909804129 := by
  unfold tailWord_3051453
  simp only [CollatzResearch.WordTrace]
  refine ⟨111295634214114402526903013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74197089476076268351268675 111295634214114402526903013)
  ·
    refine ⟨20867931415146450473794315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111295634214114402526903013 20867931415146450473794315)
    ·
      refine ⟨31301897122719675710691473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20867931415146450473794315 31301897122719675710691473)
      ·
        refine ⟨23476422842039756783018605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31301897122719675710691473 23476422842039756783018605)
        ·
          refine ⟨8803658565764908793631977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23476422842039756783018605 8803658565764908793631977)
          ·
            refine ⟨6602743924323681595223983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8803658565764908793631977 6602743924323681595223983)
            ·
              refine ⟨9904115886485522392835975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6602743924323681595223983 9904115886485522392835975)
              ·
                refine ⟨14856173829728283589253963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9904115886485522392835975 14856173829728283589253963)
                ·
                  refine ⟨22284260744592425383880945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14856173829728283589253963 22284260744592425383880945)
                  ·
                    refine ⟨16713195558444319037910709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22284260744592425383880945 16713195558444319037910709)
                    ·
                      refine ⟨1566862083604154909804129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16713195558444319037910709 1566862083604154909804129)
                      ·
                        rfl

theorem cell23_3051453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3051453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051453 prefixEnd_3051453 := by exact prefixLift 3051453
  have htrace : WordTrace (prefixWord ++ tailWord_3051453) baseStart_3051453 baseEnd_3051453 := by
    simpa [prefixWord, tailWord_3051453, baseEnd_3051453] using wordTrace_append hprefix tailTrace_3051453
  have hstable : (prefixWord ++ tailWord_3051453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051453).length < 2 ^ (prefixWord ++ tailWord_3051453).sum := by decide
  have hdescent : baseEnd_3051453 < baseStart_3051453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051463 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_3051463 : Nat := 118140960795 + 3051463 * 2 ^ 59
def prefixEnd_3051463 : Nat := 4983230072969 + 3 ^ 40 * 3051463 * 2
def baseEnd_3051463 : Nat := 1566867218410699870679083

theorem tailTrace_3051463 : CollatzResearch.WordTrace tailWord_3051463 prefixEnd_3051463 1566867218410699870679083 := by
  unfold tailWord_3051463
  simp only [CollatzResearch.WordTrace]
  refine ⟨111295998944078174234767043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74197332629385449489844695 111295998944078174234767043)
  ·
    refine ⟨166943998416117261352150565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111295998944078174234767043 166943998416117261352150565)
    ·
      refine ⟨31301999703021986503528231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166943998416117261352150565 31301999703021986503528231)
      ·
        refine ⟨46952999554532979755292347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31301999703021986503528231 46952999554532979755292347)
        ·
          refine ⟨70429499331799469632938521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46952999554532979755292347 70429499331799469632938521)
          ·
            refine ⟨52822124498849602224703891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70429499331799469632938521 52822124498849602224703891)
            ·
              refine ⟨79233186748274403337055837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52822124498849602224703891 79233186748274403337055837)
              ·
                refine ⟨29712445030602901251395939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79233186748274403337055837 29712445030602901251395939)
                ·
                  refine ⟨44568667545904351877093909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29712445030602901251395939 44568667545904351877093909)
                  ·
                    refine ⟨2089156291214266494238777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44568667545904351877093909 2089156291214266494238777)
                    ·
                      refine ⟨1566867218410699870679083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089156291214266494238777 1566867218410699870679083)
                      ·
                        rfl

theorem cell23_3051463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_3051463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051463 prefixEnd_3051463 := by exact prefixLift 3051463
  have htrace : WordTrace (prefixWord ++ tailWord_3051463) baseStart_3051463 baseEnd_3051463 := by
    simpa [prefixWord, tailWord_3051463, baseEnd_3051463] using wordTrace_append hprefix tailTrace_3051463
  have hstable : (prefixWord ++ tailWord_3051463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051463).length < 2 ^ (prefixWord ++ tailWord_3051463).sum := by decide
  have hdescent : baseEnd_3051463 < baseStart_3051463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051503 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 6]
def baseStart_3051503 : Nat := 118140960795 + 3051503 * 2 ^ 59
def prefixEnd_3051503 : Nat := 4983230072969 + 3 ^ 40 * 3051503 * 2
def baseEnd_3051503 : Nat := 174098639737431079353211

theorem tailTrace_3051503 : CollatzResearch.WordTrace tailWord_3051503 prefixEnd_3051503 174098639737431079353211 := by
  unfold tailWord_3051503
  simp only [CollatzResearch.WordTrace]
  refine ⟨111297457863933261066223163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74198305242622174044148775 111297457863933261066223163)
  ·
    refine ⟨166946186795899891599334745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111297457863933261066223163 166946186795899891599334745)
    ·
      refine ⟨125209640096924918699501059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166946186795899891599334745 125209640096924918699501059)
      ·
        refine ⟨187814460145387378049251589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125209640096924918699501059 187814460145387378049251589)
        ·
          refine ⟨35215211277260133384234673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187814460145387378049251589 35215211277260133384234673)
          ·
            refine ⟨26411408457945100038176005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35215211277260133384234673 26411408457945100038176005)
            ·
              refine ⟨4952139085864706257158001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26411408457945100038176005 4952139085864706257158001)
              ·
                refine ⟨3714104314398529692868501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952139085864706257158001 3714104314398529692868501)
                ·
                  refine ⟨174098639737431079353211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3714104314398529692868501 174098639737431079353211)
                  ·
                    rfl

theorem cell23_3051503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 6].length) (baseStart_3051503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051503 prefixEnd_3051503 := by exact prefixLift 3051503
  have htrace : WordTrace (prefixWord ++ tailWord_3051503) baseStart_3051503 baseEnd_3051503 := by
    simpa [prefixWord, tailWord_3051503, baseEnd_3051503] using wordTrace_append hprefix tailTrace_3051503
  have hstable : (prefixWord ++ tailWord_3051503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051503).length < 2 ^ (prefixWord ++ tailWord_3051503).sum := by decide
  have hdescent : baseEnd_3051503 < baseStart_3051503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051573 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3051573 : Nat := 118140960795 + 3051573 * 2 ^ 59
def prefixEnd_3051573 : Nat := 4983230072969 + 3 ^ 40 * 3051573 * 2
def baseEnd_3051573 : Nat := 1566923701282694440303577

theorem tailTrace_3051573 : CollatzResearch.WordTrace tailWord_3051573 prefixEnd_3051573 1566923701282694440303577 := by
  unfold tailWord_3051573
  simp only [CollatzResearch.WordTrace]
  refine ⟨111300010973679663021271373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74200007315786442014180915 111300010973679663021271373)
  ·
    refine ⟨41737504115129873632976765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111300010973679663021271373 41737504115129873632976765)
    ·
      refine ⟨15651564043173702612366287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41737504115129873632976765 15651564043173702612366287)
      ·
        refine ⟨23477346064760553918549431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651564043173702612366287 23477346064760553918549431)
        ·
          refine ⟨35216019097140830877824147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23477346064760553918549431 35216019097140830877824147)
          ·
            refine ⟨52824028645711246316736221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35216019097140830877824147 52824028645711246316736221)
            ·
              refine ⟨19809010742141717368776083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52824028645711246316736221 19809010742141717368776083)
              ·
                refine ⟨29713516113212576053164125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19809010742141717368776083 29713516113212576053164125)
                ·
                  refine ⟨11142568542454716019936547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29713516113212576053164125 11142568542454716019936547)
                  ·
                    refine ⟨16713852813682074029904821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11142568542454716019936547 16713852813682074029904821)
                    ·
                      refine ⟨1566923701282694440303577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16713852813682074029904821 1566923701282694440303577)
                      ·
                        rfl

theorem cell23_3051573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3051573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051573 prefixEnd_3051573 := by exact prefixLift 3051573
  have htrace : WordTrace (prefixWord ++ tailWord_3051573) baseStart_3051573 baseEnd_3051573 := by
    simpa [prefixWord, tailWord_3051573, baseEnd_3051573] using wordTrace_append hprefix tailTrace_3051573
  have hstable : (prefixWord ++ tailWord_3051573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051573).length < 2 ^ (prefixWord ++ tailWord_3051573).sum := by decide
  have hdescent : baseEnd_3051573 < baseStart_3051573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051623 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3051623 : Nat := 118140960795 + 3051623 * 2 ^ 59
def prefixEnd_3051623 : Nat := 4983230072969 + 3 ^ 40 * 3051623 * 2
def baseEnd_3051623 : Nat := 522316458438473081559449

theorem tailTrace_3051623 : CollatzResearch.WordTrace tailWord_3051623 prefixEnd_3051623 522316458438473081559449 := by
  unfold tailWord_3051623
  simp only [CollatzResearch.WordTrace]
  refine ⟨111301834623498521560591523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74201223082332347707061015 111301834623498521560591523)
  ·
    refine ⟨166952751935247782340887285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111301834623498521560591523 166952751935247782340887285)
    ·
      refine ⟨15651820493929479594458183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166952751935247782340887285 15651820493929479594458183)
      ·
        refine ⟨23477730740894219391687275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651820493929479594458183 23477730740894219391687275)
        ·
          refine ⟨35216596111341329087530913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23477730740894219391687275 35216596111341329087530913)
          ·
            refine ⟨26412447083505996815648185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35216596111341329087530913 26412447083505996815648185)
            ·
              refine ⟨19809335312629497611736139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26412447083505996815648185 19809335312629497611736139)
              ·
                refine ⟨29714002968944246417604209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19809335312629497611736139 29714002968944246417604209)
                ·
                  refine ⟨22285502226708184813203157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29714002968944246417604209 22285502226708184813203157)
                  ·
                    refine ⟨522316458438473081559449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22285502226708184813203157 522316458438473081559449)
                    ·
                      rfl

theorem cell23_3051623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3051623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051623 prefixEnd_3051623 := by exact prefixLift 3051623
  have htrace : WordTrace (prefixWord ++ tailWord_3051623) baseStart_3051623 baseEnd_3051623 := by
    simpa [prefixWord, tailWord_3051623, baseEnd_3051623] using wordTrace_append hprefix tailTrace_3051623
  have hstable : (prefixWord ++ tailWord_3051623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051623).length < 2 ^ (prefixWord ++ tailWord_3051623).sum := by decide
  have hdescent : baseEnd_3051623 < baseStart_3051623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051664 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 1, 3, 2]
def baseStart_3051664 : Nat := 118140960795 + 3051664 * 2 ^ 59
def prefixEnd_3051664 : Nat := 4983230072969 + 3 ^ 40 * 3051664 * 2
def baseEnd_3051664 : Nat := 1566970428022253584265659

theorem tailTrace_3051664 : CollatzResearch.WordTrace tailWord_3051664 prefixEnd_3051664 1566970428022253584265659 := by
  unfold tailWord_3051664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55651665008174992781417023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74202220010899990375222697 55651665008174992781417023)
  ·
    refine ⟨83477497512262489172125535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55651665008174992781417023 83477497512262489172125535)
    ·
      refine ⟨125216246268393733758188303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83477497512262489172125535 125216246268393733758188303)
      ·
        refine ⟨187824369402590600637282455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125216246268393733758188303 187824369402590600637282455)
        ·
          refine ⟨281736554103885900955923683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187824369402590600637282455 281736554103885900955923683)
          ·
            refine ⟨422604831155828851433885525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281736554103885900955923683 422604831155828851433885525)
            ·
              refine ⟨2476200182553684676370423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 422604831155828851433885525 2476200182553684676370423)
              ·
                refine ⟨3714300273830527014555635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476200182553684676370423 3714300273830527014555635)
                ·
                  refine ⟨5571450410745790521833453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714300273830527014555635 5571450410745790521833453)
                  ·
                    refine ⟨2089293904029671445687545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5571450410745790521833453 2089293904029671445687545)
                    ·
                      refine ⟨1566970428022253584265659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089293904029671445687545 1566970428022253584265659)
                      ·
                        rfl

theorem cell23_3051664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 3, 2].length) (baseStart_3051664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051664 prefixEnd_3051664 := by exact prefixLift 3051664
  have htrace : WordTrace (prefixWord ++ tailWord_3051664) baseStart_3051664 baseEnd_3051664 := by
    simpa [prefixWord, tailWord_3051664, baseEnd_3051664] using wordTrace_append hprefix tailTrace_3051664
  have hstable : (prefixWord ++ tailWord_3051664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051664).length < 2 ^ (prefixWord ++ tailWord_3051664).sum := by decide
  have hdescent : baseEnd_3051664 < baseStart_3051664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051673 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_3051673 : Nat := 118140960795 + 3051673 * 2 ^ 59
def prefixEnd_3051673 : Nat := 4983230072969 + 3 ^ 40 * 3051673 * 2
def baseEnd_3051673 : Nat := 1566975049348144049053117

theorem tailTrace_3051673 : CollatzResearch.WordTrace tailWord_3051673 prefixEnd_3051673 1566975049348144049053117 := by
  unfold tailWord_3051673
  simp only [CollatzResearch.WordTrace]
  refine ⟨111303658273317380099911673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74202438848878253399941115 111303658273317380099911673)
  ·
    refine ⟨83477743704988035074933755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111303658273317380099911673 83477743704988035074933755)
    ·
      refine ⟨125216615557482052612400633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83477743704988035074933755 125216615557482052612400633)
      ·
        refine ⟨93912461668111539459300475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125216615557482052612400633 93912461668111539459300475)
        ·
          refine ⟨140868692502167309188950713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93912461668111539459300475 140868692502167309188950713)
          ·
            refine ⟨105651519376625481891713035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140868692502167309188950713 105651519376625481891713035)
            ·
              refine ⟨158477279064938222837569553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105651519376625481891713035 158477279064938222837569553)
              ·
                refine ⟨118857959298703667128177165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158477279064938222837569553 118857959298703667128177165)
                ·
                  refine ⟨44571734737013875173066437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118857959298703667128177165 44571734737013875173066437)
                  ·
                    refine ⟨8357200263190101594949957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44571734737013875173066437 8357200263190101594949957)
                    ·
                      refine ⟨1566975049348144049053117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8357200263190101594949957 1566975049348144049053117)
                      ·
                        rfl

theorem cell23_3051673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_3051673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051673 prefixEnd_3051673 := by exact prefixLift 3051673
  have htrace : WordTrace (prefixWord ++ tailWord_3051673) baseStart_3051673 baseEnd_3051673 := by
    simpa [prefixWord, tailWord_3051673, baseEnd_3051673] using wordTrace_append hprefix tailTrace_3051673
  have hstable : (prefixWord ++ tailWord_3051673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051673).length < 2 ^ (prefixWord ++ tailWord_3051673).sum := by decide
  have hdescent : baseEnd_3051673 < baseStart_3051673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051680 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3051680 : Nat := 118140960795 + 3051680 * 2 ^ 59
def prefixEnd_3051680 : Nat := 4983230072969 + 3 ^ 40 * 3051680 * 2
def baseEnd_3051680 : Nat := 1566978643712725521665585

theorem tailTrace_3051680 : CollatzResearch.WordTrace tailWord_3051680 prefixEnd_3051680 1566978643712725521665585 := by
  unfold tailWord_3051680
  simp only [CollatzResearch.WordTrace]
  refine ⟨55651956792146010147708247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74202609056194680196944329 55651956792146010147708247)
  ·
    refine ⟨83477935188219015221562371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55651956792146010147708247 83477935188219015221562371)
    ·
      refine ⟨125216902782328522832343557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83477935188219015221562371 125216902782328522832343557)
      ·
        refine ⟨23478169271686598031064417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125216902782328522832343557 23478169271686598031064417)
        ·
          refine ⟨17608626953764948523298313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23478169271686598031064417 17608626953764948523298313)
          ·
            refine ⟨13206470215323711392473735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17608626953764948523298313 13206470215323711392473735)
            ·
              refine ⟨19809705322985567088710603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13206470215323711392473735 19809705322985567088710603)
              ·
                refine ⟨29714557984478350633065905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19809705322985567088710603 29714557984478350633065905)
                ·
                  refine ⟨22285918488358762974799429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29714557984478350633065905 22285918488358762974799429)
                  ·
                    refine ⟨4178609716567268057774893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22285918488358762974799429 4178609716567268057774893)
                    ·
                      refine ⟨1566978643712725521665585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4178609716567268057774893 1566978643712725521665585)
                      ·
                        rfl

theorem cell23_3051680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3051680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051680 prefixEnd_3051680 := by exact prefixLift 3051680
  have htrace : WordTrace (prefixWord ++ tailWord_3051680) baseStart_3051680 baseEnd_3051680 := by
    simpa [prefixWord, tailWord_3051680, baseEnd_3051680] using wordTrace_append hprefix tailTrace_3051680
  have hstable : (prefixWord ++ tailWord_3051680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051680).length < 2 ^ (prefixWord ++ tailWord_3051680).sum := by decide
  have hdescent : baseEnd_3051680 < baseStart_3051680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051687 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3051687 : Nat := 118140960795 + 3051687 * 2 ^ 59
def prefixEnd_3051687 : Nat := 4983230072969 + 3 ^ 40 * 3051687 * 2
def baseEnd_3051687 : Nat := 522327412692435664759351

theorem tailTrace_3051687 : CollatzResearch.WordTrace tailWord_3051687 prefixEnd_3051687 522327412692435664759351 := by
  unfold tailWord_3051687
  simp only [CollatzResearch.WordTrace]
  refine ⟨111304168895266660490921315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74202779263511106993947543 111304168895266660490921315)
  ·
    refine ⟨166956253342899990736381973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111304168895266660490921315 166956253342899990736381973)
    ·
      refine ⟨7826074375448437065767905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166956253342899990736381973 7826074375448437065767905)
      ·
        refine ⟨5869555781586327799325929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7826074375448437065767905 5869555781586327799325929)
        ·
          refine ⟨4402166836189745849494447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5869555781586327799325929 4402166836189745849494447)
          ·
            refine ⟨6603250254284618774241671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402166836189745849494447 6603250254284618774241671)
            ·
              refine ⟨9904875381426928161362507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603250254284618774241671 9904875381426928161362507)
              ·
                refine ⟨14857313072140392242043761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9904875381426928161362507 14857313072140392242043761)
                ·
                  refine ⟨11142984804105294181532821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14857313072140392242043761 11142984804105294181532821)
                  ·
                    refine ⟨522327412692435664759351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11142984804105294181532821 522327412692435664759351)
                    ·
                      rfl

theorem cell23_3051687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3051687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051687 prefixEnd_3051687 := by exact prefixLift 3051687
  have htrace : WordTrace (prefixWord ++ tailWord_3051687) baseStart_3051687 baseEnd_3051687 := by
    simpa [prefixWord, tailWord_3051687, baseEnd_3051687] using wordTrace_append hprefix tailTrace_3051687
  have hstable : (prefixWord ++ tailWord_3051687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051687).length < 2 ^ (prefixWord ++ tailWord_3051687).sum := by decide
  have hdescent : baseEnd_3051687 < baseStart_3051687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051734 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_3051734 : Nat := 118140960795 + 3051734 * 2 ^ 59
def prefixEnd_3051734 : Nat := 4983230072969 + 3 ^ 40 * 3051734 * 2
def baseEnd_3051734 : Nat := 174111819074229812265593

theorem tailTrace_3051734 : CollatzResearch.WordTrace tailWord_3051734 prefixEnd_3051734 174111819074229812265593 := by
  unfold tailWord_3051734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956617695381024219867641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74203922084064258345254837 6956617695381024219867641)
  ·
    refine ⟨5217463271535768164900731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6956617695381024219867641 5217463271535768164900731)
    ·
      refine ⟨7826194907303652247351097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217463271535768164900731 7826194907303652247351097)
      ·
        refine ⟨5869646180477739185513323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7826194907303652247351097 5869646180477739185513323)
        ·
          refine ⟨8804469270716608778269985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869646180477739185513323 8804469270716608778269985)
          ·
            refine ⟨6603351953037456583702489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804469270716608778269985 6603351953037456583702489)
            ·
              refine ⟨4952513964778092437776867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603351953037456583702489 4952513964778092437776867)
              ·
                refine ⟨7428770947167138656665301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952513964778092437776867 7428770947167138656665301)
                ·
                  refine ⟨174111819074229812265593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7428770947167138656665301 174111819074229812265593)
                  ·
                    rfl

theorem cell23_3051734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_3051734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051734 prefixEnd_3051734 := by exact prefixLift 3051734
  have htrace : WordTrace (prefixWord ++ tailWord_3051734) baseStart_3051734 baseEnd_3051734 := by
    simpa [prefixWord, tailWord_3051734, baseEnd_3051734] using wordTrace_append hprefix tailTrace_3051734
  have hstable : (prefixWord ++ tailWord_3051734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051734).length < 2 ^ (prefixWord ++ tailWord_3051734).sum := by decide
  have hdescent : baseEnd_3051734 < baseStart_3051734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051787 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 3]
def baseStart_3051787 : Nat := 118140960795 + 3051787 * 2 ^ 59
def prefixEnd_3051787 : Nat := 4983230072969 + 3 ^ 40 * 3051787 * 2
def baseEnd_3051787 : Nat := 1567033586142756603027593

theorem tailTrace_3051787 : CollatzResearch.WordTrace tailWord_3051787 prefixEnd_3051787 1567033586142756603027593 := by
  unfold tailWord_3051787
  simp only [CollatzResearch.WordTrace]
  refine ⟨111307816194904377569561615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74205210796602918379707743 111307816194904377569561615)
  ·
    refine ⟨166961724292356566354342423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111307816194904377569561615 166961724292356566354342423)
    ·
      refine ⟨250442586438534849531513635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166961724292356566354342423 250442586438534849531513635)
      ·
        refine ⟨375663879657802274297270453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250442586438534849531513635 375663879657802274297270453)
        ·
          refine ⟨35218488717918963215369105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375663879657802274297270453 35218488717918963215369105)
          ·
            refine ⟨26413866538439222411526829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35218488717918963215369105 26413866538439222411526829)
            ·
              refine ⟨9905199951914708404322561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26413866538439222411526829 9905199951914708404322561)
              ·
                refine ⟨7428899963936031303241921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9905199951914708404322561 7428899963936031303241921)
                ·
                  refine ⟨5571674972952023477431441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7428899963936031303241921 5571674972952023477431441)
                  ·
                    refine ⟨4178756229714017608073581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5571674972952023477431441 4178756229714017608073581)
                    ·
                      refine ⟨1567033586142756603027593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4178756229714017608073581 1567033586142756603027593)
                      ·
                        rfl

theorem cell23_3051787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 3].length) (baseStart_3051787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051787 prefixEnd_3051787 := by exact prefixLift 3051787
  have htrace : WordTrace (prefixWord ++ tailWord_3051787) baseStart_3051787 baseEnd_3051787 := by
    simpa [prefixWord, tailWord_3051787, baseEnd_3051787] using wordTrace_append hprefix tailTrace_3051787
  have hstable : (prefixWord ++ tailWord_3051787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051787).length < 2 ^ (prefixWord ++ tailWord_3051787).sum := by decide
  have hdescent : baseEnd_3051787 < baseStart_3051787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051790 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_3051790 : Nat := 118140960795 + 3051790 * 2 ^ 59
def prefixEnd_3051790 : Nat := 4983230072969 + 3 ^ 40 * 3051790 * 2
def baseEnd_3051790 : Nat := 174115014064968899032231

theorem tailTrace_3051790 : CollatzResearch.WordTrace tailWord_3051790 prefixEnd_3051790 174115014064968899032231 := by
  unfold tailWord_3051790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913490701736688635240103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74205283742595672721280549 13913490701736688635240103)
  ·
    refine ⟨20870236052605032952860155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13913490701736688635240103 20870236052605032952860155)
    ·
      refine ⟨31305354078907549429290233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20870236052605032952860155 31305354078907549429290233)
      ·
        refine ⟨23479015559180662071967675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31305354078907549429290233 23479015559180662071967675)
        ·
          refine ⟨35218523338770993107951513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23479015559180662071967675 35218523338770993107951513)
          ·
            refine ⟨26413892504078244830963635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35218523338770993107951513 26413892504078244830963635)
            ·
              refine ⟨39620838756117367246445453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26413892504078244830963635 39620838756117367246445453)
              ·
                refine ⟨14857814533544012717417045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39620838756117367246445453 14857814533544012717417045)
                ·
                  refine ⟨174115014064968899032231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14857814533544012717417045 174115014064968899032231)
                  ·
                    rfl

theorem cell23_3051790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_3051790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051790 prefixEnd_3051790 := by exact prefixLift 3051790
  have htrace : WordTrace (prefixWord ++ tailWord_3051790) baseStart_3051790 baseEnd_3051790 := by
    simpa [prefixWord, tailWord_3051790, baseEnd_3051790] using wordTrace_append hprefix tailTrace_3051790
  have hstable : (prefixWord ++ tailWord_3051790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051790).length < 2 ^ (prefixWord ++ tailWord_3051790).sum := by decide
  have hdescent : baseEnd_3051790 < baseStart_3051790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051807 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 6]
def baseStart_3051807 : Nat := 118140960795 + 3051807 * 2 ^ 59
def prefixEnd_3051807 : Nat := 4983230072969 + 3 ^ 40 * 3051807 * 2
def baseEnd_3051807 : Nat := 174115983972871836086389

theorem tailTrace_3051807 : CollatzResearch.WordTrace tailWord_3051807 prefixEnd_3051807 174115983972871836086389 := by
  unfold tailWord_3051807
  simp only [CollatzResearch.WordTrace]
  refine ⟨111308545654831920985289675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74205697103221280656859783 111308545654831920985289675)
  ·
    refine ⟨166962818482247881477934513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111308545654831920985289675 166962818482247881477934513)
    ·
      refine ⟨125222113861685911108450885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166962818482247881477934513 125222113861685911108450885)
      ·
        refine ⟨23479146349066108332834541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125222113861685911108450885 23479146349066108332834541)
        ·
          refine ⟨8804679880899790624812953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23479146349066108332834541 8804679880899790624812953)
          ·
            refine ⟨6603509910674842968609715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804679880899790624812953 6603509910674842968609715)
            ·
              refine ⟨9905264866012264452914573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603509910674842968609715 9905264866012264452914573)
              ·
                refine ⟨3714474324754599169842965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9905264866012264452914573 3714474324754599169842965)
                ·
                  refine ⟨174115983972871836086389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3714474324754599169842965 174115983972871836086389)
                  ·
                    rfl

theorem cell23_3051807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 6].length) (baseStart_3051807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051807 prefixEnd_3051807 := by exact prefixLift 3051807
  have htrace : WordTrace (prefixWord ++ tailWord_3051807) baseStart_3051807 baseEnd_3051807 := by
    simpa [prefixWord, tailWord_3051807, baseEnd_3051807] using wordTrace_append hprefix tailTrace_3051807
  have hstable : (prefixWord ++ tailWord_3051807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051807).length < 2 ^ (prefixWord ++ tailWord_3051807).sum := by decide
  have hdescent : baseEnd_3051807 < baseStart_3051807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051857 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_3051857 : Nat := 118140960795 + 3051857 * 2 ^ 59
def prefixEnd_3051857 : Nat := 4983230072969 + 3 ^ 40 * 3051857 * 2
def baseEnd_3051857 : Nat := 1567069529788571329152271

theorem tailTrace_3051857 : CollatzResearch.WordTrace tailWord_3051857 prefixEnd_3051857 1567069529788571329152271 := by
  unfold tailWord_3051857
  simp only [CollatzResearch.WordTrace]
  refine ⟨111310369304650779524609825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74206912869767186349739883 111310369304650779524609825)
  ·
    refine ⟨83482776978488084643457369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111310369304650779524609825 83482776978488084643457369)
    ·
      refine ⟨62612082733866063482593027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83482776978488084643457369 62612082733866063482593027)
      ·
        refine ⟨93918124100799095223889541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62612082733866063482593027 93918124100799095223889541)
        ·
          refine ⟨17609648268899830354479289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93918124100799095223889541 17609648268899830354479289)
          ·
            refine ⟨13207236201674872765859467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17609648268899830354479289 13207236201674872765859467)
            ·
              refine ⟨19810854302512309148789201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13207236201674872765859467 19810854302512309148789201)
              ·
                refine ⟨14858140726884231861591901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19810854302512309148789201 14858140726884231861591901)
                ·
                  refine ⟨5571802772581586948096963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14858140726884231861591901 5571802772581586948096963)
                  ·
                    refine ⟨8357704158872380422145445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5571802772581586948096963 8357704158872380422145445)
                    ·
                      refine ⟨1567069529788571329152271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8357704158872380422145445 1567069529788571329152271)
                      ·
                        rfl

theorem cell23_3051857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_3051857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051857 prefixEnd_3051857 := by exact prefixLift 3051857
  have htrace : WordTrace (prefixWord ++ tailWord_3051857) baseStart_3051857 baseEnd_3051857 := by
    simpa [prefixWord, tailWord_3051857, baseEnd_3051857] using wordTrace_append hprefix tailTrace_3051857
  have hstable : (prefixWord ++ tailWord_3051857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051857).length < 2 ^ (prefixWord ++ tailWord_3051857).sum := by decide
  have hdescent : baseEnd_3051857 < baseStart_3051857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051868 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3051868 : Nat := 118140960795 + 3051868 * 2 ^ 59
def prefixEnd_3051868 : Nat := 4983230072969 + 3 ^ 40 * 3051868 * 2
def baseEnd_3051868 : Nat := 1567075178075770786114721

theorem tailTrace_3051868 : CollatzResearch.WordTrace tailWord_3051868 prefixEnd_3051868 1567075178075770786114721 := by
  unfold tailWord_3051868
  simp only [CollatzResearch.WordTrace]
  refine ⟨55655385253805464201630129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74207180338407285602173505 55655385253805464201630129)
  ·
    refine ⟨41741538940354098151222597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55655385253805464201630129 41741538940354098151222597)
    ·
      refine ⟨7826538551316393403354237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41741538940354098151222597 7826538551316393403354237)
      ·
        refine ⟨2934951956743647526257839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7826538551316393403354237 2934951956743647526257839)
        ·
          refine ⟨4402427935115471289386759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934951956743647526257839 4402427935115471289386759)
          ·
            refine ⟨6603641902673206934080139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402427935115471289386759 6603641902673206934080139)
            ·
              refine ⟨9905462854009810401120209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603641902673206934080139 9905462854009810401120209)
              ·
                refine ⟨7429097140507357800840157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9905462854009810401120209 7429097140507357800840157)
                ·
                  refine ⟨2785911427690259175315059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7429097140507357800840157 2785911427690259175315059)
                  ·
                    refine ⟨4178867141535388762972589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2785911427690259175315059 4178867141535388762972589)
                    ·
                      refine ⟨1567075178075770786114721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4178867141535388762972589 1567075178075770786114721)
                      ·
                        rfl

theorem cell23_3051868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3051868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051868 prefixEnd_3051868 := by exact prefixLift 3051868
  have htrace : WordTrace (prefixWord ++ tailWord_3051868) baseStart_3051868 baseEnd_3051868 := by
    simpa [prefixWord, tailWord_3051868, baseEnd_3051868] using wordTrace_append hprefix tailTrace_3051868
  have hstable : (prefixWord ++ tailWord_3051868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051868).length < 2 ^ (prefixWord ++ tailWord_3051868).sum := by decide
  have hdescent : baseEnd_3051868 < baseStart_3051868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051874 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3051874 : Nat := 118140960795 + 3051874 * 2 ^ 59
def prefixEnd_3051874 : Nat := 4983230072969 + 3 ^ 40 * 3051874 * 2
def baseEnd_3051874 : Nat := 1567078258959697762639693

theorem tailTrace_3051874 : CollatzResearch.WordTrace tailWord_3051874 prefixEnd_3051874 1567078258959697762639693 := by
  unfold tailWord_3051874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27827747336397297856994669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74207326230392794285319117 27827747336397297856994669)
  ·
    refine ⟨10435405251148986696373001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27827747336397297856994669 10435405251148986696373001)
    ·
      refine ⟨7826553938361740022279751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10435405251148986696373001 7826553938361740022279751)
      ·
        refine ⟨11739830907542610033419627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7826553938361740022279751 11739830907542610033419627)
        ·
          refine ⟨17609746361313915050129441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11739830907542610033419627 17609746361313915050129441)
          ·
            refine ⟨13207309770985436287597081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17609746361313915050129441 13207309770985436287597081)
            ·
              refine ⟨9905482328239077215697811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13207309770985436287597081 9905482328239077215697811)
              ·
                refine ⟨14858223492358615823546717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9905482328239077215697811 14858223492358615823546717)
                ·
                  refine ⟨5571833809634480933830019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14858223492358615823546717 5571833809634480933830019)
                  ·
                    refine ⟨8357750714451721400745029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5571833809634480933830019 8357750714451721400745029)
                    ·
                      refine ⟨1567078258959697762639693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8357750714451721400745029 1567078258959697762639693)
                      ·
                        rfl

theorem cell23_3051874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3051874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051874 prefixEnd_3051874 := by exact prefixLift 3051874
  have htrace : WordTrace (prefixWord ++ tailWord_3051874) baseStart_3051874 baseEnd_3051874 := by
    simpa [prefixWord, tailWord_3051874, baseEnd_3051874] using wordTrace_append hprefix tailTrace_3051874
  have hstable : (prefixWord ++ tailWord_3051874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051874).length < 2 ^ (prefixWord ++ tailWord_3051874).sum := by decide
  have hdescent : baseEnd_3051874 < baseStart_3051874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051901 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_3051901 : Nat := 118140960795 + 3051901 * 2 ^ 59
def prefixEnd_3051901 : Nat := 4983230072969 + 3 ^ 40 * 3051901 * 2
def baseEnd_3051901 : Nat := 522364040979123052334023

theorem tailTrace_3051901 : CollatzResearch.WordTrace tailWord_3051901 prefixEnd_3051901 522364040979123052334023 := by
  unfold tailWord_3051901
  simp only [CollatzResearch.WordTrace]
  refine ⟨111311974116491375039211557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74207982744327583359474371 111311974116491375039211557)
  ·
    refine ⟨20870995146842132819852167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111311974116491375039211557 20870995146842132819852167)
    ·
      refine ⟨31306492720263199229778251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20870995146842132819852167 31306492720263199229778251)
      ·
        refine ⟨46959739080394798844667377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31306492720263199229778251 46959739080394798844667377)
        ·
          refine ⟨35219804310296099133500533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46959739080394798844667377 35219804310296099133500533)
          ·
            refine ⟨3301856654090259293765675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35219804310296099133500533 3301856654090259293765675)
            ·
              refine ⟨4952784981135388940648513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301856654090259293765675 4952784981135388940648513)
              ·
                refine ⟨3714588735851541705486385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952784981135388940648513 3714588735851541705486385)
                ·
                  refine ⟨2785941551888656279114789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3714588735851541705486385 2785941551888656279114789)
                  ·
                    refine ⟨522364040979123052334023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2785941551888656279114789 522364040979123052334023)
                    ·
                      rfl

theorem cell23_3051901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_3051901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051901 prefixEnd_3051901 := by exact prefixLift 3051901
  have htrace : WordTrace (prefixWord ++ tailWord_3051901) baseStart_3051901 baseEnd_3051901 := by
    simpa [prefixWord, tailWord_3051901, baseEnd_3051901] using wordTrace_append hprefix tailTrace_3051901
  have hstable : (prefixWord ++ tailWord_3051901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051901).length < 2 ^ (prefixWord ++ tailWord_3051901).sum := by decide
  have hdescent : baseEnd_3051901 < baseStart_3051901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051908 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_3051908 : Nat := 118140960795 + 3051908 * 2 ^ 59
def prefixEnd_3051908 : Nat := 4983230072969 + 3 ^ 40 * 3051908 * 2
def baseEnd_3051908 : Nat := 1567095717301950629614537

theorem tailTrace_3051908 : CollatzResearch.WordTrace tailWord_3051908 prefixEnd_3051908 1567095717301950629614537 := by
  unfold tailWord_3051908
  simp only [CollatzResearch.WordTrace]
  refine ⟨55656114713733007617358189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74208152951644010156477585 55656114713733007617358189)
  ·
    refine ⟨20871043017649877856509321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55656114713733007617358189 20871043017649877856509321)
    ·
      refine ⟨15653282263237408392381991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20871043017649877856509321 15653282263237408392381991)
      ·
        refine ⟨23479923394856112588572987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15653282263237408392381991 23479923394856112588572987)
        ·
          refine ⟨35219885092284168882859481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23479923394856112588572987 35219885092284168882859481)
          ·
            refine ⟨26414913819213126662144611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35219885092284168882859481 26414913819213126662144611)
            ·
              refine ⟨39622370728819689993216917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26414913819213126662144611 39622370728819689993216917)
              ·
                refine ⟨1857298627913422968432043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39622370728819689993216917 1857298627913422968432043)
                ·
                  refine ⟨2785947941870134452648065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857298627913422968432043 2785947941870134452648065)
                  ·
                    refine ⟨2089460956402600839486049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2785947941870134452648065 2089460956402600839486049)
                    ·
                      refine ⟨1567095717301950629614537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089460956402600839486049 1567095717301950629614537)
                      ·
                        rfl

theorem cell23_3051908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_3051908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051908 prefixEnd_3051908 := by exact prefixLift 3051908
  have htrace : WordTrace (prefixWord ++ tailWord_3051908) baseStart_3051908 baseEnd_3051908 := by
    simpa [prefixWord, tailWord_3051908, baseEnd_3051908] using wordTrace_append hprefix tailTrace_3051908
  have hstable : (prefixWord ++ tailWord_3051908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051908).length < 2 ^ (prefixWord ++ tailWord_3051908).sum := by decide
  have hdescent : baseEnd_3051908 < baseStart_3051908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051918 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_3051918 : Nat := 118140960795 + 3051918 * 2 ^ 59
def prefixEnd_3051918 : Nat := 4983230072969 + 3 ^ 40 * 3051918 * 2
def baseEnd_3051918 : Nat := 522366950702831863496497

theorem tailTrace_3051918 : CollatzResearch.WordTrace tailWord_3051918 prefixEnd_3051918 522366950702831863496497 := by
  unfold tailWord_3051918
  simp only [CollatzResearch.WordTrace]
  refine ⟨13914074269678723367822551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74208396104953191295053605 13914074269678723367822551)
  ·
    refine ⟨20871111404518085051733827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13914074269678723367822551 20871111404518085051733827)
    ·
      refine ⟨31306667106777127577600741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20871111404518085051733827 31306667106777127577600741)
      ·
        refine ⟨5870000082520711420800139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31306667106777127577600741 5870000082520711420800139)
        ·
          refine ⟨8805000123781067131200209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5870000082520711420800139 8805000123781067131200209)
          ·
            refine ⟨6603750092835800348400157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8805000123781067131200209 6603750092835800348400157)
            ·
              refine ⟨2476406284813425130650059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6603750092835800348400157 2476406284813425130650059)
              ·
                refine ⟨3714609427220137695975089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476406284813425130650059 3714609427220137695975089)
                ·
                  refine ⟨2785957070415103271981317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3714609427220137695975089 2785957070415103271981317)
                  ·
                    refine ⟨522366950702831863496497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2785957070415103271981317 522366950702831863496497)
                    ·
                      rfl

theorem cell23_3051918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_3051918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051918 prefixEnd_3051918 := by exact prefixLift 3051918
  have htrace : WordTrace (prefixWord ++ tailWord_3051918) baseStart_3051918 baseEnd_3051918 := by
    simpa [prefixWord, tailWord_3051918, baseEnd_3051918] using wordTrace_append hprefix tailTrace_3051918
  have hstable : (prefixWord ++ tailWord_3051918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051918).length < 2 ^ (prefixWord ++ tailWord_3051918).sum := by decide
  have hdescent : baseEnd_3051918 < baseStart_3051918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051969 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3051969 : Nat := 118140960795 + 3051969 * 2 ^ 59
def prefixEnd_3051969 : Nat := 4983230072969 + 3 ^ 40 * 3051969 * 2
def baseEnd_3051969 : Nat := 522375679873958296983919

theorem tailTrace_3051969 : CollatzResearch.WordTrace tailWord_3051969 prefixEnd_3051969 522375679873958296983919 := by
  unfold tailWord_3051969
  simp only [CollatzResearch.WordTrace]
  refine ⟨111314454280245022652686961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74209636186830015101791307 111314454280245022652686961)
  ·
    refine ⟨83485840710183766989515221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111314454280245022652686961 83485840710183766989515221)
    ·
      refine ⟨1956699391644932038816763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 83485840710183766989515221 1956699391644932038816763)
      ·
        refine ⟨2935049087467398058225145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956699391644932038816763 2935049087467398058225145)
        ·
          refine ⟨2201286815600548543668859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2935049087467398058225145 2201286815600548543668859)
          ·
            refine ⟨3301930223400822815503289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201286815600548543668859 3301930223400822815503289)
            ·
              refine ⟨2476447667550617111627467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301930223400822815503289 2476447667550617111627467)
              ·
                refine ⟨3714671501325925667441201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476447667550617111627467 3714671501325925667441201)
                ·
                  refine ⟨2786003625994444250580901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3714671501325925667441201 2786003625994444250580901)
                  ·
                    refine ⟨522375679873958296983919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786003625994444250580901 522375679873958296983919)
                    ·
                      rfl

theorem cell23_3051969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3051969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051969 prefixEnd_3051969 := by exact prefixLift 3051969
  have htrace : WordTrace (prefixWord ++ tailWord_3051969) baseStart_3051969 baseEnd_3051969 := by
    simpa [prefixWord, tailWord_3051969, baseEnd_3051969] using wordTrace_append hprefix tailTrace_3051969
  have hstable : (prefixWord ++ tailWord_3051969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051969).length < 2 ^ (prefixWord ++ tailWord_3051969).sum := by decide
  have hdescent : baseEnd_3051969 < baseStart_3051969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3051977 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_3051977 : Nat := 118140960795 + 3051977 * 2 ^ 59
def prefixEnd_3051977 : Nat := 4983230072969 + 3 ^ 40 * 3051977 * 2
def baseEnd_3051977 : Nat := 1567131147467110859651719

theorem tailTrace_3051977 : CollatzResearch.WordTrace tailWord_3051977 prefixEnd_3051977 1567131147467110859651719 := by
  unfold tailWord_3051977
  simp only [CollatzResearch.WordTrace]
  refine ⟨111314746064216040018978185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74209830709477360012652123 111314746064216040018978185)
  ·
    refine ⟨83486059548162030014233639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111314746064216040018978185 83486059548162030014233639)
    ·
      refine ⟨125229089322243045021350459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83486059548162030014233639 125229089322243045021350459)
      ·
        refine ⟨187843633983364567532025689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125229089322243045021350459 187843633983364567532025689)
        ·
          refine ⟨140882725487523425649019267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187843633983364567532025689 140882725487523425649019267)
          ·
            refine ⟨211324088231285138473528901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140882725487523425649019267 211324088231285138473528901)
            ·
              refine ⟨39623266543365963463786669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211324088231285138473528901 39623266543365963463786669)
              ·
                refine ⟨14858724953762236298920001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39623266543365963463786669 14858724953762236298920001)
                ·
                  refine ⟨11144043715321677224190001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14858724953762236298920001 11144043715321677224190001)
                  ·
                    refine ⟨8358032786491257918142501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11144043715321677224190001 8358032786491257918142501)
                    ·
                      refine ⟨1567131147467110859651719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8358032786491257918142501 1567131147467110859651719)
                      ·
                        rfl

theorem cell23_3051977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_3051977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3051977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3051977 prefixEnd_3051977 := by exact prefixLift 3051977
  have htrace : WordTrace (prefixWord ++ tailWord_3051977) baseStart_3051977 baseEnd_3051977 := by
    simpa [prefixWord, tailWord_3051977, baseEnd_3051977] using wordTrace_append hprefix tailTrace_3051977
  have hstable : (prefixWord ++ tailWord_3051977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3051977).length < 2 ^ (prefixWord ++ tailWord_3051977).sum := by decide
  have hdescent : baseEnd_3051977 < baseStart_3051977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3051977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052024 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 7, 2]
def baseStart_3052024 : Nat := 118140960795 + 3052024 * 2 ^ 59
def prefixEnd_3052024 : Nat := 4983230072969 + 3 ^ 40 * 3052024 * 2
def baseEnd_3052024 : Nat := 1567155281057872175764003

theorem tailTrace_3052024 : CollatzResearch.WordTrace tailWord_3052024 prefixEnd_3052024 1567155281057872175764003 := by
  unfold tailWord_3052024
  simp only [CollatzResearch.WordTrace]
  refine ⟨55658230147522883522969563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74210973530030511363959417 55658230147522883522969563)
  ·
    refine ⟨83487345221284325284454345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55658230147522883522969563 83487345221284325284454345)
    ·
      refine ⟨62615508915963243963340759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83487345221284325284454345 62615508915963243963340759)
      ·
        refine ⟨93923263373944865945011139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62615508915963243963340759 93923263373944865945011139)
        ·
          refine ⟨140884895060917298917516709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93923263373944865945011139 140884895060917298917516709)
          ·
            refine ⟨26415917823921993547034383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140884895060917298917516709 26415917823921993547034383)
            ·
              refine ⟨39623876735882990320551575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26415917823921993547034383 39623876735882990320551575)
              ·
                refine ⟨59435815103824485480827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39623876735882990320551575 59435815103824485480827363)
                ·
                  refine ⟨89153722655736728221241045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59435815103824485480827363 89153722655736728221241045)
                  ·
                    refine ⟨2089540374743829567685337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 89153722655736728221241045 2089540374743829567685337)
                    ·
                      refine ⟨1567155281057872175764003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089540374743829567685337 1567155281057872175764003)
                      ·
                        rfl

theorem cell23_3052024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_3052024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052024 prefixEnd_3052024 := by exact prefixLift 3052024
  have htrace : WordTrace (prefixWord ++ tailWord_3052024) baseStart_3052024 baseEnd_3052024 := by
    simpa [prefixWord, tailWord_3052024, baseEnd_3052024] using wordTrace_append hprefix tailTrace_3052024
  have hstable : (prefixWord ++ tailWord_3052024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052024).length < 2 ^ (prefixWord ++ tailWord_3052024).sum := by decide
  have hdescent : baseEnd_3052024 < baseStart_3052024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052038 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3052038 : Nat := 118140960795 + 3052038 * 2 ^ 59
def prefixEnd_3052038 : Nat := 4983230072969 + 3 ^ 40 * 3052038 * 2
def baseEnd_3052038 : Nat := 174129163309670568998771

theorem tailTrace_3052038 : CollatzResearch.WordTrace tailWord_3052038 prefixEnd_3052038 174129163309670568998771 := by
  unfold tailWord_3052038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478655341156095232404649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74211313944663364957965845 3478655341156095232404649)
  ·
    refine ⟨2608991505867071424303487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3478655341156095232404649 2608991505867071424303487)
    ·
      refine ⟨3913487258800607136455231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2608991505867071424303487 3913487258800607136455231)
      ·
        refine ⟨5870230888200910704682847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913487258800607136455231 5870230888200910704682847)
        ·
          refine ⟨8805346332301366057024271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5870230888200910704682847 8805346332301366057024271)
          ·
            refine ⟨13208019498452049085536407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805346332301366057024271 13208019498452049085536407)
            ·
              refine ⟨19812029247678073628304611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13208019498452049085536407 19812029247678073628304611)
              ·
                refine ⟨29718043871517110442456917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19812029247678073628304611 29718043871517110442456917)
                ·
                  refine ⟨174129163309670568998771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29718043871517110442456917 174129163309670568998771)
                  ·
                    rfl

theorem cell23_3052038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3052038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052038 prefixEnd_3052038 := by exact prefixLift 3052038
  have htrace : WordTrace (prefixWord ++ tailWord_3052038) baseStart_3052038 baseEnd_3052038 := by
    simpa [prefixWord, tailWord_3052038, baseEnd_3052038] using wordTrace_append hprefix tailTrace_3052038
  have hstable : (prefixWord ++ tailWord_3052038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052038).length < 2 ^ (prefixWord ++ tailWord_3052038).sum := by decide
  have hdescent : baseEnd_3052038 < baseStart_3052038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052161 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3052161 : Nat := 118140960795 + 3052161 * 2 ^ 59
def prefixEnd_3052161 : Nat := 4983230072969 + 3 ^ 40 * 3052161 * 2
def baseEnd_3052161 : Nat := 1567225627907538139750873

theorem tailTrace_3052161 : CollatzResearch.WordTrace tailWord_3052161 prefixEnd_3052161 1567225627907538139750873 := by
  unfold tailWord_3052161
  simp only [CollatzResearch.WordTrace]
  refine ⟨111321457095549439443676337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74214304730366292962450891 111321457095549439443676337)
  ·
    refine ⟨83491092821662079582757253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111321457095549439443676337 83491092821662079582757253)
    ·
      refine ⟨15654579904061639921766985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83491092821662079582757253 15654579904061639921766985)
      ·
        refine ⟨11740934928046229941325239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15654579904061639921766985 11740934928046229941325239)
        ·
          refine ⟨17611402392069344911987859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11740934928046229941325239 17611402392069344911987859)
          ·
            refine ⟨26417103588104017367981789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17611402392069344911987859 26417103588104017367981789)
            ·
              refine ⟨9906413845539006512993171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26417103588104017367981789 9906413845539006512993171)
              ·
                refine ⟨14859620768308509769489757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9906413845539006512993171 14859620768308509769489757)
                ·
                  refine ⟨5572357788115691163558659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14859620768308509769489757 5572357788115691163558659)
                  ·
                    refine ⟨8358536682173536745337989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5572357788115691163558659 8358536682173536745337989)
                    ·
                      refine ⟨1567225627907538139750873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8358536682173536745337989 1567225627907538139750873)
                      ·
                        rfl

theorem cell23_3052161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3052161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052161 prefixEnd_3052161 := by exact prefixLift 3052161
  have htrace : WordTrace (prefixWord ++ tailWord_3052161) baseStart_3052161 baseEnd_3052161 := by
    simpa [prefixWord, tailWord_3052161, baseEnd_3052161] using wordTrace_append hprefix tailTrace_3052161
  have hstable : (prefixWord ++ tailWord_3052161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052161).length < 2 ^ (prefixWord ++ tailWord_3052161).sum := by decide
  have hdescent : baseEnd_3052161 < baseStart_3052161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052188 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_3052188 : Nat := 118140960795 + 3052188 * 2 ^ 59
def prefixEnd_3052188 : Nat := 4983230072969 + 3 ^ 40 * 3052188 * 2
def baseEnd_3052188 : Nat := 522413163961736511371083

theorem tailTrace_3052188 : CollatzResearch.WordTrace tailWord_3052188 prefixEnd_3052188 522413163961736511371083 := by
  unfold tailWord_3052188
  simp only [CollatzResearch.WordTrace]
  refine ⟨55661220933225811527454609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74214961244301082036606145 55661220933225811527454609)
  ·
    refine ⟨41745915699919358645590957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55661220933225811527454609 41745915699919358645590957)
    ·
      refine ⟨15654718387469759492096609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41745915699919358645590957 15654718387469759492096609)
      ·
        refine ⟨11741038790602319619072457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15654718387469759492096609 11741038790602319619072457)
        ·
          refine ⟨8805779092951739714304343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11741038790602319619072457 8805779092951739714304343)
          ·
            refine ⟨13208668639427609571456515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805779092951739714304343 13208668639427609571456515)
            ·
              refine ⟨19813002959141414357184773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13208668639427609571456515 19813002959141414357184773)
              ·
                refine ⟨3714938054839015191972145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19813002959141414357184773 3714938054839015191972145)
                ·
                  refine ⟨2786203541129261393979109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3714938054839015191972145 2786203541129261393979109)
                  ·
                    refine ⟨522413163961736511371083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786203541129261393979109 522413163961736511371083)
                    ·
                      rfl

theorem cell23_3052188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_3052188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052188 prefixEnd_3052188 := by exact prefixLift 3052188
  have htrace : WordTrace (prefixWord ++ tailWord_3052188) baseStart_3052188 baseEnd_3052188 := by
    simpa [prefixWord, tailWord_3052188, baseEnd_3052188] using wordTrace_append hprefix tailTrace_3052188
  have hstable : (prefixWord ++ tailWord_3052188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052188).length < 2 ^ (prefixWord ++ tailWord_3052188).sum := by decide
  have hdescent : baseEnd_3052188 < baseStart_3052188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052211 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 3]
def baseStart_3052211 : Nat := 118140960795 + 3052211 * 2 ^ 59
def prefixEnd_3052211 : Nat := 4983230072969 + 3 ^ 40 * 3052211 * 2
def baseEnd_3052211 : Nat := 1567251301940262944125643

theorem tailTrace_3052211 : CollatzResearch.WordTrace tailWord_3052211 prefixEnd_3052211 1567251301940262944125643 := by
  unfold tailWord_3052211
  simp only [CollatzResearch.WordTrace]
  refine ⟨111323280745368297982996487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74215520496912198655330991 111323280745368297982996487)
  ·
    refine ⟨166984921118052446974494731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111323280745368297982996487 166984921118052446974494731)
    ·
      refine ⟨250477381677078670461742097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166984921118052446974494731 250477381677078670461742097)
      ·
        refine ⟨187858036257809002846306573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250477381677078670461742097 187858036257809002846306573)
        ·
          refine ⟨70446763596678376067364965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187858036257809002846306573 70446763596678376067364965)
          ·
            refine ⟨13208768174377195512630931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70446763596678376067364965 13208768174377195512630931)
            ·
              refine ⟨19813152261565793268946397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13208768174377195512630931 19813152261565793268946397)
              ·
                refine ⟨7429932098087172475854899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19813152261565793268946397 7429932098087172475854899)
                ·
                  refine ⟨11144898147130758713782349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7429932098087172475854899 11144898147130758713782349)
                  ·
                    refine ⟨4179336805174034517668381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11144898147130758713782349 4179336805174034517668381)
                    ·
                      refine ⟨1567251301940262944125643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4179336805174034517668381 1567251301940262944125643)
                      ·
                        rfl

theorem cell23_3052211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_3052211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052211 prefixEnd_3052211 := by exact prefixLift 3052211
  have htrace : WordTrace (prefixWord ++ tailWord_3052211) baseStart_3052211 baseEnd_3052211 := by
    simpa [prefixWord, tailWord_3052211, baseEnd_3052211] using wordTrace_append hprefix tailTrace_3052211
  have hstable : (prefixWord ++ tailWord_3052211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052211).length < 2 ^ (prefixWord ++ tailWord_3052211).sum := by decide
  have hdescent : baseEnd_3052211 < baseStart_3052211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052228 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3052228 : Nat := 118140960795 + 3052228 * 2 ^ 59
def prefixEnd_3052228 : Nat := 4983230072969 + 3 ^ 40 * 3052228 * 2
def baseEnd_3052228 : Nat := 1567260031111389377613065

theorem tailTrace_3052228 : CollatzResearch.WordTrace tailWord_3052228 prefixEnd_3052228 1567260031111389377613065 := by
  unfold tailWord_3052228
  simp only [CollatzResearch.WordTrace]
  refine ⟨55661950393153354943182669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74215933857537806590910225 55661950393153354943182669)
  ·
    refine ⟨20873231397432508103693501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55661950393153354943182669 20873231397432508103693501)
    ·
      refine ⟨7827461774037190538885063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20873231397432508103693501 7827461774037190538885063)
      ·
        refine ⟨11741192661055785808327595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827461774037190538885063 11741192661055785808327595)
        ·
          refine ⟨17611788991583678712491393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11741192661055785808327595 17611788991583678712491393)
          ·
            refine ⟨13208841743687759034368545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17611788991583678712491393 13208841743687759034368545)
            ·
              refine ⟨9906631307765819275776409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13208841743687759034368545 9906631307765819275776409)
              ·
                refine ⟨7429973480824364456832307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9906631307765819275776409 7429973480824364456832307)
                ·
                  refine ⟨11144960221236546685248461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7429973480824364456832307 11144960221236546685248461)
                  ·
                    refine ⟨4179360082963705006968173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11144960221236546685248461 4179360082963705006968173)
                    ·
                      refine ⟨1567260031111389377613065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4179360082963705006968173 1567260031111389377613065)
                      ·
                        rfl

theorem cell23_3052228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3052228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052228 prefixEnd_3052228 := by exact prefixLift 3052228
  have htrace : WordTrace (prefixWord ++ tailWord_3052228) baseStart_3052228 baseEnd_3052228 := by
    simpa [prefixWord, tailWord_3052228, baseEnd_3052228] using wordTrace_append hprefix tailTrace_3052228
  have hstable : (prefixWord ++ tailWord_3052228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052228).length < 2 ^ (prefixWord ++ tailWord_3052228).sum := by decide
  have hdescent : baseEnd_3052228 < baseStart_3052228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052261 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_3052261 : Nat := 118140960795 + 3052261 * 2 ^ 59
def prefixEnd_3052261 : Nat := 4983230072969 + 3 ^ 40 * 3052261 * 2
def baseEnd_3052261 : Nat := 522425658657662582833471

theorem tailTrace_3052261 : CollatzResearch.WordTrace tailWord_3052261 prefixEnd_3052261 522425658657662582833471 := by
  unfold tailWord_3052261
  simp only [CollatzResearch.WordTrace]
  refine ⟨111325104395187156522316637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74216736263458104348211091 111325104395187156522316637)
  ·
    refine ⟨41746914148195183695868739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111325104395187156522316637 41746914148195183695868739)
    ·
      refine ⟨62620371222292775543803109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41746914148195183695868739 62620371222292775543803109)
      ·
        refine ⟨11741319604179895414463083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62620371222292775543803109 11741319604179895414463083)
        ·
          refine ⟨17611979406269843121694625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11741319604179895414463083 17611979406269843121694625)
          ·
            refine ⟨13208984554702382341270969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17611979406269843121694625 13208984554702382341270969)
            ·
              refine ⟨9906738416026786755953227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13208984554702382341270969 9906738416026786755953227)
              ·
                refine ⟨14860107624040180133929841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9906738416026786755953227 14860107624040180133929841)
                ·
                  refine ⟨11145080718030135100447381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14860107624040180133929841 11145080718030135100447381)
                  ·
                    refine ⟨522425658657662582833471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11145080718030135100447381 522425658657662582833471)
                    ·
                      rfl

theorem cell23_3052261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_3052261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052261 prefixEnd_3052261 := by exact prefixLift 3052261
  have htrace : WordTrace (prefixWord ++ tailWord_3052261) baseStart_3052261 baseEnd_3052261 := by
    simpa [prefixWord, tailWord_3052261, baseEnd_3052261] using wordTrace_append hprefix tailTrace_3052261
  have hstable : (prefixWord ++ tailWord_3052261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052261).length < 2 ^ (prefixWord ++ tailWord_3052261).sum := by decide
  have hdescent : baseEnd_3052261 < baseStart_3052261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_3052304 : Nat := 118140960795 + 3052304 * 2 ^ 59
def prefixEnd_3052304 : Nat := 4983230072969 + 3 ^ 40 * 3052304 * 2
def baseEnd_3052304 : Nat := 522433018547043693420905

theorem tailTrace_3052304 : CollatzResearch.WordTrace tailWord_3052304 prefixEnd_3052304 522433018547043693420905 := by
  unfold tailWord_3052304
  simp only [CollatzResearch.WordTrace]
  refine ⟨55663336367015687433065983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74217781822687583244087977 55663336367015687433065983)
  ·
    refine ⟨83495004550523531149598975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55663336367015687433065983 83495004550523531149598975)
    ·
      refine ⟨125242506825785296724398463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83495004550523531149598975 125242506825785296724398463)
      ·
        refine ⟨187863760238677945086597695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125242506825785296724398463 187863760238677945086597695)
        ·
          refine ⟨281795640358016917629896543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187863760238677945086597695 281795640358016917629896543)
          ·
            refine ⟨422693460537025376444844815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281795640358016917629896543 422693460537025376444844815)
            ·
              refine ⟨634040190805538064667267223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422693460537025376444844815 634040190805538064667267223)
              ·
                refine ⟨951060286208307097000900835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634040190805538064667267223 951060286208307097000900835)
                ·
                  refine ⟨1426590429312460645501351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951060286208307097000900835 1426590429312460645501351253)
                  ·
                    refine ⟨522433018547043693420905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 1426590429312460645501351253 522433018547043693420905)
                    ·
                      rfl

theorem cell23_3052304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_3052304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052304 prefixEnd_3052304 := by exact prefixLift 3052304
  have htrace : WordTrace (prefixWord ++ tailWord_3052304) baseStart_3052304 baseEnd_3052304 := by
    simpa [prefixWord, tailWord_3052304, baseEnd_3052304] using wordTrace_append hprefix tailTrace_3052304
  have hstable : (prefixWord ++ tailWord_3052304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052304).length < 2 ^ (prefixWord ++ tailWord_3052304).sum := by decide
  have hdescent : baseEnd_3052304 < baseStart_3052304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052319 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 2, 2, 2]
def baseStart_3052319 : Nat := 118140960795 + 3052319 * 2 ^ 59
def prefixEnd_3052319 : Nat := 4983230072969 + 3 ^ 40 * 3052319 * 2
def baseEnd_3052319 : Nat := 1567306757850948521575147

theorem tailTrace_3052319 : CollatzResearch.WordTrace tailWord_3052319 prefixEnd_3052319 1567306757850948521575147 := by
  unfold tailWord_3052319
  simp only [CollatzResearch.WordTrace]
  refine ⟨111327219828977032427928011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74218146552651354951952007 111327219828977032427928011)
  ·
    refine ⟨166990829743465548641892017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111327219828977032427928011 166990829743465548641892017)
    ·
      refine ⟨125243122307599161481419013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166990829743465548641892017 125243122307599161481419013)
      ·
        refine ⟨23483085432674842777766065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125243122307599161481419013 23483085432674842777766065)
        ·
          refine ⟨17612314074506132083324549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23483085432674842777766065 17612314074506132083324549)
          ·
            refine ⟨3302308888969899765623353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17612314074506132083324549 3302308888969899765623353)
            ·
              refine ⟨2476731666727424824217515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302308888969899765623353 2476731666727424824217515)
              ·
                refine ⟨3715097500091137236326273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476731666727424824217515 3715097500091137236326273)
                ·
                  refine ⟨2786323125068352927244705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3715097500091137236326273 2786323125068352927244705)
                  ·
                    refine ⟨2089742343801264695433529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2786323125068352927244705 2089742343801264695433529)
                    ·
                      refine ⟨1567306757850948521575147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089742343801264695433529 1567306757850948521575147)
                      ·
                        rfl

theorem cell23_3052319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_3052319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052319 prefixEnd_3052319 := by exact prefixLift 3052319
  have htrace : WordTrace (prefixWord ++ tailWord_3052319) baseStart_3052319 baseEnd_3052319 := by
    simpa [prefixWord, tailWord_3052319, baseEnd_3052319] using wordTrace_append hprefix tailTrace_3052319
  have hstable : (prefixWord ++ tailWord_3052319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052319).length < 2 ^ (prefixWord ++ tailWord_3052319).sum := by decide
  have hdescent : baseEnd_3052319 < baseStart_3052319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052321 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_3052321 : Nat := 118140960795 + 3052321 * 2 ^ 59
def prefixEnd_3052321 : Nat := 4983230072969 + 3 ^ 40 * 3052321 * 2
def baseEnd_3052321 : Nat := 522435928270752504583379

theorem tailTrace_3052321 : CollatzResearch.WordTrace tailWord_3052321 prefixEnd_3052321 522435928270752504583379 := by
  unfold tailWord_3052321
  simp only [CollatzResearch.WordTrace]
  refine ⟨111327292774969786769500817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74218195183313191179667211 111327292774969786769500817)
  ·
    refine ⟨83495469581227340077125613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111327292774969786769500817 83495469581227340077125613)
    ·
      refine ⟨31310801092960252528922105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83495469581227340077125613 31310801092960252528922105)
      ·
        refine ⟨23483100819720189396691579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31310801092960252528922105 23483100819720189396691579)
        ·
          refine ⟨35224651229580284095037369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23483100819720189396691579 35224651229580284095037369)
          ·
            refine ⟨26418488422185213071278027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35224651229580284095037369 26418488422185213071278027)
            ·
              refine ⟨39627732633277819606917041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26418488422185213071278027 39627732633277819606917041)
              ·
                refine ⟨29720799474958364705187781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39627732633277819606917041 29720799474958364705187781)
                ·
                  refine ⟨5572649901554693382222709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29720799474958364705187781 5572649901554693382222709)
                  ·
                    refine ⟨522435928270752504583379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5572649901554693382222709 522435928270752504583379)
                    ·
                      rfl

theorem cell23_3052321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_3052321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052321 prefixEnd_3052321 := by exact prefixLift 3052321
  have htrace : WordTrace (prefixWord ++ tailWord_3052321) baseStart_3052321 baseEnd_3052321 := by
    simpa [prefixWord, tailWord_3052321, baseEnd_3052321] using wordTrace_append hprefix tailTrace_3052321
  have hstable : (prefixWord ++ tailWord_3052321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052321).length < 2 ^ (prefixWord ++ tailWord_3052321).sum := by decide
  have hdescent : baseEnd_3052321 < baseStart_3052321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052338 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3052338 : Nat := 118140960795 + 3052338 * 2 ^ 59
def prefixEnd_3052338 : Nat := 4983230072969 + 3 ^ 40 * 3052338 * 2
def baseEnd_3052338 : Nat := 522438837994461315745853

theorem tailTrace_3052338 : CollatzResearch.WordTrace tailWord_3052338 prefixEnd_3052338 522438837994461315745853 := by
  unfold tailWord_3052338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27831978203977049668217417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74218608543938799115246445 27831978203977049668217417)
  ·
    refine ⟨20873983652982787251163063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27831978203977049668217417 20873983652982787251163063)
    ·
      refine ⟨31310975479474180876744595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20873983652982787251163063 31310975479474180876744595)
      ·
        refine ⟨46966463219211271315116893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31310975479474180876744595 46966463219211271315116893)
        ·
          refine ⟨17612423707204226743168835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46966463219211271315116893 17612423707204226743168835)
          ·
            refine ⟨26418635560806340114753253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17612423707204226743168835 26418635560806340114753253)
            ·
              refine ⟨4953494167651188771516235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26418635560806340114753253 4953494167651188771516235)
              ·
                refine ⟨7430241251476783157274353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953494167651188771516235 7430241251476783157274353)
                ·
                  refine ⟨5572680938607587367955765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7430241251476783157274353 5572680938607587367955765)
                  ·
                    refine ⟨522438837994461315745853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5572680938607587367955765 522438837994461315745853)
                    ·
                      rfl

theorem cell23_3052338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3052338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052338 prefixEnd_3052338 := by exact prefixLift 3052338
  have htrace : WordTrace (prefixWord ++ tailWord_3052338) baseStart_3052338 baseEnd_3052338 := by
    simpa [prefixWord, tailWord_3052338, baseEnd_3052338] using wordTrace_append hprefix tailTrace_3052338
  have hstable : (prefixWord ++ tailWord_3052338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052338).length < 2 ^ (prefixWord ++ tailWord_3052338).sum := by decide
  have hdescent : baseEnd_3052338 < baseStart_3052338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052375 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 2, 4, 2]
def baseStart_3052375 : Nat := 118140960795 + 3052375 * 2 ^ 59
def prefixEnd_3052375 : Nat := 4983230072969 + 3 ^ 40 * 3052375 * 2
def baseEnd_3052375 : Nat := 1567335512767600302474889

theorem tailTrace_3052375 : CollatzResearch.WordTrace tailWord_3052375 prefixEnd_3052375 1567335512767600302474889 := by
  unfold tailWord_3052375
  simp only [CollatzResearch.WordTrace]
  refine ⟨111329262316774153991966579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74219508211182769327977719 111329262316774153991966579)
  ·
    refine ⟨166993893475161230987949869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111329262316774153991966579 166993893475161230987949869)
    ·
      refine ⟨62622710053185461620481201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166993893475161230987949869 62622710053185461620481201)
      ·
        refine ⟨46967032539889096215360901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62622710053185461620481201 46967032539889096215360901)
        ·
          refine ⟨8806318601229205540380169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46967032539889096215360901 8806318601229205540380169)
          ·
            refine ⟨6604738950921904155285127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8806318601229205540380169 6604738950921904155285127)
            ·
              refine ⟨9907108426382856232927691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604738950921904155285127 9907108426382856232927691)
              ·
                refine ⟨14860662639574284349391537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907108426382856232927691 14860662639574284349391537)
                ·
                  refine ⟨11145496979680713262043653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14860662639574284349391537 11145496979680713262043653)
                  ·
                    refine ⟨2089780683690133736633185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11145496979680713262043653 2089780683690133736633185)
                    ·
                      refine ⟨1567335512767600302474889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089780683690133736633185 1567335512767600302474889)
                      ·
                        rfl

theorem cell23_3052375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_3052375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052375 prefixEnd_3052375 := by exact prefixLift 3052375
  have htrace : WordTrace (prefixWord ++ tailWord_3052375) baseStart_3052375 baseEnd_3052375 := by
    simpa [prefixWord, tailWord_3052375, baseEnd_3052375] using wordTrace_append hprefix tailTrace_3052375
  have hstable : (prefixWord ++ tailWord_3052375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052375).length < 2 ^ (prefixWord ++ tailWord_3052375).sum := by decide
  have hdescent : baseEnd_3052375 < baseStart_3052375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052425 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 3]
def baseStart_3052425 : Nat := 118140960795 + 3052425 * 2 ^ 59
def prefixEnd_3052425 : Nat := 4983230072969 + 3 ^ 40 * 3052425 * 2
def baseEnd_3052425 : Nat := 1567361186800325106849659

theorem tailTrace_3052425 : CollatzResearch.WordTrace tailWord_3052425 prefixEnd_3052425 1567361186800325106849659 := by
  unfold tailWord_3052425
  simp only [CollatzResearch.WordTrace]
  refine ⟨111331085966593012531286729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74220723977728675020857819 111331085966593012531286729)
  ·
    refine ⟨83498314474944759398465047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111331085966593012531286729 83498314474944759398465047)
    ·
      refine ⟨125247471712417139097697571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83498314474944759398465047 125247471712417139097697571)
      ·
        refine ⟨187871207568625708646546357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125247471712417139097697571 187871207568625708646546357)
        ·
          refine ⟨17612925709558660185613721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187871207568625708646546357 17612925709558660185613721)
          ·
            refine ⟨13209694282168995139210291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17612925709558660185613721 13209694282168995139210291)
            ·
              refine ⟨19814541423253492708815437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13209694282168995139210291 19814541423253492708815437)
              ·
                refine ⟨7430453033720059765805789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19814541423253492708815437 7430453033720059765805789)
                ·
                  refine ⟨2786419887645022412177171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7430453033720059765805789 2786419887645022412177171)
                  ·
                    refine ⟨4179629831467533618265757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786419887645022412177171 4179629831467533618265757)
                    ·
                      refine ⟨1567361186800325106849659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4179629831467533618265757 1567361186800325106849659)
                      ·
                        rfl

theorem cell23_3052425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_3052425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052425 prefixEnd_3052425 := by exact prefixLift 3052425
  have htrace : WordTrace (prefixWord ++ tailWord_3052425) baseStart_3052425 baseEnd_3052425 := by
    simpa [prefixWord, tailWord_3052425, baseEnd_3052425] using wordTrace_append hprefix tailTrace_3052425
  have hstable : (prefixWord ++ tailWord_3052425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052425).length < 2 ^ (prefixWord ++ tailWord_3052425).sum := by decide
  have hdescent : baseEnd_3052425 < baseStart_3052425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052445 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_3052445 : Nat := 118140960795 + 3052445 * 2 ^ 59
def prefixEnd_3052445 : Nat := 4983230072969 + 3 ^ 40 * 3052445 * 2
def baseEnd_3052445 : Nat := 522457152137805009533189

theorem tailTrace_3052445 : CollatzResearch.WordTrace tailWord_3052445 prefixEnd_3052445 522457152137805009533189 := by
  unfold tailWord_3052445
  simp only [CollatzResearch.WordTrace]
  refine ⟨111331815426520555947014789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74221210284347037298009859 111331815426520555947014789)
  ·
    refine ⟨20874715392472604240065273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111331815426520555947014789 20874715392472604240065273)
    ·
      refine ⟨15656036544354453180048955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20874715392472604240065273 15656036544354453180048955)
      ·
        refine ⟨23484054816531679770073433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15656036544354453180048955 23484054816531679770073433)
        ·
          refine ⟨17613041112398759827555075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23484054816531679770073433 17613041112398759827555075)
          ·
            refine ⟨26419561668598139741332613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17613041112398759827555075 26419561668598139741332613)
            ·
              refine ⟨4953667812862151201499865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26419561668598139741332613 4953667812862151201499865)
              ·
                refine ⟨3715250859646613401124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4953667812862151201499865 3715250859646613401124899)
                ·
                  refine ⟨5572876289469920101687349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715250859646613401124899 5572876289469920101687349)
                  ·
                    refine ⟨522457152137805009533189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5572876289469920101687349 522457152137805009533189)
                    ·
                      rfl

theorem cell23_3052445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_3052445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052445 prefixEnd_3052445 := by exact prefixLift 3052445
  have htrace : WordTrace (prefixWord ++ tailWord_3052445) baseStart_3052445 baseEnd_3052445 := by
    simpa [prefixWord, tailWord_3052445, baseEnd_3052445] using wordTrace_append hprefix tailTrace_3052445
  have hstable : (prefixWord ++ tailWord_3052445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052445).length < 2 ^ (prefixWord ++ tailWord_3052445).sum := by decide
  have hdescent : baseEnd_3052445 < baseStart_3052445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052448 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3052448 : Nat := 118140960795 + 3052448 * 2 ^ 59
def prefixEnd_3052448 : Nat := 4983230072969 + 3 ^ 40 * 3052448 * 2
def baseEnd_3052448 : Nat := 1567372996855378516862053

theorem tailTrace_3052448 : CollatzResearch.WordTrace tailWord_3052448 prefixEnd_3052448 1567372996855378516862053 := by
  unfold tailWord_3052448
  simp only [CollatzResearch.WordTrace]
  refine ⟨55665962422754843729686999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74221283230339791639582665 55665962422754843729686999)
  ·
    refine ⟨83498943634132265594530499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55665962422754843729686999 83498943634132265594530499)
    ·
      refine ⟨125248415451198398391795749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83498943634132265594530499 125248415451198398391795749)
      ·
        refine ⟨23484077897099699698461703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125248415451198398391795749 23484077897099699698461703)
        ·
          refine ⟨35226116845649549547692555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23484077897099699698461703 35226116845649549547692555)
          ·
            refine ⟨52839175268474324321538833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35226116845649549547692555 52839175268474324321538833)
            ·
              refine ⟨39629381451355743241154125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52839175268474324321538833 39629381451355743241154125)
              ·
                refine ⟨14861018044258403715432797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39629381451355743241154125 14861018044258403715432797)
                ·
                  refine ⟨5572881766596901393287299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14861018044258403715432797 5572881766596901393287299)
                  ·
                    refine ⟨8359322649895352089930949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5572881766596901393287299 8359322649895352089930949)
                    ·
                      refine ⟨1567372996855378516862053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8359322649895352089930949 1567372996855378516862053)
                      ·
                        rfl

theorem cell23_3052448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3052448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052448 prefixEnd_3052448 := by exact prefixLift 3052448
  have htrace : WordTrace (prefixWord ++ tailWord_3052448) baseStart_3052448 baseEnd_3052448 := by
    simpa [prefixWord, tailWord_3052448, baseEnd_3052448] using wordTrace_append hprefix tailTrace_3052448
  have hstable : (prefixWord ++ tailWord_3052448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052448).length < 2 ^ (prefixWord ++ tailWord_3052448).sum := by decide
  have hdescent : baseEnd_3052448 < baseStart_3052448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052470 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3052470 : Nat := 118140960795 + 3052470 * 2 ^ 59
def prefixEnd_3052470 : Nat := 4983230072969 + 3 ^ 40 * 3052470 * 2
def baseEnd_3052470 : Nat := 522461431143259143595651

theorem tailTrace_3052470 : CollatzResearch.WordTrace tailWord_3052470 prefixEnd_3052470 522461431143259143595651 := by
  unfold tailWord_3052470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958295453214374076042179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74221818167619990144449909 6958295453214374076042179)
  ·
    refine ⟨10437443179821561114063269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6958295453214374076042179 10437443179821561114063269)
    ·
      refine ⟨1957020596216542708886863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10437443179821561114063269 1957020596216542708886863)
      ·
        refine ⟨2935530894324814063330295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957020596216542708886863 2935530894324814063330295)
        ·
          refine ⟨4403296341487221094995443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935530894324814063330295 4403296341487221094995443)
          ·
            refine ⟨6604944512230831642493165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403296341487221094995443 6604944512230831642493165)
            ·
              refine ⟨2476854192086561865934937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6604944512230831642493165 2476854192086561865934937)
              ·
                refine ⟨1857640644064921399451203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476854192086561865934937 1857640644064921399451203)
                ·
                  refine ⟨2786460966097382099176805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857640644064921399451203 2786460966097382099176805)
                  ·
                    refine ⟨522461431143259143595651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786460966097382099176805 522461431143259143595651)
                    ·
                      rfl

theorem cell23_3052470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3052470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052470 prefixEnd_3052470 := by exact prefixLift 3052470
  have htrace : WordTrace (prefixWord ++ tailWord_3052470) baseStart_3052470 baseEnd_3052470 := by
    simpa [prefixWord, tailWord_3052470, baseEnd_3052470] using wordTrace_append hprefix tailTrace_3052470
  have hstable : (prefixWord ++ tailWord_3052470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052470).length < 2 ^ (prefixWord ++ tailWord_3052470).sum := by decide
  have hdescent : baseEnd_3052470 < baseStart_3052470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052471 : List Nat := [1, 1, 3, 1, 3, 1, 13]
def baseStart_3052471 : Nat := 118140960795 + 3052471 * 2 ^ 59
def prefixEnd_3052471 : Nat := 4983230072969 + 3 ^ 40 * 3052471 * 2
def baseEnd_3052471 : Nat := 19350429714943604035487

theorem tailTrace_3052471 : CollatzResearch.WordTrace tailWord_3052471 prefixEnd_3052471 19350429714943604035487 := by
  unfold tailWord_3052471
  simp only [CollatzResearch.WordTrace]
  refine ⟨111332763724426362387461267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74221842482950908258307511 111332763724426362387461267)
  ·
    refine ⟨166999145586639543581191901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111332763724426362387461267 166999145586639543581191901)
    ·
      refine ⟨62624679594989828842946963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166999145586639543581191901 62624679594989828842946963)
      ·
        refine ⟨93937019392484743264420445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62624679594989828842946963 93937019392484743264420445)
        ·
          refine ⟨35226382272181778724157667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93937019392484743264420445 35226382272181778724157667)
          ·
            refine ⟨52839573408272668086236501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35226382272181778724157667 52839573408272668086236501)
            ·
              refine ⟨19350429714943604035487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 52839573408272668086236501 19350429714943604035487)
              ·
                rfl

theorem cell23_3052471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 13].length) (baseStart_3052471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052471 prefixEnd_3052471 := by exact prefixLift 3052471
  have htrace : WordTrace (prefixWord ++ tailWord_3052471) baseStart_3052471 baseEnd_3052471 := by
    simpa [prefixWord, tailWord_3052471, baseEnd_3052471] using wordTrace_append hprefix tailTrace_3052471
  have hstable : (prefixWord ++ tailWord_3052471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052471).length < 2 ^ (prefixWord ++ tailWord_3052471).sum := by decide
  have hdescent : baseEnd_3052471 < baseStart_3052471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052478 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3052478 : Nat := 118140960795 + 3052478 * 2 ^ 59
def prefixEnd_3052478 : Nat := 4983230072969 + 3 ^ 40 * 3052478 * 2
def baseEnd_3052478 : Nat := 1567388401275013399486915

theorem tailTrace_3052478 : CollatzResearch.WordTrace tailWord_3052478 prefixEnd_3052478 1567388401275013399486915 := by
  unfold tailWord_3052478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13916627379425125322870761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74222012690267335055310725 13916627379425125322870761)
  ·
    refine ⟨10437470534568843992153071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13916627379425125322870761 10437470534568843992153071)
    ·
      refine ⟨15656205801853265988229607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10437470534568843992153071 15656205801853265988229607)
      ·
        refine ⟨23484308702779898982344411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15656205801853265988229607 23484308702779898982344411)
        ·
          refine ⟨35226463054169848473516617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23484308702779898982344411 35226463054169848473516617)
          ·
            refine ⟨26419847290627386355137463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35226463054169848473516617 26419847290627386355137463)
            ·
              refine ⟨39629770935941079532706195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26419847290627386355137463 39629770935941079532706195)
              ·
                refine ⟨59444656403911619299059293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39629770935941079532706195 59444656403911619299059293)
                ·
                  refine ⟨22291746151466857237147235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59444656403911619299059293 22291746151466857237147235)
                  ·
                    refine ⟨33437619227200285855720853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22291746151466857237147235 33437619227200285855720853)
                    ·
                      refine ⟨1567388401275013399486915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33437619227200285855720853 1567388401275013399486915)
                      ·
                        rfl

theorem cell23_3052478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3052478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052478 prefixEnd_3052478 := by exact prefixLift 3052478
  have htrace : WordTrace (prefixWord ++ tailWord_3052478) baseStart_3052478 baseEnd_3052478 := by
    simpa [prefixWord, tailWord_3052478, baseEnd_3052478] using wordTrace_append hprefix tailTrace_3052478
  have hstable : (prefixWord ++ tailWord_3052478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052478).length < 2 ^ (prefixWord ++ tailWord_3052478).sum := by decide
  have hdescent : baseEnd_3052478 < baseStart_3052478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052515 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3052515 : Nat := 118140960795 + 3052515 * 2 ^ 59
def prefixEnd_3052515 : Nat := 4983230072969 + 3 ^ 40 * 3052515 * 2
def baseEnd_3052515 : Nat := 1567407400059229754724245

theorem tailTrace_3052515 : CollatzResearch.WordTrace tailWord_3052515 prefixEnd_3052515 1567407400059229754724245 := by
  unfold tailWord_3052515
  simp only [CollatzResearch.WordTrace]
  refine ⟨111334368536266957902062999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74222912357511305268041999 111334368536266957902062999)
  ·
    refine ⟨167001552804400436853094499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111334368536266957902062999 167001552804400436853094499)
    ·
      refine ⟨250502329206600655279641749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167001552804400436853094499 250502329206600655279641749)
      ·
        refine ⟨11742296681559405716233207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 250502329206600655279641749 11742296681559405716233207)
        ·
          refine ⟨17613445022339108574349811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742296681559405716233207 17613445022339108574349811)
          ·
            refine ⟨26420167533508662861524717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17613445022339108574349811 26420167533508662861524717)
            ·
              refine ⟨9907562825065748573071769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26420167533508662861524717 9907562825065748573071769)
              ·
                refine ⟨7430672118799311429803827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9907562825065748573071769 7430672118799311429803827)
                ·
                  refine ⟨11146008178198967144705741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430672118799311429803827 11146008178198967144705741)
                  ·
                    refine ⟨4179753066824612679264653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11146008178198967144705741 4179753066824612679264653)
                    ·
                      refine ⟨1567407400059229754724245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4179753066824612679264653 1567407400059229754724245)
                      ·
                        rfl

theorem cell23_3052515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3052515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052515 prefixEnd_3052515 := by exact prefixLift 3052515
  have htrace : WordTrace (prefixWord ++ tailWord_3052515) baseStart_3052515 baseEnd_3052515 := by
    simpa [prefixWord, tailWord_3052515, baseEnd_3052515] using wordTrace_append hprefix tailTrace_3052515
  have hstable : (prefixWord ++ tailWord_3052515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052515).length < 2 ^ (prefixWord ++ tailWord_3052515).sum := by decide
  have hdescent : baseEnd_3052515 < baseStart_3052515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052519 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_3052519 : Nat := 118140960795 + 3052519 * 2 ^ 59
def prefixEnd_3052519 : Nat := 4983230072969 + 3 ^ 40 * 3052519 * 2
def baseEnd_3052519 : Nat := 1567409453981847739074227

theorem tailTrace_3052519 : CollatzResearch.WordTrace tailWord_3052519 prefixEnd_3052519 1567409453981847739074227 := by
  unfold tailWord_3052519
  simp only [CollatzResearch.WordTrace]
  refine ⟨111334514428252466585208611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74223009618834977723472407 111334514428252466585208611)
  ·
    refine ⟨167001771642378699877812917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111334514428252466585208611 167001771642378699877812917)
    ·
      refine ⟨15656416091473003113544961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167001771642378699877812917 15656416091473003113544961)
      ·
        refine ⟨11742312068604752335158721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15656416091473003113544961 11742312068604752335158721)
        ·
          refine ⟨8806734051453564251369041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11742312068604752335158721 8806734051453564251369041)
          ·
            refine ⟨6605050538590173188526781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8806734051453564251369041 6605050538590173188526781)
            ·
              refine ⟨2476893951971314945697543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6605050538590173188526781 2476893951971314945697543)
              ·
                refine ⟨3715340927956972418546315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476893951971314945697543 3715340927956972418546315)
                ·
                  refine ⟨5573011391935458627819473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715340927956972418546315 5573011391935458627819473)
                  ·
                    refine ⟨4179758543951593970864605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5573011391935458627819473 4179758543951593970864605)
                    ·
                      refine ⟨1567409453981847739074227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4179758543951593970864605 1567409453981847739074227)
                      ·
                        rfl

theorem cell23_3052519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_3052519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052519 prefixEnd_3052519 := by exact prefixLift 3052519
  have htrace : WordTrace (prefixWord ++ tailWord_3052519) baseStart_3052519 baseEnd_3052519 := by
    simpa [prefixWord, tailWord_3052519, baseEnd_3052519] using wordTrace_append hprefix tailTrace_3052519
  have hstable : (prefixWord ++ tailWord_3052519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052519).length < 2 ^ (prefixWord ++ tailWord_3052519).sum := by decide
  have hdescent : baseEnd_3052519 < baseStart_3052519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052576 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3052576 : Nat := 118140960795 + 3052576 * 2 ^ 59
def prefixEnd_3052576 : Nat := 4983230072969 + 3 ^ 40 * 3052576 * 2
def baseEnd_3052576 : Nat := 1567438722379154016061465

theorem tailTrace_3052576 : CollatzResearch.WordTrace tailWord_3052576 prefixEnd_3052576 1567438722379154016061465 := by
  unfold tailWord_3052576
  simp only [CollatzResearch.WordTrace]
  refine ⟨55668296694522982660016791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74224395592697310213355721 55668296694522982660016791)
  ·
    refine ⟨83502445041784473990025187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55668296694522982660016791 83502445041784473990025187)
    ·
      refine ⟨125253667562676710985037781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83502445041784473990025187 125253667562676710985037781)
      ·
        refine ⟨2935632833500235413711823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 125253667562676710985037781 2935632833500235413711823)
        ·
          refine ⟨4403449250250353120567735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935632833500235413711823 4403449250250353120567735)
          ·
            refine ⟨6605173875375529680851603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403449250250353120567735 6605173875375529680851603)
            ·
              refine ⟨9907760813063294521277405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6605173875375529680851603 9907760813063294521277405)
              ·
                refine ⟨3715410304898735445479027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9907760813063294521277405 3715410304898735445479027)
                ·
                  refine ⟨5573115457348103168218541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715410304898735445479027 5573115457348103168218541)
                  ·
                    refine ⟨2089918296505538688081953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5573115457348103168218541 2089918296505538688081953)
                    ·
                      refine ⟨1567438722379154016061465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089918296505538688081953 1567438722379154016061465)
                      ·
                        rfl

theorem cell23_3052576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3052576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052576 prefixEnd_3052576 := by exact prefixLift 3052576
  have htrace : WordTrace (prefixWord ++ tailWord_3052576) baseStart_3052576 baseEnd_3052576 := by
    simpa [prefixWord, tailWord_3052576, baseEnd_3052576] using wordTrace_append hprefix tailTrace_3052576
  have hstable : (prefixWord ++ tailWord_3052576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052576).length < 2 ^ (prefixWord ++ tailWord_3052576).sum := by decide
  have hdescent : baseEnd_3052576 < baseStart_3052576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052606 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3052606 : Nat := 118140960795 + 3052606 * 2 ^ 59
def prefixEnd_3052606 : Nat := 4983230072969 + 3 ^ 40 * 3052606 * 2
def baseEnd_3052606 : Nat := 1567454126798788898686327

theorem tailTrace_3052606 : CollatzResearch.WordTrace tailWord_3052606 prefixEnd_3052606 1567454126798788898686327 := by
  unfold tailWord_3052606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917210947367160055453209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74225125052624853629083781 13917210947367160055453209)
  ·
    refine ⟨10437908210525370041589907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13917210947367160055453209 10437908210525370041589907)
    ·
      refine ⟨15656862315788055062384861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10437908210525370041589907 15656862315788055062384861)
      ·
        refine ⟨5871323368420520648394323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15656862315788055062384861 5871323368420520648394323)
        ·
          refine ⟨8806985052630780972591485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871323368420520648394323 8806985052630780972591485)
          ·
            refine ⟨3302619394736542864721807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8806985052630780972591485 3302619394736542864721807)
            ·
              refine ⟨4953929092104814297082711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302619394736542864721807 4953929092104814297082711)
              ·
                refine ⟨7430893638157221445624067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953929092104814297082711 7430893638157221445624067)
                ·
                  refine ⟨11146340457235832168436101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430893638157221445624067 11146340457235832168436101)
                  ·
                    refine ⟨2089938835731718531581769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11146340457235832168436101 2089938835731718531581769)
                    ·
                      refine ⟨1567454126798788898686327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2089938835731718531581769 1567454126798788898686327)
                      ·
                        rfl

theorem cell23_3052606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3052606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052606 prefixEnd_3052606 := by exact prefixLift 3052606
  have htrace : WordTrace (prefixWord ++ tailWord_3052606) baseStart_3052606 baseEnd_3052606 := by
    simpa [prefixWord, tailWord_3052606, baseEnd_3052606] using wordTrace_append hprefix tailTrace_3052606
  have hstable : (prefixWord ++ tailWord_3052606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052606).length < 2 ^ (prefixWord ++ tailWord_3052606).sum := by decide
  have hdescent : baseEnd_3052606 < baseStart_3052606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052608 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_3052608 : Nat := 118140960795 + 3052608 * 2 ^ 59
def prefixEnd_3052608 : Nat := 4983230072969 + 3 ^ 40 * 3052608 * 2
def baseEnd_3052608 : Nat := 522485051253365963620439

theorem tailTrace_3052608 : CollatzResearch.WordTrace tailWord_3052608 prefixEnd_3052608 522485051253365963620439 := by
  unfold tailWord_3052608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55668880262465017392599239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74225173683286689856798985 55668880262465017392599239)
  ·
    refine ⟨83503320393697526088898859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55668880262465017392599239 83503320393697526088898859)
    ·
      refine ⟨125254980590546289133348289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83503320393697526088898859 125254980590546289133348289)
      ·
        refine ⟨93941235442909716850011217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125254980590546289133348289 93941235442909716850011217)
        ·
          refine ⟨70455926582182287637508413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93941235442909716850011217 70455926582182287637508413)
          ·
            refine ⟨26420972468318357864065655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70455926582182287637508413 26420972468318357864065655)
            ·
              refine ⟨39631458702477536796098483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26420972468318357864065655 39631458702477536796098483)
              ·
                refine ⟨59447188053716305194147725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39631458702477536796098483 59447188053716305194147725)
                ·
                  refine ⟨22292695520143614447805397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59447188053716305194147725 22292695520143614447805397)
                  ·
                    refine ⟨522485051253365963620439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22292695520143614447805397 522485051253365963620439)
                    ·
                      rfl

theorem cell23_3052608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_3052608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052608 prefixEnd_3052608 := by exact prefixLift 3052608
  have htrace : WordTrace (prefixWord ++ tailWord_3052608) baseStart_3052608 baseEnd_3052608 := by
    simpa [prefixWord, tailWord_3052608, baseEnd_3052608] using wordTrace_append hprefix tailTrace_3052608
  have hstable : (prefixWord ++ tailWord_3052608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052608).length < 2 ^ (prefixWord ++ tailWord_3052608).sum := by decide
  have hdescent : baseEnd_3052608 < baseStart_3052608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052642 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3052642 : Nat := 118140960795 + 3052642 * 2 ^ 59
def prefixEnd_3052642 : Nat := 4983230072969 + 3 ^ 40 * 3052642 * 2
def baseEnd_3052642 : Nat := 522490870700783585945387

theorem tailTrace_3052642 : CollatzResearch.WordTrace tailWord_3052642 prefixEnd_3052642 522490870700783585945387 := by
  unfold tailWord_3052642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27834750151701714647984045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74226000404537905727957453 27834750151701714647984045)
  ·
    refine ⟨10438031306888142992994017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27834750151701714647984045 10438031306888142992994017)
    ·
      refine ⟨7828523480166107244745513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10438031306888142992994017 7828523480166107244745513)
      ·
        refine ⟨5871392610124580433559135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7828523480166107244745513 5871392610124580433559135)
        ·
          refine ⟨8807088915186870650338703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871392610124580433559135 8807088915186870650338703)
          ·
            refine ⟨13210633372780305975508055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807088915186870650338703 13210633372780305975508055)
            ·
              refine ⟨19815950059170458963262083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13210633372780305975508055 19815950059170458963262083)
              ·
                refine ⟨29723925088755688444893125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19815950059170458963262083 29723925088755688444893125)
                ·
                  refine ⟨5573235954141691583417461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29723925088755688444893125 5573235954141691583417461)
                  ·
                    refine ⟨522490870700783585945387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5573235954141691583417461 522490870700783585945387)
                    ·
                      rfl

theorem cell23_3052642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3052642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052642 prefixEnd_3052642 := by exact prefixLift 3052642
  have htrace : WordTrace (prefixWord ++ tailWord_3052642) baseStart_3052642 baseEnd_3052642 := by
    simpa [prefixWord, tailWord_3052642, baseEnd_3052642] using wordTrace_append hprefix tailTrace_3052642
  have hstable : (prefixWord ++ tailWord_3052642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052642).length < 2 ^ (prefixWord ++ tailWord_3052642).sum := by decide
  have hdescent : baseEnd_3052642 < baseStart_3052642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052662 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3052662 : Nat := 118140960795 + 3052662 * 2 ^ 59
def prefixEnd_3052662 : Nat := 4983230072969 + 3 ^ 40 * 3052662 * 2
def baseEnd_3052662 : Nat := 1567482881715440679586069

theorem tailTrace_3052662 : CollatzResearch.WordTrace tailWord_3052662 prefixEnd_3052662 1567482881715440679586069 := by
  unfold tailWord_3052662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958733129170900125479015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74226486711156268005109493 6958733129170900125479015)
  ·
    refine ⟨10438099693756350188218523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6958733129170900125479015 10438099693756350188218523)
    ·
      refine ⟨15657149540634525282327785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10438099693756350188218523 15657149540634525282327785)
      ·
        refine ⟨11742862155475893961745839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15657149540634525282327785 11742862155475893961745839)
        ·
          refine ⟨17614293233213840942618759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742862155475893961745839 17614293233213840942618759)
          ·
            refine ⟨26421439849820761413928139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17614293233213840942618759 26421439849820761413928139)
            ·
              refine ⟨39632159774731142120892209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26421439849820761413928139 39632159774731142120892209)
              ·
                refine ⟨29724119831048356590669157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39632159774731142120892209 29724119831048356590669157)
                ·
                  refine ⟨5573272468321566860750467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29724119831048356590669157 5573272468321566860750467)
                  ·
                    refine ⟨8359908702482350291125701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573272468321566860750467 8359908702482350291125701)
                    ·
                      refine ⟨1567482881715440679586069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8359908702482350291125701 1567482881715440679586069)
                      ·
                        rfl

theorem cell23_3052662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3052662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052662 prefixEnd_3052662 := by exact prefixLift 3052662
  have htrace : WordTrace (prefixWord ++ tailWord_3052662) baseStart_3052662 baseEnd_3052662 := by
    simpa [prefixWord, tailWord_3052662, baseEnd_3052662] using wordTrace_append hprefix tailTrace_3052662
  have hstable : (prefixWord ++ tailWord_3052662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052662).length < 2 ^ (prefixWord ++ tailWord_3052662).sum := by decide
  have hdescent : baseEnd_3052662 < baseStart_3052662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052705 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3052705 : Nat := 118140960795 + 3052705 * 2 ^ 59
def prefixEnd_3052705 : Nat := 4983230072969 + 3 ^ 40 * 3052705 * 2
def baseEnd_3052705 : Nat := 1567504961383584011348371

theorem tailTrace_3052705 : CollatzResearch.WordTrace tailWord_3052705 prefixEnd_3052705 1567504961383584011348371 := by
  unfold tailWord_3052705
  simp only [CollatzResearch.WordTrace]
  refine ⟨111341298405578620351479569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74227532270385746900986379 111341298405578620351479569)
  ·
    refine ⟨83505973804183965263609677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111341298405578620351479569 83505973804183965263609677)
    ·
      refine ⟨31314740176568986973853629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83505973804183965263609677 31314740176568986973853629)
      ·
        refine ⟨11743027566213370115195111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31314740176568986973853629 11743027566213370115195111)
        ·
          refine ⟨17614541349320055172792667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11743027566213370115195111 17614541349320055172792667)
          ·
            refine ⟨26421812023980082759189001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17614541349320055172792667 26421812023980082759189001)
            ·
              refine ⟨19816359017985062069391751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26421812023980082759189001 19816359017985062069391751)
              ·
                refine ⟨29724538526977593104087627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19816359017985062069391751 29724538526977593104087627)
                ·
                  refine ⟨44586807790466389656131441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29724538526977593104087627 44586807790466389656131441)
                  ·
                    refine ⟨33440105842849792242098581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44586807790466389656131441 33440105842849792242098581)
                    ·
                      refine ⟨1567504961383584011348371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33440105842849792242098581 1567504961383584011348371)
                      ·
                        rfl

theorem cell23_3052705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3052705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052705 prefixEnd_3052705 := by exact prefixLift 3052705
  have htrace : WordTrace (prefixWord ++ tailWord_3052705) baseStart_3052705 baseEnd_3052705 := by
    simpa [prefixWord, tailWord_3052705, baseEnd_3052705] using wordTrace_append hprefix tailTrace_3052705
  have hstable : (prefixWord ++ tailWord_3052705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052705).length < 2 ^ (prefixWord ++ tailWord_3052705).sum := by decide
  have hdescent : baseEnd_3052705 < baseStart_3052705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052729 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3052729 : Nat := 118140960795 + 3052729 * 2 ^ 59
def prefixEnd_3052729 : Nat := 4983230072969 + 3 ^ 40 * 3052729 * 2
def baseEnd_3052729 : Nat := 1567517284919291917448261

theorem tailTrace_3052729 : CollatzResearch.WordTrace tailWord_3052729 prefixEnd_3052729 1567517284919291917448261 := by
  unfold tailWord_3052729
  simp only [CollatzResearch.WordTrace]
  refine ⟨111342173757491672450353241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74228115838327781633568827 111342173757491672450353241)
  ·
    refine ⟨83506630318118754337764931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111342173757491672450353241 83506630318118754337764931)
    ·
      refine ⟨125259945477178131506647397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83506630318118754337764931 125259945477178131506647397)
      ·
        refine ⟨23486239776970899657496387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125259945477178131506647397 23486239776970899657496387)
        ·
          refine ⟨35229359665456349486244581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23486239776970899657496387 35229359665456349486244581)
          ·
            refine ⟨6605504937273065528670859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35229359665456349486244581 6605504937273065528670859)
            ·
              refine ⟨9908257405909598293006289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6605504937273065528670859 9908257405909598293006289)
              ·
                refine ⟨7431193054432198719754717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9908257405909598293006289 7431193054432198719754717)
                ·
                  refine ⟨2786697395412074519908019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7431193054432198719754717 2786697395412074519908019)
                  ·
                    refine ⟨4180046093118111779862029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786697395412074519908019 4180046093118111779862029)
                    ·
                      refine ⟨1567517284919291917448261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4180046093118111779862029 1567517284919291917448261)
                      ·
                        rfl

theorem cell23_3052729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3052729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052729 prefixEnd_3052729 := by exact prefixLift 3052729
  have htrace : WordTrace (prefixWord ++ tailWord_3052729) baseStart_3052729 baseEnd_3052729 := by
    simpa [prefixWord, tailWord_3052729, baseEnd_3052729] using wordTrace_append hprefix tailTrace_3052729
  have hstable : (prefixWord ++ tailWord_3052729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052729).length < 2 ^ (prefixWord ++ tailWord_3052729).sum := by decide
  have hdescent : baseEnd_3052729 < baseStart_3052729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052732 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_3052732 : Nat := 118140960795 + 3052732 * 2 ^ 59
def prefixEnd_3052732 : Nat := 4983230072969 + 3 ^ 40 * 3052732 * 2
def baseEnd_3052732 : Nat := 522506275120418468570249

theorem tailTrace_3052732 : CollatzResearch.WordTrace tailWord_3052732 prefixEnd_3052732 522506275120418468570249 := by
  unfold tailWord_3052732
  simp only [CollatzResearch.WordTrace]
  refine ⟨55671141588240401981356225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74228188784320535975141633 55671141588240401981356225)
  ·
    refine ⟨41753356191180301486017169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55671141588240401981356225 41753356191180301486017169)
    ·
      refine ⟨31315017143385226114512877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41753356191180301486017169 31315017143385226114512877)
      ·
        refine ⟨11743131428769459792942329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31315017143385226114512877 11743131428769459792942329)
        ·
          refine ⟨8807348571577094844706747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11743131428769459792942329 8807348571577094844706747)
          ·
            refine ⟨13211022857365642267060121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807348571577094844706747 13211022857365642267060121)
            ·
              refine ⟨9908267143024231700295091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13211022857365642267060121 9908267143024231700295091)
              ·
                refine ⟨14862400714536347550442637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9908267143024231700295091 14862400714536347550442637)
                ·
                  refine ⟨5573400267951130331415989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14862400714536347550442637 5573400267951130331415989)
                  ·
                    refine ⟨522506275120418468570249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5573400267951130331415989 522506275120418468570249)
                    ·
                      rfl

theorem cell23_3052732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_3052732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052732 prefixEnd_3052732 := by exact prefixLift 3052732
  have htrace : WordTrace (prefixWord ++ tailWord_3052732) baseStart_3052732 baseEnd_3052732 := by
    simpa [prefixWord, tailWord_3052732, baseEnd_3052732] using wordTrace_append hprefix tailTrace_3052732
  have hstable : (prefixWord ++ tailWord_3052732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052732).length < 2 ^ (prefixWord ++ tailWord_3052732).sum := by decide
  have hdescent : baseEnd_3052732 < baseStart_3052732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052746 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_3052746 : Nat := 118140960795 + 3052746 * 2 ^ 59
def prefixEnd_3052746 : Nat := 4983230072969 + 3 ^ 40 * 3052746 * 2
def baseEnd_3052746 : Nat := 1567526014090418350935683

theorem tailTrace_3052746 : CollatzResearch.WordTrace tailWord_3052746 prefixEnd_3052746 1567526014090418350935683 := by
  unfold tailWord_3052746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835698449607521088430523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74228529198953389569148061 27835698449607521088430523)
  ·
    refine ⟨41753547674411281632645785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27835698449607521088430523 41753547674411281632645785)
    ·
      refine ⟨31315160755808461224484339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41753547674411281632645785 31315160755808461224484339)
      ·
        refine ⟨46972741133712691836726509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31315160755808461224484339 46972741133712691836726509)
        ·
          refine ⟨17614777925142259438772441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46972741133712691836726509 17614777925142259438772441)
          ·
            refine ⟨13211083443856694579079331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17614777925142259438772441 13211083443856694579079331)
            ·
              refine ⟨19816625165785041868618997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13211083443856694579079331 19816625165785041868618997)
              ·
                refine ⟨1857808609292347675183031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19816625165785041868618997 1857808609292347675183031)
                ·
                  refine ⟨2786712913938521512774547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857808609292347675183031 2786712913938521512774547)
                  ·
                    refine ⟨4180069370907782269161821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786712913938521512774547 4180069370907782269161821)
                    ·
                      refine ⟨1567526014090418350935683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4180069370907782269161821 1567526014090418350935683)
                      ·
                        rfl

theorem cell23_3052746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_3052746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052746 prefixEnd_3052746 := by exact prefixLift 3052746
  have htrace : WordTrace (prefixWord ++ tailWord_3052746) baseStart_3052746 baseEnd_3052746 := by
    simpa [prefixWord, tailWord_3052746, baseEnd_3052746] using wordTrace_append hprefix tailTrace_3052746
  have hstable : (prefixWord ++ tailWord_3052746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052746).length < 2 ^ (prefixWord ++ tailWord_3052746).sum := by decide
  have hdescent : baseEnd_3052746 < baseStart_3052746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052772 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_3052772 : Nat := 118140960795 + 3052772 * 2 ^ 59
def prefixEnd_3052772 : Nat := 4983230072969 + 3 ^ 40 * 3052772 * 2
def baseEnd_3052772 : Nat := 1567539364587435249210563

theorem tailTrace_3052772 : CollatzResearch.WordTrace tailWord_3052772 prefixEnd_3052772 1567539364587435249210563 := by
  unfold tailWord_3052772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55671871048167945397084285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74229161397557260529445713 55671871048167945397084285)
  ·
    refine ⟨20876951643062979523906607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55671871048167945397084285 20876951643062979523906607)
    ·
      refine ⟨31315427464594469285859911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20876951643062979523906607 31315427464594469285859911)
      ·
        refine ⟨46973141196891703928789867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31315427464594469285859911 46973141196891703928789867)
        ·
          refine ⟨70459711795337555893184801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46973141196891703928789867 70459711795337555893184801)
          ·
            refine ⟨52844783846503166919888601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70459711795337555893184801 52844783846503166919888601)
            ·
              refine ⟨39633587884877375189916451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52844783846503166919888601 39633587884877375189916451)
              ·
                refine ⟨59450381827316062784874677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39633587884877375189916451 59450381827316062784874677)
                ·
                  refine ⟨5573473296310880886082001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59450381827316062784874677 5573473296310880886082001)
                  ·
                    refine ⟨4180104972233160664561501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5573473296310880886082001 4180104972233160664561501)
                    ·
                      refine ⟨1567539364587435249210563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4180104972233160664561501 1567539364587435249210563)
                      ·
                        rfl

theorem cell23_3052772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_3052772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052772 prefixEnd_3052772 := by exact prefixLift 3052772
  have htrace : WordTrace (prefixWord ++ tailWord_3052772) baseStart_3052772 baseEnd_3052772 := by
    simpa [prefixWord, tailWord_3052772, baseEnd_3052772] using wordTrace_append hprefix tailTrace_3052772
  have hstable : (prefixWord ++ tailWord_3052772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052772).length < 2 ^ (prefixWord ++ tailWord_3052772).sum := by decide
  have hdescent : baseEnd_3052772 < baseStart_3052772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052786 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3052786 : Nat := 118140960795 + 3052786 * 2 ^ 59
def prefixEnd_3052786 : Nat := 4983230072969 + 3 ^ 40 * 3052786 * 2
def baseEnd_3052786 : Nat := 1567546553316598194435499

theorem tailTrace_3052786 : CollatzResearch.WordTrace tailWord_3052786 prefixEnd_3052786 1567546553316598194435499 := by
  unfold tailWord_3052786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836063179571292796294553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74229501812190114123452141 27836063179571292796294553)
  ·
    refine ⟨20877047384678469597220915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27836063179571292796294553 20877047384678469597220915)
    ·
      refine ⟨31315571077017704395831373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20877047384678469597220915 31315571077017704395831373)
      ·
        refine ⟨11743339153881639148436765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31315571077017704395831373 11743339153881639148436765)
        ·
          refine ⟨4403752182705614680663787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11743339153881639148436765 4403752182705614680663787)
          ·
            refine ⟨6605628274058422020995681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403752182705614680663787 6605628274058422020995681)
            ·
              refine ⟨4954221205543816515746761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6605628274058422020995681 4954221205543816515746761)
              ·
                refine ⟨3715665904157862386810071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4954221205543816515746761 3715665904157862386810071)
                ·
                  refine ⟨5573498856236793580215107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715665904157862386810071 5573498856236793580215107)
                  ·
                    refine ⟨8360248284355190370322661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573498856236793580215107 8360248284355190370322661)
                    ·
                      refine ⟨1567546553316598194435499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8360248284355190370322661 1567546553316598194435499)
                      ·
                        rfl

theorem cell23_3052786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3052786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052786 prefixEnd_3052786 := by exact prefixLift 3052786
  have htrace : WordTrace (prefixWord ++ tailWord_3052786) baseStart_3052786 baseEnd_3052786 := by
    simpa [prefixWord, tailWord_3052786, baseEnd_3052786] using wordTrace_append hprefix tailTrace_3052786
  have hstable : (prefixWord ++ tailWord_3052786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052786).length < 2 ^ (prefixWord ++ tailWord_3052786).sum := by decide
  have hdescent : baseEnd_3052786 < baseStart_3052786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052803 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 1, 2, 2]
def baseStart_3052803 : Nat := 118140960795 + 3052803 * 2 ^ 59
def prefixEnd_3052803 : Nat := 4983230072969 + 3 ^ 40 * 3052803 * 2
def baseEnd_3052803 : Nat := 1567555282487724627922921

theorem tailTrace_3052803 : CollatzResearch.WordTrace tailWord_3052803 prefixEnd_3052803 1567555282487724627922921 := by
  unfold tailWord_3052803
  simp only [CollatzResearch.WordTrace]
  refine ⟨111344872759223583088547063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74229915172815722059031375 111344872759223583088547063)
  ·
    refine ⟨167017309138835374632820595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111344872759223583088547063 167017309138835374632820595)
    ·
      refine ⟨250525963708253061949230893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167017309138835374632820595 250525963708253061949230893)
      ·
        refine ⟨93947236390594898230961585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250525963708253061949230893 93947236390594898230961585)
        ·
          refine ⟨70460427292946173673221189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93947236390594898230961585 70460427292946173673221189)
          ·
            refine ⟨13211330117427407563728973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70460427292946173673221189 13211330117427407563728973)
            ·
              refine ⟨4954248794035277836398365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13211330117427407563728973 4954248794035277836398365)
              ·
                refine ⟨1857843297763229188649387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4954248794035277836398365 1857843297763229188649387)
                ·
                  refine ⟨2786764946644843782974081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857843297763229188649387 2786764946644843782974081)
                  ·
                    refine ⟨2090073709983632837230561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2786764946644843782974081 2090073709983632837230561)
                    ·
                      refine ⟨1567555282487724627922921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090073709983632837230561 1567555282487724627922921)
                      ·
                        rfl

theorem cell23_3052803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_3052803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052803 prefixEnd_3052803 := by exact prefixLift 3052803
  have htrace : WordTrace (prefixWord ++ tailWord_3052803) baseStart_3052803 baseEnd_3052803 := by
    simpa [prefixWord, tailWord_3052803, baseEnd_3052803] using wordTrace_append hprefix tailTrace_3052803
  have hstable : (prefixWord ++ tailWord_3052803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052803).length < 2 ^ (prefixWord ++ tailWord_3052803).sum := by decide
  have hdescent : baseEnd_3052803 < baseStart_3052803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052836 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3052836 : Nat := 118140960795 + 3052836 * 2 ^ 59
def prefixEnd_3052836 : Nat := 4983230072969 + 3 ^ 40 * 3052836 * 2
def baseEnd_3052836 : Nat := 1567572227349322998810269

theorem tailTrace_3052836 : CollatzResearch.WordTrace tailWord_3052836 prefixEnd_3052836 1567572227349322998810269 := by
  unfold tailWord_3052836
  simp only [CollatzResearch.WordTrace]
  refine ⟨55673038184052014862249181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74230717578736019816332241 55673038184052014862249181)
  ·
    refine ⟨20877389319019505573343443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55673038184052014862249181 20877389319019505573343443)
    ·
      refine ⟨31316083978529258360015165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20877389319019505573343443 31316083978529258360015165)
      ·
        refine ⟨11743531491948471885005687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31316083978529258360015165 11743531491948471885005687)
        ·
          refine ⟨17615297237922707827508531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11743531491948471885005687 17615297237922707827508531)
          ·
            refine ⟨26422945856884061741262797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17615297237922707827508531 26422945856884061741262797)
            ·
              refine ⟨9908604696331523152973549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26422945856884061741262797 9908604696331523152973549)
              ·
                refine ⟨3715726761124321182365081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9908604696331523152973549 3715726761124321182365081)
                ·
                  refine ⟨2786795070843240886773811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3715726761124321182365081 2786795070843240886773811)
                  ·
                    refine ⟨4180192606264861330160717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786795070843240886773811 4180192606264861330160717)
                    ·
                      refine ⟨1567572227349322998810269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4180192606264861330160717 1567572227349322998810269)
                      ·
                        rfl

theorem cell23_3052836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3052836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052836 prefixEnd_3052836 := by exact prefixLift 3052836
  have htrace : WordTrace (prefixWord ++ tailWord_3052836) baseStart_3052836 baseEnd_3052836 := by
    simpa [prefixWord, tailWord_3052836, baseEnd_3052836] using wordTrace_append hprefix tailTrace_3052836
  have hstable : (prefixWord ++ tailWord_3052836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052836).length < 2 ^ (prefixWord ++ tailWord_3052836).sum := by decide
  have hdescent : baseEnd_3052836 < baseStart_3052836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052863 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 1, 3, 2]
def baseStart_3052863 : Nat := 118140960795 + 3052863 * 2 ^ 59
def prefixEnd_3052863 : Nat := 4983230072969 + 3 ^ 40 * 3052863 * 2
def baseEnd_3052863 : Nat := 1567586091326994393172645

theorem tailTrace_3052863 : CollatzResearch.WordTrace tailWord_3052863 prefixEnd_3052863 1567586091326994393172645 := by
  unfold tailWord_3052863
  simp only [CollatzResearch.WordTrace]
  refine ⟨111347061139006213335731243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74231374092670808890487495 111347061139006213335731243)
  ·
    refine ⟨167020591708509320003596865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111347061139006213335731243 167020591708509320003596865)
    ·
      refine ⟨125265443781381990002697649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167020591708509320003596865 125265443781381990002697649)
      ·
        refine ⟨93949082836036492502023237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125265443781381990002697649 93949082836036492502023237)
        ·
          refine ⟨17615453031756842344129357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93949082836036492502023237 17615453031756842344129357)
          ·
            refine ⟨6605794886908815879048509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17615453031756842344129357 6605794886908815879048509)
            ·
              refine ⟨2477173082590805954643191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6605794886908815879048509 2477173082590805954643191)
              ·
                refine ⟨3715759623886208931964787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477173082590805954643191 3715759623886208931964787)
                ·
                  refine ⟨5573639435829313397947181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715759623886208931964787 5573639435829313397947181)
                  ·
                    refine ⟨2090114788435992524230193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5573639435829313397947181 2090114788435992524230193)
                    ·
                      refine ⟨1567586091326994393172645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090114788435992524230193 1567586091326994393172645)
                      ·
                        rfl

theorem cell23_3052863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_3052863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052863 prefixEnd_3052863 := by exact prefixLift 3052863
  have htrace : WordTrace (prefixWord ++ tailWord_3052863) baseStart_3052863 baseEnd_3052863 := by
    simpa [prefixWord, tailWord_3052863, baseEnd_3052863] using wordTrace_append hprefix tailTrace_3052863
  have hstable : (prefixWord ++ tailWord_3052863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052863).length < 2 ^ (prefixWord ++ tailWord_3052863).sum := by decide
  have hdescent : baseEnd_3052863 < baseStart_3052863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052872 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3052872 : Nat := 118140960795 + 3052872 * 2 ^ 59
def prefixEnd_3052872 : Nat := 4983230072969 + 3 ^ 40 * 3052872 * 2
def baseEnd_3052872 : Nat := 1567590712652884857960103

theorem tailTrace_3052872 : CollatzResearch.WordTrace tailWord_3052872 prefixEnd_3052872 1567590712652884857960103 := by
  unfold tailWord_3052872
  simp only [CollatzResearch.WordTrace]
  refine ⟨55673694697986803936404435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74231592930649071915205913 55673694697986803936404435)
  ·
    refine ⟨83510542046980205904606653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55673694697986803936404435 83510542046980205904606653)
    ·
      refine ⟨31316453267617577214227495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83510542046980205904606653 31316453267617577214227495)
      ·
        refine ⟨46974679901426365821341243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31316453267617577214227495 46974679901426365821341243)
        ·
          refine ⟨70462019852139548732011865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46974679901426365821341243 70462019852139548732011865)
          ·
            refine ⟨52846514889104661549008899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70462019852139548732011865 52846514889104661549008899)
            ·
              refine ⟨79269772333656992323513349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52846514889104661549008899 79269772333656992323513349)
              ·
                refine ⟨14863082312560686060658753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79269772333656992323513349 14863082312560686060658753)
                ·
                  refine ⟨11147311734420514545494065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14863082312560686060658753 11147311734420514545494065)
                  ·
                    refine ⟨8360483800815385909120549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11147311734420514545494065 8360483800815385909120549)
                    ·
                      refine ⟨1567590712652884857960103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8360483800815385909120549 1567590712652884857960103)
                      ·
                        rfl

theorem cell23_3052872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3052872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052872 prefixEnd_3052872 := by exact prefixLift 3052872
  have htrace : WordTrace (prefixWord ++ tailWord_3052872) baseStart_3052872 baseEnd_3052872 := by
    simpa [prefixWord, tailWord_3052872, baseEnd_3052872] using wordTrace_append hprefix tailTrace_3052872
  have hstable : (prefixWord ++ tailWord_3052872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052872).length < 2 ^ (prefixWord ++ tailWord_3052872).sum := by decide
  have hdescent : baseEnd_3052872 < baseStart_3052872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052882 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3052882 : Nat := 118140960795 + 3052882 * 2 ^ 59
def prefixEnd_3052882 : Nat := 4983230072969 + 3 ^ 40 * 3052882 * 2
def baseEnd_3052882 : Nat := 174177316384381090981673

theorem tailTrace_3052882 : CollatzResearch.WordTrace tailWord_3052882 prefixEnd_3052882 174177316384381090981673 := by
  unfold tailWord_3052882
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836938531484344895168225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74231836083958253053781933 27836938531484344895168225)
  ·
    refine ⟨20877703898613258671376169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27836938531484344895168225 20877703898613258671376169)
    ·
      refine ⟨15658277923959944003532127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20877703898613258671376169 15658277923959944003532127)
      ·
        refine ⟨23487416885939916005298191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15658277923959944003532127 23487416885939916005298191)
        ·
          refine ⟨35231125328909874007947287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23487416885939916005298191 35231125328909874007947287)
          ·
            refine ⟨52846687993364811011920931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35231125328909874007947287 52846687993364811011920931)
            ·
              refine ⟨79270031990047216517881397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52846687993364811011920931 79270031990047216517881397)
              ·
                refine ⟨7431565499066926548551381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79270031990047216517881397 7431565499066926548551381)
                ·
                  refine ⟨174177316384381090981673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7431565499066926548551381 174177316384381090981673)
                  ·
                    rfl

theorem cell23_3052882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3052882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052882 prefixEnd_3052882 := by exact prefixLift 3052882
  have htrace : WordTrace (prefixWord ++ tailWord_3052882) baseStart_3052882 baseEnd_3052882 := by
    simpa [prefixWord, tailWord_3052882, baseEnd_3052882] using wordTrace_append hprefix tailTrace_3052882
  have hstable : (prefixWord ++ tailWord_3052882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052882).length < 2 ^ (prefixWord ++ tailWord_3052882).sum := by decide
  have hdescent : baseEnd_3052882 < baseStart_3052882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052912 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_3052912 : Nat := 118140960795 + 3052912 * 2 ^ 59
def prefixEnd_3052912 : Nat := 4983230072969 + 3 ^ 40 * 3052912 * 2
def baseEnd_3052912 : Nat := 522537083959688233819973

theorem tailTrace_3052912 : CollatzResearch.WordTrace tailWord_3052912 prefixEnd_3052912 522537083959688233819973 := by
  unfold tailWord_3052912
  simp only [CollatzResearch.WordTrace]
  refine ⟨55674424157914347352132495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74232565543885796469509993 55674424157914347352132495)
  ·
    refine ⟨83511636236871521028198743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55674424157914347352132495 83511636236871521028198743)
    ·
      refine ⟨125267454355307281542298115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83511636236871521028198743 125267454355307281542298115)
      ·
        refine ⟨187901181532960922313447173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125267454355307281542298115 187901181532960922313447173)
        ·
          refine ⟨35231471537430172933771345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187901181532960922313447173 35231471537430172933771345)
          ·
            refine ⟨26423603653072629700328509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35231471537430172933771345 26423603653072629700328509)
            ·
              refine ⟨9908851369902236137623191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26423603653072629700328509 9908851369902236137623191)
              ·
                refine ⟨14863277054853354206434787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9908851369902236137623191 14863277054853354206434787)
                ·
                  refine ⟨22294915582280031309652181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14863277054853354206434787 22294915582280031309652181)
                  ·
                    refine ⟨522537083959688233819973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22294915582280031309652181 522537083959688233819973)
                    ·
                      rfl

theorem cell23_3052912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_3052912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052912 prefixEnd_3052912 := by exact prefixLift 3052912
  have htrace : WordTrace (prefixWord ++ tailWord_3052912) baseStart_3052912 baseEnd_3052912 := by
    simpa [prefixWord, tailWord_3052912, baseEnd_3052912] using wordTrace_append hprefix tailTrace_3052912
  have hstable : (prefixWord ++ tailWord_3052912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052912).length < 2 ^ (prefixWord ++ tailWord_3052912).sum := by decide
  have hdescent : baseEnd_3052912 < baseStart_3052912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052972 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 8]
def baseStart_3052972 : Nat := 118140960795 + 3052972 * 2 ^ 59
def prefixEnd_3052972 : Nat := 4983230072969 + 3 ^ 40 * 3052972 * 2
def baseEnd_3052972 : Nat := 174182451190926051856627

theorem tailTrace_3052972 : CollatzResearch.WordTrace tailWord_3052972 prefixEnd_3052972 174182451190926051856627 := by
  unfold tailWord_3052972
  simp only [CollatzResearch.WordTrace]
  refine ⟨55675518347805662475724585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74234024463740883300966113 55675518347805662475724585)
  ·
    refine ⟨41756638760854246856793439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55675518347805662475724585 41756638760854246856793439)
    ·
      refine ⟨62634958141281370285190159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41756638760854246856793439 62634958141281370285190159)
      ·
        refine ⟨93952437211922055427785239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62634958141281370285190159 93952437211922055427785239)
        ·
          refine ⟨140928655817883083141677859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93952437211922055427785239 140928655817883083141677859)
          ·
            refine ⟨211392983726824624712516789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140928655817883083141677859 211392983726824624712516789)
            ·
              refine ⟨19818092224389808566798449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211392983726824624712516789 19818092224389808566798449)
              ·
                refine ⟨14863569168292356425098837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19818092224389808566798449 14863569168292356425098837)
                ·
                  refine ⟨174182451190926051856627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14863569168292356425098837 174182451190926051856627)
                  ·
                    rfl

theorem cell23_3052972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_3052972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052972 prefixEnd_3052972 := by exact prefixLift 3052972
  have htrace : WordTrace (prefixWord ++ tailWord_3052972) baseStart_3052972 baseEnd_3052972 := by
    simpa [prefixWord, tailWord_3052972, baseEnd_3052972] using wordTrace_append hprefix tailTrace_3052972
  have hstable : (prefixWord ++ tailWord_3052972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052972).length < 2 ^ (prefixWord ++ tailWord_3052972).sum := by decide
  have hdescent : baseEnd_3052972 < baseStart_3052972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052976 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 1, 4]
def baseStart_3052976 : Nat := 118140960795 + 3052976 * 2 ^ 59
def prefixEnd_3052976 : Nat := 4983230072969 + 3 ^ 40 * 3052976 * 2
def baseEnd_3052976 : Nat := 522548038213650817019875

theorem tailTrace_3052976 : CollatzResearch.WordTrace tailWord_3052976 prefixEnd_3052976 522548038213650817019875 := by
  unfold tailWord_3052976
  simp only [CollatzResearch.WordTrace]
  refine ⟨55675591293798416817297391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74234121725064555756396521 55675591293798416817297391)
  ·
    refine ⟨83513386940697625225946087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55675591293798416817297391 83513386940697625225946087)
    ·
      refine ⟨125270080411046437838919131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83513386940697625225946087 125270080411046437838919131)
      ·
        refine ⟨187905120616569656758378697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125270080411046437838919131 187905120616569656758378697)
        ·
          refine ⟨140928840462427242568784023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187905120616569656758378697 140928840462427242568784023)
          ·
            refine ⟨211393260693640863853176035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140928840462427242568784023 211393260693640863853176035)
            ·
              refine ⟨317089891040461295779764053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211393260693640863853176035 317089891040461295779764053)
              ·
                refine ⟨1857948580315202904959555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 317089891040461295779764053 1857948580315202904959555)
                ·
                  refine ⟨2786922870472804357439333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857948580315202904959555 2786922870472804357439333)
                  ·
                    refine ⟨522548038213650817019875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786922870472804357439333 522548038213650817019875)
                    ·
                      rfl

theorem cell23_3052976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 4].length) (baseStart_3052976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052976 prefixEnd_3052976 := by exact prefixLift 3052976
  have htrace : WordTrace (prefixWord ++ tailWord_3052976) baseStart_3052976 baseEnd_3052976 := by
    simpa [prefixWord, tailWord_3052976, baseEnd_3052976] using wordTrace_append hprefix tailTrace_3052976
  have hstable : (prefixWord ++ tailWord_3052976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052976).length < 2 ^ (prefixWord ++ tailWord_3052976).sum := by decide
  have hdescent : baseEnd_3052976 < baseStart_3052976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052989 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 6]
def baseStart_3052989 : Nat := 118140960795 + 3052989 * 2 ^ 59
def prefixEnd_3052989 : Nat := 4983230072969 + 3 ^ 40 * 3052989 * 2
def baseEnd_3052989 : Nat := 174183421098828988910785

theorem tailTrace_3052989 : CollatzResearch.WordTrace tailWord_3052989 prefixEnd_3052989 174183421098828988910785 := by
  unfold tailWord_3052989
  simp only [CollatzResearch.WordTrace]
  refine ⟨111351656736549736854818021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74234437824366491236545347 111351656736549736854818021)
  ·
    refine ⟨20878435638103075660278379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111351656736549736854818021 20878435638103075660278379)
    ·
      refine ⟨31317653457154613490417569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20878435638103075660278379 31317653457154613490417569)
      ·
        refine ⟨23488240092865960117813177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31317653457154613490417569 23488240092865960117813177)
        ·
          refine ⟨17616180069649470088359883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23488240092865960117813177 17616180069649470088359883)
          ·
            refine ⟨26424270104474205132539825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17616180069649470088359883 26424270104474205132539825)
            ·
              refine ⟨19818202578355653849404869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26424270104474205132539825 19818202578355653849404869)
              ·
                refine ⟨3715912983441685096763413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19818202578355653849404869 3715912983441685096763413)
                ·
                  refine ⟨174183421098828988910785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3715912983441685096763413 174183421098828988910785)
                  ·
                    rfl

theorem cell23_3052989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_3052989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052989 prefixEnd_3052989 := by exact prefixLift 3052989
  have htrace : WordTrace (prefixWord ++ tailWord_3052989) baseStart_3052989 baseEnd_3052989 := by
    simpa [prefixWord, tailWord_3052989, baseEnd_3052989] using wordTrace_append hprefix tailTrace_3052989
  have hstable : (prefixWord ++ tailWord_3052989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052989).length < 2 ^ (prefixWord ++ tailWord_3052989).sum := by decide
  have hdescent : baseEnd_3052989 < baseStart_3052989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3052992 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3052992 : Nat := 118140960795 + 3052992 * 2 ^ 59
def prefixEnd_3052992 : Nat := 4983230072969 + 3 ^ 40 * 3052992 * 2
def baseEnd_3052992 : Nat := 1567652330331424388459551

theorem tailTrace_3052992 : CollatzResearch.WordTrace tailWord_3052992 prefixEnd_3052992 1567652330331424388459551 := by
  unfold tailWord_3052992
  simp only [CollatzResearch.WordTrace]
  refine ⟨55675883077769434183588615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74234510770359245578118153 55675883077769434183588615)
  ·
    refine ⟨83513824616654151275382923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55675883077769434183588615 83513824616654151275382923)
    ·
      refine ⟨125270736924981226913074385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83513824616654151275382923 125270736924981226913074385)
      ·
        refine ⟨93953052693735920184805789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125270736924981226913074385 93953052693735920184805789)
        ·
          refine ⟨35232394760150970069302171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93953052693735920184805789 35232394760150970069302171)
          ·
            refine ⟨52848592140226455103953257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35232394760150970069302171 52848592140226455103953257)
            ·
              refine ⟨39636444105169841327964943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52848592140226455103953257 39636444105169841327964943)
              ·
                refine ⟨59454666157754761991947415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39636444105169841327964943 59454666157754761991947415)
                ·
                  refine ⟨89181999236632142987921123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59454666157754761991947415 89181999236632142987921123)
                  ·
                    refine ⟨133772998854948214481881685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89181999236632142987921123 133772998854948214481881685)
                    ·
                      refine ⟨1567652330331424388459551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 133772998854948214481881685 1567652330331424388459551)
                      ·
                        rfl

theorem cell23_3052992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3052992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3052992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3052992 prefixEnd_3052992 := by exact prefixLift 3052992
  have htrace : WordTrace (prefixWord ++ tailWord_3052992) baseStart_3052992 baseEnd_3052992 := by
    simpa [prefixWord, tailWord_3052992, baseEnd_3052992] using wordTrace_append hprefix tailTrace_3052992
  have hstable : (prefixWord ++ tailWord_3052992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3052992).length < 2 ^ (prefixWord ++ tailWord_3052992).sum := by decide
  have hdescent : baseEnd_3052992 < baseStart_3052992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3052992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053006 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_3053006 : Nat := 118140960795 + 3053006 * 2 ^ 59
def prefixEnd_3053006 : Nat := 4983230072969 + 3 ^ 40 * 3053006 * 2
def baseEnd_3053006 : Nat := 174184391006731925964943

theorem tailTrace_3053006 : CollatzResearch.WordTrace tailWord_3053006 prefixEnd_3053006 174184391006731925964943 := by
  unfold tailWord_3053006
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919034597186018594773359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74234851184992099172124581 13919034597186018594773359)
  ·
    refine ⟨20878551895779027892160039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13919034597186018594773359 20878551895779027892160039)
    ·
      refine ⟨31317827843668541838240059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20878551895779027892160039 31317827843668541838240059)
      ·
        refine ⟨46976741765502812757360089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31317827843668541838240059 46976741765502812757360089)
        ·
          refine ⟨35232556324127109568020067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46976741765502812757360089 35232556324127109568020067)
          ·
            refine ⟨52848834486190664352030101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35232556324127109568020067 52848834486190664352030101)
            ·
              refine ⟨2477289116540187391501411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52848834486190664352030101 2477289116540187391501411)
              ·
                refine ⟨3715933674810281087252117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477289116540187391501411 3715933674810281087252117)
                ·
                  refine ⟨174184391006731925964943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3715933674810281087252117 174184391006731925964943)
                  ·
                    rfl

theorem cell23_3053006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_3053006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053006 prefixEnd_3053006 := by exact prefixLift 3053006
  have htrace : WordTrace (prefixWord ++ tailWord_3053006) baseStart_3053006 baseEnd_3053006 := by
    simpa [prefixWord, tailWord_3053006, baseEnd_3053006] using wordTrace_append hprefix tailTrace_3053006
  have hstable : (prefixWord ++ tailWord_3053006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053006).length < 2 ^ (prefixWord ++ tailWord_3053006).sum := by decide
  have hdescent : baseEnd_3053006 < baseStart_3053006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053016 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3053016 : Nat := 118140960795 + 3053016 * 2 ^ 59
def prefixEnd_3053016 : Nat := 4983230072969 + 3 ^ 40 * 3053016 * 2
def baseEnd_3053016 : Nat := 1567664653867132294559441

theorem tailTrace_3053016 : CollatzResearch.WordTrace tailWord_3053016 prefixEnd_3053016 1567664653867132294559441 := by
  unfold tailWord_3053016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55676320753725960233025451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74235094338301280310700601 55676320753725960233025451)
  ·
    refine ⟨83514481130588940349538177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55676320753725960233025451 83514481130588940349538177)
    ·
      refine ⟨62635860847941705262153633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83514481130588940349538177 62635860847941705262153633)
      ·
        refine ⟨46976895635956278946615225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62635860847941705262153633 46976895635956278946615225)
        ·
          refine ⟨35232671726967209209961419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46976895635956278946615225 35232671726967209209961419)
          ·
            refine ⟨52849007590450813814942129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35232671726967209209961419 52849007590450813814942129)
            ·
              refine ⟨39636755692838110361206597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52849007590450813814942129 39636755692838110361206597)
              ·
                refine ⟨7431891692407145692726237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39636755692838110361206597 7431891692407145692726237)
                ·
                  refine ⟨2786959384652679634772339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7431891692407145692726237 2786959384652679634772339)
                  ·
                    refine ⟨4180439076979019452158509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2786959384652679634772339 4180439076979019452158509)
                    ·
                      refine ⟨1567664653867132294559441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4180439076979019452158509 1567664653867132294559441)
                      ·
                        rfl

theorem cell23_3053016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3053016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053016 prefixEnd_3053016 := by exact prefixLift 3053016
  have htrace : WordTrace (prefixWord ++ tailWord_3053016) baseStart_3053016 baseEnd_3053016 := by
    simpa [prefixWord, tailWord_3053016, baseEnd_3053016] using wordTrace_append hprefix tailTrace_3053016
  have hstable : (prefixWord ++ tailWord_3053016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053016).length < 2 ^ (prefixWord ++ tailWord_3053016).sum := by decide
  have hdescent : baseEnd_3053016 < baseStart_3053016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053066 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3053066 : Nat := 118140960795 + 3053066 * 2 ^ 59
def prefixEnd_3053066 : Nat := 4983230072969 + 3 ^ 40 * 3053066 * 2
def baseEnd_3053066 : Nat := 522563442633285699644737

theorem tailTrace_3053066 : CollatzResearch.WordTrace tailWord_3053066 prefixEnd_3053066 522563442633285699644737 := by
  unfold tailWord_3053066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27838616289317694751342763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74236310104847186003580701 27838616289317694751342763)
  ·
    refine ⟨41757924433976542127014145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27838616289317694751342763 41757924433976542127014145)
    ·
      refine ⟨31318443325482406595260609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41757924433976542127014145 31318443325482406595260609)
      ·
        refine ⟨23488832494111804946445457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31318443325482406595260609 23488832494111804946445457)
        ·
          refine ⟨17616624370583853709834093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23488832494111804946445457 17616624370583853709834093)
          ·
            refine ⟨6606234138968945141187785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17616624370583853709834093 6606234138968945141187785)
            ·
              refine ⟨4954675604226708855890839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606234138968945141187785 4954675604226708855890839)
              ·
                refine ⟨7432013406340063283836259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4954675604226708855890839 7432013406340063283836259)
                ·
                  refine ⟨11148020109510094925754389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7432013406340063283836259 11148020109510094925754389)
                  ·
                    refine ⟨522563442633285699644737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11148020109510094925754389 522563442633285699644737)
                    ·
                      rfl

theorem cell23_3053066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3053066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053066 prefixEnd_3053066 := by exact prefixLift 3053066
  have htrace : WordTrace (prefixWord ++ tailWord_3053066) baseStart_3053066 baseEnd_3053066 := by
    simpa [prefixWord, tailWord_3053066, baseEnd_3053066] using wordTrace_append hprefix tailTrace_3053066
  have hstable : (prefixWord ++ tailWord_3053066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053066).length < 2 ^ (prefixWord ++ tailWord_3053066).sum := by decide
  have hdescent : baseEnd_3053066 < baseStart_3053066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053073 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 3, 2, 2]
def baseStart_3053073 : Nat := 118140960795 + 3053073 * 2 ^ 59
def prefixEnd_3053073 : Nat := 4983230072969 + 3 ^ 40 * 3053073 * 2
def baseEnd_3053073 : Nat := 1567693922264438571546679

theorem tailTrace_3053073 : CollatzResearch.WordTrace tailWord_3053073 prefixEnd_3053073 1567693922264438571546679 := by
  unfold tailWord_3053073
  simp only [CollatzResearch.WordTrace]
  refine ⟨111354720468245419200875873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74236480312163612800583915 111354720468245419200875873)
  ·
    refine ⟨83516040351184064400656905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111354720468245419200875873 83516040351184064400656905)
    ·
      refine ⟨62637030263388048300492679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83516040351184064400656905 62637030263388048300492679)
      ·
        refine ⟨93955545395082072450739019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62637030263388048300492679 93955545395082072450739019)
        ·
          refine ⟨140933318092623108676108529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93955545395082072450739019 140933318092623108676108529)
          ·
            refine ⟨105699988569467331507081397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140933318092623108676108529 105699988569467331507081397)
            ·
              refine ⟨9909373928387562328788881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105699988569467331507081397 9909373928387562328788881)
              ·
                refine ⟨7432030446290671746591661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9909373928387562328788881 7432030446290671746591661)
                ·
                  refine ⟨2787011417359001904971873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7432030446290671746591661 2787011417359001904971873)
                  ·
                    refine ⟨2090258563019251428728905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2787011417359001904971873 2090258563019251428728905)
                    ·
                      refine ⟨1567693922264438571546679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090258563019251428728905 1567693922264438571546679)
                      ·
                        rfl

theorem cell23_3053073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_3053073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053073 prefixEnd_3053073 := by exact prefixLift 3053073
  have htrace : WordTrace (prefixWord ++ tailWord_3053073) baseStart_3053073 baseEnd_3053073 := by
    simpa [prefixWord, tailWord_3053073, baseEnd_3053073] using wordTrace_append hprefix tailTrace_3053073
  have hstable : (prefixWord ++ tailWord_3053073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053073).length < 2 ^ (prefixWord ++ tailWord_3053073).sum := by decide
  have hdescent : baseEnd_3053073 < baseStart_3053073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053096 : List Nat := [2, 1, 5, 2, 2, 1, 10]
def baseStart_3053096 : Nat := 118140960795 + 3053096 * 2 ^ 59
def prefixEnd_3053096 : Nat := 4983230072969 + 3 ^ 40 * 3053096 * 2
def baseEnd_3053096 : Nat := 19354391757030765204433

theorem tailTrace_3053096 : CollatzResearch.WordTrace tailWord_3053096 prefixEnd_3053096 19354391757030765204433 := by
  unfold tailWord_3053096
  simp only [CollatzResearch.WordTrace]
  refine ⟨55677779673581047064481571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74237039564774729419308761 55677779673581047064481571)
  ·
    refine ⟨83516669510371570596722357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55677779673581047064481571 83516669510371570596722357)
    ·
      refine ⟨7829687766597334743442721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83516669510371570596722357 7829687766597334743442721)
      ·
        refine ⟨5872265824948001057582041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829687766597334743442721 5872265824948001057582041)
        ·
          refine ⟨4404199368711000793186531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5872265824948001057582041 4404199368711000793186531)
          ·
            refine ⟨6606299053066501189779797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404199368711000793186531 6606299053066501189779797)
            ·
              refine ⟨19354391757030765204433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6606299053066501189779797 19354391757030765204433)
              ·
                rfl

theorem cell23_3053096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 10].length) (baseStart_3053096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053096 prefixEnd_3053096 := by exact prefixLift 3053096
  have htrace : WordTrace (prefixWord ++ tailWord_3053096) baseStart_3053096 baseEnd_3053096 := by
    simpa [prefixWord, tailWord_3053096, baseEnd_3053096] using wordTrace_append hprefix tailTrace_3053096
  have hstable : (prefixWord ++ tailWord_3053096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053096).length < 2 ^ (prefixWord ++ tailWord_3053096).sum := by decide
  have hdescent : baseEnd_3053096 < baseStart_3053096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053129 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_3053129 : Nat := 118140960795 + 3053129 * 2 ^ 59
def prefixEnd_3053129 : Nat := 4983230072969 + 3 ^ 40 * 3053129 * 2
def baseEnd_3053129 : Nat := 1567722677181090352446421

theorem tailTrace_3053129 : CollatzResearch.WordTrace tailWord_3053129 prefixEnd_3053129 1567722677181090352446421 := by
  unfold tailWord_3053129
  simp only [CollatzResearch.WordTrace]
  refine ⟨111356762956042540764914441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74237841970695027176609627 111356762956042540764914441)
  ·
    refine ⟨83517572217031905573685831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111356762956042540764914441 83517572217031905573685831)
    ·
      refine ⟨125276358325547858360528747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83517572217031905573685831 125276358325547858360528747)
      ·
        refine ⟨187914537488321787540793121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125276358325547858360528747 187914537488321787540793121)
        ·
          refine ⟨140935903116241340655594841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187914537488321787540793121 140935903116241340655594841)
          ·
            refine ⟨105701927337181005491696131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140935903116241340655594841 105701927337181005491696131)
            ·
              refine ⟨158552891005771508237544197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105701927337181005491696131 158552891005771508237544197)
              ·
                refine ⟨29728667063582157794539537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158552891005771508237544197 29728667063582157794539537)
                ·
                  refine ⟨22296500297686618345904653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29728667063582157794539537 22296500297686618345904653)
                  ·
                    refine ⟨8361187611632481879714245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22296500297686618345904653 8361187611632481879714245)
                    ·
                      refine ⟨1567722677181090352446421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8361187611632481879714245 1567722677181090352446421)
                      ·
                        rfl

theorem cell23_3053129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_3053129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053129 prefixEnd_3053129 := by exact prefixLift 3053129
  have htrace : WordTrace (prefixWord ++ tailWord_3053129) baseStart_3053129 baseEnd_3053129 := by
    simpa [prefixWord, tailWord_3053129, baseEnd_3053129] using wordTrace_append hprefix tailTrace_3053129
  have hstable : (prefixWord ++ tailWord_3053129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053129).length < 2 ^ (prefixWord ++ tailWord_3053129).sum := by decide
  have hdescent : baseEnd_3053129 < baseStart_3053129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053174 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_3053174 : Nat := 118140960795 + 3053174 * 2 ^ 59
def prefixEnd_3053174 : Nat := 4983230072969 + 3 ^ 40 * 3053174 * 2
def baseEnd_3053174 : Nat := 1567745783810542676383715

theorem tailTrace_3053174 : CollatzResearch.WordTrace tailWord_3053174 prefixEnd_3053174 1567745783810542676383715 := by
  unfold tailWord_3053174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959900265054969590643911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74238936160586342300201717 6959900265054969590643911)
  ·
    refine ⟨10439850397582454385965867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6959900265054969590643911 10439850397582454385965867)
    ·
      refine ⟨15659775596373681578948801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439850397582454385965867 15659775596373681578948801)
      ·
        refine ⟨11744831697280261184211601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15659775596373681578948801 11744831697280261184211601)
        ·
          refine ⟨8808623772960195888158701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11744831697280261184211601 8808623772960195888158701)
          ·
            refine ⟨3303233914860073458059513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8808623772960195888158701 3303233914860073458059513)
            ·
              refine ⟨2477425436145055093544635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303233914860073458059513 2477425436145055093544635)
              ·
                refine ⟨3716138154217582640316953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477425436145055093544635 3716138154217582640316953)
                ·
                  refine ⟨2787103615663186980237715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3716138154217582640316953 2787103615663186980237715)
                  ·
                    refine ⟨4180655423494780470356573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2787103615663186980237715 4180655423494780470356573)
                    ·
                      refine ⟨1567745783810542676383715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4180655423494780470356573 1567745783810542676383715)
                      ·
                        rfl

theorem cell23_3053174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_3053174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053174 prefixEnd_3053174 := by exact prefixLift 3053174
  have htrace : WordTrace (prefixWord ++ tailWord_3053174) baseStart_3053174 baseEnd_3053174 := by
    simpa [prefixWord, tailWord_3053174, baseEnd_3053174] using wordTrace_append hprefix tailTrace_3053174
  have hstable : (prefixWord ++ tailWord_3053174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053174).length < 2 ^ (prefixWord ++ tailWord_3053174).sum := by decide
  have hdescent : baseEnd_3053174 < baseStart_3053174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053214 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_3053214 : Nat := 118140960795 + 3053214 * 2 ^ 59
def prefixEnd_3053214 : Nat := 4983230072969 + 3 ^ 40 * 3053214 * 2
def baseEnd_3053214 : Nat := 1567766323036722519883531

theorem tailTrace_3053214 : CollatzResearch.WordTrace tailWord_3053214 prefixEnd_3053214 1567766323036722519883531 := by
  unfold tailWord_3053214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919982895091825035219837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74239908773823066854505797 13919982895091825035219837)
  ·
    refine ⟨5219993585659434388207439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13919982895091825035219837 5219993585659434388207439)
    ·
      refine ⟨7829990378489151582311159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219993585659434388207439 7829990378489151582311159)
      ·
        refine ⟨11744985567733727373466739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829990378489151582311159 11744985567733727373466739)
        ·
          refine ⟨17617478351600591060200109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11744985567733727373466739 17617478351600591060200109)
          ·
            refine ⟨6606554381850221647575041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17617478351600591060200109 6606554381850221647575041)
            ·
              refine ⟨4954915786387666235681281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606554381850221647575041 4954915786387666235681281)
              ·
                refine ⟨3716186839790749676760961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4954915786387666235681281 3716186839790749676760961)
                ·
                  refine ⟨2787140129843062257570721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3716186839790749676760961 2787140129843062257570721)
                  ·
                    refine ⟨2090355097382296693178041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2787140129843062257570721 2090355097382296693178041)
                    ·
                      refine ⟨1567766323036722519883531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090355097382296693178041 1567766323036722519883531)
                      ·
                        rfl

theorem cell23_3053214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_3053214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053214 prefixEnd_3053214 := by exact prefixLift 3053214
  have htrace : WordTrace (prefixWord ++ tailWord_3053214) baseStart_3053214 baseEnd_3053214 := by
    simpa [prefixWord, tailWord_3053214, baseEnd_3053214] using wordTrace_append hprefix tailTrace_3053214
  have hstable : (prefixWord ++ tailWord_3053214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053214).length < 2 ^ (prefixWord ++ tailWord_3053214).sum := by decide
  have hdescent : baseEnd_3053214 < baseStart_3053214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053220 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 5]
def baseStart_3053220 : Nat := 118140960795 + 3053220 * 2 ^ 59
def prefixEnd_3053220 : Nat := 4983230072969 + 3 ^ 40 * 3053220 * 2
def baseEnd_3053220 : Nat := 174196600435627721823167

theorem tailTrace_3053220 : CollatzResearch.WordTrace tailWord_3053220 prefixEnd_3053220 174196600435627721823167 := by
  unfold tailWord_3053220
  simp only [CollatzResearch.WordTrace]
  refine ⟨55680040999356431653238557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74240054665808575537651409 55680040999356431653238557)
  ·
    refine ⟨20880015374758661869964459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55680040999356431653238557 20880015374758661869964459)
    ·
      refine ⟨31320023062137992804946689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20880015374758661869964459 31320023062137992804946689)
      ·
        refine ⟨23490017296603494603710017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31320023062137992804946689 23490017296603494603710017)
        ·
          refine ⟨17617512972452620952782513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23490017296603494603710017 17617512972452620952782513)
          ·
            refine ⟨13213134729339465714586885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17617512972452620952782513 13213134729339465714586885)
            ·
              refine ⟨2477462761751149821485041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13213134729339465714586885 2477462761751149821485041)
              ·
                refine ⟨1858097071313362366113781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477462761751149821485041 1858097071313362366113781)
                ·
                  refine ⟨174196600435627721823167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858097071313362366113781 174196600435627721823167)
                  ·
                    rfl

theorem cell23_3053220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_3053220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053220 prefixEnd_3053220 := by exact prefixLift 3053220
  have htrace : WordTrace (prefixWord ++ tailWord_3053220) baseStart_3053220 baseEnd_3053220 := by
    simpa [prefixWord, tailWord_3053220, baseEnd_3053220] using wordTrace_append hprefix tailTrace_3053220
  have hstable : (prefixWord ++ tailWord_3053220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053220).length < 2 ^ (prefixWord ++ tailWord_3053220).sum := by decide
  have hdescent : baseEnd_3053220 < baseStart_3053220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053254 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_3053254 : Nat := 118140960795 + 3053254 * 2 ^ 59
def prefixEnd_3053254 : Nat := 4983230072969 + 3 ^ 40 * 3053254 * 2
def baseEnd_3053254 : Nat := 174198540251433595931483

theorem tailTrace_3053254 : CollatzResearch.WordTrace tailWord_3053254 prefixEnd_3053254 174198540251433595931483 := by
  unfold tailWord_3053254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480041315018427722287963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74240881387059791408809877 3480041315018427722287963)
  ·
    refine ⟨5220061972527641583431945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3480041315018427722287963 5220061972527641583431945)
    ·
      refine ⟨3915046479395731187573959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5220061972527641583431945 3915046479395731187573959)
      ·
        refine ⟨5872569719093596781360939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915046479395731187573959 5872569719093596781360939)
        ·
          refine ⟨8808854578640395172041409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5872569719093596781360939 8808854578640395172041409)
          ·
            refine ⟨6606640933980296379031057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8808854578640395172041409 6606640933980296379031057)
            ·
              refine ⟨4954980700485222284273293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606640933980296379031057 4954980700485222284273293)
              ·
                refine ⟨1858117762681958356602485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4954980700485222284273293 1858117762681958356602485)
                ·
                  refine ⟨174198540251433595931483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858117762681958356602485 174198540251433595931483)
                  ·
                    rfl

theorem cell23_3053254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_3053254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053254 prefixEnd_3053254 := by exact prefixLift 3053254
  have htrace : WordTrace (prefixWord ++ tailWord_3053254) baseStart_3053254 baseEnd_3053254 := by
    simpa [prefixWord, tailWord_3053254, baseEnd_3053254] using wordTrace_append hprefix tailTrace_3053254
  have hstable : (prefixWord ++ tailWord_3053254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053254).length < 2 ^ (prefixWord ++ tailWord_3053254).sum := by decide
  have hdescent : baseEnd_3053254 < baseStart_3053254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053280 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 1, 4]
def baseStart_3053280 : Nat := 118140960795 + 3053280 * 2 ^ 59
def prefixEnd_3053280 : Nat := 4983230072969 + 3 ^ 40 * 3053280 * 2
def baseEnd_3053280 : Nat := 522600070919973087219409

theorem tailTrace_3053280 : CollatzResearch.WordTrace tailWord_3053280 prefixEnd_3053280 522600070919973087219409 := by
  unfold tailWord_3053280
  simp only [CollatzResearch.WordTrace]
  refine ⟨55681135189247746776830647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74241513585663662369107529 55681135189247746776830647)
  ·
    refine ⟨83521702783871620165245971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55681135189247746776830647 83521702783871620165245971)
    ·
      refine ⟨125282554175807430247868957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83521702783871620165245971 125282554175807430247868957)
      ·
        refine ⟨46980957815927786342950859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125282554175807430247868957 46980957815927786342950859)
        ·
          refine ⟨70471436723891679514426289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46980957815927786342950859 70471436723891679514426289)
          ·
            refine ⟨52853577542918759635819717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70471436723891679514426289 52853577542918759635819717)
            ·
              refine ⟨9910045789297267431716197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52853577542918759635819717 9910045789297267431716197)
              ·
                refine ⟨1858133585493237643446787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9910045789297267431716197 1858133585493237643446787)
                ·
                  refine ⟨2787200378239856465170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858133585493237643446787 2787200378239856465170181)
                  ·
                    refine ⟨522600070919973087219409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787200378239856465170181 522600070919973087219409)
                    ·
                      rfl

theorem cell23_3053280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 4].length) (baseStart_3053280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053280 prefixEnd_3053280 := by exact prefixLift 3053280
  have htrace : WordTrace (prefixWord ++ tailWord_3053280) baseStart_3053280 baseEnd_3053280 := by
    simpa [prefixWord, tailWord_3053280, baseEnd_3053280] using wordTrace_append hprefix tailTrace_3053280
  have hstable : (prefixWord ++ tailWord_3053280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053280).length < 2 ^ (prefixWord ++ tailWord_3053280).sum := by decide
  have hdescent : baseEnd_3053280 < baseStart_3053280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053323 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 1, 5]
def baseStart_3053323 : Nat := 118140960795 + 3053323 * 2 ^ 59
def prefixEnd_3053323 : Nat := 4983230072969 + 3 ^ 40 * 3053323 * 2
def baseEnd_3053323 : Nat := 522607430809354197806843

theorem tailTrace_3053323 : CollatzResearch.WordTrace tailWord_3053323 prefixEnd_3053323 522607430809354197806843 := by
  unfold tailWord_3053323
  simp only [CollatzResearch.WordTrace]
  refine ⟨111363838717339711897476623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74242559144893141264984415 111363838717339711897476623)
  ·
    refine ⟨167045758076009567846214935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111363838717339711897476623 167045758076009567846214935)
    ·
      refine ⟨250568637114014351769322403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167045758076009567846214935 250568637114014351769322403)
      ·
        refine ⟨375852955671021527653983605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250568637114014351769322403 375852955671021527653983605)
        ·
          refine ⟨35236214594158268217560963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375852955671021527653983605 35236214594158268217560963)
          ·
            refine ⟨52854321891237402326341445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35236214594158268217560963 52854321891237402326341445)
            ·
              refine ⟨9910185354607012936189021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52854321891237402326341445 9910185354607012936189021)
              ·
                refine ⟨3716319507977629851070883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9910185354607012936189021 3716319507977629851070883)
                ·
                  refine ⟨5574479261966444776606325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716319507977629851070883 5574479261966444776606325)
                  ·
                    refine ⟨522607430809354197806843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5574479261966444776606325 522607430809354197806843)
                    ·
                      rfl

theorem cell23_3053323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 5].length) (baseStart_3053323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053323 prefixEnd_3053323 := by exact prefixLift 3053323
  have htrace : WordTrace (prefixWord ++ tailWord_3053323) baseStart_3053323 baseEnd_3053323 := by
    simpa [prefixWord, tailWord_3053323, baseEnd_3053323] using wordTrace_append hprefix tailTrace_3053323
  have hstable : (prefixWord ++ tailWord_3053323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053323).length < 2 ^ (prefixWord ++ tailWord_3053323).sum := by decide
  have hdescent : baseEnd_3053323 < baseStart_3053323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053343 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3053343 : Nat := 118140960795 + 3053343 * 2 ^ 59
def prefixEnd_3053343 : Nat := 4983230072969 + 3 ^ 40 * 3053343 * 2
def baseEnd_3053343 : Nat := 1567832562041152515170437

theorem tailTrace_3053343 : CollatzResearch.WordTrace tailWord_3053343 prefixEnd_3053343 1567832562041152515170437 := by
  unfold tailWord_3053343
  simp only [CollatzResearch.WordTrace]
  refine ⟨111364568177267255313204683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74243045451511503542136455 111364568177267255313204683)
  ·
    refine ⟨167046852265900882969807025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111364568177267255313204683 167046852265900882969807025)
    ·
      refine ⟨125285139199425662227355269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167046852265900882969807025 125285139199425662227355269)
      ·
        refine ⟨23490963599892311667629113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125285139199425662227355269 23490963599892311667629113)
        ·
          refine ⟨17618222699919233750721835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23490963599892311667629113 17618222699919233750721835)
          ·
            refine ⟨26427334049878850626082753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17618222699919233750721835 26427334049878850626082753)
            ·
              refine ⟨19820500537409137969562065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26427334049878850626082753 19820500537409137969562065)
              ·
                refine ⟨14865375403056853477171549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19820500537409137969562065 14865375403056853477171549)
                ·
                  refine ⟨5574515776146320053939331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14865375403056853477171549 5574515776146320053939331)
                  ·
                    refine ⟨8361773664219480080908997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5574515776146320053939331 8361773664219480080908997)
                    ·
                      refine ⟨1567832562041152515170437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8361773664219480080908997 1567832562041152515170437)
                      ·
                        rfl

theorem cell23_3053343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3053343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053343 prefixEnd_3053343 := by exact prefixLift 3053343
  have htrace : WordTrace (prefixWord ++ tailWord_3053343) baseStart_3053343 baseEnd_3053343 := by
    simpa [prefixWord, tailWord_3053343, baseEnd_3053343] using wordTrace_append hprefix tailTrace_3053343
  have hstable : (prefixWord ++ tailWord_3053343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053343).length < 2 ^ (prefixWord ++ tailWord_3053343).sum := by decide
  have hdescent : baseEnd_3053343 < baseStart_3053343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053364 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3053364 : Nat := 118140960795 + 3053364 * 2 ^ 59
def prefixEnd_3053364 : Nat := 4983230072969 + 3 ^ 40 * 3053364 * 2
def baseEnd_3053364 : Nat := 1567843345134896933007841

theorem tailTrace_3053364 : CollatzResearch.WordTrace tailWord_3053364 prefixEnd_3053364 1567843345134896933007841 := by
  unfold tailWord_3053364
  simp only [CollatzResearch.WordTrace]
  refine ⟨55682667055095587949859573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74243556073460783933146097 55682667055095587949859573)
  ·
    refine ⟨5220250036415211370299335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55682667055095587949859573 5220250036415211370299335)
    ·
      refine ⟨7830375054622817055449003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5220250036415211370299335 7830375054622817055449003)
      ·
        refine ⟨11745562581934225583173505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830375054622817055449003 11745562581934225583173505)
        ·
          refine ⟨8809171936450669187380129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11745562581934225583173505 8809171936450669187380129)
          ·
            refine ⟨6606878952338001890535097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8809171936450669187380129 6606878952338001890535097)
            ·
              refine ⟨4955159214253501417901323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606878952338001890535097 4955159214253501417901323)
              ·
                refine ⟨7432738821380252126851985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955159214253501417901323 7432738821380252126851985)
                ·
                  refine ⟨5574554116035189095138989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7432738821380252126851985 5574554116035189095138989)
                  ·
                    refine ⟨2090457793513195910677121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5574554116035189095138989 2090457793513195910677121)
                    ·
                      refine ⟨1567843345134896933007841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090457793513195910677121 1567843345134896933007841)
                      ·
                        rfl

theorem cell23_3053364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3053364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053364 prefixEnd_3053364 := by exact prefixLift 3053364
  have htrace : WordTrace (prefixWord ++ tailWord_3053364) baseStart_3053364 baseEnd_3053364 := by
    simpa [prefixWord, tailWord_3053364, baseEnd_3053364] using wordTrace_append hprefix tailTrace_3053364
  have hstable : (prefixWord ++ tailWord_3053364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053364).length < 2 ^ (prefixWord ++ tailWord_3053364).sum := by decide
  have hdescent : baseEnd_3053364 < baseStart_3053364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053388 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3053388 : Nat := 118140960795 + 3053388 * 2 ^ 59
def prefixEnd_3053388 : Nat := 4983230072969 + 3 ^ 40 * 3053388 * 2
def baseEnd_3053388 : Nat := 1567855668670604839107731

theorem tailTrace_3053388 : CollatzResearch.WordTrace tailWord_3053388 prefixEnd_3053388 1567855668670604839107731 := by
  unfold tailWord_3053388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55683104731052113999296409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74244139641402818665728545 55683104731052113999296409)
  ·
    refine ⟨41762328548289085499472307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55683104731052113999296409 41762328548289085499472307)
    ·
      refine ⟨62643492822433628249208461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41762328548289085499472307 62643492822433628249208461)
      ·
        refine ⟨23491309808412610593453173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62643492822433628249208461 23491309808412610593453173)
        ·
          refine ⟨2202310294538682243136235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23491309808412610593453173 2202310294538682243136235)
          ·
            refine ⟨3303465441808023364704353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202310294538682243136235 3303465441808023364704353)
            ·
              refine ⟨2477599081356017523528265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303465441808023364704353 2477599081356017523528265)
              ·
                refine ⟨1858199311017013142646199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477599081356017523528265 1858199311017013142646199)
                ·
                  refine ⟨2787298966525519713969299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858199311017013142646199 2787298966525519713969299)
                  ·
                    refine ⟨4180948449788279570953949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2787298966525519713969299 4180948449788279570953949)
                    ·
                      refine ⟨1567855668670604839107731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4180948449788279570953949 1567855668670604839107731)
                      ·
                        rfl

theorem cell23_3053388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3053388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053388 prefixEnd_3053388 := by exact prefixLift 3053388
  have htrace : WordTrace (prefixWord ++ tailWord_3053388) baseStart_3053388 baseEnd_3053388 := by
    simpa [prefixWord, tailWord_3053388, baseEnd_3053388] using wordTrace_append hprefix tailTrace_3053388
  have hstable : (prefixWord ++ tailWord_3053388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053388).length < 2 ^ (prefixWord ++ tailWord_3053388).sum := by decide
  have hdescent : baseEnd_3053388 < baseStart_3053388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053443 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 2, 6]
def baseStart_3053443 : Nat := 118140960795 + 3053443 * 2 ^ 59
def prefixEnd_3053443 : Nat := 4983230072969 + 3 ^ 40 * 3053443 * 2
def baseEnd_3053443 : Nat := 522627970035534041306659

theorem tailTrace_3053443 : CollatzResearch.WordTrace tailWord_3053443 prefixEnd_3053443 522627970035534041306659 := by
  unfold tailWord_3053443
  simp only [CollatzResearch.WordTrace]
  refine ⟨111368215476904972391844983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74245476984603314927896655 111368215476904972391844983)
  ·
    refine ⟨167052323215357458587767475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111368215476904972391844983 167052323215357458587767475)
    ·
      refine ⟨250578484823036187881651213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167052323215357458587767475 250578484823036187881651213)
      ·
        refine ⟨93966931808638570455619205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250578484823036187881651213 93966931808638570455619205)
        ·
          refine ⟨17618799714119731960428601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93966931808638570455619205 17618799714119731960428601)
          ·
            refine ⟨13214099785589798970321451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17618799714119731960428601 13214099785589798970321451)
            ·
              refine ⟨19821149678384698455482177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13214099785589798970321451 19821149678384698455482177)
              ·
                refine ⟨14865862258788523841611633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19821149678384698455482177 14865862258788523841611633)
                ·
                  refine ⟨11149396694091392881208725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14865862258788523841611633 11149396694091392881208725)
                  ·
                    refine ⟨522627970035534041306659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11149396694091392881208725 522627970035534041306659)
                    ·
                      rfl

theorem cell23_3053443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 6].length) (baseStart_3053443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053443 prefixEnd_3053443 := by exact prefixLift 3053443
  have htrace : WordTrace (prefixWord ++ tailWord_3053443) baseStart_3053443 baseEnd_3053443 := by
    simpa [prefixWord, tailWord_3053443, baseEnd_3053443] using wordTrace_append hprefix tailTrace_3053443
  have hstable : (prefixWord ++ tailWord_3053443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053443).length < 2 ^ (prefixWord ++ tailWord_3053443).sum := by decide
  have hdescent : baseEnd_3053443 < baseStart_3053443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053460 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3053460 : Nat := 118140960795 + 3053460 * 2 ^ 59
def prefixEnd_3053460 : Nat := 4983230072969 + 3 ^ 40 * 3053460 * 2
def baseEnd_3053460 : Nat := 522630879759242852469133

theorem tailTrace_3053460 : CollatzResearch.WordTrace tailWord_3053460 prefixEnd_3053460 522630879759242852469133 := by
  unfold tailWord_3053460
  simp only [CollatzResearch.WordTrace]
  refine ⟨55684417758921692147606917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74245890345228922863475889 55684417758921692147606917)
  ·
    refine ⟨10440828329797817277676297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55684417758921692147606917 10440828329797817277676297)
    ·
      refine ⟨7830621247348362958257223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10440828329797817277676297 7830621247348362958257223)
      ·
        refine ⟨11745931871022544437385835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830621247348362958257223 11745931871022544437385835)
        ·
          refine ⟨17618897806533816656078753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11745931871022544437385835 17618897806533816656078753)
          ·
            refine ⟨13214173354900362492059065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17618897806533816656078753 13214173354900362492059065)
            ·
              refine ⟨9910630016175271869044299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13214173354900362492059065 9910630016175271869044299)
              ·
                refine ⟨14865945024262907803566449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9910630016175271869044299 14865945024262907803566449)
                ·
                  refine ⟨11149458768197180852674837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14865945024262907803566449 11149458768197180852674837)
                  ·
                    refine ⟨522630879759242852469133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11149458768197180852674837 522630879759242852469133)
                    ·
                      rfl

theorem cell23_3053460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3053460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053460 prefixEnd_3053460 := by exact prefixLift 3053460
  have htrace : WordTrace (prefixWord ++ tailWord_3053460) baseStart_3053460 baseEnd_3053460 := by
    simpa [prefixWord, tailWord_3053460, baseEnd_3053460] using wordTrace_append hprefix tailTrace_3053460
  have hstable : (prefixWord ++ tailWord_3053460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053460).length < 2 ^ (prefixWord ++ tailWord_3053460).sum := by decide
  have hdescent : baseEnd_3053460 < baseStart_3053460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053513 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_3053513 : Nat := 118140960795 + 3053513 * 2 ^ 59
def prefixEnd_3053513 : Nat := 4983230072969 + 3 ^ 40 * 3053513 * 2
def baseEnd_3053513 : Nat := 1567919853752416850044655

theorem tailTrace_3053513 : CollatzResearch.WordTrace tailWord_3053513 prefixEnd_3053513 1567919853752416850044655 := by
  unfold tailWord_3053513
  simp only [CollatzResearch.WordTrace]
  refine ⟨111370768586651374346893193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74247179057767582897928795 111370768586651374346893193)
  ·
    refine ⟨83528076439988530760169895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111370768586651374346893193 83528076439988530760169895)
    ·
      refine ⟨125292114659982796140254843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83528076439988530760169895 125292114659982796140254843)
      ·
        refine ⟨187938171989974194210382265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125292114659982796140254843 187938171989974194210382265)
        ·
          refine ⟨140953628992480645657786699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187938171989974194210382265 140953628992480645657786699)
          ·
            refine ⟨211430443488720968486680049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140953628992480645657786699 211430443488720968486680049)
            ·
              refine ⟨158572832616540726365010037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211430443488720968486680049 158572832616540726365010037)
              ·
                refine ⟨14866203057800693096719691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158572832616540726365010037 14866203057800693096719691)
                ·
                  refine ⟨22299304586701039645079537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14866203057800693096719691 22299304586701039645079537)
                  ·
                    refine ⟨16724478440025779733809653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22299304586701039645079537 16724478440025779733809653)
                    ·
                      refine ⟨1567919853752416850044655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16724478440025779733809653 1567919853752416850044655)
                      ·
                        rfl

theorem cell23_3053513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_3053513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053513 prefixEnd_3053513 := by exact prefixLift 3053513
  have htrace : WordTrace (prefixWord ++ tailWord_3053513) baseStart_3053513 baseEnd_3053513 := by
    simpa [prefixWord, tailWord_3053513, baseEnd_3053513] using wordTrace_append hprefix tailTrace_3053513
  have hstable : (prefixWord ++ tailWord_3053513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053513).length < 2 ^ (prefixWord ++ tailWord_3053513).sum := by decide
  have hdescent : baseEnd_3053513 < baseStart_3053513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053558 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_3053558 : Nat := 118140960795 + 3053558 * 2 ^ 59
def prefixEnd_3053558 : Nat := 4983230072969 + 3 ^ 40 * 3053558 * 2
def baseEnd_3053558 : Nat := 174215884486874352664661

theorem tailTrace_3053558 : CollatzResearch.WordTrace tailWord_3053558 prefixEnd_3053558 174215884486874352664661 := by
  unfold tailWord_3053558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6960775616968021689517583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74248273247658898021520885 6960775616968021689517583)
  ·
    refine ⟨10441163425452032534276375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6960775616968021689517583 10441163425452032534276375)
    ·
      refine ⟨15661745138178048801414563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10441163425452032534276375 15661745138178048801414563)
      ·
        refine ⟨23492617707267073202121845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15661745138178048801414563 23492617707267073202121845)
        ·
          refine ⟨2202432910056288112698923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23492617707267073202121845 2202432910056288112698923)
          ·
            refine ⟨3303649365084432169048385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202432910056288112698923 3303649365084432169048385)
            ·
              refine ⟨2477737023813324126786289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303649365084432169048385 2477737023813324126786289)
              ·
                refine ⟨1858302767859993095089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477737023813324126786289 1858302767859993095089717)
                ·
                  refine ⟨174215884486874352664661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858302767859993095089717 174215884486874352664661)
                  ·
                    rfl

theorem cell23_3053558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_3053558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053558 prefixEnd_3053558 := by exact prefixLift 3053558
  have htrace : WordTrace (prefixWord ++ tailWord_3053558) baseStart_3053558 baseEnd_3053558 := by
    simpa [prefixWord, tailWord_3053558, baseEnd_3053558] using wordTrace_append hprefix tailTrace_3053558
  have hstable : (prefixWord ++ tailWord_3053558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053558).length < 2 ^ (prefixWord ++ tailWord_3053558).sum := by decide
  have hdescent : baseEnd_3053558 < baseStart_3053558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053563 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 8]
def baseStart_3053563 : Nat := 118140960795 + 3053563 * 2 ^ 59
def prefixEnd_3053563 : Nat := 4983230072969 + 3 ^ 40 * 3053563 * 2
def baseEnd_3053563 : Nat := 174216169753904628268825

theorem tailTrace_3053563 : CollatzResearch.WordTrace tailWord_3053563 prefixEnd_3053563 174216169753904628268825 := by
  unfold tailWord_3053563
  simp only [CollatzResearch.WordTrace]
  refine ⟨111372592236470232886213343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74248394824313488590808895 111372592236470232886213343)
  ·
    refine ⟨167058888354705349329320015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111372592236470232886213343 167058888354705349329320015)
    ·
      refine ⟨250588332532058023993980023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167058888354705349329320015 250588332532058023993980023)
      ·
        refine ⟨375882498798087035990970035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250588332532058023993980023 375882498798087035990970035)
        ·
          refine ⟨563823748197130553986455053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375882498798087035990970035 563823748197130553986455053)
          ·
            refine ⟨211433905573923957744920645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563823748197130553986455053 211433905573923957744920645)
            ·
              refine ⟨39643857295110742077172621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211433905573923957744920645 39643857295110742077172621)
              ·
                refine ⟨14866446485666528278939733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39643857295110742077172621 14866446485666528278939733)
                ·
                  refine ⟨174216169753904628268825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14866446485666528278939733 174216169753904628268825)
                  ·
                    rfl

theorem cell23_3053563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 8].length) (baseStart_3053563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053563 prefixEnd_3053563 := by exact prefixLift 3053563
  have htrace : WordTrace (prefixWord ++ tailWord_3053563) baseStart_3053563 baseEnd_3053563 := by
    simpa [prefixWord, tailWord_3053563, baseEnd_3053563] using wordTrace_append hprefix tailTrace_3053563
  have hstable : (prefixWord ++ tailWord_3053563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053563).length < 2 ^ (prefixWord ++ tailWord_3053563).sum := by decide
  have hdescent : baseEnd_3053563 < baseStart_3053563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053580 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 6]
def baseStart_3053580 : Nat := 118140960795 + 3053580 * 2 ^ 59
def prefixEnd_3053580 : Nat := 4983230072969 + 3 ^ 40 * 3053580 * 2
def baseEnd_3053580 : Nat := 174217139661807565322983

theorem tailTrace_3053580 : CollatzResearch.WordTrace tailWord_3053580 prefixEnd_3053580 174217139661807565322983 := by
  unfold tailWord_3053580
  simp only [CollatzResearch.WordTrace]
  refine ⟨55686606138704322394791097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74248808184939096526388129 55686606138704322394791097)
  ·
    refine ⟨41764954604028241796093323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55686606138704322394791097 41764954604028241796093323)
    ·
      refine ⟨62647431906042362694139985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41764954604028241796093323 62647431906042362694139985)
      ·
        refine ⟨46985573929531772020604989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62647431906042362694139985 46985573929531772020604989)
        ·
          refine ⟨17619590223574414507726871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46985573929531772020604989 17619590223574414507726871)
          ·
            refine ⟨26429385335361621761590307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17619590223574414507726871 26429385335361621761590307)
            ·
              refine ⟨39644078003042432642385461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26429385335361621761590307 39644078003042432642385461)
              ·
                refine ⟨3716632312785228060223637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39644078003042432642385461 3716632312785228060223637)
                ·
                  refine ⟨174217139661807565322983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3716632312785228060223637 174217139661807565322983)
                  ·
                    rfl

theorem cell23_3053580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_3053580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053580 prefixEnd_3053580 := by exact prefixLift 3053580
  have htrace : WordTrace (prefixWord ++ tailWord_3053580) baseStart_3053580 baseEnd_3053580 := by
    simpa [prefixWord, tailWord_3053580, baseEnd_3053580] using wordTrace_append hprefix tailTrace_3053580
  have hstable : (prefixWord ++ tailWord_3053580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053580).length < 2 ^ (prefixWord ++ tailWord_3053580).sum := by decide
  have hdescent : baseEnd_3053580 < baseStart_3053580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053588 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3053588 : Nat := 118140960795 + 3053588 * 2 ^ 59
def prefixEnd_3053588 : Nat := 4983230072969 + 3 ^ 40 * 3053588 * 2
def baseEnd_3053588 : Nat := 522652788267168018868937

theorem tailTrace_3053588 : CollatzResearch.WordTrace tailWord_3053588 prefixEnd_3053588 522652788267168018868937 := by
  unfold tailWord_3053588
  simp only [CollatzResearch.WordTrace]
  refine ⟨55686752030689831077936709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74249002707586441437248945 55686752030689831077936709)
  ·
    refine ⟨10441266005754343327113133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55686752030689831077936709 10441266005754343327113133)
    ·
      refine ⟨3915474752157878747667425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10441266005754343327113133 3915474752157878747667425)
      ·
        refine ⟨2936606064118409060750569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3915474752157878747667425 2936606064118409060750569)
        ·
          refine ⟨2202454548088806795562927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936606064118409060750569 2202454548088806795562927)
          ·
            refine ⟨3303681822133210193344391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202454548088806795562927 3303681822133210193344391)
            ·
              refine ⟨4955522733199815290016587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303681822133210193344391 4955522733199815290016587)
              ·
                refine ⟨7433284099799722935024881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955522733199815290016587 7433284099799722935024881)
                ·
                  refine ⟨5574963074849792201268661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7433284099799722935024881 5574963074849792201268661)
                  ·
                    refine ⟨522652788267168018868937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5574963074849792201268661 522652788267168018868937)
                    ·
                      rfl

theorem cell23_3053588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3053588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053588 prefixEnd_3053588 := by exact prefixLift 3053588
  have htrace : WordTrace (prefixWord ++ tailWord_3053588) baseStart_3053588 baseEnd_3053588 := by
    simpa [prefixWord, tailWord_3053588, baseEnd_3053588] using wordTrace_append hprefix tailTrace_3053588
  have hstable : (prefixWord ++ tailWord_3053588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053588).length < 2 ^ (prefixWord ++ tailWord_3053588).sum := by decide
  have hdescent : baseEnd_3053588 < baseStart_3053588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053591 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3053591 : Nat := 118140960795 + 3053591 * 2 ^ 59
def prefixEnd_3053591 : Nat := 4983230072969 + 3 ^ 40 * 3053591 * 2
def baseEnd_3053591 : Nat := 1567959905243467544869297

theorem tailTrace_3053591 : CollatzResearch.WordTrace tailWord_3053591 prefixEnd_3053591 1567959905243467544869297 := by
  unfold tailWord_3053591
  simp only [CollatzResearch.WordTrace]
  refine ⟨111373613480368793668232627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74249075653579195778821751 111373613480368793668232627)
  ·
    refine ⟨167060420220553190502348941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111373613480368793668232627 167060420220553190502348941)
    ·
      refine ⟨62647657582707446438380853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167060420220553190502348941 62647657582707446438380853)
      ·
        refine ⟨5873217898378823103598205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62647657582707446438380853 5873217898378823103598205)
        ·
          refine ⟨2202456711892058663849327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5873217898378823103598205 2202456711892058663849327)
          ·
            refine ⟨3303685067838087995773991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202456711892058663849327 3303685067838087995773991)
            ·
              refine ⟨4955527601757131993660987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303685067838087995773991 4955527601757131993660987)
              ·
                refine ⟨7433291402635697990491481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955527601757131993660987 7433291402635697990491481)
                ·
                  refine ⟨5574968551976773492868611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7433291402635697990491481 5574968551976773492868611)
                  ·
                    refine ⟨8362452827965160239302917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5574968551976773492868611 8362452827965160239302917)
                    ·
                      refine ⟨1567959905243467544869297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8362452827965160239302917 1567959905243467544869297)
                      ·
                        rfl

theorem cell23_3053591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3053591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053591 prefixEnd_3053591 := by exact prefixLift 3053591
  have htrace : WordTrace (prefixWord ++ tailWord_3053591) baseStart_3053591 baseEnd_3053591 := by
    simpa [prefixWord, tailWord_3053591, baseEnd_3053591] using wordTrace_append hprefix tailTrace_3053591
  have hstable : (prefixWord ++ tailWord_3053591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053591).length < 2 ^ (prefixWord ++ tailWord_3053591).sum := by decide
  have hdescent : baseEnd_3053591 < baseStart_3053591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053594 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_3053594 : Nat := 118140960795 + 3053594 * 2 ^ 59
def prefixEnd_3053594 : Nat := 4983230072969 + 3 ^ 40 * 3053594 * 2
def baseEnd_3053594 : Nat := 1567961445685431033131783

theorem tailTrace_3053594 : CollatzResearch.WordTrace tailWord_3053594 prefixEnd_3053594 1567961445685431033131783 := by
  unfold tailWord_3053594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27843430724839481295147959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74249148599571950120394557 27843430724839481295147959)
  ·
    refine ⟨41765146087259221942721939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27843430724839481295147959 41765146087259221942721939)
    ·
      refine ⟨62647719130888832914082909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41765146087259221942721939 62647719130888832914082909)
      ·
        refine ⟨23492894674083312342781091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62647719130888832914082909 23492894674083312342781091)
        ·
          refine ⟨35239342011124968514171637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23492894674083312342781091 35239342011124968514171637)
          ·
            refine ⟨3303688313542965798203591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35239342011124968514171637 3303688313542965798203591)
            ·
              refine ⟨4955532470314448697305387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303688313542965798203591 4955532470314448697305387)
              ·
                refine ⟨7433298705471673045958081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955532470314448697305387 7433298705471673045958081)
                ·
                  refine ⟨5574974029103754784468561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7433298705471673045958081 5574974029103754784468561)
                  ·
                    refine ⟨4181230521827816088351421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5574974029103754784468561 4181230521827816088351421)
                    ·
                      refine ⟨1567961445685431033131783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181230521827816088351421 1567961445685431033131783)
                      ·
                        rfl

theorem cell23_3053594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_3053594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053594 prefixEnd_3053594 := by exact prefixLift 3053594
  have htrace : WordTrace (prefixWord ++ tailWord_3053594) baseStart_3053594 baseEnd_3053594 := by
    simpa [prefixWord, tailWord_3053594, baseEnd_3053594] using wordTrace_append hprefix tailTrace_3053594
  have hstable : (prefixWord ++ tailWord_3053594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053594).length < 2 ^ (prefixWord ++ tailWord_3053594).sum := by decide
  have hdescent : baseEnd_3053594 < baseStart_3053594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053601 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 1, 4]
def baseStart_3053601 : Nat := 118140960795 + 3053601 * 2 ^ 59
def prefixEnd_3053601 : Nat := 4983230072969 + 3 ^ 40 * 3053601 * 2
def baseEnd_3053601 : Nat := 522655013350004168581417

theorem tailTrace_3053601 : CollatzResearch.WordTrace tailWord_3053601 prefixEnd_3053601 522655013350004168581417 := by
  unfold tailWord_3053601
  simp only [CollatzResearch.WordTrace]
  refine ⟨111373978210332565376096657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74249318806888376917397771 111373978210332565376096657)
  ·
    refine ⟨83530483657749424032072493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111373978210332565376096657 83530483657749424032072493)
    ·
      refine ⟨31323931371656034012027185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83530483657749424032072493 31323931371656034012027185)
      ·
        refine ⟨23492948528742025509020389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31323931371656034012027185 23492948528742025509020389)
        ·
          refine ⟨4404927849139129782941323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23492948528742025509020389 4404927849139129782941323)
          ·
            refine ⟨6607391773708694674411985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404927849139129782941323 6607391773708694674411985)
            ·
              refine ⟨4955543830281521005808989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6607391773708694674411985 4955543830281521005808989)
              ·
                refine ⟨1858328936355570377178371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4955543830281521005808989 1858328936355570377178371)
                ·
                  refine ⟨2787493404533355565767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858328936355570377178371 2787493404533355565767557)
                  ·
                    refine ⟨522655013350004168581417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787493404533355565767557 522655013350004168581417)
                    ·
                      rfl

theorem cell23_3053601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_3053601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053601 prefixEnd_3053601 := by exact prefixLift 3053601
  have htrace : WordTrace (prefixWord ++ tailWord_3053601) baseStart_3053601 baseEnd_3053601 := by
    simpa [prefixWord, tailWord_3053601, baseEnd_3053601] using wordTrace_append hprefix tailTrace_3053601
  have hstable : (prefixWord ++ tailWord_3053601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053601).length < 2 ^ (prefixWord ++ tailWord_3053601).sum := by decide
  have hdescent : baseEnd_3053601 < baseStart_3053601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053614 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_3053614 : Nat := 118140960795 + 3053614 * 2 ^ 59
def prefixEnd_3053614 : Nat := 4983230072969 + 3 ^ 40 * 3053614 * 2
def baseEnd_3053614 : Nat := 174219079477613439431299

theorem tailTrace_3053614 : CollatzResearch.WordTrace tailWord_3053614 prefixEnd_3053614 174219079477613439431299 := by
  unfold tailWord_3053614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13921806544910683574539987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74249634906190312397546597 13921806544910683574539987)
  ·
    refine ⟨20882709817366025361809981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13921806544910683574539987 20882709817366025361809981)
    ·
      refine ⟨7831016181512259510678743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20882709817366025361809981 7831016181512259510678743)
      ·
        refine ⟨11746524272268389266018115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831016181512259510678743 11746524272268389266018115)
        ·
          refine ⟨17619786408402583899027173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11746524272268389266018115 17619786408402583899027173)
          ·
            refine ⟨3303709951575484481067595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17619786408402583899027173 3303709951575484481067595)
            ·
              refine ⟨4955564927363226721601393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303709951575484481067595 4955564927363226721601393)
              ·
                refine ⟨3716673695522420041201045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4955564927363226721601393 3716673695522420041201045)
                ·
                  refine ⟨174219079477613439431299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3716673695522420041201045 174219079477613439431299)
                  ·
                    rfl

theorem cell23_3053614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_3053614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053614 prefixEnd_3053614 := by exact prefixLift 3053614
  have htrace : WordTrace (prefixWord ++ tailWord_3053614) baseStart_3053614 baseEnd_3053614 := by
    simpa [prefixWord, tailWord_3053614, baseEnd_3053614] using wordTrace_append hprefix tailTrace_3053614
  have hstable : (prefixWord ++ tailWord_3053614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053614).length < 2 ^ (prefixWord ++ tailWord_3053614).sum := by decide
  have hdescent : baseEnd_3053614 < baseStart_3053614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053640 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3053640 : Nat := 118140960795 + 3053640 * 2 ^ 59
def prefixEnd_3053640 : Nat := 4983230072969 + 3 ^ 40 * 3053640 * 2
def baseEnd_3053640 : Nat := 522661688598512617718857

theorem tailTrace_3053640 : CollatzResearch.WordTrace tailWord_3053640 prefixEnd_3053640 522661688598512617718857 := by
  unfold tailWord_3053640
  simp only [CollatzResearch.WordTrace]
  refine ⟨55687700328595637518383187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74250267104794183357844249 55687700328595637518383187)
  ·
    refine ⟨83531550492893456277574781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55687700328595637518383187 83531550492893456277574781)
    ·
      refine ⟨31324331434835046104090543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83531550492893456277574781 31324331434835046104090543)
      ·
        refine ⟨46986497152252569156135815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31324331434835046104090543 46986497152252569156135815)
        ·
          refine ⟨70479745728378853734203723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46986497152252569156135815 70479745728378853734203723)
          ·
            refine ⟨105719618592568280601305585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70479745728378853734203723 105719618592568280601305585)
            ·
              refine ⟨79289713944426210450979189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105719618592568280601305585 79289713944426210450979189)
              ·
                refine ⟨7433410682289957229779299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79289713944426210450979189 7433410682289957229779299)
                ·
                  refine ⟨11150116023434935844668949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433410682289957229779299 11150116023434935844668949)
                  ·
                    refine ⟨522661688598512617718857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11150116023434935844668949 522661688598512617718857)
                    ·
                      rfl

theorem cell23_3053640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3053640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053640 prefixEnd_3053640 := by exact prefixLift 3053640
  have htrace : WordTrace (prefixWord ++ tailWord_3053640) baseStart_3053640 baseEnd_3053640 := by
    simpa [prefixWord, tailWord_3053640, baseEnd_3053640] using wordTrace_append hprefix tailTrace_3053640
  have hstable : (prefixWord ++ tailWord_3053640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053640).length < 2 ^ (prefixWord ++ tailWord_3053640).sum := by decide
  have hdescent : baseEnd_3053640 < baseStart_3053640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053701 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_3053701 : Nat := 118140960795 + 3053701 * 2 ^ 59
def prefixEnd_3053701 : Nat := 4983230072969 + 3 ^ 40 * 3053701 * 2
def baseEnd_3053701 : Nat := 1568016388115462114493791

theorem tailTrace_3053701 : CollatzResearch.WordTrace tailWord_3053701 prefixEnd_3053701 1568016388115462114493791 := by
  unfold tailWord_3053701
  simp only [CollatzResearch.WordTrace]
  refine ⟨111377625509970282454736957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74251750339980188303157971 111377625509970282454736957)
  ·
    refine ⟨41766609566238855920526359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111377625509970282454736957 41766609566238855920526359)
    ·
      refine ⟨62649914349358283880789539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41766609566238855920526359 62649914349358283880789539)
      ·
        refine ⟨93974871524037425821184309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62649914349358283880789539 93974871524037425821184309)
        ·
          refine ⟨8810144205378508670736029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93974871524037425821184309 8810144205378508670736029)
          ·
            refine ⟨3303804077016940751526011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8810144205378508670736029 3303804077016940751526011)
            ·
              refine ⟨4955706115525411127289017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303804077016940751526011 4955706115525411127289017)
              ·
                refine ⟨3716779586644058345466763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4955706115525411127289017 3716779586644058345466763)
                ·
                  refine ⟨5575169379966087518200145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716779586644058345466763 5575169379966087518200145)
                  ·
                    refine ⟨4181377034974565638650109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5575169379966087518200145 4181377034974565638650109)
                    ·
                      refine ⟨1568016388115462114493791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181377034974565638650109 1568016388115462114493791)
                      ·
                        rfl

theorem cell23_3053701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_3053701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053701 prefixEnd_3053701 := by exact prefixLift 3053701
  have htrace : WordTrace (prefixWord ++ tailWord_3053701) baseStart_3053701 baseEnd_3053701 := by
    simpa [prefixWord, tailWord_3053701, baseEnd_3053701] using wordTrace_append hprefix tailTrace_3053701
  have hstable : (prefixWord ++ tailWord_3053701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053701).length < 2 ^ (prefixWord ++ tailWord_3053701).sum := by decide
  have hdescent : baseEnd_3053701 < baseStart_3053701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053714 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3053714 : Nat := 118140960795 + 3053714 * 2 ^ 59
def prefixEnd_3053714 : Nat := 4983230072969 + 3 ^ 40 * 3053714 * 2
def baseEnd_3053714 : Nat := 1568023063363970563631231

theorem tailTrace_3053714 : CollatzResearch.WordTrace tailWord_3053714 prefixEnd_3053714 1568023063363970563631231 := by
  unfold tailWord_3053714
  simp only [CollatzResearch.WordTrace]
  refine ⟨27844524914730796418740049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74252066439282123783306797 27844524914730796418740049)
  ·
    refine ⟨20883393686048097314055037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27844524914730796418740049 20883393686048097314055037)
    ·
      refine ⟨7831272632268036492770639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20883393686048097314055037 7831272632268036492770639)
      ·
        refine ⟨11746908948402054739155959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831272632268036492770639 11746908948402054739155959)
        ·
          refine ⟨17620363422603082108733939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11746908948402054739155959 17620363422603082108733939)
          ·
            refine ⟨26430545133904623163100909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17620363422603082108733939 26430545133904623163100909)
            ·
              refine ⟨9911454425214233686162841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26430545133904623163100909 9911454425214233686162841)
              ·
                refine ⟨7433590818910675264622131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9911454425214233686162841 7433590818910675264622131)
                ·
                  refine ⟨11150386228366012896933197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433590818910675264622131 11150386228366012896933197)
                  ·
                    refine ⟨4181394835637254836349949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11150386228366012896933197 4181394835637254836349949)
                    ·
                      refine ⟨1568023063363970563631231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181394835637254836349949 1568023063363970563631231)
                      ·
                        rfl

theorem cell23_3053714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3053714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053714 prefixEnd_3053714 := by exact prefixLift 3053714
  have htrace : WordTrace (prefixWord ++ tailWord_3053714) baseStart_3053714 baseEnd_3053714 := by
    simpa [prefixWord, tailWord_3053714, baseEnd_3053714] using wordTrace_append hprefix tailTrace_3053714
  have hstable : (prefixWord ++ tailWord_3053714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053714).length < 2 ^ (prefixWord ++ tailWord_3053714).sum := by decide
  have hdescent : baseEnd_3053714 < baseStart_3053714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053732 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_3053732 : Nat := 118140960795 + 3053732 * 2 ^ 59
def prefixEnd_3053732 : Nat := 4983230072969 + 3 ^ 40 * 3053732 * 2
def baseEnd_3053732 : Nat := 1568032306015751493206149

theorem tailTrace_3053732 : CollatzResearch.WordTrace tailWord_3053732 prefixEnd_3053732 1568032306015751493206149 := by
  unfold tailWord_3053732
  simp only [CollatzResearch.WordTrace]
  refine ⟨55689378086428987374557725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74252504115238649832743633 55689378086428987374557725)
  ·
    refine ⟨20883516782410870265459147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55689378086428987374557725 20883516782410870265459147)
    ·
      refine ⟨31325275173616305398188721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20883516782410870265459147 31325275173616305398188721)
      ·
        refine ⟨23493956380212229048641541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31325275173616305398188721 23493956380212229048641541)
        ·
          refine ⟨4405116821289792946620289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23493956380212229048641541 4405116821289792946620289)
          ·
            refine ⟨3303837615967344709965217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4405116821289792946620289 3303837615967344709965217)
            ·
              refine ⟨2477878211975508532473913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303837615967344709965217 2477878211975508532473913)
              ·
                refine ⟨1858408658981631399355435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477878211975508532473913 1858408658981631399355435)
                ·
                  refine ⟨2787612988472447099033153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858408658981631399355435 2787612988472447099033153)
                  ·
                    refine ⟨2090709741354335324274865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2787612988472447099033153 2090709741354335324274865)
                    ·
                      refine ⟨1568032306015751493206149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090709741354335324274865 1568032306015751493206149)
                      ·
                        rfl

theorem cell23_3053732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_3053732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053732 prefixEnd_3053732 := by exact prefixLift 3053732
  have htrace : WordTrace (prefixWord ++ tailWord_3053732) baseStart_3053732 baseEnd_3053732 := by
    simpa [prefixWord, tailWord_3053732, baseEnd_3053732] using wordTrace_append hprefix tailTrace_3053732
  have hstable : (prefixWord ++ tailWord_3053732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053732).length < 2 ^ (prefixWord ++ tailWord_3053732).sum := by decide
  have hdescent : baseEnd_3053732 < baseStart_3053732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053737 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 10, 2]
def baseStart_3053737 : Nat := 118140960795 + 3053737 * 2 ^ 59
def prefixEnd_3053737 : Nat := 4983230072969 + 3 ^ 40 * 3053737 * 2
def baseEnd_3053737 : Nat := 1568034873419023973643625

theorem tailTrace_3053737 : CollatzResearch.WordTrace tailWord_3053737 prefixEnd_3053737 1568034873419023973643625 := by
  unfold tailWord_3053737
  simp only [CollatzResearch.WordTrace]
  refine ⟨111378938537839860603047465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74252625691893240402031643 111378938537839860603047465)
  ·
    refine ⟨83534203903379895452285599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111378938537839860603047465 83534203903379895452285599)
    ·
      refine ⟨125301305855069843178428399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83534203903379895452285599 125301305855069843178428399)
      ·
        refine ⟨187951958782604764767642599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125301305855069843178428399 187951958782604764767642599)
        ·
          refine ⟨281927938173907147151463899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187951958782604764767642599 281927938173907147151463899)
          ·
            refine ⟨422891907260860720727195849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281927938173907147151463899 422891907260860720727195849)
            ·
              refine ⟨317168930445645540545396887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422891907260860720727195849 317168930445645540545396887)
              ·
                refine ⟨475753395668468310818095331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317168930445645540545396887 475753395668468310818095331)
                ·
                  refine ⟨713630093502702466227142997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475753395668468310818095331 713630093502702466227142997)
                  ·
                    refine ⟨2090713164558698631524833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 713630093502702466227142997 2090713164558698631524833)
                    ·
                      refine ⟨1568034873419023973643625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090713164558698631524833 1568034873419023973643625)
                      ·
                        rfl

theorem cell23_3053737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 10, 2].length) (baseStart_3053737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053737 prefixEnd_3053737 := by exact prefixLift 3053737
  have htrace : WordTrace (prefixWord ++ tailWord_3053737) baseStart_3053737 baseEnd_3053737 := by
    simpa [prefixWord, tailWord_3053737, baseEnd_3053737] using wordTrace_append hprefix tailTrace_3053737
  have hstable : (prefixWord ++ tailWord_3053737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053737).length < 2 ^ (prefixWord ++ tailWord_3053737).sum := by decide
  have hdescent : baseEnd_3053737 < baseStart_3053737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053741 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3053741 : Nat := 118140960795 + 3053741 * 2 ^ 59
def prefixEnd_3053741 : Nat := 4983230072969 + 3 ^ 40 * 3053741 * 2
def baseEnd_3053741 : Nat := 1568036927341641957993607

theorem tailTrace_3053741 : CollatzResearch.WordTrace tailWord_3053741 prefixEnd_3053741 1568036927341641957993607 := by
  unfold tailWord_3053741
  simp only [CollatzResearch.WordTrace]
  refine ⟨111379084429825369286193077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74252722953216912857462051 111379084429825369286193077)
  ·
    refine ⟨10441789165296128370580601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111379084429825369286193077 10441789165296128370580601)
    ·
      refine ⟨7831341873972096277935451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10441789165296128370580601 7831341873972096277935451)
      ·
        refine ⟨11747012810958144416903177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831341873972096277935451 11747012810958144416903177)
        ·
          refine ⟨8810259608218608312677383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11747012810958144416903177 8810259608218608312677383)
          ·
            refine ⟨13215389412327912469016075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810259608218608312677383 13215389412327912469016075)
            ·
              refine ⟨19823084118491868703524113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215389412327912469016075 19823084118491868703524113)
              ·
                refine ⟨14867313088868901527643085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19823084118491868703524113 14867313088868901527643085)
                ·
                  refine ⟨5575242408325838072866157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14867313088868901527643085 5575242408325838072866157)
                  ·
                    refine ⟨2090715903122189277324809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5575242408325838072866157 2090715903122189277324809)
                    ·
                      refine ⟨1568036927341641957993607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090715903122189277324809 1568036927341641957993607)
                      ·
                        rfl

theorem cell23_3053741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3053741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053741 prefixEnd_3053741 := by exact prefixLift 3053741
  have htrace : WordTrace (prefixWord ++ tailWord_3053741) baseStart_3053741 baseEnd_3053741 := by
    simpa [prefixWord, tailWord_3053741, baseEnd_3053741] using wordTrace_append hprefix tailTrace_3053741
  have hstable : (prefixWord ++ tailWord_3053741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053741).length < 2 ^ (prefixWord ++ tailWord_3053741).sum := by decide
  have hdescent : baseEnd_3053741 < baseStart_3053741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053754 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2]
def baseStart_3053754 : Nat := 118140960795 + 3053754 * 2 ^ 59
def prefixEnd_3053754 : Nat := 4983230072969 + 3 ^ 40 * 3053754 * 2
def baseEnd_3053754 : Nat := 1568043602590150407131047

theorem tailTrace_3053754 : CollatzResearch.WordTrace tailWord_3053754 prefixEnd_3053754 1568043602590150407131047 := by
  unfold tailWord_3053754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27844889644694568126604079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74253039052518848337610877 27844889644694568126604079)
  ·
    refine ⟨41767334467041852189906119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27844889644694568126604079 41767334467041852189906119)
    ·
      refine ⟨62651001700562778284859179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41767334467041852189906119 62651001700562778284859179)
      ·
        refine ⟨93976502550844167427288769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62651001700562778284859179 93976502550844167427288769)
        ·
          refine ⟨70482376913133125570466577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93976502550844167427288769 70482376913133125570466577)
          ·
            refine ⟨52861782684849844177849933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70482376913133125570466577 52861782684849844177849933)
            ·
              refine ⟨19823168506818691566693725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52861782684849844177849933 19823168506818691566693725)
              ·
                refine ⟨7433688190057009337510147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19823168506818691566693725 7433688190057009337510147)
                ·
                  refine ⟨11150532285085514006265221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433688190057009337510147 11150532285085514006265221)
                  ·
                    refine ⟨2090724803453533876174729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11150532285085514006265221 2090724803453533876174729)
                    ·
                      refine ⟨1568043602590150407131047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090724803453533876174729 1568043602590150407131047)
                      ·
                        rfl

theorem cell23_3053754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_3053754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053754 prefixEnd_3053754 := by exact prefixLift 3053754
  have htrace : WordTrace (prefixWord ++ tailWord_3053754) baseStart_3053754 baseEnd_3053754 := by
    simpa [prefixWord, tailWord_3053754, baseEnd_3053754] using wordTrace_append hprefix tailTrace_3053754
  have hstable : (prefixWord ++ tailWord_3053754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053754).length < 2 ^ (prefixWord ++ tailWord_3053754).sum := by decide
  have hdescent : baseEnd_3053754 < baseStart_3053754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053757 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3053757 : Nat := 118140960795 + 3053757 * 2 ^ 59
def prefixEnd_3053757 : Nat := 4983230072969 + 3 ^ 40 * 3053757 * 2
def baseEnd_3053757 : Nat := 1568045143032113895393533

theorem tailTrace_3053757 : CollatzResearch.WordTrace tailWord_3053757 prefixEnd_3053757 1568045143032113895393533 := by
  unfold tailWord_3053757
  simp only [CollatzResearch.WordTrace]
  refine ⟨111379667997767404018775525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74253111998511602679183683 111379667997767404018775525)
  ·
    refine ⟨20883687749581388253520411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111379667997767404018775525 20883687749581388253520411)
    ·
      refine ⟨31325531624372082380280617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20883687749581388253520411 31325531624372082380280617)
      ·
        refine ⟨23494148718279061785210463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31325531624372082380280617 23494148718279061785210463)
        ·
          refine ⟨35241223077418592677815695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23494148718279061785210463 35241223077418592677815695)
          ·
            refine ⟨52861834616127889016723543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35241223077418592677815695 52861834616127889016723543)
            ·
              refine ⟨79292751924191833525085315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52861834616127889016723543 79292751924191833525085315)
              ·
                refine ⟨118939127886287750287627973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79292751924191833525085315 118939127886287750287627973)
                ·
                  refine ⟨22301086478678953178930245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118939127886287750287627973 22301086478678953178930245)
                  ·
                    refine ⟨4181453714752303721049421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22301086478678953178930245 4181453714752303721049421)
                    ·
                      refine ⟨1568045143032113895393533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181453714752303721049421 1568045143032113895393533)
                      ·
                        rfl

theorem cell23_3053757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3053757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053757 prefixEnd_3053757 := by exact prefixLift 3053757
  have htrace : WordTrace (prefixWord ++ tailWord_3053757) baseStart_3053757 baseEnd_3053757 := by
    simpa [prefixWord, tailWord_3053757, baseEnd_3053757] using wordTrace_append hprefix tailTrace_3053757
  have hstable : (prefixWord ++ tailWord_3053757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053757).length < 2 ^ (prefixWord ++ tailWord_3053757).sum := by decide
  have hdescent : baseEnd_3053757 < baseStart_3053757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053787 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 3]
def baseStart_3053787 : Nat := 118140960795 + 3053787 * 2 ^ 59
def prefixEnd_3053787 : Nat := 4983230072969 + 3 ^ 40 * 3053787 * 2
def baseEnd_3053787 : Nat := 1568060547451748778018395

theorem tailTrace_3053787 : CollatzResearch.WordTrace tailWord_3053787 prefixEnd_3053787 1568060547451748778018395 := by
  unfold tailWord_3053787
  simp only [CollatzResearch.WordTrace]
  refine ⟨111380762187658719142367615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74253841458439146094911743 111380762187658719142367615)
  ·
    refine ⟨167071143281488078713551423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111380762187658719142367615 167071143281488078713551423)
    ·
      refine ⟨250606714922232118070327135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167071143281488078713551423 250606714922232118070327135)
      ·
        refine ⟨375910072383348177105490703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250606714922232118070327135 375910072383348177105490703)
        ·
          refine ⟨563865108575022265658236055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375910072383348177105490703 563865108575022265658236055)
          ·
            refine ⟨845797662862533398487354083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563865108575022265658236055 845797662862533398487354083)
            ·
              refine ⟨1268696494293800097731031125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845797662862533398487354083 1268696494293800097731031125)
              ·
                refine ⟨14867537042505469895285521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1268696494293800097731031125 14867537042505469895285521)
                ·
                  refine ⟨11150652781879102421464141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14867537042505469895285521 11150652781879102421464141)
                  ·
                    refine ⟨4181494793204663408049053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11150652781879102421464141 4181494793204663408049053)
                    ·
                      refine ⟨1568060547451748778018395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181494793204663408049053 1568060547451748778018395)
                      ·
                        rfl

theorem cell23_3053787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 3].length) (baseStart_3053787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053787 prefixEnd_3053787 := by exact prefixLift 3053787
  have htrace : WordTrace (prefixWord ++ tailWord_3053787) baseStart_3053787 baseEnd_3053787 := by
    simpa [prefixWord, tailWord_3053787, baseEnd_3053787] using wordTrace_append hprefix tailTrace_3053787
  have hstable : (prefixWord ++ tailWord_3053787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053787).length < 2 ^ (prefixWord ++ tailWord_3053787).sum := by decide
  have hdescent : baseEnd_3053787 < baseStart_3053787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053805 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3053805 : Nat := 118140960795 + 3053805 * 2 ^ 59
def prefixEnd_3053805 : Nat := 4983230072969 + 3 ^ 40 * 3053805 * 2
def baseEnd_3053805 : Nat := 1568069790103529707593313

theorem tailTrace_3053805 : CollatzResearch.WordTrace tailWord_3053805 prefixEnd_3053805 1568069790103529707593313 := by
  unfold tailWord_3053805
  simp only [CollatzResearch.WordTrace]
  refine ⟨111381418701593508216522869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74254279134395672144348579 111381418701593508216522869)
  ·
    refine ⟨10442008003274391395299019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111381418701593508216522869 10442008003274391395299019)
    ·
      refine ⟨15663012004911587092948529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10442008003274391395299019 15663012004911587092948529)
      ·
        refine ⟨11747259003683690319711397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15663012004911587092948529 11747259003683690319711397)
        ·
          refine ⟨2202611063190691934945887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11747259003683690319711397 2202611063190691934945887)
          ·
            refine ⟨3303916594786037902418831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202611063190691934945887 3303916594786037902418831)
            ·
              refine ⟨4955874892179056853628247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303916594786037902418831 4955874892179056853628247)
              ·
                refine ⟨7433812338268585280442371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955874892179056853628247 7433812338268585280442371)
                ·
                  refine ⟨11150718507402877920663557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433812338268585280442371 11150718507402877920663557)
                  ·
                    refine ⟨2090759720138039610124417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11150718507402877920663557 2090759720138039610124417)
                    ·
                      refine ⟨1568069790103529707593313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090759720138039610124417 1568069790103529707593313)
                      ·
                        rfl

theorem cell23_3053805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3053805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053805 prefixEnd_3053805 := by exact prefixLift 3053805
  have htrace : WordTrace (prefixWord ++ tailWord_3053805) baseStart_3053805 baseEnd_3053805 := by
    simpa [prefixWord, tailWord_3053805, baseEnd_3053805] using wordTrace_append hprefix tailTrace_3053805
  have hstable : (prefixWord ++ tailWord_3053805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053805).length < 2 ^ (prefixWord ++ tailWord_3053805).sum := by decide
  have hdescent : baseEnd_3053805 < baseStart_3053805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053807 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 1, 7]
def baseStart_3053807 : Nat := 118140960795 + 3053807 * 2 ^ 59
def prefixEnd_3053807 : Nat := 4983230072969 + 3 ^ 40 * 3053807 * 2
def baseEnd_3053807 : Nat := 522690272354946233256101

theorem tailTrace_3053807 : CollatzResearch.WordTrace tailWord_3053807 prefixEnd_3053807 522690272354946233256101 := by
  unfold tailWord_3053807
  simp only [CollatzResearch.WordTrace]
  refine ⟨111381491647586262558095675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74254327765057508372063783 111381491647586262558095675)
  ·
    refine ⟨167072237471379393837143513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111381491647586262558095675 167072237471379393837143513)
    ·
      refine ⟨125304178103534545377857635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167072237471379393837143513 125304178103534545377857635)
      ·
        refine ⟨187956267155301818066786453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125304178103534545377857635 187956267155301818066786453)
        ·
          refine ⟨8810450022904772721880615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187956267155301818066786453 8810450022904772721880615)
          ·
            refine ⟨13215675034357159082820923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810450022904772721880615 13215675034357159082820923)
            ·
              refine ⟨19823512551535738624231385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215675034357159082820923 19823512551535738624231385)
              ·
                refine ⟨14867634413651803968173539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19823512551535738624231385 14867634413651803968173539)
                ·
                  refine ⟨22301451620477705952260309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14867634413651803968173539 22301451620477705952260309)
                  ·
                    refine ⟨522690272354946233256101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22301451620477705952260309 522690272354946233256101)
                    ·
                      rfl

theorem cell23_3053807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_3053807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053807 prefixEnd_3053807 := by exact prefixLift 3053807
  have htrace : WordTrace (prefixWord ++ tailWord_3053807) baseStart_3053807 baseEnd_3053807 := by
    simpa [prefixWord, tailWord_3053807, baseEnd_3053807] using wordTrace_append hprefix tailTrace_3053807
  have hstable : (prefixWord ++ tailWord_3053807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053807).length < 2 ^ (prefixWord ++ tailWord_3053807).sum := by decide
  have hdescent : baseEnd_3053807 < baseStart_3053807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053827 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4]
def baseStart_3053827 : Nat := 118140960795 + 3053827 * 2 ^ 59
def prefixEnd_3053827 : Nat := 4983230072969 + 3 ^ 40 * 3053827 * 2
def baseEnd_3053827 : Nat := 1568081086677928621518211

theorem tailTrace_3053827 : CollatzResearch.WordTrace tailWord_3053827 prefixEnd_3053827 1568081086677928621518211 := by
  unfold tailWord_3053827
  simp only [CollatzResearch.WordTrace]
  refine ⟨111382221107513805973823735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74254814071675870649215823 111382221107513805973823735)
  ·
    refine ⟨167073331661270708960735603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111382221107513805973823735 167073331661270708960735603)
    ·
      refine ⟨250609997491906063441103405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167073331661270708960735603 250609997491906063441103405)
      ·
        refine ⟨93978749059464773790413777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250609997491906063441103405 93978749059464773790413777)
        ·
          refine ⟨70484061794598580342810333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93978749059464773790413777 70484061794598580342810333)
          ·
            refine ⟨26431523172974467628553875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70484061794598580342810333 26431523172974467628553875)
            ·
              refine ⟨39647284759461701442830813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26431523172974467628553875 39647284759461701442830813)
              ·
                refine ⟨14867731784798138041061555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39647284759461701442830813 14867731784798138041061555)
                ·
                  refine ⟨22301597677197207061592333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14867731784798138041061555 22301597677197207061592333)
                  ·
                    refine ⟨8363099128948952648097125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22301597677197207061592333 8363099128948952648097125)
                    ·
                      refine ⟨1568081086677928621518211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8363099128948952648097125 1568081086677928621518211)
                      ·
                        rfl

theorem cell23_3053827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_3053827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053827 prefixEnd_3053827 := by exact prefixLift 3053827
  have htrace : WordTrace (prefixWord ++ tailWord_3053827) baseStart_3053827 baseEnd_3053827 := by
    simpa [prefixWord, tailWord_3053827, baseEnd_3053827] using wordTrace_append hprefix tailTrace_3053827
  have hstable : (prefixWord ++ tailWord_3053827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053827).length < 2 ^ (prefixWord ++ tailWord_3053827).sum := by decide
  have hdescent : baseEnd_3053827 < baseStart_3053827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053828 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 5]
def baseStart_3053828 : Nat := 118140960795 + 3053828 * 2 ^ 59
def prefixEnd_3053828 : Nat := 4983230072969 + 3 ^ 40 * 3053828 * 2
def baseEnd_3053828 : Nat := 174231288906509235289523

theorem tailTrace_3053828 : CollatzResearch.WordTrace tailWord_3053828 prefixEnd_3053828 174231288906509235289523 := by
  unfold tailWord_3053828
  simp only [CollatzResearch.WordTrace]
  refine ⟨55691128790255091572305069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74254838387006788763073425 55691128790255091572305069)
  ·
    refine ⟨20884173296345659339614401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55691128790255091572305069 20884173296345659339614401)
    ·
      refine ⟨15663129972259244504710801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20884173296345659339614401 15663129972259244504710801)
      ·
        refine ⟨11747347479194433378533101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15663129972259244504710801 11747347479194433378533101)
        ·
          refine ⟨4405255304697912516949913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11747347479194433378533101 4405255304697912516949913)
          ·
            refine ⟨3303941478523434387712435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4405255304697912516949913 3303941478523434387712435)
            ·
              refine ⟨4955912217785151581568653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303941478523434387712435 4955912217785151581568653)
              ·
                refine ⟨1858467081669431843088245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4955912217785151581568653 1858467081669431843088245)
                ·
                  refine ⟨174231288906509235289523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858467081669431843088245 174231288906509235289523)
                  ·
                    rfl

theorem cell23_3053828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_3053828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053828 prefixEnd_3053828 := by exact prefixLift 3053828
  have htrace : WordTrace (prefixWord ++ tailWord_3053828) baseStart_3053828 baseEnd_3053828 := by
    simpa [prefixWord, tailWord_3053828, baseEnd_3053828] using wordTrace_append hprefix tailTrace_3053828
  have hstable : (prefixWord ++ tailWord_3053828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053828).length < 2 ^ (prefixWord ++ tailWord_3053828).sum := by decide
  have hdescent : baseEnd_3053828 < baseStart_3053828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053857 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3053857 : Nat := 118140960795 + 3053857 * 2 ^ 59
def prefixEnd_3053857 : Nat := 4983230072969 + 3 ^ 40 * 3053857 * 2
def baseEnd_3053857 : Nat := 1568096491097563504143073

theorem tailTrace_3053857 : CollatzResearch.WordTrace tailWord_3053857 prefixEnd_3053857 1568096491097563504143073 := by
  unfold tailWord_3053857
  simp only [CollatzResearch.WordTrace]
  refine ⟨111383315297405121097415825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74255543531603414064943883 111383315297405121097415825)
  ·
    refine ⟨83537486473053840823061869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111383315297405121097415825 83537486473053840823061869)
    ·
      refine ⟨31326557427395190308648201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83537486473053840823061869 31326557427395190308648201)
      ·
        refine ⟨23494918070546392731486151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31326557427395190308648201 23494918070546392731486151)
        ·
          refine ⟨35242377105819589097229227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23494918070546392731486151 35242377105819589097229227)
          ·
            refine ⟨52863565658729383645843841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35242377105819589097229227 52863565658729383645843841)
            ·
              refine ⟨39647674244047037734382881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52863565658729383645843841 39647674244047037734382881)
              ·
                refine ⟨29735755683035278300787161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39647674244047037734382881 29735755683035278300787161)
                ·
                  refine ⟨22301816762276458725590371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29735755683035278300787161 22301816762276458725590371)
                  ·
                    refine ⟨33452725143414688088385557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22301816762276458725590371 33452725143414688088385557)
                    ·
                      refine ⟨1568096491097563504143073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33452725143414688088385557 1568096491097563504143073)
                      ·
                        rfl

theorem cell23_3053857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3053857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053857 prefixEnd_3053857 := by exact prefixLift 3053857
  have htrace : WordTrace (prefixWord ++ tailWord_3053857) baseStart_3053857 baseEnd_3053857 := by
    simpa [prefixWord, tailWord_3053857, baseEnd_3053857] using wordTrace_append hprefix tailTrace_3053857
  have hstable : (prefixWord ++ tailWord_3053857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053857).length < 2 ^ (prefixWord ++ tailWord_3053857).sum := by decide
  have hdescent : baseEnd_3053857 < baseStart_3053857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053881 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3053881 : Nat := 118140960795 + 3053881 * 2 ^ 59
def prefixEnd_3053881 : Nat := 4983230072969 + 3 ^ 40 * 3053881 * 2
def baseEnd_3053881 : Nat := 1568108814633271410242963

theorem tailTrace_3053881 : CollatzResearch.WordTrace tailWord_3053881 prefixEnd_3053881 1568108814633271410242963 := by
  unfold tailWord_3053881
  simp only [CollatzResearch.WordTrace]
  refine ⟨111384190649318173196289497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74256127099545448797526331 111384190649318173196289497)
  ·
    refine ⟨83538142986988629897217123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111384190649318173196289497 83538142986988629897217123)
    ·
      refine ⟨125307214480482944845825685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83538142986988629897217123 125307214480482944845825685)
      ·
        refine ⟨5873775678772638039648079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125307214480482944845825685 5873775678772638039648079)
        ·
          refine ⟨8810663518158957059472119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873775678772638039648079 8810663518158957059472119)
          ·
            refine ⟨13215995277238435589208179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810663518158957059472119 13215995277238435589208179)
            ·
              refine ⟨19823992915857653383812269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215995277238435589208179 19823992915857653383812269)
              ·
                refine ⟨7433997343446620018929601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19823992915857653383812269 7433997343446620018929601)
                ·
                  refine ⟨5575498007584965014197201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7433997343446620018929601 5575498007584965014197201)
                  ·
                    refine ⟨4181623505688723760647901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5575498007584965014197201 4181623505688723760647901)
                    ·
                      refine ⟨1568108814633271410242963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181623505688723760647901 1568108814633271410242963)
                      ·
                        rfl

theorem cell23_3053881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3053881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053881 prefixEnd_3053881 := by exact prefixLift 3053881
  have htrace : WordTrace (prefixWord ++ tailWord_3053881) baseStart_3053881 baseEnd_3053881 := by
    simpa [prefixWord, tailWord_3053881, baseEnd_3053881] using wordTrace_append hprefix tailTrace_3053881
  have hstable : (prefixWord ++ tailWord_3053881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053881).length < 2 ^ (prefixWord ++ tailWord_3053881).sum := by decide
  have hdescent : baseEnd_3053881 < baseStart_3053881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053905 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 1, 4]
def baseStart_3053905 : Nat := 118140960795 + 3053905 * 2 ^ 59
def prefixEnd_3053905 : Nat := 4983230072969 + 3 ^ 40 * 3053905 * 2
def baseEnd_3053905 : Nat := 522707046056326438780951

theorem tailTrace_3053905 : CollatzResearch.WordTrace tailWord_3053905 prefixEnd_3053905 522707046056326438780951 := by
  unfold tailWord_3053905
  simp only [CollatzResearch.WordTrace]
  refine ⟨111385066001231225295163169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74256710667487483530108779 111385066001231225295163169)
  ·
    refine ⟨83538799500923418971372377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111385066001231225295163169 83538799500923418971372377)
    ·
      refine ⟨62654099625692564228529283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83538799500923418971372377 62654099625692564228529283)
      ·
        refine ⟨93981149438538846342793925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62654099625692564228529283 93981149438538846342793925)
        ·
          refine ⟨17621465519726033689273861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93981149438538846342793925 17621465519726033689273861)
          ·
            refine ⟨3304024784948631316738849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17621465519726033689273861 3304024784948631316738849)
            ·
              refine ⟨2478018588711473487554137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3304024784948631316738849 2478018588711473487554137)
              ·
                refine ⟨1858513941533605115665603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478018588711473487554137 1858513941533605115665603)
                ·
                  refine ⟨2787770912300407673498405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858513941533605115665603 2787770912300407673498405)
                  ·
                    refine ⟨522707046056326438780951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787770912300407673498405 522707046056326438780951)
                    ·
                      rfl

theorem cell23_3053905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_3053905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053905 prefixEnd_3053905 := by exact prefixLift 3053905
  have htrace : WordTrace (prefixWord ++ tailWord_3053905) baseStart_3053905 baseEnd_3053905 := by
    simpa [prefixWord, tailWord_3053905, baseEnd_3053905] using wordTrace_append hprefix tailTrace_3053905
  have hstable : (prefixWord ++ tailWord_3053905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053905).length < 2 ^ (prefixWord ++ tailWord_3053905).sum := by decide
  have hdescent : baseEnd_3053905 < baseStart_3053905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053911 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_3053911 : Nat := 118140960795 + 3053911 * 2 ^ 59
def prefixEnd_3053911 : Nat := 4983230072969 + 3 ^ 40 * 3053911 * 2
def baseEnd_3053911 : Nat := 1568124219052906292867825

theorem tailTrace_3053911 : CollatzResearch.WordTrace tailWord_3053911 prefixEnd_3053911 1568124219052906292867825 := by
  unfold tailWord_3053911
  simp only [CollatzResearch.WordTrace]
  refine ⟨111385284839209488319881587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74256856559472992213254391 111385284839209488319881587)
  ·
    refine ⟨167077927258814232479822381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111385284839209488319881587 167077927258814232479822381)
    ·
      refine ⟨62654222722055337179933393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167077927258814232479822381 62654222722055337179933393)
      ·
        refine ⟨46990667041541502884950045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62654222722055337179933393 46990667041541502884950045)
        ·
          refine ⟨17621500140578063581856267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46990667041541502884950045 17621500140578063581856267)
          ·
            refine ⟨26432250210867095372784401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17621500140578063581856267 26432250210867095372784401)
            ·
              refine ⟨19824187658150321529588301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26432250210867095372784401 19824187658150321529588301)
              ·
                refine ⟨7434070371806370573595613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19824187658150321529588301 7434070371806370573595613)
                ·
                  refine ⟨2787776389427388965098355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7434070371806370573595613 2787776389427388965098355)
                  ·
                    refine ⟨4181664584141083447647533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2787776389427388965098355 4181664584141083447647533)
                    ·
                      refine ⟨1568124219052906292867825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181664584141083447647533 1568124219052906292867825)
                      ·
                        rfl

theorem cell23_3053911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_3053911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053911 prefixEnd_3053911 := by exact prefixLift 3053911
  have htrace : WordTrace (prefixWord ++ tailWord_3053911) baseStart_3053911 baseEnd_3053911 := by
    simpa [prefixWord, tailWord_3053911, baseEnd_3053911] using wordTrace_append hprefix tailTrace_3053911
  have hstable : (prefixWord ++ tailWord_3053911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053911).length < 2 ^ (prefixWord ++ tailWord_3053911).sum := by decide
  have hdescent : baseEnd_3053911 < baseStart_3053911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053928 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3053928 : Nat := 118140960795 + 3053928 * 2 ^ 59
def prefixEnd_3053928 : Nat := 4983230072969 + 3 ^ 40 * 3053928 * 2
def baseEnd_3053928 : Nat := 1568132948224032726355247

theorem tailTrace_3053928 : CollatzResearch.WordTrace tailWord_3053928 prefixEnd_3053928 1568132948224032726355247 := by
  unfold tailWord_3053928
  simp only [CollatzResearch.WordTrace]
  refine ⟨55692952440073950111625219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74257269920098600148833625 55692952440073950111625219)
  ·
    refine ⟨83539428660110925167437829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55692952440073950111625219 83539428660110925167437829)
    ·
      refine ⟨15663642873770798468894593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83539428660110925167437829 15663642873770798468894593)
      ·
        refine ⟨11747732155328098851670945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15663642873770798468894593 11747732155328098851670945)
        ·
          refine ⟨8810799116496074138753209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11747732155328098851670945 8810799116496074138753209)
          ·
            refine ⟨6608099337372055604064907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8810799116496074138753209 6608099337372055604064907)
            ·
              refine ⟨9912149006058083406097361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6608099337372055604064907 9912149006058083406097361)
              ·
                refine ⟨7434111754543562554573021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9912149006058083406097361 7434111754543562554573021)
                ·
                  refine ⟨2787791907953835957964883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7434111754543562554573021 2787791907953835957964883)
                  ·
                    refine ⟨4181687861930753936947325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2787791907953835957964883 4181687861930753936947325)
                    ·
                      refine ⟨1568132948224032726355247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181687861930753936947325 1568132948224032726355247)
                      ·
                        rfl

theorem cell23_3053928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3053928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053928 prefixEnd_3053928 := by exact prefixLift 3053928
  have htrace : WordTrace (prefixWord ++ tailWord_3053928) baseStart_3053928 baseEnd_3053928 := by
    simpa [prefixWord, tailWord_3053928, baseEnd_3053928] using wordTrace_append hprefix tailTrace_3053928
  have hstable : (prefixWord ++ tailWord_3053928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053928).length < 2 ^ (prefixWord ++ tailWord_3053928).sum := by decide
  have hdescent : baseEnd_3053928 < baseStart_3053928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053938 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_3053938 : Nat := 118140960795 + 3053938 * 2 ^ 59
def prefixEnd_3053938 : Nat := 4983230072969 + 3 ^ 40 * 3053938 * 2
def baseEnd_3053938 : Nat := 1568138083030577687230201

theorem tailTrace_3053938 : CollatzResearch.WordTrace tailWord_3053938 prefixEnd_3053938 1568138083030577687230201 := by
  unfold tailWord_3053938
  simp only [CollatzResearch.WordTrace]
  refine ⟨27846567402527917982778617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74257513073407781287409645 27846567402527917982778617)
  ·
    refine ⟨20884925551895938487083963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27846567402527917982778617 20884925551895938487083963)
    ·
      refine ⟨31327388327843907730625945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20884925551895938487083963 31327388327843907730625945)
      ·
        refine ⟨23495541245882930797969459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31327388327843907730625945 23495541245882930797969459)
        ·
          refine ⟨35243311868824396196954189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23495541245882930797969459 35243311868824396196954189)
          ·
            refine ⟨13216241950809148573857821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35243311868824396196954189 13216241950809148573857821)
            ·
              refine ⟨4956090731553430715196683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13216241950809148573857821 4956090731553430715196683)
              ·
                refine ⟨7434136097330146072795025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956090731553430715196683 7434136097330146072795025)
                ·
                  refine ⟨5575602072997609554596269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7434136097330146072795025 5575602072997609554596269)
                  ·
                    refine ⟨2090850777374103582973601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5575602072997609554596269 2090850777374103582973601)
                    ·
                      refine ⟨1568138083030577687230201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090850777374103582973601 1568138083030577687230201)
                      ·
                        rfl

theorem cell23_3053938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_3053938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053938 prefixEnd_3053938 := by exact prefixLift 3053938
  have htrace : WordTrace (prefixWord ++ tailWord_3053938) baseStart_3053938 baseEnd_3053938 := by
    simpa [prefixWord, tailWord_3053938, baseEnd_3053938] using wordTrace_append hprefix tailTrace_3053938
  have hstable : (prefixWord ++ tailWord_3053938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053938).length < 2 ^ (prefixWord ++ tailWord_3053938).sum := by decide
  have hdescent : baseEnd_3053938 < baseStart_3053938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053961 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 4, 4]
def baseStart_3053961 : Nat := 118140960795 + 3053961 * 2 ^ 59
def prefixEnd_3053961 : Nat := 4983230072969 + 3 ^ 40 * 3053961 * 2
def baseEnd_3053961 : Nat := 522716631028543699080865

theorem tailTrace_3053961 : CollatzResearch.WordTrace tailWord_3053961 prefixEnd_3053961 522716631028543699080865 := by
  unfold tailWord_3053961
  simp only [CollatzResearch.WordTrace]
  refine ⟨111387108489028346859201737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74258072326018897906134491 111387108489028346859201737)
  ·
    refine ⟨83540331366771260144401303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111387108489028346859201737 83540331366771260144401303)
    ·
      refine ⟨125310497050156890216601955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83540331366771260144401303 125310497050156890216601955)
      ·
        refine ⟨187965745575235335324902933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125310497050156890216601955 187965745575235335324902933)
        ·
          refine ⟨8810894323839156343354825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187965745575235335324902933 8810894323839156343354825)
          ·
            refine ⟨6608170742879367257516119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8810894323839156343354825 6608170742879367257516119)
            ·
              refine ⟨9912256114319050886274179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6608170742879367257516119 9912256114319050886274179)
              ·
                refine ⟨14868384171478576329411269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9912256114319050886274179 14868384171478576329411269)
                ·
                  refine ⟨2787822032152233061764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14868384171478576329411269 2787822032152233061764613)
                  ·
                    refine ⟨522716631028543699080865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787822032152233061764613 522716631028543699080865)
                    ·
                      rfl

theorem cell23_3053961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_3053961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053961 prefixEnd_3053961 := by exact prefixLift 3053961
  have htrace : WordTrace (prefixWord ++ tailWord_3053961) baseStart_3053961 baseEnd_3053961 := by
    simpa [prefixWord, tailWord_3053961, baseEnd_3053961] using wordTrace_append hprefix tailTrace_3053961
  have hstable : (prefixWord ++ tailWord_3053961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053961).length < 2 ^ (prefixWord ++ tailWord_3053961).sum := by decide
  have hdescent : baseEnd_3053961 < baseStart_3053961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053981 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3053981 : Nat := 118140960795 + 3053981 * 2 ^ 59
def prefixEnd_3053981 : Nat := 4983230072969 + 3 ^ 40 * 3053981 * 2
def baseEnd_3053981 : Nat := 1568160162698721018992503

theorem tailTrace_3053981 : CollatzResearch.WordTrace tailWord_3053981 prefixEnd_3053981 1568160162698721018992503 := by
  unfold tailWord_3053981
  simp only [CollatzResearch.WordTrace]
  refine ⟨111387837948955890274929797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74258558632637260183286531 111387837948955890274929797)
  ·
    refine ⟨20885219615429229426549337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111387837948955890274929797 20885219615429229426549337)
    ·
      refine ⟨15663914711571922069912003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20885219615429229426549337 15663914711571922069912003)
      ·
        refine ⟨23495872067357883104868005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15663914711571922069912003 23495872067357883104868005)
        ·
          refine ⟨4405476012629603082162751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23495872067357883104868005 4405476012629603082162751)
          ·
            refine ⟨6608214018944404623244127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4405476012629603082162751 6608214018944404623244127)
            ·
              refine ⟨9912321028416606934866191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6608214018944404623244127 9912321028416606934866191)
              ·
                refine ⟨14868481542624910402299287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9912321028416606934866191 14868481542624910402299287)
                ·
                  refine ⟨22302722313937365603448931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14868481542624910402299287 22302722313937365603448931)
                  ·
                    refine ⟨33454083470906048405173397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22302722313937365603448931 33454083470906048405173397)
                    ·
                      refine ⟨1568160162698721018992503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33454083470906048405173397 1568160162698721018992503)
                      ·
                        rfl

theorem cell23_3053981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3053981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053981 prefixEnd_3053981 := by exact prefixLift 3053981
  have htrace : WordTrace (prefixWord ++ tailWord_3053981) baseStart_3053981 baseEnd_3053981 := by
    simpa [prefixWord, tailWord_3053981, baseEnd_3053981] using wordTrace_append hprefix tailTrace_3053981
  have hstable : (prefixWord ++ tailWord_3053981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053981).length < 2 ^ (prefixWord ++ tailWord_3053981).sum := by decide
  have hdescent : baseEnd_3053981 < baseStart_3053981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053985 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3053985 : Nat := 118140960795 + 3053985 * 2 ^ 59
def prefixEnd_3053985 : Nat := 4983230072969 + 3 ^ 40 * 3053985 * 2
def baseEnd_3053985 : Nat := 1568162216621339003342485

theorem tailTrace_3053985 : CollatzResearch.WordTrace tailWord_3053985 prefixEnd_3053985 1568162216621339003342485 := by
  unfold tailWord_3053985
  simp only [CollatzResearch.WordTrace]
  refine ⟨111387983840941398958075409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74258655893960932638716939 111387983840941398958075409)
  ·
    refine ⟨83540987880706049218556557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111387983840941398958075409 83540987880706049218556557)
    ·
      refine ⟨31327870455264768456958709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83540987880706049218556557 31327870455264768456958709)
      ·
        refine ⟨2936987855181072042839879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31327870455264768456958709 2936987855181072042839879)
        ·
          refine ⟨4405481782771608064259819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936987855181072042839879 4405481782771608064259819)
          ·
            refine ⟨6608222674157412096389729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4405481782771608064259819 6608222674157412096389729)
            ·
              refine ⟨4956167005618059072292297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6608222674157412096389729 4956167005618059072292297)
              ·
                refine ⟨3717125254213544304219223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956167005618059072292297 3717125254213544304219223)
                ·
                  refine ⟨5575687881320316456328835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717125254213544304219223 5575687881320316456328835)
                  ·
                    refine ⟨8363531821980474684493253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575687881320316456328835 8363531821980474684493253)
                    ·
                      refine ⟨1568162216621339003342485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8363531821980474684493253 1568162216621339003342485)
                      ·
                        rfl

theorem cell23_3053985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3053985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053985 prefixEnd_3053985 := by exact prefixLift 3053985
  have htrace : WordTrace (prefixWord ++ tailWord_3053985) baseStart_3053985 baseEnd_3053985 := by
    simpa [prefixWord, tailWord_3053985, baseEnd_3053985] using wordTrace_append hprefix tailTrace_3053985
  have hstable : (prefixWord ++ tailWord_3053985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053985).length < 2 ^ (prefixWord ++ tailWord_3053985).sum := by decide
  have hdescent : baseEnd_3053985 < baseStart_3053985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053991 : List Nat := [1, 1, 6, 1, 1, 2, 4, 7]
def baseStart_3053991 : Nat := 118140960795 + 3053991 * 2 ^ 59
def prefixEnd_3053991 : Nat := 4983230072969 + 3 ^ 40 * 3053991 * 2
def baseEnd_3053991 : Nat := 58080196203898739995091

theorem tailTrace_3053991 : CollatzResearch.WordTrace tailWord_3053991 prefixEnd_3053991 58080196203898739995091 := by
  unfold tailWord_3053991
  simp only [CollatzResearch.WordTrace]
  refine ⟨111388202678919661982793827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74258801785946441321862551 111388202678919661982793827)
  ·
    refine ⟨167082304018379492974190741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111388202678919661982793827 167082304018379492974190741)
    ·
      refine ⟨7831983000861538733165191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167082304018379492974190741 7831983000861538733165191)
      ·
        refine ⟨11747974501292308099747787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831983000861538733165191 11747974501292308099747787)
        ·
          refine ⟨17621961751938462149621681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11747974501292308099747787 17621961751938462149621681)
          ·
            refine ⟨13216471313953846612216261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17621961751938462149621681 13216471313953846612216261)
            ·
              refine ⟨2478088371366346239790549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13216471313953846612216261 2478088371366346239790549)
              ·
                refine ⟨58080196203898739995091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2478088371366346239790549 58080196203898739995091)
                ·
                  rfl

theorem cell23_3053991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 7].length) (baseStart_3053991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3053991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3053991 prefixEnd_3053991 := by exact prefixLift 3053991
  have htrace : WordTrace (prefixWord ++ tailWord_3053991) baseStart_3053991 baseEnd_3053991 := by
    simpa [prefixWord, tailWord_3053991, baseEnd_3053991] using wordTrace_append hprefix tailTrace_3053991
  have hstable : (prefixWord ++ tailWord_3053991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053991).length < 2 ^ (prefixWord ++ tailWord_3053991).sum := by decide
  have hdescent : baseEnd_3053991 < baseStart_3053991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054058 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_3054058 : Nat := 118140960795 + 3054058 * 2 ^ 59
def prefixEnd_3054058 : Nat := 4983230072969 + 3 ^ 40 * 3054058 * 2
def baseEnd_3054058 : Nat := 1568199700709117217729649

theorem tailTrace_3054058 : CollatzResearch.WordTrace tailWord_3054058 prefixEnd_3054058 1568199700709117217729649 := by
  unfold tailWord_3054058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27847661592419233106370707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74260430913117954950321885 27847661592419233106370707)
  ·
    refine ⟨41771492388628849659556061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27847661592419233106370707 41771492388628849659556061)
    ·
      refine ⟨15664309645735818622333523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41771492388628849659556061 15664309645735818622333523)
      ·
        refine ⟨23496464468603727933500285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15664309645735818622333523 23496464468603727933500285)
        ·
          refine ⟨8811174175726397975062607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23496464468603727933500285 8811174175726397975062607)
          ·
            refine ⟨13216761263589596962593911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811174175726397975062607 13216761263589596962593911)
            ·
              refine ⟨19825141895384395443890867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13216761263589596962593911 19825141895384395443890867)
              ·
                refine ⟨29737712843076593165836301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19825141895384395443890867 29737712843076593165836301)
                ·
                  refine ⟨11151642316153722437188613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29737712843076593165836301 11151642316153722437188613)
                  ·
                    refine ⟨2090932934278822956972865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11151642316153722437188613 2090932934278822956972865)
                    ·
                      refine ⟨1568199700709117217729649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090932934278822956972865 1568199700709117217729649)
                      ·
                        rfl

theorem cell23_3054058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_3054058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054058 prefixEnd_3054058 := by exact prefixLift 3054058
  have htrace : WordTrace (prefixWord ++ tailWord_3054058) baseStart_3054058 baseEnd_3054058 := by
    simpa [prefixWord, tailWord_3054058, baseEnd_3054058] using wordTrace_append hprefix tailTrace_3054058
  have hstable : (prefixWord ++ tailWord_3054058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054058).length < 2 ^ (prefixWord ++ tailWord_3054058).sum := by decide
  have hdescent : baseEnd_3054058 < baseStart_3054058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054062 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_3054062 : Nat := 118140960795 + 3054062 * 2 ^ 59
def prefixEnd_3054062 : Nat := 4983230072969 + 3 ^ 40 * 3054062 * 2
def baseEnd_3054062 : Nat := 1568201754631735202079631

theorem tailTrace_3054062 : CollatzResearch.WordTrace tailWord_3054062 prefixEnd_3054062 1568201754631735202079631 := by
  unfold tailWord_3054062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923849032707805138578555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74260528174441627405752293 13923849032707805138578555)
  ·
    refine ⟨20885773549061707707867833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13923849032707805138578555 20885773549061707707867833)
    ·
      refine ⟨15664330161796280780900875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20885773549061707707867833 15664330161796280780900875)
      ·
        refine ⟨23496495242694421171351313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15664330161796280780900875 23496495242694421171351313)
        ·
          refine ⟨17622371432020815878513485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23496495242694421171351313 17622371432020815878513485)
          ·
            refine ⟨6608389287007805954442557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17622371432020815878513485 6608389287007805954442557)
            ·
              refine ⟨2478145982627927232915959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6608389287007805954442557 2478145982627927232915959)
              ·
                refine ⟨3717218973941890849373939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478145982627927232915959 3717218973941890849373939)
                ·
                  refine ⟨5575828460912836274060909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717218973941890849373939 5575828460912836274060909)
                  ·
                    refine ⟨2090935672842313602772841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5575828460912836274060909 2090935672842313602772841)
                    ·
                      refine ⟨1568201754631735202079631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090935672842313602772841 1568201754631735202079631)
                      ·
                        rfl

theorem cell23_3054062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_3054062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054062 prefixEnd_3054062 := by exact prefixLift 3054062
  have htrace : WordTrace (prefixWord ++ tailWord_3054062) baseStart_3054062 baseEnd_3054062 := by
    simpa [prefixWord, tailWord_3054062, baseEnd_3054062] using wordTrace_append hprefix tailTrace_3054062
  have hstable : (prefixWord ++ tailWord_3054062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054062).length < 2 ^ (prefixWord ++ tailWord_3054062).sum := by decide
  have hdescent : baseEnd_3054062 < baseStart_3054062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054091 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 3]
def baseStart_3054091 : Nat := 118140960795 + 3054091 * 2 ^ 59
def prefixEnd_3054091 : Nat := 4983230072969 + 3 ^ 40 * 3054091 * 2
def baseEnd_3054091 : Nat := 1568216645570715588616997

theorem tailTrace_3054091 : CollatzResearch.WordTrace tailWord_3054091 prefixEnd_3054091 1568216645570715588616997 := by
  unfold tailWord_3054091
  simp only [CollatzResearch.WordTrace]
  refine ⟨111391849978557379061434127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74261233319038252707622751 111391849978557379061434127)
  ·
    refine ⟨167087774967836068592151191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111391849978557379061434127 167087774967836068592151191)
    ·
      refine ⟨250631662451754102888226787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167087774967836068592151191 250631662451754102888226787)
      ·
        refine ⟨375947493677631154332340181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250631662451754102888226787 375947493677631154332340181)
        ·
          refine ⟨8811269383069480179664223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 375947493677631154332340181 8811269383069480179664223)
          ·
            refine ⟨13216904074604220269496335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811269383069480179664223 13216904074604220269496335)
            ·
              refine ⟨19825356111906330404244503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13216904074604220269496335 19825356111906330404244503)
              ·
                refine ⟨29738034167859495606366755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19825356111906330404244503 29738034167859495606366755)
                ·
                  refine ⟨44607051251789243409550133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29738034167859495606366755 44607051251789243409550133)
                  ·
                    refine ⟨4181911054855241569645325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44607051251789243409550133 4181911054855241569645325)
                    ·
                      refine ⟨1568216645570715588616997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4181911054855241569645325 1568216645570715588616997)
                      ·
                        rfl

theorem cell23_3054091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 3].length) (baseStart_3054091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054091 prefixEnd_3054091 := by exact prefixLift 3054091
  have htrace : WordTrace (prefixWord ++ tailWord_3054091) baseStart_3054091 baseEnd_3054091 := by
    simpa [prefixWord, tailWord_3054091, baseEnd_3054091] using wordTrace_append hprefix tailTrace_3054091
  have hstable : (prefixWord ++ tailWord_3054091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054091).length < 2 ^ (prefixWord ++ tailWord_3054091).sum := by decide
  have hdescent : baseEnd_3054091 < baseStart_3054091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054124 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_3054124 : Nat := 118140960795 + 3054124 * 2 ^ 59
def prefixEnd_3054124 : Nat := 4983230072969 + 3 ^ 40 * 3054124 * 2
def baseEnd_3054124 : Nat := 522744530144104653168115

theorem tailTrace_3054124 : CollatzResearch.WordTrace tailWord_3054124 prefixEnd_3054124 522744530144104653168115 := by
  unfold tailWord_3054124
  simp only [CollatzResearch.WordTrace]
  refine ⟨55696526793718912848692713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74262035724958550464923617 55696526793718912848692713)
  ·
    refine ⟨41772395095289184636519535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55696526793718912848692713 41772395095289184636519535)
    ·
      refine ⟨62658592642933776954779303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41772395095289184636519535 62658592642933776954779303)
      ·
        refine ⟨93987888964400665432168955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62658592642933776954779303 93987888964400665432168955)
        ·
          refine ⟨140981833446600998148253433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93987888964400665432168955 140981833446600998148253433)
          ·
            refine ⟨105736375084950748611190075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140981833446600998148253433 105736375084950748611190075)
            ·
              refine ⟨158604562627426122916785113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105736375084950748611190075 158604562627426122916785113)
              ·
                refine ⟨118953421970569592187588835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158604562627426122916785113 118953421970569592187588835)
                ·
                  refine ⟨178430132955854388281383253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118953421970569592187588835 178430132955854388281383253)
                  ·
                    refine ⟨522744530144104653168115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 178430132955854388281383253 522744530144104653168115)
                    ·
                      rfl

theorem cell23_3054124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_3054124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054124 prefixEnd_3054124 := by exact prefixLift 3054124
  have htrace : WordTrace (prefixWord ++ tailWord_3054124) baseStart_3054124 baseEnd_3054124 := by
    simpa [prefixWord, tailWord_3054124, baseEnd_3054124] using wordTrace_append hprefix tailTrace_3054124
  have hstable : (prefixWord ++ tailWord_3054124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054124).length < 2 ^ (prefixWord ++ tailWord_3054124).sum := by decide
  have hdescent : baseEnd_3054124 < baseStart_3054124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054126 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3054126 : Nat := 118140960795 + 3054126 * 2 ^ 59
def prefixEnd_3054126 : Nat := 4983230072969 + 3 ^ 40 * 3054126 * 2
def baseEnd_3054126 : Nat := 1568234617393622951679337

theorem tailTrace_3054126 : CollatzResearch.WordTrace tailWord_3054126 prefixEnd_3054126 1568234617393622951679337 := by
  unfold tailWord_3054126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924140816678822504869779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74262084355620386692638821 13924140816678822504869779)
  ·
    refine ⟨20886211225018233757304669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13924140816678822504869779 20886211225018233757304669)
    ·
      refine ⟨7832329209381837658989251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20886211225018233757304669 7832329209381837658989251)
      ·
        refine ⟨11748493814072756488483877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7832329209381837658989251 11748493814072756488483877)
        ·
          refine ⟨2202842590138641841590727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11748493814072756488483877 2202842590138641841590727)
          ·
            refine ⟨3304263885207962762386091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202842590138641841590727 3304263885207962762386091)
            ·
              refine ⟨4956395827811944143579137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304263885207962762386091 4956395827811944143579137)
              ·
                refine ⟨3717296870858958107684353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956395827811944143579137 3717296870858958107684353)
                ·
                  refine ⟨2787972653144218580763265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3717296870858958107684353 2787972653144218580763265)
                  ·
                    refine ⟨2090979489858163935572449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2787972653144218580763265 2090979489858163935572449)
                    ·
                      refine ⟨1568234617393622951679337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2090979489858163935572449 1568234617393622951679337)
                      ·
                        rfl

theorem cell23_3054126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3054126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054126 prefixEnd_3054126 := by exact prefixLift 3054126
  have htrace : WordTrace (prefixWord ++ tailWord_3054126) baseStart_3054126 baseEnd_3054126 := by
    simpa [prefixWord, tailWord_3054126, baseEnd_3054126] using wordTrace_append hprefix tailTrace_3054126
  have hstable : (prefixWord ++ tailWord_3054126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054126).length < 2 ^ (prefixWord ++ tailWord_3054126).sum := by decide
  have hdescent : baseEnd_3054126 < baseStart_3054126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054131 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 4]
def baseStart_3054131 : Nat := 118140960795 + 3054131 * 2 ^ 59
def prefixEnd_3054131 : Nat := 4983230072969 + 3 ^ 40 * 3054131 * 2
def baseEnd_3054131 : Nat := 1568237184796895432116813

theorem tailTrace_3054131 : CollatzResearch.WordTrace tailWord_3054131 prefixEnd_3054131 1568237184796895432116813 := by
  unfold tailWord_3054131
  simp only [CollatzResearch.WordTrace]
  refine ⟨111393308898412465892890247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74262205932274977261926831 111393308898412465892890247)
  ·
    refine ⟨167089963347618698839335371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111393308898412465892890247 167089963347618698839335371)
    ·
      refine ⟨250634945021428048259003057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167089963347618698839335371 250634945021428048259003057)
      ·
        refine ⟨187976208766071036194252293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250634945021428048259003057 187976208766071036194252293)
        ·
          refine ⟨35245539143638319286422305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187976208766071036194252293 35245539143638319286422305)
          ·
            refine ⟨26434154357728739464816729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35245539143638319286422305 26434154357728739464816729)
            ·
              refine ⟨19825615768296554598612547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26434154357728739464816729 19825615768296554598612547)
              ·
                refine ⟨29738423652444831897918821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19825615768296554598612547 29738423652444831897918821)
                ·
                  refine ⟨5575954434833405980859779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29738423652444831897918821 5575954434833405980859779)
                  ·
                    refine ⟨8363931652250108971289669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575954434833405980859779 8363931652250108971289669)
                    ·
                      refine ⟨1568237184796895432116813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8363931652250108971289669 1568237184796895432116813)
                      ·
                        rfl

theorem cell23_3054131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_3054131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054131 prefixEnd_3054131 := by exact prefixLift 3054131
  have htrace : WordTrace (prefixWord ++ tailWord_3054131) baseStart_3054131 baseEnd_3054131 := by
    simpa [prefixWord, tailWord_3054131, baseEnd_3054131] using wordTrace_append hprefix tailTrace_3054131
  have hstable : (prefixWord ++ tailWord_3054131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054131).length < 2 ^ (prefixWord ++ tailWord_3054131).sum := by decide
  have hdescent : baseEnd_3054131 < baseStart_3054131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054158 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_3054158 : Nat := 118140960795 + 3054158 * 2 ^ 59
def prefixEnd_3054158 : Nat := 4983230072969 + 3 ^ 40 * 3054158 * 2
def baseEnd_3054158 : Nat := 522750349591522275493063

theorem tailTrace_3054158 : CollatzResearch.WordTrace tailWord_3054158 prefixEnd_3054158 522750349591522275493063 := by
  unfold tailWord_3054158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924286708664331188015391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74262862446209766336082085 13924286708664331188015391)
  ·
    refine ⟨20886430062996496782023087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13924286708664331188015391 20886430062996496782023087)
    ·
      refine ⟨31329645094494745173034631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20886430062996496782023087 31329645094494745173034631)
      ·
        refine ⟨46994467641742117759551947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31329645094494745173034631 46994467641742117759551947)
        ·
          refine ⟨70491701462613176639327921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46994467641742117759551947 70491701462613176639327921)
          ·
            refine ⟨52868776096959882479495941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70491701462613176639327921 52868776096959882479495941)
            ·
              refine ⟨9912895518179977964905489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52868776096959882479495941 9912895518179977964905489)
              ·
                refine ⟨7434671638634983473679117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9912895518179977964905489 7434671638634983473679117)
                ·
                  refine ⟨2788001864488118802629669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7434671638634983473679117 2788001864488118802629669)
                  ·
                    refine ⟨522750349591522275493063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2788001864488118802629669 522750349591522275493063)
                    ·
                      rfl

theorem cell23_3054158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_3054158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054158 prefixEnd_3054158 := by exact prefixLift 3054158
  have htrace : WordTrace (prefixWord ++ tailWord_3054158) baseStart_3054158 baseEnd_3054158 := by
    simpa [prefixWord, tailWord_3054158, baseEnd_3054158] using wordTrace_append hprefix tailTrace_3054158
  have hstable : (prefixWord ++ tailWord_3054158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054158).length < 2 ^ (prefixWord ++ tailWord_3054158).sum := by decide
  have hdescent : baseEnd_3054158 < baseStart_3054158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054192 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 3, 4]
def baseStart_3054192 : Nat := 118140960795 + 3054192 * 2 ^ 59
def prefixEnd_3054192 : Nat := 4983230072969 + 3 ^ 40 * 3054192 * 2
def baseEnd_3054192 : Nat := 522756169038939897818011

theorem tailTrace_3054192 : CollatzResearch.WordTrace tailWord_3054192 prefixEnd_3054192 522756169038939897818011 := by
  unfold tailWord_3054192
  simp only [CollatzResearch.WordTrace]
  refine ⟨55697766875595736655430415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74263689167460982207240553 55697766875595736655430415)
  ·
    refine ⟨83546650313393604983145623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55697766875595736655430415 83546650313393604983145623)
    ·
      refine ⟨125319975470090407474718435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83546650313393604983145623 125319975470090407474718435)
      ·
        refine ⟨187979963205135611212077653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125319975470090407474718435 187979963205135611212077653)
        ·
          refine ⟨2202890193810182943891535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 187979963205135611212077653 2202890193810182943891535)
          ·
            refine ⟨3304335290715274415837303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202890193810182943891535 3304335290715274415837303)
            ·
              refine ⟨4956502936072911623755955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304335290715274415837303 4956502936072911623755955)
              ·
                refine ⟨7434754404109367435633933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956502936072911623755955 7434754404109367435633933)
                ·
                  refine ⟨2788032901541012788362725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7434754404109367435633933 2788032901541012788362725)
                  ·
                    refine ⟨522756169038939897818011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2788032901541012788362725 522756169038939897818011)
                    ·
                      rfl

theorem cell23_3054192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 4].length) (baseStart_3054192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054192 prefixEnd_3054192 := by exact prefixLift 3054192
  have htrace : WordTrace (prefixWord ++ tailWord_3054192) baseStart_3054192 baseEnd_3054192 := by
    simpa [prefixWord, tailWord_3054192, baseEnd_3054192] using wordTrace_append hprefix tailTrace_3054192
  have hstable : (prefixWord ++ tailWord_3054192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054192).length < 2 ^ (prefixWord ++ tailWord_3054192).sum := by decide
  have hdescent : baseEnd_3054192 < baseStart_3054192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054232 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3054232 : Nat := 118140960795 + 3054232 * 2 ^ 59
def prefixEnd_3054232 : Nat := 4983230072969 + 3 ^ 40 * 3054232 * 2
def baseEnd_3054232 : Nat := 1568289046342999536953849

theorem tailTrace_3054232 : CollatzResearch.WordTrace tailWord_3054232 prefixEnd_3054232 1568289046342999536953849 := by
  unfold tailWord_3054232
  simp only [CollatzResearch.WordTrace]
  refine ⟨55698496335523280071158475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74264661780697706761544633 55698496335523280071158475)
  ·
    refine ⟨83547744503284920106737713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55698496335523280071158475 83547744503284920106737713)
    ·
      refine ⟨62660808377463690080053285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83547744503284920106737713 62660808377463690080053285)
      ·
        refine ⟨11748901570774441890009991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62660808377463690080053285 11748901570774441890009991)
        ·
          refine ⟨17623352356161662835014987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11748901570774441890009991 17623352356161662835014987)
          ·
            refine ⟨26435028534242494252522481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17623352356161662835014987 26435028534242494252522481)
            ·
              refine ⟨19826271400681870689391861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26435028534242494252522481 19826271400681870689391861)
              ·
                refine ⟨1858712943813925377130487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19826271400681870689391861 1858712943813925377130487)
                ·
                  refine ⟨2788069415720888065695731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858712943813925377130487 2788069415720888065695731)
                  ·
                    refine ⟨4182104123581332098543597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2788069415720888065695731 4182104123581332098543597)
                    ·
                      refine ⟨1568289046342999536953849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4182104123581332098543597 1568289046342999536953849)
                      ·
                        rfl

theorem cell23_3054232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3054232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054232 prefixEnd_3054232 := by exact prefixLift 3054232
  have htrace : WordTrace (prefixWord ++ tailWord_3054232) baseStart_3054232 baseEnd_3054232 := by
    simpa [prefixWord, tailWord_3054232, baseEnd_3054232] using wordTrace_append hprefix tailTrace_3054232
  have hstable : (prefixWord ++ tailWord_3054232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054232).length < 2 ^ (prefixWord ++ tailWord_3054232).sum := by decide
  have hdescent : baseEnd_3054232 < baseStart_3054232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054272 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 3, 2, 2]
def baseStart_3054272 : Nat := 118140960795 + 3054272 * 2 ^ 59
def prefixEnd_3054272 : Nat := 4983230072969 + 3 ^ 40 * 3054272 * 2
def baseEnd_3054272 : Nat := 1568309585569179380453665

theorem tailTrace_3054272 : CollatzResearch.WordTrace tailWord_3054272 prefixEnd_3054272 1568309585569179380453665 := by
  unfold tailWord_3054272
  simp only [CollatzResearch.WordTrace]
  refine ⟨55699225795450823486886535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74265634393934431315848713 55699225795450823486886535)
  ·
    refine ⟨83548838693176235230329803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55699225795450823486886535 83548838693176235230329803)
    ·
      refine ⟨125323258039764352845494705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83548838693176235230329803 125323258039764352845494705)
      ·
        refine ⟨93992443529823264634121029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125323258039764352845494705 93992443529823264634121029)
        ·
          refine ⟨17623583161841862118897693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93992443529823264634121029 17623583161841862118897693)
          ·
            refine ⟨6608843685690698294586635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17623583161841862118897693 6608843685690698294586635)
            ·
              refine ⟨9913265528536047441879953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6608843685690698294586635 9913265528536047441879953)
              ·
                refine ⟨7434949146402035581409965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9913265528536047441879953 7434949146402035581409965)
                ·
                  refine ⟨2788105929900763343028737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7434949146402035581409965 2788105929900763343028737)
                  ·
                    refine ⟨2091079447425572507271553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788105929900763343028737 2091079447425572507271553)
                    ·
                      refine ⟨1568309585569179380453665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091079447425572507271553 1568309585569179380453665)
                      ·
                        rfl

theorem cell23_3054272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_3054272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054272 prefixEnd_3054272 := by exact prefixLift 3054272
  have htrace : WordTrace (prefixWord ++ tailWord_3054272) baseStart_3054272 baseEnd_3054272 := by
    simpa [prefixWord, tailWord_3054272, baseEnd_3054272] using wordTrace_append hprefix tailTrace_3054272
  have hstable : (prefixWord ++ tailWord_3054272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054272).length < 2 ^ (prefixWord ++ tailWord_3054272).sum := by decide
  have hdescent : baseEnd_3054272 < baseStart_3054272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054289 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 1, 2, 2]
def baseStart_3054289 : Nat := 118140960795 + 3054289 * 2 ^ 59
def prefixEnd_3054289 : Nat := 4983230072969 + 3 ^ 40 * 3054289 * 2
def baseEnd_3054289 : Nat := 1568318314740305813941087

theorem tailTrace_3054289 : CollatzResearch.WordTrace tailWord_3054289 prefixEnd_3054289 1568318314740305813941087 := by
  unfold tailWord_3054289
  simp only [CollatzResearch.WordTrace]
  refine ⟨111399071631840058877141921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74266047754560039251427947 111399071631840058877141921)
  ·
    refine ⟨83549303723880044157856441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111399071631840058877141921 83549303723880044157856441)
    ·
      refine ⟨62661977792910033118392331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83549303723880044157856441 62661977792910033118392331)
      ·
        refine ⟨93992966689365049677588497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62661977792910033118392331 93992966689365049677588497)
        ·
          refine ⟨70494725017023787258191373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93992966689365049677588497 70494725017023787258191373)
          ·
            refine ⟨26435521881383920221821765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70494725017023787258191373 26435521881383920221821765)
            ·
              refine ⟨4956660352759485041591581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26435521881383920221821765 4956660352759485041591581)
              ·
                refine ⟨1858747632284806890596843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4956660352759485041591581 1858747632284806890596843)
                ·
                  refine ⟨2788121448427210335895265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858747632284806890596843 2788121448427210335895265)
                  ·
                    refine ⟨2091091086320407751921449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788121448427210335895265 2091091086320407751921449)
                    ·
                      refine ⟨1568318314740305813941087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091091086320407751921449 1568318314740305813941087)
                      ·
                        rfl

theorem cell23_3054289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_3054289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054289 prefixEnd_3054289 := by exact prefixLift 3054289
  have htrace : WordTrace (prefixWord ++ tailWord_3054289) baseStart_3054289 baseEnd_3054289 := by
    simpa [prefixWord, tailWord_3054289, baseEnd_3054289] using wordTrace_append hprefix tailTrace_3054289
  have hstable : (prefixWord ++ tailWord_3054289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054289).length < 2 ^ (prefixWord ++ tailWord_3054289).sum := by decide
  have hdescent : baseEnd_3054289 < baseStart_3054289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054322 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3054322 : Nat := 118140960795 + 3054322 * 2 ^ 59
def prefixEnd_3054322 : Nat := 4983230072969 + 3 ^ 40 * 3054322 * 2
def baseEnd_3054322 : Nat := 1568335259601904184828435

theorem tailTrace_3054322 : CollatzResearch.WordTrace tailWord_3054322 prefixEnd_3054322 1568335259601904184828435 := by
  unfold tailWord_3054322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27850068810180126378273305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74266850160480337008728813 27850068810180126378273305)
  ·
    refine ⟨20887551607635094783704979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27850068810180126378273305 20887551607635094783704979)
    ·
      refine ⟨31331327411452642175557469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20887551607635094783704979 31331327411452642175557469)
      ·
        refine ⟨11749247779294740815834051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31331327411452642175557469 11749247779294740815834051)
        ·
          refine ⟨17623871668942111223751077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11749247779294740815834051 17623871668942111223751077)
          ·
            refine ⟨3304475937926645854453327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17623871668942111223751077 3304475937926645854453327)
            ·
              refine ⟨4956713906889968781679991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304475937926645854453327 4956713906889968781679991)
              ·
                refine ⟨7435070860334953172519987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956713906889968781679991 7435070860334953172519987)
                ·
                  refine ⟨11152606290502429758779981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435070860334953172519987 11152606290502429758779981)
                  ·
                    refine ⟨4182227358938411159542493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11152606290502429758779981 4182227358938411159542493)
                    ·
                      refine ⟨1568335259601904184828435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4182227358938411159542493 1568335259601904184828435)
                      ·
                        rfl

theorem cell23_3054322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3054322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054322 prefixEnd_3054322 := by exact prefixLift 3054322
  have htrace : WordTrace (prefixWord ++ tailWord_3054322) baseStart_3054322 baseEnd_3054322 := by
    simpa [prefixWord, tailWord_3054322, baseEnd_3054322] using wordTrace_append hprefix tailTrace_3054322
  have hstable : (prefixWord ++ tailWord_3054322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054322).length < 2 ^ (prefixWord ++ tailWord_3054322).sum := by decide
  have hdescent : baseEnd_3054322 < baseStart_3054322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054332 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_3054332 : Nat := 118140960795 + 3054332 * 2 ^ 59
def prefixEnd_3054332 : Nat := 4983230072969 + 3 ^ 40 * 3054332 * 2
def baseEnd_3054332 : Nat := 1568340394408449145703389

theorem tailTrace_3054332 : CollatzResearch.WordTrace tailWord_3054332 prefixEnd_3054332 1568340394408449145703389 := by
  unfold tailWord_3054332
  simp only [CollatzResearch.WordTrace]
  refine ⟨55700319985342138610478625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74267093313789518147304833 55700319985342138610478625)
  ·
    refine ⟨41775239989006603957858969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55700319985342138610478625 41775239989006603957858969)
    ·
      refine ⟨31331429991754952968394227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41775239989006603957858969 31331429991754952968394227)
      ·
        refine ⟨46997144987632429452591341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31331429991754952968394227 46997144987632429452591341)
        ·
          refine ⟨17623929370362161044721753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46997144987632429452591341 17623929370362161044721753)
          ·
            refine ⟨13217947027771620783541315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17623929370362161044721753 13217947027771620783541315)
            ·
              refine ⟨19826920541657431175311973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13217947027771620783541315 19826920541657431175311973)
              ·
                refine ⟨3717547601560768345370995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19826920541657431175311973 3717547601560768345370995)
                ·
                  refine ⟨5576321402341152518056493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717547601560768345370995 5576321402341152518056493)
                  ·
                    refine ⟨2091120525877932194271185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5576321402341152518056493 2091120525877932194271185)
                    ·
                      refine ⟨1568340394408449145703389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091120525877932194271185 1568340394408449145703389)
                      ·
                        rfl

theorem cell23_3054332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_3054332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054332 prefixEnd_3054332 := by exact prefixLift 3054332
  have htrace : WordTrace (prefixWord ++ tailWord_3054332) baseStart_3054332 baseEnd_3054332 := by
    simpa [prefixWord, tailWord_3054332, baseEnd_3054332] using wordTrace_append hprefix tailTrace_3054332
  have hstable : (prefixWord ++ tailWord_3054332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054332).length < 2 ^ (prefixWord ++ tailWord_3054332).sum := by decide
  have hdescent : baseEnd_3054332 < baseStart_3054332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054345 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 1, 4, 2]
def baseStart_3054345 : Nat := 118140960795 + 3054345 * 2 ^ 59
def prefixEnd_3054345 : Nat := 4983230072969 + 3 ^ 40 * 3054345 * 2
def baseEnd_3054345 : Nat := 1568347069656957594840829

theorem tailTrace_3054345 : CollatzResearch.WordTrace tailWord_3054345 prefixEnd_3054345 1568347069656957594840829 := by
  unfold tailWord_3054345
  simp only [CollatzResearch.WordTrace]
  refine ⟨111401114119637180441180489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74267409413091453627453659 111401114119637180441180489)
  ·
    refine ⟨83550835589727885330885367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111401114119637180441180489 83550835589727885330885367)
    ·
      refine ⟨125326253384591827996328051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83550835589727885330885367 125326253384591827996328051)
      ·
        refine ⟨187989380076887741994492077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125326253384591827996328051 187989380076887741994492077)
        ·
          refine ⟨70496017528832903247934529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187989380076887741994492077 70496017528832903247934529)
          ·
            refine ⟨52872013146624677435950897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70496017528832903247934529 52872013146624677435950897)
            ·
              refine ⟨39654009859968508076963173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52872013146624677435950897 39654009859968508076963173)
              ·
                refine ⟨7435126848744095264430595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39654009859968508076963173 7435126848744095264430595)
                ·
                  refine ⟨11152690273116142896645893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435126848744095264430595 11152690273116142896645893)
                  ·
                    refine ⟨2091129426209276793121105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11152690273116142896645893 2091129426209276793121105)
                    ·
                      refine ⟨1568347069656957594840829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091129426209276793121105 1568347069656957594840829)
                      ·
                        rfl

theorem cell23_3054345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 4, 2].length) (baseStart_3054345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054345 prefixEnd_3054345 := by exact prefixLift 3054345
  have htrace : WordTrace (prefixWord ++ tailWord_3054345) baseStart_3054345 baseEnd_3054345 := by
    simpa [prefixWord, tailWord_3054345, baseEnd_3054345] using wordTrace_append hprefix tailTrace_3054345
  have hstable : (prefixWord ++ tailWord_3054345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054345).length < 2 ^ (prefixWord ++ tailWord_3054345).sum := by decide
  have hdescent : baseEnd_3054345 < baseStart_3054345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054348 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3054348 : Nat := 118140960795 + 3054348 * 2 ^ 59
def prefixEnd_3054348 : Nat := 4983230072969 + 3 ^ 40 * 3054348 * 2
def baseEnd_3054348 : Nat := 1568348610098921083103315

theorem tailTrace_3054348 : CollatzResearch.WordTrace tailWord_3054348 prefixEnd_3054348 1568348610098921083103315 := by
  unfold tailWord_3054348
  simp only [CollatzResearch.WordTrace]
  refine ⟨55700611769313155976769849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74267482359084207969026465 55700611769313155976769849)
  ·
    refine ⟨41775458826984866982577387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55700611769313155976769849 41775458826984866982577387)
    ·
      refine ⟨62663188240477300473866081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41775458826984866982577387 62663188240477300473866081)
      ·
        refine ⟨46997391180357975355399561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62663188240477300473866081 46997391180357975355399561)
        ·
          refine ⟨35248043385268481516549671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46997391180357975355399561 35248043385268481516549671)
          ·
            refine ⟨52872065077902722274824507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35248043385268481516549671 52872065077902722274824507)
            ·
              refine ⟨79308097616854083412236761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52872065077902722274824507 79308097616854083412236761)
              ·
                refine ⟨59481073212640562559177571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79308097616854083412236761 59481073212640562559177571)
                ·
                  refine ⟨89221609818960843838766357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59481073212640562559177571 89221609818960843838766357)
                  ·
                    refine ⟨4182262960263789554942173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89221609818960843838766357 4182262960263789554942173)
                    ·
                      refine ⟨1568348610098921083103315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4182262960263789554942173 1568348610098921083103315)
                      ·
                        rfl

theorem cell23_3054348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3054348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054348 prefixEnd_3054348 := by exact prefixLift 3054348
  have htrace : WordTrace (prefixWord ++ tailWord_3054348) baseStart_3054348 baseEnd_3054348 := by
    simpa [prefixWord, tailWord_3054348, baseEnd_3054348] using wordTrace_append hprefix tailTrace_3054348
  have hstable : (prefixWord ++ tailWord_3054348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054348).length < 2 ^ (prefixWord ++ tailWord_3054348).sum := by decide
  have hdescent : baseEnd_3054348 < baseStart_3054348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054362 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2]
def baseStart_3054362 : Nat := 118140960795 + 3054362 * 2 ^ 59
def prefixEnd_3054362 : Nat := 4983230072969 + 3 ^ 40 * 3054362 * 2
def baseEnd_3054362 : Nat := 1568355798828084028328251

theorem tailTrace_3054362 : CollatzResearch.WordTrace tailWord_3054362 prefixEnd_3054362 1568355798828084028328251 := by
  unfold tailWord_3054362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27850433540143898086137335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74267822773717061563032893 27850433540143898086137335)
  ·
    refine ⟨41775650310215847129206003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27850433540143898086137335 41775650310215847129206003)
    ·
      refine ⟨62663475465323770693809005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41775650310215847129206003 62663475465323770693809005)
      ·
        refine ⟨23498803299496414010178377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62663475465323770693809005 23498803299496414010178377)
        ·
          refine ⟨17624102474622310507633783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23498803299496414010178377 17624102474622310507633783)
          ·
            refine ⟨26436153711933465761450675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17624102474622310507633783 26436153711933465761450675)
            ·
              refine ⟨39654230567900198642176013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26436153711933465761450675 39654230567900198642176013)
              ·
                refine ⟨14870336462962574490816005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39654230567900198642176013 14870336462962574490816005)
                ·
                  refine ⟨2788188086805482717028001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14870336462962574490816005 2788188086805482717028001)
                  ·
                    refine ⟨2091141065104112037771001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788188086805482717028001 2091141065104112037771001)
                    ·
                      refine ⟨1568355798828084028328251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091141065104112037771001 1568355798828084028328251)
                      ·
                        rfl

theorem cell23_3054362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_3054362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054362 prefixEnd_3054362 := by exact prefixLift 3054362
  have htrace : WordTrace (prefixWord ++ tailWord_3054362) baseStart_3054362 baseEnd_3054362 := by
    simpa [prefixWord, tailWord_3054362, baseEnd_3054362] using wordTrace_append hprefix tailTrace_3054362
  have hstable : (prefixWord ++ tailWord_3054362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054362).length < 2 ^ (prefixWord ++ tailWord_3054362).sum := by decide
  have hdescent : baseEnd_3054362 < baseStart_3054362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054408 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3054408 : Nat := 118140960795 + 3054408 * 2 ^ 59
def prefixEnd_3054408 : Nat := 4983230072969 + 3 ^ 40 * 3054408 * 2
def baseEnd_3054408 : Nat := 1568379418938190848353039

theorem tailTrace_3054408 : CollatzResearch.WordTrace tailWord_3054408 prefixEnd_3054408 1568379418938190848353039 := by
  unfold tailWord_3054408
  simp only [CollatzResearch.WordTrace]
  refine ⟨55701705959204471100361939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74268941278939294800482585 55701705959204471100361939)
  ·
    refine ⟨83552558938806706650542909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55701705959204471100361939 83552558938806706650542909)
    ·
      refine ⟨31332209602052514993953591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83552558938806706650542909 31332209602052514993953591)
      ·
        refine ⟨46998314403078772490930387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31332209602052514993953591 46998314403078772490930387)
        ·
          refine ⟨70497471604618158736395581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46998314403078772490930387 70497471604618158736395581)
          ·
            refine ⟨26436551851731809526148343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70497471604618158736395581 26436551851731809526148343)
            ·
              refine ⟨39654827777597714289222515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26436551851731809526148343 39654827777597714289222515)
              ·
                refine ⟨59482241666396571433833773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39654827777597714289222515 59482241666396571433833773)
                ·
                  refine ⟨22305840624898714287687665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59482241666396571433833773 22305840624898714287687665)
                  ·
                    refine ⟨16729380468674035715765749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22305840624898714287687665 16729380468674035715765749)
                    ·
                      refine ⟨1568379418938190848353039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16729380468674035715765749 1568379418938190848353039)
                      ·
                        rfl

theorem cell23_3054408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3054408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054408 prefixEnd_3054408 := by exact prefixLift 3054408
  have htrace : WordTrace (prefixWord ++ tailWord_3054408) baseStart_3054408 baseEnd_3054408 := by
    simpa [prefixWord, tailWord_3054408, baseEnd_3054408] using wordTrace_append hprefix tailTrace_3054408
  have hstable : (prefixWord ++ tailWord_3054408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054408).length < 2 ^ (prefixWord ++ tailWord_3054408).sum := by decide
  have hdescent : baseEnd_3054408 < baseStart_3054408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054413 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3054413 : Nat := 118140960795 + 3054413 * 2 ^ 59
def prefixEnd_3054413 : Nat := 4983230072969 + 3 ^ 40 * 3054413 * 2
def baseEnd_3054413 : Nat := 1568381986341463328790517

theorem tailTrace_3054413 : CollatzResearch.WordTrace tailWord_3054413 prefixEnd_3054413 1568381986341463328790517 := by
  unfold tailWord_3054413
  simp only [CollatzResearch.WordTrace]
  refine ⟨111403594283390828054655893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74269062855593885369770595 111403594283390828054655893)
  ·
    refine ⟨5222043482033945065061995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111403594283390828054655893 5222043482033945065061995)
    ·
      refine ⟨7833065223050917597592993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222043482033945065061995 7833065223050917597592993)
      ·
        refine ⟨5874798917288188198194745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7833065223050917597592993 5874798917288188198194745)
        ·
          refine ⟨4406099187966141148646059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5874798917288188198194745 4406099187966141148646059)
          ·
            refine ⟨6609148781949211722969089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406099187966141148646059 6609148781949211722969089)
            ·
              refine ⟨4956861586461908792226817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6609148781949211722969089 4956861586461908792226817)
              ·
                refine ⟨3717646189846431594170113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956861586461908792226817 3717646189846431594170113)
                ·
                  refine ⟨2788234642384823695627585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3717646189846431594170113 2788234642384823695627585)
                  ·
                    refine ⟨2091175981788617771720689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788234642384823695627585 2091175981788617771720689)
                    ·
                      refine ⟨1568381986341463328790517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091175981788617771720689 1568381986341463328790517)
                      ·
                        rfl

theorem cell23_3054413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3054413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054413 prefixEnd_3054413 := by exact prefixLift 3054413
  have htrace : WordTrace (prefixWord ++ tailWord_3054413) baseStart_3054413 baseEnd_3054413 := by
    simpa [prefixWord, tailWord_3054413, baseEnd_3054413] using wordTrace_append hprefix tailTrace_3054413
  have hstable : (prefixWord ++ tailWord_3054413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054413).length < 2 ^ (prefixWord ++ tailWord_3054413).sum := by decide
  have hdescent : baseEnd_3054413 < baseStart_3054413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054458 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_3054458 : Nat := 118140960795 + 3054458 * 2 ^ 59
def prefixEnd_3054458 : Nat := 4983230072969 + 3 ^ 40 * 3054458 * 2
def baseEnd_3054458 : Nat := 174267232552323961414201

theorem tailTrace_3054458 : CollatzResearch.WordTrace tailWord_3054458 prefixEnd_3054458 174267232552323961414201 := by
  unfold tailWord_3054458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27851308892056950185011007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74270157045485200493362685 27851308892056950185011007)
  ·
    refine ⟨41776963338085425277516511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27851308892056950185011007 41776963338085425277516511)
    ·
      refine ⟨62665445007128137916274767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41776963338085425277516511 62665445007128137916274767)
      ·
        refine ⟨93998167510692206874412151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62665445007128137916274767 93998167510692206874412151)
        ·
          refine ⟨140997251266038310311618227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93998167510692206874412151 140997251266038310311618227)
          ·
            refine ⟨211495876899057465467427341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140997251266038310311618227 211495876899057465467427341)
            ·
              refine ⟨79310953837146549550285253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211495876899057465467427341 79310953837146549550285253)
              ·
                refine ⟨14870803844464978040678485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79310953837146549550285253 14870803844464978040678485)
                ·
                  refine ⟨174267232552323961414201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14870803844464978040678485 174267232552323961414201)
                  ·
                    rfl

theorem cell23_3054458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_3054458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054458 prefixEnd_3054458 := by exact prefixLift 3054458
  have htrace : WordTrace (prefixWord ++ tailWord_3054458) baseStart_3054458 baseEnd_3054458 := by
    simpa [prefixWord, tailWord_3054458, baseEnd_3054458] using wordTrace_append hprefix tailTrace_3054458
  have hstable : (prefixWord ++ tailWord_3054458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054458).length < 2 ^ (prefixWord ++ tailWord_3054458).sum := by decide
  have hdescent : baseEnd_3054458 < baseStart_3054458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054475 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 6]
def baseStart_3054475 : Nat := 118140960795 + 3054475 * 2 ^ 59
def prefixEnd_3054475 : Nat := 4983230072969 + 3 ^ 40 * 3054475 * 2
def baseEnd_3054475 : Nat := 174268202460226898468359

theorem tailTrace_3054475 : CollatzResearch.WordTrace tailWord_3054475 prefixEnd_3054475 174268202460226898468359 := by
  unfold tailWord_3054475
  simp only [CollatzResearch.WordTrace]
  refine ⟨111405855609166212643412879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74270570406110808428941919 111405855609166212643412879)
  ·
    refine ⟨167108783413749318965119319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111405855609166212643412879 167108783413749318965119319)
    ·
      refine ⟨250663175120623978447678979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167108783413749318965119319 250663175120623978447678979)
      ·
        refine ⟨375994762680935967671518469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250663175120623978447678979 375994762680935967671518469)
        ·
          refine ⟨70499018002675493938409713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375994762680935967671518469 70499018002675493938409713)
          ·
            refine ⟨52874263502006620453807285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70499018002675493938409713 52874263502006620453807285)
            ·
              refine ⟨4956962203313120667544433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52874263502006620453807285 4956962203313120667544433)
              ·
                refine ⟨3717721652484840500658325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956962203313120667544433 3717721652484840500658325)
                ·
                  refine ⟨174268202460226898468359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3717721652484840500658325 174268202460226898468359)
                  ·
                    rfl

theorem cell23_3054475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 6].length) (baseStart_3054475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054475 prefixEnd_3054475 := by exact prefixLift 3054475
  have htrace : WordTrace (prefixWord ++ tailWord_3054475) baseStart_3054475 baseEnd_3054475 := by
    simpa [prefixWord, tailWord_3054475, baseEnd_3054475] using wordTrace_append hprefix tailTrace_3054475
  have hstable : (prefixWord ++ tailWord_3054475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054475).length < 2 ^ (prefixWord ++ tailWord_3054475).sum := by decide
  have hdescent : baseEnd_3054475 < baseStart_3054475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054513 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 1, 4]
def baseStart_3054513 : Nat := 118140960795 + 3054513 * 2 ^ 59
def prefixEnd_3054513 : Nat := 4983230072969 + 3 ^ 40 * 3054513 * 2
def baseEnd_3054513 : Nat := 522811111468970979180019

theorem tailTrace_3054513 : CollatzResearch.WordTrace tailWord_3054513 prefixEnd_3054513 522811111468970979180019 := by
  unfold tailWord_3054513
  simp only [CollatzResearch.WordTrace]
  refine ⟨111407241583028545133296193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74271494388685696755530795 111407241583028545133296193)
  ·
    refine ⟨83555431187271408849972145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111407241583028545133296193 83555431187271408849972145)
    ·
      refine ⟨62666573390453556637479109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83555431187271408849972145 62666573390453556637479109)
      ·
        refine ⟨11749982510710041869527333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62666573390453556637479109 11749982510710041869527333)
        ·
          refine ⟨2203121720758132850536375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11749982510710041869527333 2203121720758132850536375)
          ·
            refine ⟨3304682581137199275804563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203121720758132850536375 3304682581137199275804563)
            ·
              refine ⟨4957023871705798913706845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304682581137199275804563 4957023871705798913706845)
              ·
                refine ⟨1858883951889674592640067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4957023871705798913706845 1858883951889674592640067)
                ·
                  refine ⟨2788325927834511888960101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858883951889674592640067 2788325927834511888960101)
                  ·
                    refine ⟨522811111468970979180019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2788325927834511888960101 522811111468970979180019)
                    ·
                      rfl

theorem cell23_3054513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_3054513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054513 prefixEnd_3054513 := by exact prefixLift 3054513
  have htrace : WordTrace (prefixWord ++ tailWord_3054513) baseStart_3054513 baseEnd_3054513 := by
    simpa [prefixWord, tailWord_3054513, baseEnd_3054513] using wordTrace_append hprefix tailTrace_3054513
  have hstable : (prefixWord ++ tailWord_3054513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054513).length < 2 ^ (prefixWord ++ tailWord_3054513).sum := by decide
  have hdescent : baseEnd_3054513 < baseStart_3054513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054536 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_3054536 : Nat := 118140960795 + 3054536 * 2 ^ 59
def prefixEnd_3054536 : Nat := 4983230072969 + 3 ^ 40 * 3054536 * 2
def baseEnd_3054536 : Nat := 1568445144461966347552451

theorem tailTrace_3054536 : CollatzResearch.WordTrace tailWord_3054536 prefixEnd_3054536 1568445144461966347552451 := by
  unfold tailWord_3054536
  simp only [CollatzResearch.WordTrace]
  refine ⟨55704040230972610030691731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74272053641296813374255641 55704040230972610030691731)
  ·
    refine ⟨83556060346458915046037597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55704040230972610030691731 83556060346458915046037597)
    ·
      refine ⟨31333522629922093142264099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83556060346458915046037597 31333522629922093142264099)
      ·
        refine ⟨47000283944883139713396149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31333522629922093142264099 47000283944883139713396149)
        ·
          refine ⟨4406276619832794348130889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47000283944883139713396149 4406276619832794348130889)
          ·
            refine ⟨3304707464874595761098167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4406276619832794348130889 3304707464874595761098167)
            ·
              refine ⟨4957061197311893641647251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304707464874595761098167 4957061197311893641647251)
              ·
                refine ⟨7435591795967840462470877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957061197311893641647251 7435591795967840462470877)
                ·
                  refine ⟨2788346923487940173426579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7435591795967840462470877 2788346923487940173426579)
                  ·
                    refine ⟨4182520385231910260139869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2788346923487940173426579 4182520385231910260139869)
                    ·
                      refine ⟨1568445144461966347552451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4182520385231910260139869 1568445144461966347552451)
                      ·
                        rfl

theorem cell23_3054536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_3054536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054536 prefixEnd_3054536 := by exact prefixLift 3054536
  have htrace : WordTrace (prefixWord ++ tailWord_3054536) baseStart_3054536 baseEnd_3054536 := by
    simpa [prefixWord, tailWord_3054536, baseEnd_3054536] using wordTrace_append hprefix tailTrace_3054536
  have hstable : (prefixWord ++ tailWord_3054536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054536).length < 2 ^ (prefixWord ++ tailWord_3054536).sum := by decide
  have hdescent : baseEnd_3054536 < baseStart_3054536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054545 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_3054545 : Nat := 118140960795 + 3054545 * 2 ^ 59
def prefixEnd_3054545 : Nat := 4983230072969 + 3 ^ 40 * 3054545 * 2
def baseEnd_3054545 : Nat := 1568449765787856812339909

theorem tailTrace_3054545 : CollatzResearch.WordTrace tailWord_3054545 prefixEnd_3054545 1568449765787856812339909 := by
  unfold tailWord_3054545
  simp only [CollatzResearch.WordTrace]
  refine ⟨111408408718912614598461089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74272272479275076398974059 111408408718912614598461089)
  ·
    refine ⟨83556306539184460948845817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111408408718912614598461089 83556306539184460948845817)
    ·
      refine ⟨62667229904388345711634363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83556306539184460948845817 62667229904388345711634363)
      ·
        refine ⟨94000844856582518567451545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62667229904388345711634363 94000844856582518567451545)
        ·
          refine ⟨70500633642436888925588659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94000844856582518567451545 70500633642436888925588659)
          ·
            refine ⟨105750950463655333388382989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70500633642436888925588659 105750950463655333388382989)
            ·
              refine ⟨39656606423870750020643621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105750950463655333388382989 39656606423870750020643621)
              ·
                refine ⟨7435613704475765628870679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39656606423870750020643621 7435613704475765628870679)
                ·
                  refine ⟨11153420556713648443306019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435613704475765628870679 11153420556713648443306019)
                  ·
                    refine ⟨16730130835070472664959029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11153420556713648443306019 16730130835070472664959029)
                    ·
                      refine ⟨1568449765787856812339909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16730130835070472664959029 1568449765787856812339909)
                      ·
                        rfl

theorem cell23_3054545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_3054545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054545 prefixEnd_3054545 := by exact prefixLift 3054545
  have htrace : WordTrace (prefixWord ++ tailWord_3054545) baseStart_3054545 baseEnd_3054545 := by
    simpa [prefixWord, tailWord_3054545, baseEnd_3054545] using wordTrace_append hprefix tailTrace_3054545
  have hstable : (prefixWord ++ tailWord_3054545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054545).length < 2 ^ (prefixWord ++ tailWord_3054545).sum := by decide
  have hdescent : baseEnd_3054545 < baseStart_3054545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054576 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 1, 2, 2]
def baseStart_3054576 : Nat := 118140960795 + 3054576 * 2 ^ 59
def prefixEnd_3054576 : Nat := 4983230072969 + 3 ^ 40 * 3054576 * 2
def baseEnd_3054576 : Nat := 1568465683688146191052267

theorem tailTrace_3054576 : CollatzResearch.WordTrace tailWord_3054576 prefixEnd_3054576 1568465683688146191052267 := by
  unfold tailWord_3054576
  simp only [CollatzResearch.WordTrace]
  refine ⟨55704769690900153446419791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74273026254533537928559721 55704769690900153446419791)
  ·
    refine ⟨83557154536350230169629687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55704769690900153446419791 83557154536350230169629687)
    ·
      refine ⟨125335731804525345254444531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83557154536350230169629687 125335731804525345254444531)
      ·
        refine ⟨188003597706788017881666797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125335731804525345254444531 188003597706788017881666797)
        ·
          refine ⟨70501349140045506705625049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188003597706788017881666797 70501349140045506705625049)
          ·
            refine ⟨52876011855034130029218787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70501349140045506705625049 52876011855034130029218787)
            ·
              refine ⟨79314017782551195043828181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52876011855034130029218787 79314017782551195043828181)
              ·
                refine ⟨1858922291778543633839723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79314017782551195043828181 1858922291778543633839723)
                ·
                  refine ⟨2788383437667815450759585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858922291778543633839723 2788383437667815450759585)
                  ·
                    refine ⟨2091287578250861588069689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788383437667815450759585 2091287578250861588069689)
                    ·
                      refine ⟨1568465683688146191052267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091287578250861588069689 1568465683688146191052267)
                      ·
                        rfl

theorem cell23_3054576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 2, 2].length) (baseStart_3054576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054576 prefixEnd_3054576 := by exact prefixLift 3054576
  have htrace : WordTrace (prefixWord ++ tailWord_3054576) baseStart_3054576 baseEnd_3054576 := by
    simpa [prefixWord, tailWord_3054576, baseEnd_3054576] using wordTrace_append hprefix tailTrace_3054576
  have hstable : (prefixWord ++ tailWord_3054576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054576).length < 2 ^ (prefixWord ++ tailWord_3054576).sum := by decide
  have hdescent : baseEnd_3054576 < baseStart_3054576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054592 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 8, 1, 3]
def baseStart_3054592 : Nat := 118140960795 + 3054592 * 2 ^ 59
def prefixEnd_3054592 : Nat := 4983230072969 + 3 ^ 40 * 3054592 * 2
def baseEnd_3054592 : Nat := 1568473899378618128452193

theorem tailTrace_3054592 : CollatzResearch.WordTrace tailWord_3054592 prefixEnd_3054592 1568473899378618128452193 := by
  unfold tailWord_3054592
  simp only [CollatzResearch.WordTrace]
  refine ⟨55705061474871170812711015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74273415299828227750281353 55705061474871170812711015)
  ·
    refine ⟨83557592212306756219066523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55705061474871170812711015 83557592212306756219066523)
    ·
      refine ⟨125336388318460134328599785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83557592212306756219066523 125336388318460134328599785)
      ·
        refine ⟨94002291238845100746449839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125336388318460134328599785 94002291238845100746449839)
        ·
          refine ⟨141003436858267651119674759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94002291238845100746449839 141003436858267651119674759)
          ·
            refine ⟨211505155287401476679512139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141003436858267651119674759 211505155287401476679512139)
            ·
              refine ⟨317257732931102215019268209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211505155287401476679512139 317257732931102215019268209)
              ·
                refine ⟨237943299698326661264451157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317257732931102215019268209 237943299698326661264451157)
                ·
                  refine ⟨2788398043339765561692787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 237943299698326661264451157 2788398043339765561692787)
                  ·
                    refine ⟨4182597065009648342539181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2788398043339765561692787 4182597065009648342539181)
                    ·
                      refine ⟨1568473899378618128452193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4182597065009648342539181 1568473899378618128452193)
                      ·
                        rfl

theorem cell23_3054592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_3054592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054592 prefixEnd_3054592 := by exact prefixLift 3054592
  have htrace : WordTrace (prefixWord ++ tailWord_3054592) baseStart_3054592 baseEnd_3054592 := by
    simpa [prefixWord, tailWord_3054592, baseEnd_3054592] using wordTrace_append hprefix tailTrace_3054592
  have hstable : (prefixWord ++ tailWord_3054592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054592).length < 2 ^ (prefixWord ++ tailWord_3054592).sum := by decide
  have hdescent : baseEnd_3054592 < baseStart_3054592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054593 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_3054593 : Nat := 118140960795 + 3054593 * 2 ^ 59
def prefixEnd_3054593 : Nat := 4983230072969 + 3 ^ 40 * 3054593 * 2
def baseEnd_3054593 : Nat := 1568474412859272624539689

theorem tailTrace_3054593 : CollatzResearch.WordTrace tailWord_3054593 prefixEnd_3054593 1568474412859272624539689 := by
  unfold tailWord_3054593
  simp only [CollatzResearch.WordTrace]
  refine ⟨111410159422738718796208433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74273439615159145864138955 111410159422738718796208433)
  ·
    refine ⟨83557619567054039097156325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111410159422738718796208433 83557619567054039097156325)
    ·
      refine ⟨15667053668822632330716811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83557619567054039097156325 15667053668822632330716811)
      ·
        refine ⟨23500580503233948496075217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15667053668822632330716811 23500580503233948496075217)
        ·
          refine ⟨17625435377425461372056413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23500580503233948496075217 17625435377425461372056413)
          ·
            refine ⟨6609538266534548014521155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17625435377425461372056413 6609538266534548014521155)
            ·
              refine ⟨9914307399801822021781733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6609538266534548014521155 9914307399801822021781733)
              ·
                refine ⟨1858932637462841629084075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9914307399801822021781733 1858932637462841629084075)
                ·
                  refine ⟨2788398956194262443626113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858932637462841629084075 2788398956194262443626113)
                  ·
                    refine ⟨2091299217145696832719585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788398956194262443626113 2091299217145696832719585)
                    ·
                      refine ⟨1568474412859272624539689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091299217145696832719585 1568474412859272624539689)
                      ·
                        rfl

theorem cell23_3054593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_3054593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054593 prefixEnd_3054593 := by exact prefixLift 3054593
  have htrace : WordTrace (prefixWord ++ tailWord_3054593) baseStart_3054593 baseEnd_3054593 := by
    simpa [prefixWord, tailWord_3054593, baseEnd_3054593] using wordTrace_append hprefix tailTrace_3054593
  have hstable : (prefixWord ++ tailWord_3054593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054593).length < 2 ^ (prefixWord ++ tailWord_3054593).sum := by decide
  have hdescent : baseEnd_3054593 < baseStart_3054593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054635 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_3054635 : Nat := 118140960795 + 3054635 * 2 ^ 59
def prefixEnd_3054635 : Nat := 4983230072969 + 3 ^ 40 * 3054635 * 2
def baseEnd_3054635 : Nat := 1568495979046761460214495

theorem tailTrace_3054635 : CollatzResearch.WordTrace tailWord_3054635 prefixEnd_3054635 1568495979046761460214495 := by
  unfold tailWord_3054635
  simp only [CollatzResearch.WordTrace]
  refine ⟨111411691288586559969237359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74274460859057706646158239 111411691288586559969237359)
  ·
    refine ⟨167117536932879839953856039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111411691288586559969237359 167117536932879839953856039)
    ·
      refine ⟨250676305399319759930784059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167117536932879839953856039 250676305399319759930784059)
      ·
        refine ⟨376014458098979639896176089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250676305399319759930784059 376014458098979639896176089)
        ·
          refine ⟨282010843574234729922132067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376014458098979639896176089 282010843574234729922132067)
          ·
            refine ⟨423016265361352094883198101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282010843574234729922132067 423016265361352094883198101)
            ·
              refine ⟨19828887438813379447649911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 423016265361352094883198101 19828887438813379447649911)
              ·
                refine ⟨29743331158220069171474867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19828887438813379447649911 29743331158220069171474867)
                ·
                  refine ⟨44614996737330103757212301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29743331158220069171474867 44614996737330103757212301)
                  ·
                    refine ⟨16730623776498788908954613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44614996737330103757212301 16730623776498788908954613)
                    ·
                      refine ⟨1568495979046761460214495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16730623776498788908954613 1568495979046761460214495)
                      ·
                        rfl

theorem cell23_3054635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_3054635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054635 prefixEnd_3054635 := by exact prefixLift 3054635
  have htrace : WordTrace (prefixWord ++ tailWord_3054635) baseStart_3054635 baseEnd_3054635 := by
    simpa [prefixWord, tailWord_3054635, baseEnd_3054635] using wordTrace_append hprefix tailTrace_3054635
  have hstable : (prefixWord ++ tailWord_3054635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054635).length < 2 ^ (prefixWord ++ tailWord_3054635).sum := by decide
  have hdescent : baseEnd_3054635 < baseStart_3054635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054666 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_3054666 : Nat := 118140960795 + 3054666 * 2 ^ 59
def prefixEnd_3054666 : Nat := 4983230072969 + 3 ^ 40 * 3054666 * 2
def baseEnd_3054666 : Nat := 1568511896947050838926853

theorem tailTrace_3054666 : CollatzResearch.WordTrace tailWord_3054666 prefixEnd_3054666 1568511896947050838926853 := by
  unfold tailWord_3054666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27853205487868563065903963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74275214634316168175743901 27853205487868563065903963)
  ·
    refine ⟨41779808231802844598855945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27853205487868563065903963 41779808231802844598855945)
    ·
      refine ⟨31334856173852133449141959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41779808231802844598855945 31334856173852133449141959)
      ·
        refine ⟨47002284260778200173712939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31334856173852133449141959 47002284260778200173712939)
        ·
          refine ⟨70503426391167300260569409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47002284260778200173712939 70503426391167300260569409)
          ·
            refine ⟨52877569793375475195427057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70503426391167300260569409 52877569793375475195427057)
            ·
              refine ⟨39658177345031606396570293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52877569793375475195427057 39658177345031606396570293)
              ·
                refine ⟨3717954126096713099678465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39658177345031606396570293 3717954126096713099678465)
                ·
                  refine ⟨2788465594572534824758849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3717954126096713099678465 2788465594572534824758849)
                  ·
                    refine ⟨2091349195929401118569137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788465594572534824758849 2091349195929401118569137)
                    ·
                      refine ⟨1568511896947050838926853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091349195929401118569137 1568511896947050838926853)
                      ·
                        rfl

theorem cell23_3054666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_3054666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054666 prefixEnd_3054666 := by exact prefixLift 3054666
  have htrace : WordTrace (prefixWord ++ tailWord_3054666) baseStart_3054666 baseEnd_3054666 := by
    simpa [prefixWord, tailWord_3054666, baseEnd_3054666] using wordTrace_append hprefix tailTrace_3054666
  have hstable : (prefixWord ++ tailWord_3054666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054666).length < 2 ^ (prefixWord ++ tailWord_3054666).sum := by decide
  have hdescent : baseEnd_3054666 < baseStart_3054666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054682 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_3054682 : Nat := 118140960795 + 3054682 * 2 ^ 59
def prefixEnd_3054682 : Nat := 4983230072969 + 3 ^ 40 * 3054682 * 2
def baseEnd_3054682 : Nat := 1568520112637522776326779

theorem tailTrace_3054682 : CollatzResearch.WordTrace tailWord_3054682 prefixEnd_3054682 1568520112637522776326779 := by
  unfold tailWord_3054682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27853351379854071749049575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74275603679610857997465533 27853351379854071749049575)
  ·
    refine ⟨41780027069781107623574363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27853351379854071749049575 41780027069781107623574363)
    ·
      refine ⟨62670040604671661435361545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41780027069781107623574363 62670040604671661435361545)
      ·
        refine ⟨47002530453503746076521159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62670040604671661435361545 47002530453503746076521159)
        ·
          refine ⟨70503795680255619114781739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47002530453503746076521159 70503795680255619114781739)
          ·
            refine ⟨105755693520383428672172609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70503795680255619114781739 105755693520383428672172609)
            ·
              refine ⟨79316770140287571504129457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105755693520383428672172609 79316770140287571504129457)
              ·
                refine ⟨59487577605215678628097093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79316770140287571504129457 59487577605215678628097093)
                ·
                  refine ⟨11153920800977939742768205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59487577605215678628097093 11153920800977939742768205)
                  ·
                    refine ⟨4182720300366727403538077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11153920800977939742768205 4182720300366727403538077)
                    ·
                      refine ⟨1568520112637522776326779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4182720300366727403538077 1568520112637522776326779)
                      ·
                        rfl

theorem cell23_3054682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_3054682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054682 prefixEnd_3054682 := by exact prefixLift 3054682
  have htrace : WordTrace (prefixWord ++ tailWord_3054682) baseStart_3054682 baseEnd_3054682 := by
    simpa [prefixWord, tailWord_3054682, baseEnd_3054682] using wordTrace_append hprefix tailTrace_3054682
  have hstable : (prefixWord ++ tailWord_3054682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054682).length < 2 ^ (prefixWord ++ tailWord_3054682).sum := by decide
  have hdescent : baseEnd_3054682 < baseStart_3054682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054686 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3054686 : Nat := 118140960795 + 3054686 * 2 ^ 59
def prefixEnd_3054686 : Nat := 4983230072969 + 3 ^ 40 * 3054686 * 2
def baseEnd_3054686 : Nat := 1568522166560140760676761

theorem tailTrace_3054686 : CollatzResearch.WordTrace tailWord_3054686 prefixEnd_3054686 1568522166560140760676761 := by
  unfold tailWord_3054686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13926693926425224459917989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74275700940934530452895941 13926693926425224459917989)
  ·
    refine ⟨2611255111204729586234623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13926693926425224459917989 2611255111204729586234623)
    ·
      refine ⟨3916882666807094379351935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611255111204729586234623 3916882666807094379351935)
      ·
        refine ⟨5875324000210641569027903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3916882666807094379351935 5875324000210641569027903)
        ·
          refine ⟨8812986000315962353541855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875324000210641569027903 8812986000315962353541855)
          ·
            refine ⟨13219479000473943530312783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8812986000315962353541855 13219479000473943530312783)
            ·
              refine ⟨19829218500710915295469175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13219479000473943530312783 19829218500710915295469175)
              ·
                refine ⟨29743827751066372943203763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19829218500710915295469175 29743827751066372943203763)
                ·
                  refine ⟨44615741626599559414805645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29743827751066372943203763 44615741626599559414805645)
                  ·
                    refine ⟨16730903109974834780552117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44615741626599559414805645 16730903109974834780552117)
                    ·
                      refine ⟨1568522166560140760676761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16730903109974834780552117 1568522166560140760676761)
                      ·
                        rfl

theorem cell23_3054686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3054686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054686 prefixEnd_3054686 := by exact prefixLift 3054686
  have htrace : WordTrace (prefixWord ++ tailWord_3054686) baseStart_3054686 baseEnd_3054686 := by
    simpa [prefixWord, tailWord_3054686, baseEnd_3054686] using wordTrace_append hprefix tailTrace_3054686
  have hstable : (prefixWord ++ tailWord_3054686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054686).length < 2 ^ (prefixWord ++ tailWord_3054686).sum := by decide
  have hdescent : baseEnd_3054686 < baseStart_3054686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054689 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 5]
def baseStart_3054689 : Nat := 118140960795 + 3054689 * 2 ^ 59
def prefixEnd_3054689 : Nat := 4983230072969 + 3 ^ 40 * 3054689 * 2
def baseEnd_3054689 : Nat := 174280411889122694326583

theorem tailTrace_3054689 : CollatzResearch.WordTrace tailWord_3054689 prefixEnd_3054689 174280411889122694326583 := by
  unfold tailWord_3054689
  simp only [CollatzResearch.WordTrace]
  refine ⟨111413660830390927191703121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74275773886927284794468747 111413660830390927191703121)
  ·
    refine ⟨83560245622793195393777341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111413660830390927191703121 83560245622793195393777341)
    ·
      refine ⟨31335092108547448272666503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83560245622793195393777341 31335092108547448272666503)
      ·
        refine ⟨47002638162821172408999755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31335092108547448272666503 47002638162821172408999755)
        ·
          refine ⟨70503957244231758613499633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47002638162821172408999755 70503957244231758613499633)
          ·
            refine ⟨52877967933173818960124725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70503957244231758613499633 52877967933173818960124725)
            ·
              refine ⟨4957309493735045527511693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52877967933173818960124725 4957309493735045527511693)
              ·
                refine ⟨1858991060150642072816885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4957309493735045527511693 1858991060150642072816885)
                ·
                  refine ⟨174280411889122694326583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858991060150642072816885 174280411889122694326583)
                  ·
                    rfl

theorem cell23_3054689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 5].length) (baseStart_3054689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054689 prefixEnd_3054689 := by exact prefixLift 3054689
  have htrace : WordTrace (prefixWord ++ tailWord_3054689) baseStart_3054689 baseEnd_3054689 := by
    simpa [prefixWord, tailWord_3054689, baseEnd_3054689] using wordTrace_append hprefix tailTrace_3054689
  have hstable : (prefixWord ++ tailWord_3054689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054689).length < 2 ^ (prefixWord ++ tailWord_3054689).sum := by decide
  have hdescent : baseEnd_3054689 < baseStart_3054689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054706 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3054706 : Nat := 118140960795 + 3054706 * 2 ^ 59
def prefixEnd_3054706 : Nat := 4983230072969 + 3 ^ 40 * 3054706 * 2
def baseEnd_3054706 : Nat := 174281381797025631380741

theorem tailTrace_3054706 : CollatzResearch.WordTrace tailWord_3054706 prefixEnd_3054706 174281381797025631380741 := by
  unfold tailWord_3054706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27853570217832334773767993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74276187247552892730047981 27853570217832334773767993)
  ·
    refine ⟨20890177663374251080325995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27853570217832334773767993 20890177663374251080325995)
    ·
      refine ⟨31335266495061376620488993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20890177663374251080325995 31335266495061376620488993)
      ·
        refine ⟨23501449871296032465366745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31335266495061376620488993 23501449871296032465366745)
        ·
          refine ⟨17626087403472024349025059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23501449871296032465366745 17626087403472024349025059)
          ·
            refine ⟨26439131105208036523537589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17626087403472024349025059 26439131105208036523537589)
            ·
              refine ⟨2478668541113253424081649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26439131105208036523537589 2478668541113253424081649)
              ·
                refine ⟨1859001405834940068061237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478668541113253424081649 1859001405834940068061237)
                ·
                  refine ⟨174281381797025631380741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859001405834940068061237 174281381797025631380741)
                  ·
                    rfl

theorem cell23_3054706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3054706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054706 prefixEnd_3054706 := by exact prefixLift 3054706
  have htrace : WordTrace (prefixWord ++ tailWord_3054706) baseStart_3054706 baseEnd_3054706 := by
    simpa [prefixWord, tailWord_3054706, baseEnd_3054706] using wordTrace_append hprefix tailTrace_3054706
  have hstable : (prefixWord ++ tailWord_3054706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054706).length < 2 ^ (prefixWord ++ tailWord_3054706).sum := by decide
  have hdescent : baseEnd_3054706 < baseStart_3054706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054752 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3054752 : Nat := 118140960795 + 3054752 * 2 ^ 59
def prefixEnd_3054752 : Nat := 4983230072969 + 3 ^ 40 * 3054752 * 2
def baseEnd_3054752 : Nat := 1568556056283337502451457

theorem tailTrace_3054752 : CollatzResearch.WordTrace tailWord_3054752 prefixEnd_3054752 1568556056283337502451457 := by
  unfold tailWord_3054752
  simp only [CollatzResearch.WordTrace]
  refine ⟨55707979314581344475623255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74277305752775125967497673 55707979314581344475623255)
  ·
    refine ⟨83561968971872016713434883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55707979314581344475623255 83561968971872016713434883)
    ·
      refine ⟨125342953457808025070152325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83561968971872016713434883 125342953457808025070152325)
      ·
        refine ⟨23501803773339004700653561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125342953457808025070152325 23501803773339004700653561)
        ·
          refine ⟨17626352830004253525490171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23501803773339004700653561 17626352830004253525490171)
          ·
            refine ⟨26439529245006380288235257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17626352830004253525490171 26439529245006380288235257)
            ·
              refine ⟨19829646933754785216176443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26439529245006380288235257 19829646933754785216176443)
              ·
                refine ⟨29744470400632177824264665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19829646933754785216176443 29744470400632177824264665)
                ·
                  refine ⟨22308352800474133368198499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29744470400632177824264665 22308352800474133368198499)
                  ·
                    refine ⟨33462529200711200052297749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22308352800474133368198499 33462529200711200052297749)
                    ·
                      refine ⟨1568556056283337502451457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33462529200711200052297749 1568556056283337502451457)
                      ·
                        rfl

theorem cell23_3054752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3054752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054752 prefixEnd_3054752 := by exact prefixLift 3054752
  have htrace : WordTrace (prefixWord ++ tailWord_3054752) baseStart_3054752 baseEnd_3054752 := by
    simpa [prefixWord, tailWord_3054752, baseEnd_3054752] using wordTrace_append hprefix tailTrace_3054752
  have hstable : (prefixWord ++ tailWord_3054752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054752).length < 2 ^ (prefixWord ++ tailWord_3054752).sum := by decide
  have hdescent : baseEnd_3054752 < baseStart_3054752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054790 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3054790 : Nat := 118140960795 + 3054790 * 2 ^ 59
def prefixEnd_3054790 : Nat := 4983230072969 + 3 ^ 40 * 3054790 * 2
def baseEnd_3054790 : Nat := 1568575568548208353776283

theorem tailTrace_3054790 : CollatzResearch.WordTrace tailWord_3054790 prefixEnd_3054790 1568575568548208353776283 := by
  unfold tailWord_3054790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481792018844531920035307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74278229735350014294086549 3481792018844531920035307)
  ·
    refine ⟨5222688028266797880052961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481792018844531920035307 5222688028266797880052961)
    ·
      refine ⟨3917016021200098410039721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5222688028266797880052961 3917016021200098410039721)
      ·
        refine ⟨2937762015900073807529791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917016021200098410039721 2937762015900073807529791)
        ·
          refine ⟨4406643023850110711294687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937762015900073807529791 4406643023850110711294687)
          ·
            refine ⟨6609964535775166066942031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406643023850110711294687 6609964535775166066942031)
            ·
              refine ⟨9914946803662749100413047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6609964535775166066942031 9914946803662749100413047)
              ·
                refine ⟨14872420205494123650619571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9914946803662749100413047 14872420205494123650619571)
                ·
                  refine ⟨22308630308241185475929357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14872420205494123650619571 22308630308241185475929357)
                  ·
                    refine ⟨8365736365590444553473509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22308630308241185475929357 8365736365590444553473509)
                    ·
                      refine ⟨1568575568548208353776283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8365736365590444553473509 1568575568548208353776283)
                      ·
                        rfl

theorem cell23_3054790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3054790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054790 prefixEnd_3054790 := by exact prefixLift 3054790
  have htrace : WordTrace (prefixWord ++ tailWord_3054790) baseStart_3054790 baseEnd_3054790 := by
    simpa [prefixWord, tailWord_3054790, baseEnd_3054790] using wordTrace_append hprefix tailTrace_3054790
  have hstable : (prefixWord ++ tailWord_3054790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054790).length < 2 ^ (prefixWord ++ tailWord_3054790).sum := by decide
  have hdescent : baseEnd_3054790 < baseStart_3054790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054813 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 6]
def baseStart_3054813 : Nat := 118140960795 + 3054813 * 2 ^ 59
def prefixEnd_3054813 : Nat := 4983230072969 + 3 ^ 40 * 3054813 * 2
def baseEnd_3054813 : Nat := 174287486511473529309853

theorem tailTrace_3054813 : CollatzResearch.WordTrace tailWord_3054813 prefixEnd_3054813 174287486511473529309853 := by
  unfold tailWord_3054813
  simp only [CollatzResearch.WordTrace]
  refine ⟨111418183481941696369217093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74278788987961130912811395 111418183481941696369217093)
  ·
    refine ⟨20890909402864068069228205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111418183481941696369217093 20890909402864068069228205)
    ·
      refine ⟨7834091026074025525960577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20890909402864068069228205 7834091026074025525960577)
      ·
        refine ⟨5875568269555519144470433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7834091026074025525960577 5875568269555519144470433)
        ·
          refine ⟨4406676202166639358352825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5875568269555519144470433 4406676202166639358352825)
          ·
            refine ⟨3305007151624979518764619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4406676202166639358352825 3305007151624979518764619)
            ·
              refine ⟨4957510727437469278146929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305007151624979518764619 4957510727437469278146929)
              ·
                refine ⟨3718133045578101958610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957510727437469278146929 3718133045578101958610197)
                ·
                  refine ⟨174287486511473529309853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3718133045578101958610197 174287486511473529309853)
                  ·
                    rfl

theorem cell23_3054813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_3054813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054813 prefixEnd_3054813 := by exact prefixLift 3054813
  have htrace : WordTrace (prefixWord ++ tailWord_3054813) baseStart_3054813 baseEnd_3054813 := by
    simpa [prefixWord, tailWord_3054813, baseEnd_3054813] using wordTrace_append hprefix tailTrace_3054813
  have hstable : (prefixWord ++ tailWord_3054813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054813).length < 2 ^ (prefixWord ++ tailWord_3054813).sum := by decide
  have hdescent : baseEnd_3054813 < baseStart_3054813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054890 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3054890 : Nat := 118140960795 + 3054890 * 2 ^ 59
def prefixEnd_3054890 : Nat := 4983230072969 + 3 ^ 40 * 3054890 * 2
def baseEnd_3054890 : Nat := 522875638871219320841941

theorem tailTrace_3054890 : CollatzResearch.WordTrace tailWord_3054890 prefixEnd_3054890 522875638871219320841941 := by
  unfold tailWord_3054890
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855247975665684629942531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74280661268441825679846749 27855247975665684629942531)
  ·
    refine ⟨41782871963498526944913797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27855247975665684629942531 41782871963498526944913797)
    ·
      refine ⟨7834288493155973802171337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41782871963498526944913797 7834288493155973802171337)
      ·
        refine ⟨5875716369866980351628503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7834288493155973802171337 5875716369866980351628503)
        ·
          refine ⟨8813574554800470527442755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875716369866980351628503 8813574554800470527442755)
          ·
            refine ⟨13220361832200705791164133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8813574554800470527442755 13220361832200705791164133)
            ·
              refine ⟨2478817843537632335843275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13220361832200705791164133 2478817843537632335843275)
              ·
                refine ⟨3718226765306448503764913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478817843537632335843275 3718226765306448503764913)
                ·
                  refine ⟨2788670073979836377823685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3718226765306448503764913 2788670073979836377823685)
                  ·
                    refine ⟨522875638871219320841941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2788670073979836377823685 522875638871219320841941)
                    ·
                      rfl

theorem cell23_3054890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3054890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054890 prefixEnd_3054890 := by exact prefixLift 3054890
  have htrace : WordTrace (prefixWord ++ tailWord_3054890) baseStart_3054890 baseEnd_3054890 := by
    simpa [prefixWord, tailWord_3054890, baseEnd_3054890] using wordTrace_append hprefix tailTrace_3054890
  have hstable : (prefixWord ++ tailWord_3054890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054890).length < 2 ^ (prefixWord ++ tailWord_3054890).sum := by decide
  have hdescent : baseEnd_3054890 < baseStart_3054890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054913 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3054913 : Nat := 118140960795 + 3054913 * 2 ^ 59
def prefixEnd_3054913 : Nat := 4983230072969 + 3 ^ 40 * 3054913 * 2
def baseEnd_3054913 : Nat := 1568638726668711372538217

theorem tailTrace_3054913 : CollatzResearch.WordTrace tailWord_3054913 prefixEnd_3054913 1568638726668711372538217 := by
  unfold tailWord_3054913
  simp only [CollatzResearch.WordTrace]
  refine ⟨111421830781579413447857393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74281220521052942298571595 111421830781579413447857393)
  ·
    refine ⟨83566373086184560085893045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111421830781579413447857393 83566373086184560085893045)
    ·
      refine ⟨7834347476829802508052473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83566373086184560085893045 7834347476829802508052473)
      ·
        refine ⟨5875760607622351881039355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7834347476829802508052473 5875760607622351881039355)
        ·
          refine ⟨8813640911433527821559033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875760607622351881039355 8813640911433527821559033)
          ·
            refine ⟨6610230683575145866169275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8813640911433527821559033 6610230683575145866169275)
            ·
              refine ⟨9915346025362718799253913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610230683575145866169275 9915346025362718799253913)
              ·
                refine ⟨7436509519022039099440435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9915346025362718799253913 7436509519022039099440435)
                ·
                  refine ⟨11154764278533058649160653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7436509519022039099440435 11154764278533058649160653)
                  ·
                    refine ⟨4183036604449896993435245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11154764278533058649160653 4183036604449896993435245)
                    ·
                      refine ⟨1568638726668711372538217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4183036604449896993435245 1568638726668711372538217)
                      ·
                        rfl

theorem cell23_3054913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3054913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054913 prefixEnd_3054913 := by exact prefixLift 3054913
  have htrace : WordTrace (prefixWord ++ tailWord_3054913) baseStart_3054913 baseEnd_3054913 := by
    simpa [prefixWord, tailWord_3054913, baseEnd_3054913] using wordTrace_append hprefix tailTrace_3054913
  have hstable : (prefixWord ++ tailWord_3054913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054913).length < 2 ^ (prefixWord ++ tailWord_3054913).sum := by decide
  have hdescent : baseEnd_3054913 < baseStart_3054913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054929 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_3054929 : Nat := 118140960795 + 3054929 * 2 ^ 59
def prefixEnd_3054929 : Nat := 4983230072969 + 3 ^ 40 * 3054929 * 2
def baseEnd_3054929 : Nat := 522882314119727769979381

theorem tailTrace_3054929 : CollatzResearch.WordTrace tailWord_3054929 prefixEnd_3054929 522882314119727769979381 := by
  unfold tailWord_3054929
  simp only [CollatzResearch.WordTrace]
  refine ⟨111422414349521448180439841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74281609566347632120293227 111422414349521448180439841)
  ·
    refine ⟨83566810762141086135329881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111422414349521448180439841 83566810762141086135329881)
    ·
      refine ⟨62675108071605814601497411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83566810762141086135329881 62675108071605814601497411)
      ·
        refine ⟨94012662107408721902246117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62675108071605814601497411 94012662107408721902246117)
        ·
          refine ⟨17627374145139135356671147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94012662107408721902246117 17627374145139135356671147)
          ·
            refine ⟨26441061217708703035006721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17627374145139135356671147 26441061217708703035006721)
            ·
              refine ⟨19830795913281527276255041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26441061217708703035006721 19830795913281527276255041)
              ·
                refine ⟨14873096934961145457191281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19830795913281527276255041 14873096934961145457191281)
                ·
                  refine ⟨11154822701220859092893461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14873096934961145457191281 11154822701220859092893461)
                  ·
                    refine ⟨522882314119727769979381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11154822701220859092893461 522882314119727769979381)
                    ·
                      rfl

theorem cell23_3054929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_3054929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054929 prefixEnd_3054929 := by exact prefixLift 3054929
  have htrace : WordTrace (prefixWord ++ tailWord_3054929) baseStart_3054929 baseEnd_3054929 := by
    simpa [prefixWord, tailWord_3054929, baseEnd_3054929] using wordTrace_append hprefix tailTrace_3054929
  have hstable : (prefixWord ++ tailWord_3054929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054929).length < 2 ^ (prefixWord ++ tailWord_3054929).sum := by decide
  have hdescent : baseEnd_3054929 < baseStart_3054929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054936 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 3, 4, 2]
def baseStart_3054936 : Nat := 118140960795 + 3054936 * 2 ^ 59
def prefixEnd_3054936 : Nat := 4983230072969 + 3 ^ 40 * 3054936 * 2
def baseEnd_3054936 : Nat := 1568650536723764782550611

theorem tailTrace_3054936 : CollatzResearch.WordTrace tailWord_3054936 prefixEnd_3054936 1568650536723764782550611 := by
  unfold tailWord_3054936
  simp only [CollatzResearch.WordTrace]
  refine ⟨55711334830248044187972331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74281779773664058917296441 55711334830248044187972331)
  ·
    refine ⟨83567002245372066281958497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55711334830248044187972331 83567002245372066281958497)
    ·
      refine ⟨62675251684029049711468873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83567002245372066281958497 62675251684029049711468873)
      ·
        refine ⟨47006438763021787283601655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62675251684029049711468873 47006438763021787283601655)
        ·
          refine ⟨70509658144532680925402483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47006438763021787283601655 70509658144532680925402483)
          ·
            refine ⟨105764487216799021388103725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70509658144532680925402483 105764487216799021388103725)
            ·
              refine ⟨39661682706299633020538897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105764487216799021388103725 39661682706299633020538897)
              ·
                refine ⟨29746262029724724765404173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39661682706299633020538897 29746262029724724765404173)
                ·
                  refine ⟨11154848261146771787026565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29746262029724724765404173 11154848261146771787026565)
                  ·
                    refine ⟨2091534048965019710067481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11154848261146771787026565 2091534048965019710067481)
                    ·
                      refine ⟨1568650536723764782550611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091534048965019710067481 1568650536723764782550611)
                      ·
                        rfl

theorem cell23_3054936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_3054936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054936 prefixEnd_3054936 := by exact prefixLift 3054936
  have htrace : WordTrace (prefixWord ++ tailWord_3054936) baseStart_3054936 baseEnd_3054936 := by
    simpa [prefixWord, tailWord_3054936, baseEnd_3054936] using wordTrace_append hprefix tailTrace_3054936
  have hstable : (prefixWord ++ tailWord_3054936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054936).length < 2 ^ (prefixWord ++ tailWord_3054936).sum := by decide
  have hdescent : baseEnd_3054936 < baseStart_3054936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054946 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3054946 : Nat := 118140960795 + 3054946 * 2 ^ 59
def prefixEnd_3054946 : Nat := 4983230072969 + 3 ^ 40 * 3054946 * 2
def baseEnd_3054946 : Nat := 522885223843436581141855

theorem tailTrace_3054946 : CollatzResearch.WordTrace tailWord_3054946 prefixEnd_3054946 522885223843436581141855 := by
  unfold tailWord_3054946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855758597614965020952173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74282022926973240055872461 27855758597614965020952173)
  ·
    refine ⟨10445909474105611882857065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27855758597614965020952173 10445909474105611882857065)
    ·
      refine ⟨7834432105579208912142799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10445909474105611882857065 7834432105579208912142799)
      ·
        refine ⟨11751648158368813368214199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834432105579208912142799 11751648158368813368214199)
        ·
          refine ⟨17627472237553220052321299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11751648158368813368214199 17627472237553220052321299)
          ·
            refine ⟨26441208356329830078481949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17627472237553220052321299 26441208356329830078481949)
            ·
              refine ⟨9915453133623686279430731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26441208356329830078481949 9915453133623686279430731)
              ·
                refine ⟨14873179700435529419146097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9915453133623686279430731 14873179700435529419146097)
                ·
                  refine ⟨11154884775326647064359573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14873179700435529419146097 11154884775326647064359573)
                  ·
                    refine ⟨522885223843436581141855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11154884775326647064359573 522885223843436581141855)
                    ·
                      rfl

theorem cell23_3054946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3054946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054946 prefixEnd_3054946 := by exact prefixLift 3054946
  have htrace : WordTrace (prefixWord ++ tailWord_3054946) baseStart_3054946 baseEnd_3054946 := by
    simpa [prefixWord, tailWord_3054946, baseEnd_3054946] using wordTrace_append hprefix tailTrace_3054946
  have hstable : (prefixWord ++ tailWord_3054946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054946).length < 2 ^ (prefixWord ++ tailWord_3054946).sum := by decide
  have hdescent : baseEnd_3054946 < baseStart_3054946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054959 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 7]
def baseStart_3054959 : Nat := 118140960795 + 3054959 * 2 ^ 59
def prefixEnd_3054959 : Nat := 4983230072969 + 3 ^ 40 * 3054959 * 2
def baseEnd_3054959 : Nat := 174295816308757576951445

theorem tailTrace_3054959 : CollatzResearch.WordTrace tailWord_3054959 prefixEnd_3054959 174295816308757576951445 := by
  unfold tailWord_3054959
  simp only [CollatzResearch.WordTrace]
  refine ⟨111423508539412763304031931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74282339026275175536021287 111423508539412763304031931)
  ·
    refine ⟨167135262809119144956047897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111423508539412763304031931 167135262809119144956047897)
    ·
      refine ⟨125351447106839358717035923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167135262809119144956047897 125351447106839358717035923)
      ·
        refine ⟨188027170660259038075553885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125351447106839358717035923 188027170660259038075553885)
        ·
          refine ⟨70510188997597139278332707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188027170660259038075553885 70510188997597139278332707)
          ·
            refine ⟨105765283496395708917499061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70510188997597139278332707 105765283496395708917499061)
            ·
              refine ⟨9915495327787097711015537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105765283496395708917499061 9915495327787097711015537)
              ·
                refine ⟨7436621495840323283261653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9915495327787097711015537 7436621495840323283261653)
                ·
                  refine ⟨174295816308757576951445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7436621495840323283261653 174295816308757576951445)
                  ·
                    rfl

theorem cell23_3054959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 7].length) (baseStart_3054959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054959 prefixEnd_3054959 := by exact prefixLift 3054959
  have htrace : WordTrace (prefixWord ++ tailWord_3054959) baseStart_3054959 baseEnd_3054959 := by
    simpa [prefixWord, tailWord_3054959, baseEnd_3054959] using wordTrace_append hprefix tailTrace_3054959
  have hstable : (prefixWord ++ tailWord_3054959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054959).length < 2 ^ (prefixWord ++ tailWord_3054959).sum := by decide
  have hdescent : baseEnd_3054959 < baseStart_3054959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054974 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3054974 : Nat := 118140960795 + 3054974 * 2 ^ 59
def prefixEnd_3054974 : Nat := 4983230072969 + 3 ^ 40 * 3054974 * 2
def baseEnd_3054974 : Nat := 1568670048988635633875437

theorem tailTrace_3054974 : CollatzResearch.WordTrace tailWord_3054974 prefixEnd_3054974 1568670048988635633875437 := by
  unfold tailWord_3054974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928006954294802608228497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74282703756238947243885317 13928006954294802608228497)
  ·
    refine ⟨10446005215721101956171373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13928006954294802608228497 10446005215721101956171373)
    ·
      refine ⟨3917251955895413233564265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10446005215721101956171373 3917251955895413233564265)
      ·
        refine ⟨2937938966921559925173199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917251955895413233564265 2937938966921559925173199)
        ·
          refine ⟨4406908450382339887759799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937938966921559925173199 4406908450382339887759799)
          ·
            refine ⟨6610362675573509831639699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406908450382339887759799 6610362675573509831639699)
            ·
              refine ⟨9915544013360264747459549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610362675573509831639699 9915544013360264747459549)
              ·
                refine ⟨3718329005010099280297331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9915544013360264747459549 3718329005010099280297331)
                ·
                  refine ⟨5577493507515148920445997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718329005010099280297331 5577493507515148920445997)
                  ·
                    refine ⟨2091560065318180845167249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5577493507515148920445997 2091560065318180845167249)
                    ·
                      refine ⟨1568670048988635633875437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091560065318180845167249 1568670048988635633875437)
                      ·
                        rfl

theorem cell23_3054974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3054974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054974 prefixEnd_3054974 := by exact prefixLift 3054974
  have htrace : WordTrace (prefixWord ++ tailWord_3054974) baseStart_3054974 baseEnd_3054974 := by
    simpa [prefixWord, tailWord_3054974, baseEnd_3054974] using wordTrace_append hprefix tailTrace_3054974
  have hstable : (prefixWord ++ tailWord_3054974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054974).length < 2 ^ (prefixWord ++ tailWord_3054974).sum := by decide
  have hdescent : baseEnd_3054974 < baseStart_3054974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3054999 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3054999 : Nat := 118140960795 + 3054999 * 2 ^ 59
def prefixEnd_3054999 : Nat := 4983230072969 + 3 ^ 40 * 3054999 * 2
def baseEnd_3054999 : Nat := 1568682886004998036062821

theorem tailTrace_3054999 : CollatzResearch.WordTrace tailWord_3054999 prefixEnd_3054999 1568682886004998036062821 := by
  unfold tailWord_3054999
  simp only [CollatzResearch.WordTrace]
  refine ⟨111424967459267850135488051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74283311639511900090325367 111424967459267850135488051)
  ·
    refine ⟨167137451188901775203232077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111424967459267850135488051 167137451188901775203232077)
    ·
      refine ⟨62676544195838165701212029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167137451188901775203232077 62676544195838165701212029)
      ·
        refine ⟨23503704073439312137954511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62676544195838165701212029 23503704073439312137954511)
        ·
          refine ⟨35255556110158968206931767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23503704073439312137954511 35255556110158968206931767)
          ·
            refine ⟨52883334165238452310397651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35255556110158968206931767 52883334165238452310397651)
            ·
              refine ⟨79325001247857678465596477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52883334165238452310397651 79325001247857678465596477)
              ·
                refine ⟨29746875467946629424598679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79325001247857678465596477 29746875467946629424598679)
                ·
                  refine ⟨44620313201919944136898019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29746875467946629424598679 44620313201919944136898019)
                  ·
                    refine ⟨66930469802879916205347029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44620313201919944136898019 66930469802879916205347029)
                    ·
                      refine ⟨1568682886004998036062821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66930469802879916205347029 1568682886004998036062821)
                      ·
                        rfl

theorem cell23_3054999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3054999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3054999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3054999 prefixEnd_3054999 := by exact prefixLift 3054999
  have htrace : WordTrace (prefixWord ++ tailWord_3054999) baseStart_3054999 baseEnd_3054999 := by
    simpa [prefixWord, tailWord_3054999, baseEnd_3054999] using wordTrace_append hprefix tailTrace_3054999
  have hstable : (prefixWord ++ tailWord_3054999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3054999).length < 2 ^ (prefixWord ++ tailWord_3054999).sum := by decide
  have hdescent : baseEnd_3054999 < baseStart_3054999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3054999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055004 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3055004 : Nat := 118140960795 + 3055004 * 2 ^ 59
def prefixEnd_3055004 : Nat := 4983230072969 + 3 ^ 40 * 3055004 * 2
def baseEnd_3055004 : Nat := 1568685453408270516500299

theorem tailTrace_3055004 : CollatzResearch.WordTrace tailWord_3055004 prefixEnd_3055004 1568685453408270516500299 := by
  unfold tailWord_3055004
  simp only [CollatzResearch.WordTrace]
  refine ⟨55712574912124867994710033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74283433216166490659613377 55712574912124867994710033)
  ·
    refine ⟨41784431184093650996032525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55712574912124867994710033 41784431184093650996032525)
    ·
      refine ⟨15669161694035119123512197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41784431184093650996032525 15669161694035119123512197)
      ·
        refine ⟨2937967817631584835658537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15669161694035119123512197 2937967817631584835658537)
        ·
          refine ⟨2203475863223688626743903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2937967817631584835658537 2203475863223688626743903)
          ·
            refine ⟨3305213794835532940115855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203475863223688626743903 3305213794835532940115855)
            ·
              refine ⟨4957820692253299410173783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305213794835532940115855 4957820692253299410173783)
              ·
                refine ⟨7436731038379949115260675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957820692253299410173783 7436731038379949115260675)
                ·
                  refine ⟨11155096557569923672891013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7436731038379949115260675 11155096557569923672891013)
                  ·
                    refine ⟨2091580604544360688667065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11155096557569923672891013 2091580604544360688667065)
                    ·
                      refine ⟨1568685453408270516500299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091580604544360688667065 1568685453408270516500299)
                      ·
                        rfl

theorem cell23_3055004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3055004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055004 prefixEnd_3055004 := by exact prefixLift 3055004
  have htrace : WordTrace (prefixWord ++ tailWord_3055004) baseStart_3055004 baseEnd_3055004 := by
    simpa [prefixWord, tailWord_3055004, baseEnd_3055004] using wordTrace_append hprefix tailTrace_3055004
  have hstable : (prefixWord ++ tailWord_3055004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055004).length < 2 ^ (prefixWord ++ tailWord_3055004).sum := by decide
  have hdescent : baseEnd_3055004 < baseStart_3055004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055039 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3055039 : Nat := 118140960795 + 3055039 * 2 ^ 59
def prefixEnd_3055039 : Nat := 4983230072969 + 3 ^ 40 * 3055039 * 2
def baseEnd_3055039 : Nat := 1568703425231177879562637

theorem tailTrace_3055039 : CollatzResearch.WordTrace tailWord_3055039 prefixEnd_3055039 1568703425231177879562637 := by
  unfold tailWord_3055039
  simp only [CollatzResearch.WordTrace]
  refine ⟨111426426379122936966944171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74284284252748624644629447 111426426379122936966944171)
  ·
    refine ⟨167139639568684405450416257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111426426379122936966944171 167139639568684405450416257)
    ·
      refine ⟨125354729676513304087812193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167139639568684405450416257 125354729676513304087812193)
      ·
        refine ⟨94016047257384978065859145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125354729676513304087812193 94016047257384978065859145)
        ·
          refine ⟨70512035443038733549394359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94016047257384978065859145 70512035443038733549394359)
          ·
            refine ⟨105768053164558100324091539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70512035443038733549394359 105768053164558100324091539)
            ·
              refine ⟨158652079746837150486137309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105768053164558100324091539 158652079746837150486137309)
              ·
                refine ⟨59494529905063931432301491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158652079746837150486137309 59494529905063931432301491)
                ·
                  refine ⟨89241794857595897148452237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59494529905063931432301491 89241794857595897148452237)
                  ·
                    refine ⟨33465673071598461430669589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89241794857595897148452237 33465673071598461430669589)
                    ·
                      refine ⟨1568703425231177879562637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33465673071598461430669589 1568703425231177879562637)
                      ·
                        rfl

theorem cell23_3055039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3055039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055039 prefixEnd_3055039 := by exact prefixLift 3055039
  have htrace : WordTrace (prefixWord ++ tailWord_3055039) baseStart_3055039 baseEnd_3055039 := by
    simpa [prefixWord, tailWord_3055039, baseEnd_3055039] using wordTrace_append hprefix tailTrace_3055039
  have hstable : (prefixWord ++ tailWord_3055039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055039).length < 2 ^ (prefixWord ++ tailWord_3055039).sum := by decide
  have hdescent : baseEnd_3055039 < baseStart_3055039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055076 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_3055076 : Nat := 118140960795 + 3055076 * 2 ^ 59
def prefixEnd_3055076 : Nat := 4983230072969 + 3 ^ 40 * 3055076 * 2
def baseEnd_3055076 : Nat := 1568722424015394234799967

theorem tailTrace_3055076 : CollatzResearch.WordTrace tailWord_3055076 prefixEnd_3055076 1568722424015394234799967 := by
  unfold tailWord_3055076
  simp only [CollatzResearch.WordTrace]
  refine ⟨55713887939994446143020541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74285183919992594857360721 55713887939994446143020541)
  ·
    refine ⟨20892707977497917303632703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55713887939994446143020541 20892707977497917303632703)
    ·
      refine ⟨31339061966246875955449055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20892707977497917303632703 31339061966246875955449055)
      ·
        refine ⟨47008592949370313933173583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31339061966246875955449055 47008592949370313933173583)
        ·
          refine ⟨70512889424055470899760375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47008592949370313933173583 70512889424055470899760375)
          ·
            refine ⟨105769334136083206349640563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70512889424055470899760375 105769334136083206349640563)
            ·
              refine ⟨158654001204124809524460845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105769334136083206349640563 158654001204124809524460845)
              ·
                refine ⟨59495250451546803571672817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158654001204124809524460845 59495250451546803571672817)
                ·
                  refine ⟨44621437838660102678754613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59495250451546803571672817 44621437838660102678754613)
                  ·
                    refine ⟨4183259797374384626133245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44621437838660102678754613 4183259797374384626133245)
                    ·
                      refine ⟨1568722424015394234799967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4183259797374384626133245 1568722424015394234799967)
                      ·
                        rfl

theorem cell23_3055076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_3055076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055076 prefixEnd_3055076 := by exact prefixLift 3055076
  have htrace : WordTrace (prefixWord ++ tailWord_3055076) baseStart_3055076 baseEnd_3055076 := by
    simpa [prefixWord, tailWord_3055076, baseEnd_3055076] using wordTrace_append hprefix tailTrace_3055076
  have hstable : (prefixWord ++ tailWord_3055076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055076).length < 2 ^ (prefixWord ++ tailWord_3055076).sum := by decide
  have hdescent : baseEnd_3055076 < baseStart_3055076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055103 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 4, 3, 2]
def baseStart_3055103 : Nat := 118140960795 + 3055103 * 2 ^ 59
def prefixEnd_3055103 : Nat := 4983230072969 + 3 ^ 40 * 3055103 * 2
def baseEnd_3055103 : Nat := 1568736287993065629162343

theorem tailTrace_3055103 : CollatzResearch.WordTrace tailWord_3055103 prefixEnd_3055103 1568736287993065629162343 := by
  unfold tailWord_3055103
  simp only [CollatzResearch.WordTrace]
  refine ⟨111428760650891075897273963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74285840433927383931515975 111428760650891075897273963)
  ·
    refine ⟨167143140976336613845910945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111428760650891075897273963 167143140976336613845910945)
    ·
      refine ⟨125357355732252460384433209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167143140976336613845910945 125357355732252460384433209)
      ·
        refine ⟨94018016799189345288324907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125357355732252460384433209 94018016799189345288324907)
        ·
          refine ⟨141027025198784017932487361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94018016799189345288324907 141027025198784017932487361)
          ·
            refine ⟨105770268899088013449365521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141027025198784017932487361 105770268899088013449365521)
            ·
              refine ⟨79327701674316010087024141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105770268899088013449365521 79327701674316010087024141)
              ·
                refine ⟨29747888127868503782634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79327701674316010087024141 29747888127868503782634053)
                ·
                  refine ⟨5577729023975344459243885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29747888127868503782634053 5577729023975344459243885)
                  ·
                    refine ⟨2091648383990754172216457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5577729023975344459243885 2091648383990754172216457)
                    ·
                      refine ⟨1568736287993065629162343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091648383990754172216457 1568736287993065629162343)
                      ·
                        rfl

theorem cell23_3055103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_3055103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055103 prefixEnd_3055103 := by exact prefixLift 3055103
  have htrace : WordTrace (prefixWord ++ tailWord_3055103) baseStart_3055103 baseEnd_3055103 := by
    simpa [prefixWord, tailWord_3055103, baseEnd_3055103] using wordTrace_append hprefix tailTrace_3055103
  have hstable : (prefixWord ++ tailWord_3055103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055103).length < 2 ^ (prefixWord ++ tailWord_3055103).sum := by decide
  have hdescent : baseEnd_3055103 < baseStart_3055103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055133 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3055133 : Nat := 118140960795 + 3055133 * 2 ^ 59
def prefixEnd_3055133 : Nat := 4983230072969 + 3 ^ 40 * 3055133 * 2
def baseEnd_3055133 : Nat := 1568751692412700511787205

theorem tailTrace_3055133 : CollatzResearch.WordTrace tailWord_3055133 prefixEnd_3055133 1568751692412700511787205 := by
  unfold tailWord_3055133
  simp only [CollatzResearch.WordTrace]
  refine ⟨111429854840782391020866053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74286569893854927347244035 111429854840782391020866053)
  ·
    refine ⟨20893097782646698316412385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111429854840782391020866053 20893097782646698316412385)
    ·
      refine ⟨15669823336985023737309289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20893097782646698316412385 15669823336985023737309289)
      ·
        refine ⟨11752367502738767802981967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15669823336985023737309289 11752367502738767802981967)
        ·
          refine ⟨17628551254108151704472951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752367502738767802981967 17628551254108151704472951)
          ·
            refine ⟨26442826881162227556709427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17628551254108151704472951 26442826881162227556709427)
            ·
              refine ⟨39664240321743341335064141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26442826881162227556709427 39664240321743341335064141)
              ·
                refine ⟨14874090120653753000649053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39664240321743341335064141 14874090120653753000649053)
                ·
                  refine ⟨5577783795245157375243395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14874090120653753000649053 5577783795245157375243395)
                  ·
                    refine ⟨8366675692867736062865093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577783795245157375243395 8366675692867736062865093)
                    ·
                      refine ⟨1568751692412700511787205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8366675692867736062865093 1568751692412700511787205)
                      ·
                        rfl

theorem cell23_3055133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3055133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055133 prefixEnd_3055133 := by exact prefixLift 3055133
  have htrace : WordTrace (prefixWord ++ tailWord_3055133) baseStart_3055133 baseEnd_3055133 := by
    simpa [prefixWord, tailWord_3055133, baseEnd_3055133] using wordTrace_append hprefix tailTrace_3055133
  have hstable : (prefixWord ++ tailWord_3055133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055133).length < 2 ^ (prefixWord ++ tailWord_3055133).sum := by decide
  have hdescent : baseEnd_3055133 < baseStart_3055133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055137 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_3055137 : Nat := 118140960795 + 3055137 * 2 ^ 59
def prefixEnd_3055137 : Nat := 4983230072969 + 3 ^ 40 * 3055137 * 2
def baseEnd_3055137 : Nat := 1568753746335318496137187

theorem tailTrace_3055137 : CollatzResearch.WordTrace tailWord_3055137 prefixEnd_3055137 1568753746335318496137187 := by
  unfold tailWord_3055137
  simp only [CollatzResearch.WordTrace]
  refine ⟨111430000732767899704011665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74286667155178599802674443 111430000732767899704011665)
  ·
    refine ⟨83572500549575924778008749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111430000732767899704011665 83572500549575924778008749)
    ·
      refine ⟨31339687706090971791753281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83572500549575924778008749 31339687706090971791753281)
      ·
        refine ⟨23504765779568228843814961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31339687706090971791753281 23504765779568228843814961)
        ·
          refine ⟨17628574334676171632861221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23504765779568228843814961 17628574334676171632861221)
          ·
            refine ⟨3305357687751782181161479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17628574334676171632861221 3305357687751782181161479)
            ·
              refine ⟨4958036531627673271742219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305357687751782181161479 4958036531627673271742219)
              ·
                refine ⟨7437054797441509907613329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958036531627673271742219 7437054797441509907613329)
                ·
                  refine ⟨5577791098081132430709997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7437054797441509907613329 5577791098081132430709997)
                  ·
                    refine ⟨2091671661780424661516249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5577791098081132430709997 2091671661780424661516249)
                    ·
                      refine ⟨1568753746335318496137187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091671661780424661516249 1568753746335318496137187)
                      ·
                        rfl

theorem cell23_3055137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_3055137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055137 prefixEnd_3055137 := by exact prefixLift 3055137
  have htrace : WordTrace (prefixWord ++ tailWord_3055137) baseStart_3055137 baseEnd_3055137 := by
    simpa [prefixWord, tailWord_3055137, baseEnd_3055137] using wordTrace_append hprefix tailTrace_3055137
  have hstable : (prefixWord ++ tailWord_3055137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055137).length < 2 ^ (prefixWord ++ tailWord_3055137).sum := by decide
  have hdescent : baseEnd_3055137 < baseStart_3055137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055160 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 2, 4]
def baseStart_3055160 : Nat := 118140960795 + 3055160 * 2 ^ 59
def prefixEnd_3055160 : Nat := 4983230072969 + 3 ^ 40 * 3055160 * 2
def baseEnd_3055160 : Nat := 522921852130123968716527

theorem tailTrace_3055160 : CollatzResearch.WordTrace tailWord_3055160 prefixEnd_3055160 522921852130123968716527 := by
  unfold tailWord_3055160
  simp only [CollatzResearch.WordTrace]
  refine ⟨55715419805842287316049467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74287226407789716421399289 55715419805842287316049467)
  ·
    refine ⟨83573129708763430974074201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55715419805842287316049467 83573129708763430974074201)
    ·
      refine ⟨62679847281572573230555651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83573129708763430974074201 62679847281572573230555651)
      ·
        refine ⟨94019770922358859845833477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62679847281572573230555651 94019770922358859845833477)
        ·
          refine ⟨17628707047942286221093777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94019770922358859845833477 17628707047942286221093777)
          ·
            refine ⟨13221530285956714665820333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17628707047942286221093777 13221530285956714665820333)
            ·
              refine ⟨4958073857233767999682625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13221530285956714665820333 4958073857233767999682625)
              ·
                refine ⟨3718555392925325999761969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958073857233767999682625 3718555392925325999761969)
                ·
                  refine ⟨2788916544693994499821477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3718555392925325999761969 2788916544693994499821477)
                  ·
                    refine ⟨522921852130123968716527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2788916544693994499821477 522921852130123968716527)
                    ·
                      rfl

theorem cell23_3055160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_3055160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055160 prefixEnd_3055160 := by exact prefixLift 3055160
  have htrace : WordTrace (prefixWord ++ tailWord_3055160) baseStart_3055160 baseEnd_3055160 := by
    simpa [prefixWord, tailWord_3055160, baseEnd_3055160] using wordTrace_append hprefix tailTrace_3055160
  have hstable : (prefixWord ++ tailWord_3055160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055160).length < 2 ^ (prefixWord ++ tailWord_3055160).sum := by decide
  have hdescent : baseEnd_3055160 < baseStart_3055160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055167 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 3, 2, 2]
def baseStart_3055167 : Nat := 118140960795 + 3055167 * 2 ^ 59
def prefixEnd_3055167 : Nat := 4983230072969 + 3 ^ 40 * 3055167 * 2
def baseEnd_3055167 : Nat := 1568769150754953378762049

theorem tailTrace_3055167 : CollatzResearch.WordTrace tailWord_3055167 prefixEnd_3055167 1568769150754953378762049 := by
  unfold tailWord_3055167
  simp only [CollatzResearch.WordTrace]
  refine ⟨111431094922659214827603755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74287396615106143218402503 111431094922659214827603755)
  ·
    refine ⟨167146642383988822241405633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111431094922659214827603755 167146642383988822241405633)
    ·
      refine ⟨125359981787991616681054225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167146642383988822241405633 125359981787991616681054225)
      ·
        refine ⟨94019986340993712510790669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125359981787991616681054225 94019986340993712510790669)
        ·
          refine ⟨35257494877872642191546501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94019986340993712510790669 35257494877872642191546501)
          ·
            refine ⟨6610780289601120410914969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35257494877872642191546501 6610780289601120410914969)
            ·
              refine ⟨4958085217200840308186227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6610780289601120410914969 4958085217200840308186227)
              ·
                refine ⟨7437127825801260462279341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958085217200840308186227 7437127825801260462279341)
                ·
                  refine ⟨2788922934675472673354753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7437127825801260462279341 2788922934675472673354753)
                  ·
                    refine ⟨2091692201006604505016065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2788922934675472673354753 2091692201006604505016065)
                    ·
                      refine ⟨1568769150754953378762049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091692201006604505016065 1568769150754953378762049)
                      ·
                        rfl

theorem cell23_3055167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_3055167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055167 prefixEnd_3055167 := by exact prefixLift 3055167
  have htrace : WordTrace (prefixWord ++ tailWord_3055167) baseStart_3055167 baseEnd_3055167 := by
    simpa [prefixWord, tailWord_3055167, baseEnd_3055167] using wordTrace_append hprefix tailTrace_3055167
  have hstable : (prefixWord ++ tailWord_3055167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055167).length < 2 ^ (prefixWord ++ tailWord_3055167).sum := by decide
  have hdescent : baseEnd_3055167 < baseStart_3055167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055180 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3055180 : Nat := 118140960795 + 3055180 * 2 ^ 59
def prefixEnd_3055180 : Nat := 4983230072969 + 3 ^ 40 * 3055180 * 2
def baseEnd_3055180 : Nat := 1568775826003461827899489

theorem tailTrace_3055180 : CollatzResearch.WordTrace tailWord_3055180 prefixEnd_3055180 1568775826003461827899489 := by
  unfold tailWord_3055180
  simp only [CollatzResearch.WordTrace]
  refine ⟨55715784535806059023913497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74287712714408078698551329 55715784535806059023913497)
  ·
    refine ⟨41786838401854544267935123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55715784535806059023913497 41786838401854544267935123)
    ·
      refine ⟨62680257602781816401902685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41786838401854544267935123 62680257602781816401902685)
      ·
        refine ⟨23505096601043181150713507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62680257602781816401902685 23505096601043181150713507)
        ·
          refine ⟨35257644901564771726070261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23505096601043181150713507 35257644901564771726070261)
          ·
            refine ⟨3305404209521697349319087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35257644901564771726070261 3305404209521697349319087)
            ·
              refine ⟨4958106314282546023978631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305404209521697349319087 4958106314282546023978631)
              ·
                refine ⟨7437159471423819035967947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958106314282546023978631 7437159471423819035967947)
                ·
                  refine ⟨11155739207135728553951921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437159471423819035967947 11155739207135728553951921)
                  ·
                    refine ⟨8366804405351796415463941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11155739207135728553951921 8366804405351796415463941)
                    ·
                      refine ⟨1568775826003461827899489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8366804405351796415463941 1568775826003461827899489)
                      ·
                        rfl

theorem cell23_3055180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3055180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055180 prefixEnd_3055180 := by exact prefixLift 3055180
  have htrace : WordTrace (prefixWord ++ tailWord_3055180) baseStart_3055180 baseEnd_3055180 := by
    simpa [prefixWord, tailWord_3055180, baseEnd_3055180] using wordTrace_append hprefix tailTrace_3055180
  have hstable : (prefixWord ++ tailWord_3055180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055180).length < 2 ^ (prefixWord ++ tailWord_3055180).sum := by decide
  have hdescent : baseEnd_3055180 < baseStart_3055180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055193 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 7, 2]
def baseStart_3055193 : Nat := 118140960795 + 3055193 * 2 ^ 59
def prefixEnd_3055193 : Nat := 4983230072969 + 3 ^ 40 * 3055193 * 2
def baseEnd_3055193 : Nat := 1568782501251970277036929

theorem tailTrace_3055193 : CollatzResearch.WordTrace tailWord_3055193 prefixEnd_3055193 1568782501251970277036929 := by
  unfold tailWord_3055193
  simp only [CollatzResearch.WordTrace]
  refine ⟨111432043220565021268050233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74288028813710014178700155 111432043220565021268050233)
  ·
    refine ⟨83574032415423765951037675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111432043220565021268050233 83574032415423765951037675)
    ·
      refine ⟨125361048623135648926556513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83574032415423765951037675 125361048623135648926556513)
      ·
        refine ⟨94020786467351736694917385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125361048623135648926556513 94020786467351736694917385)
        ·
          refine ⟨70515589850513802521188039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94020786467351736694917385 70515589850513802521188039)
          ·
            refine ⟨105773384775770703781782059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70515589850513802521188039 105773384775770703781782059)
            ·
              refine ⟨158660077163656055672673089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105773384775770703781782059 158660077163656055672673089)
              ·
                refine ⟨118995057872742041754504817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158660077163656055672673089 118995057872742041754504817)
                ·
                  refine ⟨89246293404556531315878613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118995057872742041754504817 89246293404556531315878613)
                  ·
                    refine ⟨2091710001669293702715905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 89246293404556531315878613 2091710001669293702715905)
                    ·
                      refine ⟨1568782501251970277036929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091710001669293702715905 1568782501251970277036929)
                      ·
                        rfl

theorem cell23_3055193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_3055193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055193 prefixEnd_3055193 := by exact prefixLift 3055193
  have htrace : WordTrace (prefixWord ++ tailWord_3055193) baseStart_3055193 baseEnd_3055193 := by
    simpa [prefixWord, tailWord_3055193, baseEnd_3055193] using wordTrace_append hprefix tailTrace_3055193
  have hstable : (prefixWord ++ tailWord_3055193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055193).length < 2 ^ (prefixWord ++ tailWord_3055193).sum := by decide
  have hdescent : baseEnd_3055193 < baseStart_3055193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055290 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_3055290 : Nat := 118140960795 + 3055290 * 2 ^ 59
def prefixEnd_3055290 : Nat := 4983230072969 + 3 ^ 40 * 3055290 * 2
def baseEnd_3055290 : Nat := 1568832308875456397523983

theorem tailTrace_3055290 : CollatzResearch.WordTrace tailWord_3055290 prefixEnd_3055290 1568832308875456397523983 := by
  unfold tailWord_3055290
  simp only [CollatzResearch.WordTrace]
  refine ⟨27858895275303401708582831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74290387400809071222887549 27858895275303401708582831)
  ·
    refine ⟨41788342912955102562874247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27858895275303401708582831 41788342912955102562874247)
    ·
      refine ⟨62682514369432653844311371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41788342912955102562874247 62682514369432653844311371)
      ·
        refine ⟨94023771554148980766467057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62682514369432653844311371 94023771554148980766467057)
        ·
          refine ⟨70517828665611735574850293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94023771554148980766467057 70517828665611735574850293)
          ·
            refine ⟨6611046437401100210142215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70517828665611735574850293 6611046437401100210142215)
            ·
              refine ⟨9916569656101650315213323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611046437401100210142215 9916569656101650315213323)
              ·
                refine ⟨14874854484152475472819985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9916569656101650315213323 14874854484152475472819985)
                ·
                  refine ⟨11156140863114356604614989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14874854484152475472819985 11156140863114356604614989)
                  ·
                    refine ⟨4183552823667883726730621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11156140863114356604614989 4183552823667883726730621)
                    ·
                      refine ⟨1568832308875456397523983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4183552823667883726730621 1568832308875456397523983)
                      ·
                        rfl

theorem cell23_3055290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_3055290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055290 prefixEnd_3055290 := by exact prefixLift 3055290
  have htrace : WordTrace (prefixWord ++ tailWord_3055290) baseStart_3055290 baseEnd_3055290 := by
    simpa [prefixWord, tailWord_3055290, baseEnd_3055290] using wordTrace_append hprefix tailTrace_3055290
  have hstable : (prefixWord ++ tailWord_3055290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055290).length < 2 ^ (prefixWord ++ tailWord_3055290).sum := by decide
  have hdescent : baseEnd_3055290 < baseStart_3055290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055293 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_3055293 : Nat := 118140960795 + 3055293 * 2 ^ 59
def prefixEnd_3055293 : Nat := 4983230072969 + 3 ^ 40 * 3055293 * 2
def baseEnd_3055293 : Nat := 522944616439139961928823

theorem tailTrace_3055293 : CollatzResearch.WordTrace tailWord_3055293 prefixEnd_3055293 522944616439139961928823 := by
  unfold tailWord_3055293
  simp only [CollatzResearch.WordTrace]
  refine ⟨111435690520202738346690533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74290460346801825564460355 111435690520202738346690533)
  ·
    refine ⟨20894191972538013440004475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111435690520202738346690533 20894191972538013440004475)
    ·
      refine ⟨31341287958807020160006713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20894191972538013440004475 31341287958807020160006713)
      ·
        refine ⟨23505965969105265120005035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31341287958807020160006713 23505965969105265120005035)
        ·
          refine ⟨35258948953657897680007553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23505965969105265120005035 35258948953657897680007553)
          ·
            refine ⟨26444211715243423260005665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35258948953657897680007553 26444211715243423260005665)
            ·
              refine ⟨19833158786432567445004249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26444211715243423260005665 19833158786432567445004249)
              ·
                refine ⟨14874869089824425583753187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19833158786432567445004249 14874869089824425583753187)
                ·
                  refine ⟨22312303634736638375629781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14874869089824425583753187 22312303634736638375629781)
                  ·
                    refine ⟨522944616439139961928823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22312303634736638375629781 522944616439139961928823)
                    ·
                      rfl

theorem cell23_3055293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_3055293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055293 prefixEnd_3055293 := by exact prefixLift 3055293
  have htrace : WordTrace (prefixWord ++ tailWord_3055293) baseStart_3055293 baseEnd_3055293 := by
    simpa [prefixWord, tailWord_3055293, baseEnd_3055293] using wordTrace_append hprefix tailTrace_3055293
  have hstable : (prefixWord ++ tailWord_3055293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055293).length < 2 ^ (prefixWord ++ tailWord_3055293).sum := by decide
  have hdescent : baseEnd_3055293 < baseStart_3055293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055325 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3055325 : Nat := 118140960795 + 3055325 * 2 ^ 59
def prefixEnd_3055325 : Nat := 4983230072969 + 3 ^ 40 * 3055325 * 2
def baseEnd_3055325 : Nat := 1568850280698363760586323

theorem tailTrace_3055325 : CollatzResearch.WordTrace tailWord_3055325 prefixEnd_3055325 1568850280698363760586323 := by
  unfold tailWord_3055325
  simp only [CollatzResearch.WordTrace]
  refine ⟨111436857656086807811855429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74291238437391205207903619 111436857656086807811855429)
  ·
    refine ⟨20894410810516276464722893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111436857656086807811855429 20894410810516276464722893)
    ·
      refine ⟨7835404053943603674271085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20894410810516276464722893 7835404053943603674271085)
      ·
        refine ⟨2938276520228851377851657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7835404053943603674271085 2938276520228851377851657)
        ·
          refine ⟨2203707390171638533388743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938276520228851377851657 2203707390171638533388743)
          ·
            refine ⟨3305561085257457800083115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203707390171638533388743 3305561085257457800083115)
            ·
              refine ⟨4958341627886186700124673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305561085257457800083115 4958341627886186700124673)
              ·
                refine ⟨3718756220914640025093505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958341627886186700124673 3718756220914640025093505)
                ·
                  refine ⟨2789067165685980018820129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3718756220914640025093505 2789067165685980018820129)
                  ·
                    refine ⟨2091800374264485014115097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789067165685980018820129 2091800374264485014115097)
                    ·
                      refine ⟨1568850280698363760586323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091800374264485014115097 1568850280698363760586323)
                      ·
                        rfl

theorem cell23_3055325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3055325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055325 prefixEnd_3055325 := by exact prefixLift 3055325
  have htrace : WordTrace (prefixWord ++ tailWord_3055325) baseStart_3055325 baseEnd_3055325 := by
    simpa [prefixWord, tailWord_3055325, baseEnd_3055325] using wordTrace_append hprefix tailTrace_3055325
  have hstable : (prefixWord ++ tailWord_3055325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055325).length < 2 ^ (prefixWord ++ tailWord_3055325).sum := by decide
  have hdescent : baseEnd_3055325 < baseStart_3055325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055340 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_3055340 : Nat := 118140960795 + 3055340 * 2 ^ 59
def prefixEnd_3055340 : Nat := 4983230072969 + 3 ^ 40 * 3055340 * 2
def baseEnd_3055340 : Nat := 522952660969393733966251

theorem tailTrace_3055340 : CollatzResearch.WordTrace tailWord_3055340 prefixEnd_3055340 522952660969393733966251 := by
  unfold tailWord_3055340
  simp only [CollatzResearch.WordTrace]
  refine ⟨55718702375516232686825737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74291603167354976915767649 55718702375516232686825737)
  ·
    refine ⟨41789026781637174515119303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55718702375516232686825737 41789026781637174515119303)
    ·
      refine ⟨62683540172455761772678955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41789026781637174515119303 62683540172455761772678955)
      ·
        refine ⟨94025310258683642659018433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62683540172455761772678955 94025310258683642659018433)
        ·
          refine ⟨70518982694012731994263825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94025310258683642659018433 70518982694012731994263825)
          ·
            refine ⟨52889237020509548995697869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70518982694012731994263825 52889237020509548995697869)
            ·
              refine ⟨19833463882691080873386701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52889237020509548995697869 19833463882691080873386701)
              ·
                refine ⟨7437548956009155327520013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19833463882691080873386701 7437548956009155327520013)
                ·
                  refine ⟨2789080858503433247820005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7437548956009155327520013 2789080858503433247820005)
                  ·
                    refine ⟨522952660969393733966251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789080858503433247820005 522952660969393733966251)
                    ·
                      rfl

theorem cell23_3055340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_3055340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055340 prefixEnd_3055340 := by exact prefixLift 3055340
  have htrace : WordTrace (prefixWord ++ tailWord_3055340) baseStart_3055340 baseEnd_3055340 := by
    simpa [prefixWord, tailWord_3055340, baseEnd_3055340] using wordTrace_append hprefix tailTrace_3055340
  have hstable : (prefixWord ++ tailWord_3055340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055340).length < 2 ^ (prefixWord ++ tailWord_3055340).sum := by decide
  have hdescent : baseEnd_3055340 < baseStart_3055340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055343 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_3055343 : Nat := 118140960795 + 3055343 * 2 ^ 59
def prefixEnd_3055343 : Nat := 4983230072969 + 3 ^ 40 * 3055343 * 2
def baseEnd_3055343 : Nat := 1568859523350144690161239

theorem tailTrace_3055343 : CollatzResearch.WordTrace tailWord_3055343 prefixEnd_3055343 1568859523350144690161239 := by
  unfold tailWord_3055343
  simp only [CollatzResearch.WordTrace]
  refine ⟨111437514170021596886010683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74291676113347731257340455 111437514170021596886010683)
  ·
    refine ⟨167156271255032395329016025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111437514170021596886010683 167156271255032395329016025)
    ·
      refine ⟨125367203441274296496762019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167156271255032395329016025 125367203441274296496762019)
      ·
        refine ⟨188050805161911444745143029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125367203441274296496762019 188050805161911444745143029)
        ·
          refine ⟨17629762983929197944857159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188050805161911444745143029 17629762983929197944857159)
          ·
            refine ⟨26444644475893796917285739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17629762983929197944857159 26444644475893796917285739)
            ·
              refine ⟨39666966713840695375928609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26444644475893796917285739 39666966713840695375928609)
              ·
                refine ⟨29750225035380521531946457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39666966713840695375928609 29750225035380521531946457)
                ·
                  refine ⟨22312668776535391148959843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29750225035380521531946457 22312668776535391148959843)
                  ·
                    refine ⟨33469003164803086723439765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22312668776535391148959843 33469003164803086723439765)
                    ·
                      refine ⟨1568859523350144690161239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33469003164803086723439765 1568859523350144690161239)
                      ·
                        rfl

theorem cell23_3055343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_3055343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055343 prefixEnd_3055343 := by exact prefixLift 3055343
  have htrace : WordTrace (prefixWord ++ tailWord_3055343) baseStart_3055343 baseEnd_3055343 := by
    simpa [prefixWord, tailWord_3055343, baseEnd_3055343] using wordTrace_append hprefix tailTrace_3055343
  have hstable : (prefixWord ++ tailWord_3055343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055343).length < 2 ^ (prefixWord ++ tailWord_3055343).sum := by decide
  have hdescent : baseEnd_3055343 < baseStart_3055343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055374 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_3055374 : Nat := 118140960795 + 3055374 * 2 ^ 59
def prefixEnd_3055374 : Nat := 4983230072969 + 3 ^ 40 * 3055374 * 2
def baseEnd_3055374 : Nat := 522958480416811356291199

theorem tailTrace_3055374 : CollatzResearch.WordTrace tailWord_3055374 prefixEnd_3055374 522958480416811356291199 := by
  unfold tailWord_3055374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929830604113661147548647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74292429888606192786926117 13929830604113661147548647)
  ·
    refine ⟨20894745906170491721322971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13929830604113661147548647 20894745906170491721322971)
    ·
      refine ⟨31342118859255737581984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20894745906170491721322971 31342118859255737581984457)
      ·
        refine ⟨23506589144441803186488343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31342118859255737581984457 23506589144441803186488343)
        ·
          refine ⟨35259883716662704779732515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23506589144441803186488343 35259883716662704779732515)
          ·
            refine ⟨52889825574994057169598773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35259883716662704779732515 52889825574994057169598773)
            ·
              refine ⟨4958421147655692859649885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52889825574994057169598773 4958421147655692859649885)
              ·
                refine ⟨1859407930370884822368707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4958421147655692859649885 1859407930370884822368707)
                ·
                  refine ⟨2789111895556327233553061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859407930370884822368707 2789111895556327233553061)
                  ·
                    refine ⟨522958480416811356291199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789111895556327233553061 522958480416811356291199)
                    ·
                      rfl

theorem cell23_3055374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_3055374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055374 prefixEnd_3055374 := by exact prefixLift 3055374
  have htrace : WordTrace (prefixWord ++ tailWord_3055374) baseStart_3055374 baseEnd_3055374 := by
    simpa [prefixWord, tailWord_3055374, baseEnd_3055374] using wordTrace_append hprefix tailTrace_3055374
  have hstable : (prefixWord ++ tailWord_3055374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055374).length < 2 ^ (prefixWord ++ tailWord_3055374).sum := by decide
  have hdescent : baseEnd_3055374 < baseStart_3055374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055450 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_3055450 : Nat := 118140960795 + 3055450 * 2 ^ 59
def prefixEnd_3055450 : Nat := 4983230072969 + 3 ^ 40 * 3055450 * 2
def baseEnd_3055450 : Nat := 1568914465780175771523247

theorem tailTrace_3055450 : CollatzResearch.WordTrace tailWord_3055450 prefixEnd_3055450 1568914465780175771523247 := by
  unfold tailWord_3055450
  simp only [CollatzResearch.WordTrace]
  refine ⟨27860354195158488540038951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74294277853755969440103869 27860354195158488540038951)
  ·
    refine ⟨41790531292737732810058427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27860354195158488540038951 41790531292737732810058427)
    ·
      refine ⟨62685796939106599215087641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41790531292737732810058427 62685796939106599215087641)
      ·
        refine ⟨47014347704329949411315731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62685796939106599215087641 47014347704329949411315731)
        ·
          refine ⟨70521521556494924116973597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47014347704329949411315731 70521521556494924116973597)
          ·
            refine ⟨26445570583685596543865099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70521521556494924116973597 26445570583685596543865099)
            ·
              refine ⟨39668355875528394815797649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26445570583685596543865099 39668355875528394815797649)
              ·
                refine ⟨29751266906646296111848237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39668355875528394815797649 29751266906646296111848237)
                ·
                  refine ⟨11156725089992361041943089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29751266906646296111848237 11156725089992361041943089)
                  ·
                    refine ⟨8367543817494270781457317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11156725089992361041943089 8367543817494270781457317)
                    ·
                      refine ⟨1568914465780175771523247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8367543817494270781457317 1568914465780175771523247)
                      ·
                        rfl

theorem cell23_3055450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_3055450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055450 prefixEnd_3055450 := by exact prefixLift 3055450
  have htrace : WordTrace (prefixWord ++ tailWord_3055450) baseStart_3055450 baseEnd_3055450 := by
    simpa [prefixWord, tailWord_3055450, baseEnd_3055450] using wordTrace_append hprefix tailTrace_3055450
  have hstable : (prefixWord ++ tailWord_3055450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055450).length < 2 ^ (prefixWord ++ tailWord_3055450).sum := by decide
  have hdescent : baseEnd_3055450 < baseStart_3055450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055477 : List Nat := [1, 3, 4, 1, 1, 1, 5, 7]
def baseStart_3055477 : Nat := 118140960795 + 3055477 * 2 ^ 59
def prefixEnd_3055477 : Nat := 4983230072969 + 3 ^ 40 * 3055477 * 2
def baseEnd_3055477 : Nat := 58108456657698043180949

theorem tailTrace_3055477 : CollatzResearch.WordTrace tailWord_3055477 prefixEnd_3055477 58108456657698043180949 := by
  unfold tailWord_3055477
  simp only [CollatzResearch.WordTrace]
  refine ⟨111442401551536137771388685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74294934367690758514259123 111442401551536137771388685)
  ·
    refine ⟨41790900581826051664270757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111442401551536137771388685 41790900581826051664270757)
    ·
      refine ⟨7835793859092384687050767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41790900581826051664270757 7835793859092384687050767)
      ·
        refine ⟨11753690788638577030576151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7835793859092384687050767 11753690788638577030576151)
        ·
          refine ⟨17630536182957865545864227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11753690788638577030576151 17630536182957865545864227)
          ·
            refine ⟨26445804274436798318796341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17630536182957865545864227 26445804274436798318796341)
            ·
              refine ⟨2479294150728449842387157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26445804274436798318796341 2479294150728449842387157)
              ·
                refine ⟨58108456657698043180949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2479294150728449842387157 58108456657698043180949)
                ·
                  rfl

theorem cell23_3055477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 7].length) (baseStart_3055477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055477 prefixEnd_3055477 := by exact prefixLift 3055477
  have htrace : WordTrace (prefixWord ++ tailWord_3055477) baseStart_3055477 baseEnd_3055477 := by
    simpa [prefixWord, tailWord_3055477, baseEnd_3055477] using wordTrace_append hprefix tailTrace_3055477
  have hstable : (prefixWord ++ tailWord_3055477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055477).length < 2 ^ (prefixWord ++ tailWord_3055477).sum := by decide
  have hdescent : baseEnd_3055477 < baseStart_3055477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055487 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 3]
def baseStart_3055487 : Nat := 118140960795 + 3055487 * 2 ^ 59
def prefixEnd_3055487 : Nat := 4983230072969 + 3 ^ 40 * 3055487 * 2
def baseEnd_3055487 : Nat := 1568933464564392126760577

theorem tailTrace_3055487 : CollatzResearch.WordTrace tailWord_3055487 prefixEnd_3055487 1568933464564392126760577 := by
  unfold tailWord_3055487
  simp only [CollatzResearch.WordTrace]
  refine ⟨111442766281499909479252715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74295177520999939652835143 111442766281499909479252715)
  ·
    refine ⟨167164149422249864218879073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111442766281499909479252715 167164149422249864218879073)
    ·
      refine ⟨125373112066687398164159305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167164149422249864218879073 125373112066687398164159305)
      ·
        refine ⟨94029834050015548623119479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125373112066687398164159305 94029834050015548623119479)
        ·
          refine ⟨141044751075023322934679219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94029834050015548623119479 141044751075023322934679219)
          ·
            refine ⟨211567126612534984402018829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141044751075023322934679219 211567126612534984402018829)
            ·
              refine ⟨79337672479700619150757061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211567126612534984402018829 79337672479700619150757061)
              ·
                refine ⟨14875813589943866090766949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79337672479700619150757061 14875813589943866090766949)
                ·
                  refine ⟨2789215048114474892018803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14875813589943866090766949 2789215048114474892018803)
                  ·
                    refine ⟨4183822572171712338028205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2789215048114474892018803 4183822572171712338028205)
                    ·
                      refine ⟨1568933464564392126760577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4183822572171712338028205 1568933464564392126760577)
                      ·
                        rfl

theorem cell23_3055487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_3055487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055487 prefixEnd_3055487 := by exact prefixLift 3055487
  have htrace : WordTrace (prefixWord ++ tailWord_3055487) baseStart_3055487 baseEnd_3055487 := by
    simpa [prefixWord, tailWord_3055487, baseEnd_3055487] using wordTrace_append hprefix tailTrace_3055487
  have hstable : (prefixWord ++ tailWord_3055487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055487).length < 2 ^ (prefixWord ++ tailWord_3055487).sum := by decide
  have hdescent : baseEnd_3055487 < baseStart_3055487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055491 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 1, 2, 3]
def baseStart_3055491 : Nat := 118140960795 + 3055491 * 2 ^ 59
def prefixEnd_3055491 : Nat := 4983230072969 + 3 ^ 40 * 3055491 * 2
def baseEnd_3055491 : Nat := 1568935518487010111110559

theorem tailTrace_3055491 : CollatzResearch.WordTrace tailWord_3055491 prefixEnd_3055491 1568935518487010111110559 := by
  unfold tailWord_3055491
  simp only [CollatzResearch.WordTrace]
  refine ⟨111442912173485418162398327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74295274782323612108265551 111442912173485418162398327)
  ·
    refine ⟨167164368260228127243597491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111442912173485418162398327 167164368260228127243597491)
    ·
      refine ⟨250746552390342190865396237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167164368260228127243597491 250746552390342190865396237)
      ·
        refine ⟨94029957146378321574523589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250746552390342190865396237 94029957146378321574523589)
        ·
          refine ⟨17630616964945935295223173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94029957146378321574523589 17630616964945935295223173)
          ·
            refine ⟨3305740680927362867854345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17630616964945935295223173 3305740680927362867854345)
            ·
              refine ⟨2479305510695522150890759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305740680927362867854345 2479305510695522150890759)
              ·
                refine ⟨3718958266043283226336139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479305510695522150890759 3718958266043283226336139)
                ·
                  refine ⟨5578437399064924839504209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718958266043283226336139 5578437399064924839504209)
                  ·
                    refine ⟨4183828049298693629628157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5578437399064924839504209 4183828049298693629628157)
                    ·
                      refine ⟨1568935518487010111110559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4183828049298693629628157 1568935518487010111110559)
                      ·
                        rfl

theorem cell23_3055491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_3055491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055491 prefixEnd_3055491 := by exact prefixLift 3055491
  have htrace : WordTrace (prefixWord ++ tailWord_3055491) baseStart_3055491 baseEnd_3055491 := by
    simpa [prefixWord, tailWord_3055491, baseEnd_3055491] using wordTrace_append hprefix tailTrace_3055491
  have hstable : (prefixWord ++ tailWord_3055491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055491).length < 2 ^ (prefixWord ++ tailWord_3055491).sum := by decide
  have hdescent : baseEnd_3055491 < baseStart_3055491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055498 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3055498 : Nat := 118140960795 + 3055498 * 2 ^ 59
def prefixEnd_3055498 : Nat := 4983230072969 + 3 ^ 40 * 3055498 * 2
def baseEnd_3055498 : Nat := 522979704283863861241009

theorem tailTrace_3055498 : CollatzResearch.WordTrace tailWord_3055498 prefixEnd_3055498 522979704283863861241009 := by
  unfold tailWord_3055498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27860791871115014589475787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74295444989640038905268765 27860791871115014589475787)
  ·
    refine ⟨41791187806672521884213681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27860791871115014589475787 41791187806672521884213681)
    ·
      refine ⟨31343390855004391413160261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41791187806672521884213681 31343390855004391413160261)
      ·
        refine ⟨5876885785313323389967549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31343390855004391413160261 5876885785313323389967549)
        ·
          refine ⟨2203832169492496271237831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5876885785313323389967549 2203832169492496271237831)
          ·
            refine ⟨3305748254238744406856747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203832169492496271237831 3305748254238744406856747)
            ·
              refine ⟨4958622381358116610285121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305748254238744406856747 4958622381358116610285121)
              ·
                refine ⟨3718966786018587457713841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958622381358116610285121 3718966786018587457713841)
                ·
                  refine ⟨2789225089513940593285381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3718966786018587457713841 2789225089513940593285381)
                  ·
                    refine ⟨522979704283863861241009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789225089513940593285381 522979704283863861241009)
                    ·
                      rfl

theorem cell23_3055498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3055498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055498 prefixEnd_3055498 := by exact prefixLift 3055498
  have htrace : WordTrace (prefixWord ++ tailWord_3055498) baseStart_3055498 baseEnd_3055498 := by
    simpa [prefixWord, tailWord_3055498, baseEnd_3055498] using wordTrace_append hprefix tailTrace_3055498
  have hstable : (prefixWord ++ tailWord_3055498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055498).length < 2 ^ (prefixWord ++ tailWord_3055498).sum := by decide
  have hdescent : baseEnd_3055498 < baseStart_3055498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055518 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3055518 : Nat := 118140960795 + 3055518 * 2 ^ 59
def prefixEnd_3055518 : Nat := 4983230072969 + 3 ^ 40 * 3055518 * 2
def baseEnd_3055518 : Nat := 1568949382464681505472935

theorem tailTrace_3055518 : CollatzResearch.WordTrace tailWord_3055518 prefixEnd_3055518 1568949382464681505472935 := by
  unfold tailWord_3055518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13930487118048450221703901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74295931296258401182420805 13930487118048450221703901)
  ·
    refine ⟨5223932669268168833138963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13930487118048450221703901 5223932669268168833138963)
    ·
      refine ⟨7835899003902253249708445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5223932669268168833138963 7835899003902253249708445)
      ·
        refine ⟨2938462126463344968640667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7835899003902253249708445 2938462126463344968640667)
        ·
          refine ⟨4407693189695017452961001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938462126463344968640667 4407693189695017452961001)
          ·
            refine ⟨3305769892271263089720751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407693189695017452961001 3305769892271263089720751)
            ·
              refine ⟨4958654838406894634581127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305769892271263089720751 4958654838406894634581127)
              ·
                refine ⟨7437982257610341951871691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958654838406894634581127 7437982257610341951871691)
                ·
                  refine ⟨11156973386415512927807537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437982257610341951871691 11156973386415512927807537)
                  ·
                    refine ⟨8367730039811634695855653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11156973386415512927807537 8367730039811634695855653)
                    ·
                      refine ⟨1568949382464681505472935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8367730039811634695855653 1568949382464681505472935)
                      ·
                        rfl

theorem cell23_3055518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3055518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055518 prefixEnd_3055518 := by exact prefixLift 3055518
  have htrace : WordTrace (prefixWord ++ tailWord_3055518) baseStart_3055518 baseEnd_3055518 := by
    simpa [prefixWord, tailWord_3055518, baseEnd_3055518] using wordTrace_append hprefix tailTrace_3055518
  have hstable : (prefixWord ++ tailWord_3055518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055518).length < 2 ^ (prefixWord ++ tailWord_3055518).sum := by decide
  have hdescent : baseEnd_3055518 < baseStart_3055518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055521 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3055521 : Nat := 118140960795 + 3055521 * 2 ^ 59
def prefixEnd_3055521 : Nat := 4983230072969 + 3 ^ 40 * 3055521 * 2
def baseEnd_3055521 : Nat := 1568950922906644993735421

theorem tailTrace_3055521 : CollatzResearch.WordTrace tailWord_3055521 prefixEnd_3055521 1568950922906644993735421 := by
  unfold tailWord_3055521
  simp only [CollatzResearch.WordTrace]
  refine ⟨111444006363376733285990417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74296004242251155523993611 111444006363376733285990417)
  ·
    refine ⟨83583004772532549964492813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111444006363376733285990417 83583004772532549964492813)
    ·
      refine ⟨31343626789699706236684805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83583004772532549964492813 31343626789699706236684805)
      ·
        refine ⟨5876930023068694919378401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31343626789699706236684805 5876930023068694919378401)
        ·
          refine ⟨4407697517301521189533801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5876930023068694919378401 4407697517301521189533801)
          ·
            refine ⟨3305773137976140892150351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407697517301521189533801 3305773137976140892150351)
            ·
              refine ⟨4958659706964211338225527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305773137976140892150351 4958659706964211338225527)
              ·
                refine ⟨7437989560446317007338291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958659706964211338225527 7437989560446317007338291)
                ·
                  refine ⟨11156984340669475511007437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437989560446317007338291 11156984340669475511007437)
                  ·
                    refine ⟨4183869127751053316627789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11156984340669475511007437 4183869127751053316627789)
                    ·
                      refine ⟨1568950922906644993735421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4183869127751053316627789 1568950922906644993735421)
                      ·
                        rfl

theorem cell23_3055521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3055521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055521 prefixEnd_3055521 := by exact prefixLift 3055521
  have htrace : WordTrace (prefixWord ++ tailWord_3055521) baseStart_3055521 baseEnd_3055521 := by
    simpa [prefixWord, tailWord_3055521, baseEnd_3055521] using wordTrace_append hprefix tailTrace_3055521
  have hstable : (prefixWord ++ tailWord_3055521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055521).length < 2 ^ (prefixWord ++ tailWord_3055521).sum := by decide
  have hdescent : baseEnd_3055521 < baseStart_3055521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055528 : List Nat := [2, 1, 6, 2, 2, 1, 2, 7]
def baseStart_3055528 : Nat := 118140960795 + 3055528 * 2 ^ 59
def prefixEnd_3055528 : Nat := 4983230072969 + 3 ^ 40 * 3055528 * 2
def baseEnd_3055528 : Nat := 58109426565600980235107

theorem tailTrace_3055528 : CollatzResearch.WordTrace tailWord_3055528 prefixEnd_3055528 58109426565600980235107 := by
  unfold tailWord_3055528
  simp only [CollatzResearch.WordTrace]
  refine ⟨55722130837175686740747619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74296174449567582320996825 55722130837175686740747619)
  ·
    refine ⟨83583196255763530111121429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55722130837175686740747619 83583196255763530111121429)
    ·
      refine ⟨3917962324488915473958817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83583196255763530111121429 3917962324488915473958817)
      ·
        refine ⟨2938471743366686605469113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917962324488915473958817 2938471743366686605469113)
        ·
          refine ⟨2203853807525014954101835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938471743366686605469113 2203853807525014954101835)
          ·
            refine ⟨3305780711287522431152753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203853807525014954101835 3305780711287522431152753)
            ·
              refine ⟨2479335533465641823364565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305780711287522431152753 2479335533465641823364565)
              ·
                refine ⟨58109426565600980235107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2479335533465641823364565 58109426565600980235107)
                ·
                  rfl

theorem cell23_3055528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 7].length) (baseStart_3055528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055528 prefixEnd_3055528 := by exact prefixLift 3055528
  have htrace : WordTrace (prefixWord ++ tailWord_3055528) baseStart_3055528 baseEnd_3055528 := by
    simpa [prefixWord, tailWord_3055528, baseEnd_3055528] using wordTrace_append hprefix tailTrace_3055528
  have hstable : (prefixWord ++ tailWord_3055528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055528).length < 2 ^ (prefixWord ++ tailWord_3055528).sum := by decide
  have hdescent : baseEnd_3055528 < baseStart_3055528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055544 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 6, 2, 2]
def baseStart_3055544 : Nat := 118140960795 + 3055544 * 2 ^ 59
def prefixEnd_3055544 : Nat := 4983230072969 + 3 ^ 40 * 3055544 * 2
def baseEnd_3055544 : Nat := 1568962732961698403747815

theorem tailTrace_3055544 : CollatzResearch.WordTrace tailWord_3055544 prefixEnd_3055544 1568962732961698403747815 := by
  unfold tailWord_3055544
  simp only [CollatzResearch.WordTrace]
  refine ⟨55722422621146704107038843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74296563494862272142718457 55722422621146704107038843)
  ·
    refine ⟨83583633931720056160558265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55722422621146704107038843 83583633931720056160558265)
    ·
      refine ⟨62687725448790042120418699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83583633931720056160558265 62687725448790042120418699)
      ·
        refine ⟨94031588173185063180628049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62687725448790042120418699 94031588173185063180628049)
        ·
          refine ⟨70523691129888797385471037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94031588173185063180628049 70523691129888797385471037)
          ·
            refine ⟨26446384173708299019551639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70523691129888797385471037 26446384173708299019551639)
            ·
              refine ⟨39669576260562448529327459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26446384173708299019551639 39669576260562448529327459)
              ·
                refine ⟨59504364390843672793991189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39669576260562448529327459 59504364390843672793991189)
                ·
                  refine ⟨2789267080820797162218337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59504364390843672793991189 2789267080820797162218337)
                  ·
                    refine ⟨2091950310615597871663753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789267080820797162218337 2091950310615597871663753)
                    ·
                      refine ⟨1568962732961698403747815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091950310615597871663753 1568962732961698403747815)
                      ·
                        rfl

theorem cell23_3055544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_3055544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055544 prefixEnd_3055544 := by exact prefixLift 3055544
  have htrace : WordTrace (prefixWord ++ tailWord_3055544) baseStart_3055544 baseEnd_3055544 := by
    simpa [prefixWord, tailWord_3055544, baseEnd_3055544] using wordTrace_append hprefix tailTrace_3055544
  have hstable : (prefixWord ++ tailWord_3055544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055544).length < 2 ^ (prefixWord ++ tailWord_3055544).sum := by decide
  have hdescent : baseEnd_3055544 < baseStart_3055544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055578 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2]
def baseStart_3055578 : Nat := 118140960795 + 3055578 * 2 ^ 59
def prefixEnd_3055578 : Nat := 4983230072969 + 3 ^ 40 * 3055578 * 2
def baseEnd_3055578 : Nat := 1568980191303951270722659

theorem tailTrace_3055578 : CollatzResearch.WordTrace tailWord_3055578 prefixEnd_3055578 1568980191303951270722659 := by
  unfold tailWord_3055578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27861521331042558005203847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74297390216113488013876925 27861521331042558005203847)
  ·
    refine ⟨41792281996563837007805771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27861521331042558005203847 41792281996563837007805771)
    ·
      refine ⟨62688422994845755511708657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41792281996563837007805771 62688422994845755511708657)
      ·
        refine ⟨47016317246134316633781493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62688422994845755511708657 47016317246134316633781493)
        ·
          refine ⟨4407779741825092184417015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47016317246134316633781493 4407779741825092184417015)
          ·
            refine ⟨6611669612737638276625523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407779741825092184417015 6611669612737638276625523)
            ·
              refine ⟨9917504419106457414938285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611669612737638276625523 9917504419106457414938285)
              ·
                refine ⟨3719064157164921530601857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9917504419106457414938285 3719064157164921530601857)
                ·
                  refine ⟨2789298117873691147951393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3719064157164921530601857 2789298117873691147951393)
                  ·
                    refine ⟨2091973588405268360963545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789298117873691147951393 2091973588405268360963545)
                    ·
                      refine ⟨1568980191303951270722659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2091973588405268360963545 1568980191303951270722659)
                      ·
                        rfl

theorem cell23_3055578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_3055578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055578 prefixEnd_3055578 := by exact prefixLift 3055578
  have htrace : WordTrace (prefixWord ++ tailWord_3055578) baseStart_3055578 baseEnd_3055578 := by
    simpa [prefixWord, tailWord_3055578, baseEnd_3055578] using wordTrace_append hprefix tailTrace_3055578
  have hstable : (prefixWord ++ tailWord_3055578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055578).length < 2 ^ (prefixWord ++ tailWord_3055578).sum := by decide
  have hdescent : baseEnd_3055578 < baseStart_3055578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055644 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_3055644 : Nat := 118140960795 + 3055644 * 2 ^ 59
def prefixEnd_3055644 : Nat := 4983230072969 + 3 ^ 40 * 3055644 * 2
def baseEnd_3055644 : Nat := 523004693675716004165785

theorem tailTrace_3055644 : CollatzResearch.WordTrace tailWord_3055644 prefixEnd_3055644 523004693675716004165785 := by
  unfold tailWord_3055644
  simp only [CollatzResearch.WordTrace]
  refine ⟨55724246270965562646358993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74298995027954083528478657 55724246270965562646358993)
  ·
    refine ⟨41793184703224171984769245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55724246270965562646358993 41793184703224171984769245)
    ·
      refine ⟨15672444263709064494288467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41793184703224171984769245 15672444263709064494288467)
      ·
        refine ⟨23508666395563596741432701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15672444263709064494288467 23508666395563596741432701)
        ·
          refine ⟨8815749898336348778037263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23508666395563596741432701 8815749898336348778037263)
          ·
            refine ⟨13223624847504523167055895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8815749898336348778037263 13223624847504523167055895)
            ·
              refine ⟨19835437271256784750583843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13223624847504523167055895 19835437271256784750583843)
              ·
                refine ⟨29753155906885177125875765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19835437271256784750583843 29753155906885177125875765)
                ·
                  refine ⟨2789358366270485355550853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29753155906885177125875765 2789358366270485355550853)
                  ·
                    refine ⟨523004693675716004165785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789358366270485355550853 523004693675716004165785)
                    ·
                      rfl

theorem cell23_3055644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_3055644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055644 prefixEnd_3055644 := by exact prefixLift 3055644
  have htrace : WordTrace (prefixWord ++ tailWord_3055644) baseStart_3055644 baseEnd_3055644 := by
    simpa [prefixWord, tailWord_3055644, baseEnd_3055644] using wordTrace_append hprefix tailTrace_3055644
  have hstable : (prefixWord ++ tailWord_3055644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055644).length < 2 ^ (prefixWord ++ tailWord_3055644).sum := by decide
  have hdescent : baseEnd_3055644 < baseStart_3055644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055677 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3055677 : Nat := 118140960795 + 3055677 * 2 ^ 59
def prefixEnd_3055677 : Nat := 4983230072969 + 3 ^ 40 * 3055677 * 2
def baseEnd_3055677 : Nat := 1569031025888746383384703

theorem tailTrace_3055677 : CollatzResearch.WordTrace tailWord_3055677 prefixEnd_3055677 1569031025888746383384703 := by
  unfold tailWord_3055677
  simp only [CollatzResearch.WordTrace]
  refine ⟨111449696150811571928669285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74299797433874381285779523 111449696150811571928669285)
  ·
    refine ⟨20896818028277169736625491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111449696150811571928669285 20896818028277169736625491)
    ·
      refine ⟨31345227042415754604938237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20896818028277169736625491 31345227042415754604938237)
      ·
        refine ⟨11754460140905907976851839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31345227042415754604938237 11754460140905907976851839)
        ·
          refine ⟨17631690211358861965277759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11754460140905907976851839 17631690211358861965277759)
          ·
            refine ⟨26447535317038292947916639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17631690211358861965277759 26447535317038292947916639)
            ·
              refine ⟨39671302975557439421874959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26447535317038292947916639 39671302975557439421874959)
              ·
                refine ⟨59506954463336159132812439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39671302975557439421874959 59506954463336159132812439)
                ·
                  refine ⟨89260431695004238699218659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59506954463336159132812439 89260431695004238699218659)
                  ·
                    refine ⟨133890647542506358048827989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89260431695004238699218659 133890647542506358048827989)
                    ·
                      refine ⟨1569031025888746383384703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 133890647542506358048827989 1569031025888746383384703)
                      ·
                        rfl

theorem cell23_3055677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3055677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055677 prefixEnd_3055677 := by exact prefixLift 3055677
  have htrace : WordTrace (prefixWord ++ tailWord_3055677) baseStart_3055677 baseEnd_3055677 := by
    simpa [prefixWord, tailWord_3055677, baseEnd_3055677] using wordTrace_append hprefix tailTrace_3055677
  have hstable : (prefixWord ++ tailWord_3055677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055677).length < 2 ^ (prefixWord ++ tailWord_3055677).sum := by decide
  have hdescent : baseEnd_3055677 < baseStart_3055677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055678 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_3055678 : Nat := 118140960795 + 3055678 * 2 ^ 59
def prefixEnd_3055678 : Nat := 4983230072969 + 3 ^ 40 * 3055678 * 2
def baseEnd_3055678 : Nat := 523010513123133626490733

theorem tailTrace_3055678 : CollatzResearch.WordTrace tailWord_3055678 prefixEnd_3055678 523010513123133626490733 := by
  unfold tailWord_3055678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931216577975993637431961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74299821749205299399637125 13931216577975993637431961)
  ·
    refine ⟨10448412433481995228073971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13931216577975993637431961 10448412433481995228073971)
    ·
      refine ⟨15672618650222992842110957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448412433481995228073971 15672618650222992842110957)
      ·
        refine ⟨5877231993833622315791609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15672618650222992842110957 5877231993833622315791609)
        ·
          refine ⟨4407923995375216736843707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877231993833622315791609 4407923995375216736843707)
          ·
            refine ⟨6611885993062825105265561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407923995375216736843707 6611885993062825105265561)
            ·
              refine ⟨4958914494797118828949171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6611885993062825105265561 4958914494797118828949171)
              ·
                refine ⟨7438371742195678243423757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958914494797118828949171 7438371742195678243423757)
                ·
                  refine ⟨2789389403323379341283909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7438371742195678243423757 2789389403323379341283909)
                  ·
                    refine ⟨523010513123133626490733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789389403323379341283909 523010513123133626490733)
                    ·
                      rfl

theorem cell23_3055678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_3055678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055678 prefixEnd_3055678 := by exact prefixLift 3055678
  have htrace : WordTrace (prefixWord ++ tailWord_3055678) baseStart_3055678 baseEnd_3055678 := by
    simpa [prefixWord, tailWord_3055678, baseEnd_3055678] using wordTrace_append hprefix tailTrace_3055678
  have hstable : (prefixWord ++ tailWord_3055678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055678).length < 2 ^ (prefixWord ++ tailWord_3055678).sum := by decide
  have hdescent : baseEnd_3055678 < baseStart_3055678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055701 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3055701 : Nat := 118140960795 + 3055701 * 2 ^ 59
def prefixEnd_3055701 : Nat := 4983230072969 + 3 ^ 40 * 3055701 * 2
def baseEnd_3055701 : Nat := 1569043349424454289484593

theorem tailTrace_3055701 : CollatzResearch.WordTrace tailWord_3055701 prefixEnd_3055701 1569043349424454289484593 := by
  unfold tailWord_3055701
  simp only [CollatzResearch.WordTrace]
  refine ⟨111450571502724624027542957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74300381001816416018361971 111450571502724624027542957)
  ·
    refine ⟨41793964313521734010328609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111450571502724624027542957 41793964313521734010328609)
    ·
      refine ⟨31345473235141300507746457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41793964313521734010328609 31345473235141300507746457)
      ·
        refine ⟨23509104926355975380809843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31345473235141300507746457 23509104926355975380809843)
        ·
          refine ⟨35263657389533963071214765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23509104926355975380809843 35263657389533963071214765)
          ·
            refine ⟨13223871521075236151705537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35263657389533963071214765 13223871521075236151705537)
            ·
              refine ⟨9917903640806427113779153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13223871521075236151705537 9917903640806427113779153)
              ·
                refine ⟨7438427730604820335334365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9917903640806427113779153 7438427730604820335334365)
                ·
                  refine ⟨2789410398976807625750387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7438427730604820335334365 2789410398976807625750387)
                  ·
                    refine ⟨4184115598465211438625581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2789410398976807625750387 4184115598465211438625581)
                    ·
                      refine ⟨1569043349424454289484593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4184115598465211438625581 1569043349424454289484593)
                      ·
                        rfl

theorem cell23_3055701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3055701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055701 prefixEnd_3055701 := by exact prefixLift 3055701
  have htrace : WordTrace (prefixWord ++ tailWord_3055701) baseStart_3055701 baseEnd_3055701 := by
    simpa [prefixWord, tailWord_3055701, baseEnd_3055701] using wordTrace_append hprefix tailTrace_3055701
  have hstable : (prefixWord ++ tailWord_3055701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055701).length < 2 ^ (prefixWord ++ tailWord_3055701).sum := by decide
  have hdescent : baseEnd_3055701 < baseStart_3055701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055704 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 1, 5]
def baseStart_3055704 : Nat := 118140960795 + 3055704 * 2 ^ 59
def prefixEnd_3055704 : Nat := 4983230072969 + 3 ^ 40 * 3055704 * 2
def baseEnd_3055704 : Nat := 523014963288805925915693

theorem tailTrace_3055704 : CollatzResearch.WordTrace tailWord_3055704 prefixEnd_3055704 523014963288805925915693 := by
  unfold tailWord_3055704
  simp only [CollatzResearch.WordTrace]
  refine ⟨55725340460856877769951083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74300453947809170359934777 55725340460856877769951083)
  ·
    refine ⟨83588010691285316654926625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55725340460856877769951083 83588010691285316654926625)
    ·
      refine ⟨62691008018463987491194969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83588010691285316654926625 62691008018463987491194969)
      ·
        refine ⟨47018256013847990618396227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62691008018463987491194969 47018256013847990618396227)
        ·
          refine ⟨70527384020771985927594341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47018256013847990618396227 70527384020771985927594341)
          ·
            refine ⟨13223884503894747361423939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70527384020771985927594341 13223884503894747361423939)
            ·
              refine ⟨19835826755842121042135909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13223884503894747361423939 19835826755842121042135909)
              ·
                refine ⟨3719217516720397695400483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19835826755842121042135909 3719217516720397695400483)
                ·
                  refine ⟨5578826275080596543100725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719217516720397695400483 5578826275080596543100725)
                  ·
                    refine ⟨523014963288805925915693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5578826275080596543100725 523014963288805925915693)
                    ·
                      rfl

theorem cell23_3055704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_3055704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055704 prefixEnd_3055704 := by exact prefixLift 3055704
  have htrace : WordTrace (prefixWord ++ tailWord_3055704) baseStart_3055704 baseEnd_3055704 := by
    simpa [prefixWord, tailWord_3055704, baseEnd_3055704] using wordTrace_append hprefix tailTrace_3055704
  have hstable : (prefixWord ++ tailWord_3055704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055704).length < 2 ^ (prefixWord ++ tailWord_3055704).sum := by decide
  have hdescent : baseEnd_3055704 < baseStart_3055704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055735 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 1, 1, 3]
def baseStart_3055735 : Nat := 118140960795 + 3055735 * 2 ^ 59
def prefixEnd_3055735 : Nat := 4983230072969 + 3 ^ 40 * 3055735 * 2
def baseEnd_3055735 : Nat := 1569060807766707156459437

theorem tailTrace_3055735 : CollatzResearch.WordTrace tailWord_3055735 prefixEnd_3055735 1569060807766707156459437 := by
  unfold tailWord_3055735
  simp only [CollatzResearch.WordTrace]
  refine ⟨111451811584601447834280659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74301207723067631889520439 111451811584601447834280659)
  ·
    refine ⟨167177717376902171751420989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111451811584601447834280659 167177717376902171751420989)
    ·
      refine ⟨62691644016338314406782871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167177717376902171751420989 62691644016338314406782871)
      ·
        refine ⟨94037466024507471610174307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62691644016338314406782871 94037466024507471610174307)
        ·
          refine ⟨141056199036761207415261461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94037466024507471610174307 141056199036761207415261461)
          ·
            refine ⟨6612009329848181597590381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141056199036761207415261461 6612009329848181597590381)
            ·
              refine ⟨2479503498693068099096393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6612009329848181597590381 2479503498693068099096393)
              ·
                refine ⟨1859627624019801074322295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479503498693068099096393 1859627624019801074322295)
                ·
                  refine ⟨2789441436029701611483443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859627624019801074322295 2789441436029701611483443)
                  ·
                    refine ⟨4184162154044552417225165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2789441436029701611483443 4184162154044552417225165)
                    ·
                      refine ⟨1569060807766707156459437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4184162154044552417225165 1569060807766707156459437)
                      ·
                        rfl

theorem cell23_3055735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_3055735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055735 prefixEnd_3055735 := by exact prefixLift 3055735
  have htrace : WordTrace (prefixWord ++ tailWord_3055735) baseStart_3055735 baseEnd_3055735 := by
    simpa [prefixWord, tailWord_3055735, baseEnd_3055735] using wordTrace_append hprefix tailTrace_3055735
  have hstable : (prefixWord ++ tailWord_3055735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055735).length < 2 ^ (prefixWord ++ tailWord_3055735).sum := by decide
  have hdescent : baseEnd_3055735 < baseStart_3055735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055744 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_3055744 : Nat := 118140960795 + 3055744 * 2 ^ 59
def prefixEnd_3055744 : Nat := 4983230072969 + 3 ^ 40 * 3055744 * 2
def baseEnd_3055744 : Nat := 1569065429092597621246895

theorem tailTrace_3055744 : CollatzResearch.WordTrace tailWord_3055744 prefixEnd_3055744 1569065429092597621246895 := by
  unfold tailWord_3055744
  simp only [CollatzResearch.WordTrace]
  refine ⟨55726069920784421185679143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74301426561045894914238857 55726069920784421185679143)
  ·
    refine ⟨83589104881176631778518715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55726069920784421185679143 83589104881176631778518715)
    ·
      refine ⟨125383657321764947667778073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83589104881176631778518715 125383657321764947667778073)
      ·
        refine ⟨94037742991323710750833555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125383657321764947667778073 94037742991323710750833555)
        ·
          refine ⟨141056614486985566126250333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94037742991323710750833555 141056614486985566126250333)
          ·
            refine ⟨52896230432619587297343875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141056614486985566126250333 52896230432619587297343875)
            ·
              refine ⟨79344345648929380946015813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52896230432619587297343875 79344345648929380946015813)
              ·
                refine ⟨14877064809174258927377965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79344345648929380946015813 14877064809174258927377965)
                ·
                  refine ⟨5578899303440347097766737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14877064809174258927377965 5578899303440347097766737)
                  ·
                    refine ⟨4184174477580260323325053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5578899303440347097766737 4184174477580260323325053)
                    ·
                      refine ⟨1569065429092597621246895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4184174477580260323325053 1569065429092597621246895)
                      ·
                        rfl

theorem cell23_3055744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_3055744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055744 prefixEnd_3055744 := by exact prefixLift 3055744
  have htrace : WordTrace (prefixWord ++ tailWord_3055744) baseStart_3055744 baseEnd_3055744 := by
    simpa [prefixWord, tailWord_3055744, baseEnd_3055744] using wordTrace_append hprefix tailTrace_3055744
  have hstable : (prefixWord ++ tailWord_3055744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055744).length < 2 ^ (prefixWord ++ tailWord_3055744).sum := by decide
  have hdescent : baseEnd_3055744 < baseStart_3055744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055747 : List Nat := [1, 1, 1, 3, 3, 3, 1, 10]
def baseStart_3055747 : Nat := 118140960795 + 3055747 * 2 ^ 59
def prefixEnd_3055747 : Nat := 4983230072969 + 3 ^ 40 * 3055747 * 2
def baseEnd_3055747 : Nat := 58113591464243004055903

theorem tailTrace_3055747 : CollatzResearch.WordTrace tailWord_3055747 prefixEnd_3055747 58113591464243004055903 := by
  unfold tailWord_3055747
  simp only [CollatzResearch.WordTrace]
  refine ⟨111452249260557973883717495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74301499507038649255811663 111452249260557973883717495)
  ·
    refine ⟨167178373890836960825576243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111452249260557973883717495 167178373890836960825576243)
    ·
      refine ⟨250767560836255441238364365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167178373890836960825576243 250767560836255441238364365)
      ·
        refine ⟨94037835313595790464386637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250767560836255441238364365 94037835313595790464386637)
        ·
          refine ⟨35264188242598421424144989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94037835313595790464386637 35264188242598421424144989)
          ·
            refine ⟨13224070590974408034054371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35264188242598421424144989 13224070590974408034054371)
            ·
              refine ⟨19836105886461612051081557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13224070590974408034054371 19836105886461612051081557)
              ·
                refine ⟨58113591464243004055903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19836105886461612051081557 58113591464243004055903)
                ·
                  rfl

theorem cell23_3055747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 10].length) (baseStart_3055747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055747 prefixEnd_3055747 := by exact prefixLift 3055747
  have htrace : WordTrace (prefixWord ++ tailWord_3055747) baseStart_3055747 baseEnd_3055747 := by
    simpa [prefixWord, tailWord_3055747, baseEnd_3055747] using wordTrace_append hprefix tailTrace_3055747
  have hstable : (prefixWord ++ tailWord_3055747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055747).length < 2 ^ (prefixWord ++ tailWord_3055747).sum := by decide
  have hdescent : baseEnd_3055747 < baseStart_3055747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055754 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3055754 : Nat := 118140960795 + 3055754 * 2 ^ 59
def prefixEnd_3055754 : Nat := 4983230072969 + 3 ^ 40 * 3055754 * 2
def baseEnd_3055754 : Nat := 1569070563899142582121849

theorem tailTrace_3055754 : CollatzResearch.WordTrace tailWord_3055754 prefixEnd_3055754 1569070563899142582121849 := by
  unfold tailWord_3055754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27863126142883153519805579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74301669714355076052814877 27863126142883153519805579)
  ·
    refine ⟨41794689214324730279708369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27863126142883153519805579 41794689214324730279708369)
    ·
      refine ⟨31346016910743547709781277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41794689214324730279708369 31346016910743547709781277)
      ·
        refine ⟨11754756341528830391167979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31346016910743547709781277 11754756341528830391167979)
        ·
          refine ⟨17632134512293245586751969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11754756341528830391167979 17632134512293245586751969)
          ·
            refine ⟨13224100884219934190063977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17632134512293245586751969 13224100884219934190063977)
            ·
              refine ⟨9918075663164950642547983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13224100884219934190063977 9918075663164950642547983)
              ·
                refine ⟨14877113494747425963821975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9918075663164950642547983 14877113494747425963821975)
                ·
                  refine ⟨22315670242121138945732963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14877113494747425963821975 22315670242121138945732963)
                  ·
                    refine ⟨33473505363181708418599445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22315670242121138945732963 33473505363181708418599445)
                    ·
                      refine ⟨1569070563899142582121849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33473505363181708418599445 1569070563899142582121849)
                      ·
                        rfl

theorem cell23_3055754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3055754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055754 prefixEnd_3055754 := by exact prefixLift 3055754
  have htrace : WordTrace (prefixWord ++ tailWord_3055754) baseStart_3055754 baseEnd_3055754 := by
    simpa [prefixWord, tailWord_3055754, baseEnd_3055754] using wordTrace_append hprefix tailTrace_3055754
  have hstable : (prefixWord ++ tailWord_3055754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055754).length < 2 ^ (prefixWord ++ tailWord_3055754).sum := by decide
  have hdescent : baseEnd_3055754 < baseStart_3055754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055778 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3055778 : Nat := 118140960795 + 3055778 * 2 ^ 59
def prefixEnd_3055778 : Nat := 4983230072969 + 3 ^ 40 * 3055778 * 2
def baseEnd_3055778 : Nat := 1569082887434850488221739

theorem tailTrace_3055778 : CollatzResearch.WordTrace tailWord_3055778 prefixEnd_3055778 1569082887434850488221739 := by
  unfold tailWord_3055778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27863344980861416544523997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74302253282297110785397325 27863344980861416544523997)
  ·
    refine ⟨10448754367823031204196499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27863344980861416544523997 10448754367823031204196499)
    ·
      refine ⟨15673131551734546806294749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448754367823031204196499 15673131551734546806294749)
      ·
        refine ⟨5877424331900455052360531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15673131551734546806294749 5877424331900455052360531)
        ·
          refine ⟨8816136497850682578540797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877424331900455052360531 8816136497850682578540797)
          ·
            refine ⟨3306051186694005966952799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8816136497850682578540797 3306051186694005966952799)
            ·
              refine ⟨4959076780041008950429199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306051186694005966952799 4959076780041008950429199)
              ·
                refine ⟨7438615170061513425643799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959076780041008950429199 7438615170061513425643799)
                ·
                  refine ⟨11157922755092270138465699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7438615170061513425643799 11157922755092270138465699)
                  ·
                    refine ⟨16736884132638405207698549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11157922755092270138465699 16736884132638405207698549)
                    ·
                      refine ⟨1569082887434850488221739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16736884132638405207698549 1569082887434850488221739)
                      ·
                        rfl

theorem cell23_3055778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3055778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055778 prefixEnd_3055778 := by exact prefixLift 3055778
  have htrace : WordTrace (prefixWord ++ tailWord_3055778) baseStart_3055778 baseEnd_3055778 := by
    simpa [prefixWord, tailWord_3055778, baseEnd_3055778] using wordTrace_append hprefix tailTrace_3055778
  have hstable : (prefixWord ++ tailWord_3055778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055778).length < 2 ^ (prefixWord ++ tailWord_3055778).sum := by decide
  have hdescent : baseEnd_3055778 < baseStart_3055778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055786 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3055786 : Nat := 118140960795 + 3055786 * 2 ^ 59
def prefixEnd_3055786 : Nat := 4983230072969 + 3 ^ 40 * 3055786 * 2
def baseEnd_3055786 : Nat := 1569086995280086456921703

theorem tailTrace_3055786 : CollatzResearch.WordTrace tailWord_3055786 prefixEnd_3055786 1569086995280086456921703 := by
  unfold tailWord_3055786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27863417926854170886096803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74302447804944455696258141 27863417926854170886096803)
  ·
    refine ⟨41795126890281256329145205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27863417926854170886096803 41795126890281256329145205)
    ·
      refine ⟨3918293145963867780857363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41795126890281256329145205 3918293145963867780857363)
      ·
        refine ⟨5877439718945801671286045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918293145963867780857363 5877439718945801671286045)
        ·
          refine ⟨2204039894604675626732267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5877439718945801671286045 2204039894604675626732267)
          ·
            refine ⟨3306059841907013440098401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204039894604675626732267 3306059841907013440098401)
            ·
              refine ⟨2479544881430260080073801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306059841907013440098401 2479544881430260080073801)
              ·
                refine ⟨1859658661072695060055351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479544881430260080073801 1859658661072695060055351)
                ·
                  refine ⟨2789487991609042590083027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859658661072695060055351 2789487991609042590083027)
                  ·
                    refine ⟨4184231987413563885124541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2789487991609042590083027 4184231987413563885124541)
                    ·
                      refine ⟨1569086995280086456921703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4184231987413563885124541 1569086995280086456921703)
                      ·
                        rfl

theorem cell23_3055786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3055786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055786 prefixEnd_3055786 := by exact prefixLift 3055786
  have htrace : WordTrace (prefixWord ++ tailWord_3055786) baseStart_3055786 baseEnd_3055786 := by
    simpa [prefixWord, tailWord_3055786, baseEnd_3055786] using wordTrace_append hprefix tailTrace_3055786
  have hstable : (prefixWord ++ tailWord_3055786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055786).length < 2 ^ (prefixWord ++ tailWord_3055786).sum := by decide
  have hdescent : baseEnd_3055786 < baseStart_3055786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055787 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_3055787 : Nat := 118140960795 + 3055787 * 2 ^ 59
def prefixEnd_3055787 : Nat := 4983230072969 + 3 ^ 40 * 3055787 * 2
def baseEnd_3055787 : Nat := 1569087508760740953009197

theorem tailTrace_3055787 : CollatzResearch.WordTrace tailWord_3055787 prefixEnd_3055787 1569087508760740953009197 := by
  unfold tailWord_3055787
  simp only [CollatzResearch.WordTrace]
  refine ⟨111453708180413060715173615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74302472120275373810115743 111453708180413060715173615)
  ·
    refine ⟨167180562270619591072760423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111453708180413060715173615 167180562270619591072760423)
    ·
      refine ⟨250770843405929386609140635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167180562270619591072760423 250770843405929386609140635)
      ·
        refine ⟨376156265108894079913710953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250770843405929386609140635 376156265108894079913710953)
        ·
          refine ⟨282117198831670559935283215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376156265108894079913710953 282117198831670559935283215)
          ·
            refine ⟨423175798247505839902924823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282117198831670559935283215 423175798247505839902924823)
            ·
              refine ⟨634763697371258759854387235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423175798247505839902924823 634763697371258759854387235)
              ·
                refine ⟨952145546056888139781580853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634763697371258759854387235 952145546056888139781580853)
                ·
                  refine ⟨89263644942833263104523205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952145546056888139781580853 89263644942833263104523205)
                  ·
                    refine ⟨16736933426781236832098101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89263644942833263104523205 16736933426781236832098101)
                    ·
                      refine ⟨1569087508760740953009197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16736933426781236832098101 1569087508760740953009197)
                      ·
                        rfl

theorem cell23_3055787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_3055787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055787 prefixEnd_3055787 := by exact prefixLift 3055787
  have htrace : WordTrace (prefixWord ++ tailWord_3055787) baseStart_3055787 baseEnd_3055787 := by
    simpa [prefixWord, tailWord_3055787, baseEnd_3055787] using wordTrace_append hprefix tailTrace_3055787
  have hstable : (prefixWord ++ tailWord_3055787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055787).length < 2 ^ (prefixWord ++ tailWord_3055787).sum := by decide
  have hdescent : baseEnd_3055787 < baseStart_3055787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055801 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 5, 3, 2]
def baseStart_3055801 : Nat := 118140960795 + 3055801 * 2 ^ 59
def prefixEnd_3055801 : Nat := 4983230072969 + 3 ^ 40 * 3055801 * 2
def baseEnd_3055801 : Nat := 1569094697489903898234133

theorem tailTrace_3055801 : CollatzResearch.WordTrace tailWord_3055801 prefixEnd_3055801 1569094697489903898234133 := by
  unfold tailWord_3055801
  simp only [CollatzResearch.WordTrace]
  refine ⟨111454218802362341106183257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74302812534908227404122171 111454218802362341106183257)
  ·
    refine ⟨83590664101771755829637443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111454218802362341106183257 83590664101771755829637443)
    ·
      refine ⟨125385996152657633744456165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83590664101771755829637443 125385996152657633744456165)
      ·
        refine ⟨23509874278623306327085531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125385996152657633744456165 23509874278623306327085531)
        ·
          refine ⟨35264811417934959490628297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23509874278623306327085531 35264811417934959490628297)
          ·
            refine ⟨26448608563451219617971223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35264811417934959490628297 26448608563451219617971223)
            ·
              refine ⟨39672912845176829426956835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26448608563451219617971223 39672912845176829426956835)
              ·
                refine ⟨59509369267765244140435253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39672912845176829426956835 59509369267765244140435253)
                ·
                  refine ⟨5579003368852991638165805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59509369267765244140435253 5579003368852991638165805)
                  ·
                    refine ⟨2092126263319871864312177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5579003368852991638165805 2092126263319871864312177)
                    ·
                      refine ⟨1569094697489903898234133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092126263319871864312177 1569094697489903898234133)
                      ·
                        rfl

theorem cell23_3055801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_3055801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055801 prefixEnd_3055801 := by exact prefixLift 3055801
  have htrace : WordTrace (prefixWord ++ tailWord_3055801) baseStart_3055801 baseEnd_3055801 := by
    simpa [prefixWord, tailWord_3055801, baseEnd_3055801] using wordTrace_append hprefix tailTrace_3055801
  have hstable : (prefixWord ++ tailWord_3055801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055801).length < 2 ^ (prefixWord ++ tailWord_3055801).sum := by decide
  have hdescent : baseEnd_3055801 < baseStart_3055801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055808 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 2, 1, 3]
def baseStart_3055808 : Nat := 118140960795 + 3055808 * 2 ^ 59
def prefixEnd_3055808 : Nat := 4983230072969 + 3 ^ 40 * 3055808 * 2
def baseEnd_3055808 : Nat := 1569098291854485370846601

theorem tailTrace_3055808 : CollatzResearch.WordTrace tailWord_3055808 prefixEnd_3055808 1569098291854485370846601 := by
  unfold tailWord_3055808
  simp only [CollatzResearch.WordTrace]
  refine ⟨55727237056668490650844039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74302982742224654201125385 55727237056668490650844039)
  ·
    refine ⟨83590855585002735976266059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55727237056668490650844039 83590855585002735976266059)
    ·
      refine ⟨125386283377504103964399089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83590855585002735976266059 125386283377504103964399089)
      ·
        refine ⟨94039712533128077973299317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125386283377504103964399089 94039712533128077973299317)
        ·
          refine ⟨8816223049980757309996811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94039712533128077973299317 8816223049980757309996811)
          ·
            refine ⟨13224334574971135964995217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8816223049980757309996811 13224334574971135964995217)
            ·
              refine ⟨9918250931228351973746413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13224334574971135964995217 9918250931228351973746413)
              ·
                refine ⟨3719344099210631990154905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9918250931228351973746413 3719344099210631990154905)
                ·
                  refine ⟨2789508074407973992616179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3719344099210631990154905 2789508074407973992616179)
                  ·
                    refine ⟨4184262111611960988924269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2789508074407973992616179 4184262111611960988924269)
                    ·
                      refine ⟨1569098291854485370846601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4184262111611960988924269 1569098291854485370846601)
                      ·
                        rfl

theorem cell23_3055808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_3055808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055808 prefixEnd_3055808 := by exact prefixLift 3055808
  have htrace : WordTrace (prefixWord ++ tailWord_3055808) baseStart_3055808 baseEnd_3055808 := by
    simpa [prefixWord, tailWord_3055808, baseEnd_3055808] using wordTrace_append hprefix tailTrace_3055808
  have hstable : (prefixWord ++ tailWord_3055808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055808).length < 2 ^ (prefixWord ++ tailWord_3055808).sum := by decide
  have hdescent : baseEnd_3055808 < baseStart_3055808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055818 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_3055818 : Nat := 118140960795 + 3055818 * 2 ^ 59
def prefixEnd_3055818 : Nat := 4983230072969 + 3 ^ 40 * 3055818 * 2
def baseEnd_3055818 : Nat := 1569103426661030331721555

theorem tailTrace_3055818 : CollatzResearch.WordTrace tailWord_3055818 prefixEnd_3055818 1569103426661030331721555 := by
  unfold tailWord_3055818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27863709710825188252388027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74303225895533835339701405 27863709710825188252388027)
  ·
    refine ⟨41795564566237782378582041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27863709710825188252388027 41795564566237782378582041)
    ·
      refine ⟨31346673424678336783936531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41795564566237782378582041 31346673424678336783936531)
      ·
        refine ⟨47020010137017505175904797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31346673424678336783936531 47020010137017505175904797)
        ·
          refine ⟨17632503801381564440964299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47020010137017505175904797 17632503801381564440964299)
          ·
            refine ⟨26448755702072346661446449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17632503801381564440964299 26448755702072346661446449)
            ·
              refine ⟨19836566776554259996084837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26448755702072346661446449 19836566776554259996084837)
              ·
                refine ⟨3719356270603923749265907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19836566776554259996084837 3719356270603923749265907)
                ·
                  refine ⟨5579034405905885623898861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719356270603923749265907 5579034405905885623898861)
                  ·
                    refine ⟨2092137902214707108962073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5579034405905885623898861 2092137902214707108962073)
                    ·
                      refine ⟨1569103426661030331721555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092137902214707108962073 1569103426661030331721555)
                      ·
                        rfl

theorem cell23_3055818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_3055818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055818 prefixEnd_3055818 := by exact prefixLift 3055818
  have htrace : WordTrace (prefixWord ++ tailWord_3055818) baseStart_3055818 baseEnd_3055818 := by
    simpa [prefixWord, tailWord_3055818, baseEnd_3055818] using wordTrace_append hprefix tailTrace_3055818
  have hstable : (prefixWord ++ tailWord_3055818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055818).length < 2 ^ (prefixWord ++ tailWord_3055818).sum := by decide
  have hdescent : baseEnd_3055818 < baseStart_3055818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055834 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_3055834 : Nat := 118140960795 + 3055834 * 2 ^ 59
def prefixEnd_3055834 : Nat := 4983230072969 + 3 ^ 40 * 3055834 * 2
def baseEnd_3055834 : Nat := 1569111642351502269121481

theorem tailTrace_3055834 : CollatzResearch.WordTrace tailWord_3055834 prefixEnd_3055834 1569111642351502269121481 := by
  unfold tailWord_3055834
  simp only [CollatzResearch.WordTrace]
  refine ⟨27863855602810696935533639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74303614940828525161423037 27863855602810696935533639)
  ·
    refine ⟨41795783404216045403300459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27863855602810696935533639 41795783404216045403300459)
    ·
      refine ⟨62693675106324068104950689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41795783404216045403300459 62693675106324068104950689)
      ·
        refine ⟨47020256329743051078713017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62693675106324068104950689 47020256329743051078713017)
        ·
          refine ⟨35265192247307288309034763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47020256329743051078713017 35265192247307288309034763)
          ·
            refine ⟨52897788370960932463552145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35265192247307288309034763 52897788370960932463552145)
            ·
              refine ⟨39673341278220699347664109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52897788370960932463552145 39673341278220699347664109)
              ·
                refine ⟨14877502979332762255374041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39673341278220699347664109 14877502979332762255374041)
                ·
                  refine ⟨11158127234499571691530531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14877502979332762255374041 11158127234499571691530531)
                  ·
                    refine ⟨16737190851749357537295797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11158127234499571691530531 16737190851749357537295797)
                    ·
                      refine ⟨1569111642351502269121481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16737190851749357537295797 1569111642351502269121481)
                      ·
                        rfl

theorem cell23_3055834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_3055834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055834 prefixEnd_3055834 := by exact prefixLift 3055834
  have htrace : WordTrace (prefixWord ++ tailWord_3055834) baseStart_3055834 baseEnd_3055834 := by
    simpa [prefixWord, tailWord_3055834, baseEnd_3055834] using wordTrace_append hprefix tailTrace_3055834
  have hstable : (prefixWord ++ tailWord_3055834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055834).length < 2 ^ (prefixWord ++ tailWord_3055834).sum := by decide
  have hdescent : baseEnd_3055834 < baseStart_3055834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055884 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_3055884 : Nat := 118140960795 + 3055884 * 2 ^ 59
def prefixEnd_3055884 : Nat := 4983230072969 + 3 ^ 40 * 3055884 * 2
def baseEnd_3055884 : Nat := 523045772128075691165417

theorem tailTrace_3055884 : CollatzResearch.WordTrace tailWord_3055884 prefixEnd_3055884 523045772128075691165417 := by
  unfold tailWord_3055884
  simp only [CollatzResearch.WordTrace]
  refine ⟨55728623030530823140727353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74304830707374430854303137 55728623030530823140727353)
  ·
    refine ⟨41796467272898117355545515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55728623030530823140727353 41796467272898117355545515)
    ·
      refine ⟨62694700909347176033318273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41796467272898117355545515 62694700909347176033318273)
      ·
        refine ⟨47021025682010382024988705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62694700909347176033318273 47021025682010382024988705)
        ·
          refine ⟨35265769261507786518741529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47021025682010382024988705 35265769261507786518741529)
          ·
            refine ⟨26449326946130839889056147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35265769261507786518741529 26449326946130839889056147)
            ·
              refine ⟨39673990419196259833584221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26449326946130839889056147 39673990419196259833584221)
              ·
                refine ⟨14877746407198597437594083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39673990419196259833584221 14877746407198597437594083)
                ·
                  refine ⟨22316619610797896156391125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14877746407198597437594083 22316619610797896156391125)
                  ·
                    refine ⟨523045772128075691165417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22316619610797896156391125 523045772128075691165417)
                    ·
                      rfl

theorem cell23_3055884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_3055884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055884 prefixEnd_3055884 := by exact prefixLift 3055884
  have htrace : WordTrace (prefixWord ++ tailWord_3055884) baseStart_3055884 baseEnd_3055884 := by
    simpa [prefixWord, tailWord_3055884, baseEnd_3055884] using wordTrace_append hprefix tailTrace_3055884
  have hstable : (prefixWord ++ tailWord_3055884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055884).length < 2 ^ (prefixWord ++ tailWord_3055884).sum := by decide
  have hdescent : baseEnd_3055884 < baseStart_3055884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055944 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 10]
def baseStart_3055944 : Nat := 118140960795 + 3055944 * 2 ^ 59
def prefixEnd_3055944 : Nat := 4983230072969 + 3 ^ 40 * 3055944 * 2
def baseEnd_3055944 : Nat := 174352013913721870971775

theorem tailTrace_3055944 : CollatzResearch.WordTrace tailWord_3055944 prefixEnd_3055944 174352013913721870971775 := by
  unfold tailWord_3055944
  simp only [CollatzResearch.WordTrace]
  refine ⟨55729717220422138264319443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74306289627229517685759257 55729717220422138264319443)
  ·
    refine ⟨83594575830633207396479165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55729717220422138264319443 83594575830633207396479165)
    ·
      refine ⟨31347965936487452773679687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83594575830633207396479165 31347965936487452773679687)
      ·
        refine ⟨47021948904731179160519531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31347965936487452773679687 47021948904731179160519531)
        ·
          refine ⟨70532923357096768740779297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47021948904731179160519531 70532923357096768740779297)
          ·
            refine ⟨52899692517822576555584473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70532923357096768740779297 52899692517822576555584473)
            ·
              refine ⟨39674769388366932416688355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52899692517822576555584473 39674769388366932416688355)
              ·
                refine ⟨59512154082550398625032533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39674769388366932416688355 59512154082550398625032533)
                ·
                  refine ⟨174352013913721870971775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 59512154082550398625032533 174352013913721870971775)
                  ·
                    rfl

theorem cell23_3055944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_3055944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055944 prefixEnd_3055944 := by exact prefixLift 3055944
  have htrace : WordTrace (prefixWord ++ tailWord_3055944) baseStart_3055944 baseEnd_3055944 := by
    simpa [prefixWord, tailWord_3055944, baseEnd_3055944] using wordTrace_append hprefix tailTrace_3055944
  have hstable : (prefixWord ++ tailWord_3055944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055944).length < 2 ^ (prefixWord ++ tailWord_3055944).sum := by decide
  have hdescent : baseEnd_3055944 < baseStart_3055944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3055978 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_3055978 : Nat := 118140960795 + 3055978 * 2 ^ 59
def prefixEnd_3055978 : Nat := 4983230072969 + 3 ^ 40 * 3055978 * 2
def baseEnd_3055978 : Nat := 174353953729527745080091

theorem tailTrace_3055978 : CollatzResearch.WordTrace tailWord_3055978 prefixEnd_3055978 174353953729527745080091 := by
  unfold tailWord_3055978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27865168630680275083844147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74307116348480733556917725 27865168630680275083844147)
  ·
    refine ⟨41797752946020412625766221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27865168630680275083844147 41797752946020412625766221)
    ·
      refine ⟨15674157354757654734662333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41797752946020412625766221 15674157354757654734662333)
      ·
        refine ⟨5877809008034120525498375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15674157354757654734662333 5877809008034120525498375)
        ·
          refine ⟨8816713512051180788247563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877809008034120525498375 8816713512051180788247563)
          ·
            refine ⟨13225070268076771182371345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8816713512051180788247563 13225070268076771182371345)
            ·
              refine ⟨9918802701057578386778509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13225070268076771182371345 9918802701057578386778509)
              ·
                refine ⟨3719551012896591895041941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9918802701057578386778509 3719551012896591895041941)
                ·
                  refine ⟨174353953729527745080091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3719551012896591895041941 174353953729527745080091)
                  ·
                    rfl

theorem cell23_3055978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_3055978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3055978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3055978 prefixEnd_3055978 := by exact prefixLift 3055978
  have htrace : WordTrace (prefixWord ++ tailWord_3055978) baseStart_3055978 baseEnd_3055978 := by
    simpa [prefixWord, tailWord_3055978, baseEnd_3055978] using wordTrace_append hprefix tailTrace_3055978
  have hstable : (prefixWord ++ tailWord_3055978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3055978).length < 2 ^ (prefixWord ++ tailWord_3055978).sum := by decide
  have hdescent : baseEnd_3055978 < baseStart_3055978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3055978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056008 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 1, 5]
def baseStart_3056008 : Nat := 118140960795 + 3056008 * 2 ^ 59
def prefixEnd_3056008 : Nat := 4983230072969 + 3 ^ 40 * 3056008 * 2
def baseEnd_3056008 : Nat := 523066995995128196115227

theorem tailTrace_3056008 : CollatzResearch.WordTrace tailWord_3056008 prefixEnd_3056008 523066995995128196115227 := by
  unfold tailWord_3056008
  simp only [CollatzResearch.WordTrace]
  refine ⟨55730884356306207729484339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74307845808408276972645785 55730884356306207729484339)
  ·
    refine ⟨83596326534459311594226509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55730884356306207729484339 83596326534459311594226509)
    ·
      refine ⟨31348622450422241847834941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83596326534459311594226509 31348622450422241847834941)
      ·
        refine ⟨11755733418908340692938103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31348622450422241847834941 11755733418908340692938103)
        ·
          refine ⟨17633600128362511039407155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11755733418908340692938103 17633600128362511039407155)
          ·
            refine ⟨26450400192543766559110733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17633600128362511039407155 26450400192543766559110733)
            ·
              refine ⟨9918900072203912459666525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26450400192543766559110733 9918900072203912459666525)
              ·
                refine ⟨3719587527076467172374947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9918900072203912459666525 3719587527076467172374947)
                ·
                  refine ⟨5579381290614700758562421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719587527076467172374947 5579381290614700758562421)
                  ·
                    refine ⟨523066995995128196115227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5579381290614700758562421 523066995995128196115227)
                    ·
                      rfl

theorem cell23_3056008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_3056008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056008 prefixEnd_3056008 := by exact prefixLift 3056008
  have htrace : WordTrace (prefixWord ++ tailWord_3056008) baseStart_3056008 baseEnd_3056008 := by
    simpa [prefixWord, tailWord_3056008, baseEnd_3056008] using wordTrace_append hprefix tailTrace_3056008
  have hstable : (prefixWord ++ tailWord_3056008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056008).length < 2 ^ (prefixWord ++ tailWord_3056008).sum := by decide
  have hdescent : baseEnd_3056008 < baseStart_3056008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056088 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 7, 2]
def baseStart_3056088 : Nat := 118140960795 + 3056088 * 2 ^ 59
def prefixEnd_3056088 : Nat := 4983230072969 + 3 ^ 40 * 3056088 * 2
def baseEnd_3056088 : Nat := 1569242066437744275345313

theorem tailTrace_3056088 : CollatzResearch.WordTrace tailWord_3056088 prefixEnd_3056088 1569242066437744275345313 := by
  unfold tailWord_3056088
  simp only [CollatzResearch.WordTrace]
  refine ⟨55732343276161294560940459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74309791034881726081253945 55732343276161294560940459)
  ·
    refine ⟨83598514914241941841410689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55732343276161294560940459 83598514914241941841410689)
    ·
      refine ⟨62698886185681456381058017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83598514914241941841410689 62698886185681456381058017)
      ·
        refine ⟨47024164639261092285793513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62698886185681456381058017 47024164639261092285793513)
        ·
          refine ⟨35268123479445819214345135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47024164639261092285793513 35268123479445819214345135)
          ·
            refine ⟨52902185219168728821517703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35268123479445819214345135 52902185219168728821517703)
            ·
              refine ⟨79353277828753093232276555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52902185219168728821517703 79353277828753093232276555)
              ·
                refine ⟨119029916743129639848414833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79353277828753093232276555 119029916743129639848414833)
                ·
                  refine ⟨89272437557347229886311125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119029916743129639848414833 89272437557347229886311125)
                  ·
                    refine ⟨2092322755250325700460417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 89272437557347229886311125 2092322755250325700460417)
                    ·
                      refine ⟨1569242066437744275345313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092322755250325700460417 1569242066437744275345313)
                      ·
                        rfl

theorem cell23_3056088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_3056088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056088 prefixEnd_3056088 := by exact prefixLift 3056088
  have htrace : WordTrace (prefixWord ++ tailWord_3056088) baseStart_3056088 baseEnd_3056088 := by
    simpa [prefixWord, tailWord_3056088, baseEnd_3056088] using wordTrace_append hprefix tailTrace_3056088
  have hstable : (prefixWord ++ tailWord_3056088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056088).length < 2 ^ (prefixWord ++ tailWord_3056088).sum := by decide
  have hdescent : baseEnd_3056088 < baseStart_3056088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056099 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 1, 2, 3]
def baseStart_3056099 : Nat := 118140960795 + 3056099 * 2 ^ 59
def prefixEnd_3056099 : Nat := 4983230072969 + 3 ^ 40 * 3056099 * 2
def baseEnd_3056099 : Nat := 1569247714724943732307763

theorem tailTrace_3056099 : CollatzResearch.WordTrace tailWord_3056099 prefixEnd_3056099 1569247714724943732307763 := by
  unfold tailWord_3056099
  simp only [CollatzResearch.WordTrace]
  refine ⟨111465087755282738000531351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74310058503521825333687567 111465087755282738000531351)
  ·
    refine ⟨167197631632924107000797027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111465087755282738000531351 167197631632924107000797027)
    ·
      refine ⟨250796447449386160501195541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167197631632924107000797027 250796447449386160501195541)
      ·
        refine ⟨11756083474189976273493541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 250796447449386160501195541 11756083474189976273493541)
        ·
          refine ⟨2204265651410620551280039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11756083474189976273493541 2204265651410620551280039)
          ·
            refine ⟨3306398477115930826920059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204265651410620551280039 3306398477115930826920059)
            ·
              refine ⟨4959597715673896240380089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306398477115930826920059 4959597715673896240380089)
              ·
                refine ⟨3719698286755422180285067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4959597715673896240380089 3719698286755422180285067)
                ·
                  refine ⟨5579547430133133270427601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719698286755422180285067 5579547430133133270427601)
                  ·
                    refine ⟨4184660572599849952820701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5579547430133133270427601 4184660572599849952820701)
                    ·
                      refine ⟨1569247714724943732307763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4184660572599849952820701 1569247714724943732307763)
                      ·
                        rfl

theorem cell23_3056099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_3056099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056099 prefixEnd_3056099 := by exact prefixLift 3056099
  have htrace : WordTrace (prefixWord ++ tailWord_3056099) baseStart_3056099 baseEnd_3056099 := by
    simpa [prefixWord, tailWord_3056099, baseEnd_3056099] using wordTrace_append hprefix tailTrace_3056099
  have hstable : (prefixWord ++ tailWord_3056099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056099).length < 2 ^ (prefixWord ++ tailWord_3056099).sum := by decide
  have hdescent : baseEnd_3056099 < baseStart_3056099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056105 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 1, 3, 2]
def baseStart_3056105 : Nat := 118140960795 + 3056105 * 2 ^ 59
def prefixEnd_3056105 : Nat := 4983230072969 + 3 ^ 40 * 3056105 * 2
def baseEnd_3056105 : Nat := 1569250795608870708832735

theorem tailTrace_3056105 : CollatzResearch.WordTrace tailWord_3056105 prefixEnd_3056105 1569250795608870708832735 := by
  unfold tailWord_3056105
  simp only [CollatzResearch.WordTrace]
  refine ⟨111465306593261001025249769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74310204395507334016833179 111465306593261001025249769)
  ·
    refine ⟨83598979944945750768937327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111465306593261001025249769 83598979944945750768937327)
    ·
      refine ⟨125398469917418626153405991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83598979944945750768937327 125398469917418626153405991)
      ·
        refine ⟨188097704876127939230108987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125398469917418626153405991 188097704876127939230108987)
        ·
          refine ⟨282146557314191908845163481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188097704876127939230108987 282146557314191908845163481)
          ·
            refine ⟨211609917985643931633872611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282146557314191908845163481 211609917985643931633872611)
            ·
              refine ⟨317414876978465897450808917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211609917985643931633872611 317414876978465897450808917)
              ·
                refine ⟨3719705589591397235751667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 317414876978465897450808917 3719705589591397235751667)
                ·
                  refine ⟨5579558384387095853627501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719705589591397235751667 5579558384387095853627501)
                  ·
                    refine ⟨2092334394145160945110313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5579558384387095853627501 2092334394145160945110313)
                    ·
                      refine ⟨1569250795608870708832735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092334394145160945110313 1569250795608870708832735)
                      ·
                        rfl

theorem cell23_3056105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 3, 2].length) (baseStart_3056105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056105 prefixEnd_3056105 := by exact prefixLift 3056105
  have htrace : WordTrace (prefixWord ++ tailWord_3056105) baseStart_3056105 baseEnd_3056105 := by
    simpa [prefixWord, tailWord_3056105, baseEnd_3056105] using wordTrace_append hprefix tailTrace_3056105
  have hstable : (prefixWord ++ tailWord_3056105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056105).length < 2 ^ (prefixWord ++ tailWord_3056105).sum := by decide
  have hdescent : baseEnd_3056105 < baseStart_3056105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056111 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 4, 6]
def baseStart_3056111 : Nat := 118140960795 + 3056111 * 2 ^ 59
def prefixEnd_3056111 : Nat := 4983230072969 + 3 ^ 40 * 3056111 * 2
def baseEnd_3056111 : Nat := 523084625497599228452569

theorem tailTrace_3056111 : CollatzResearch.WordTrace tailWord_3056111 prefixEnd_3056111 523084625497599228452569 := by
  unfold tailWord_3056111
  simp only [CollatzResearch.WordTrace]
  refine ⟨111465525431239264049968187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74310350287492842699978791 111465525431239264049968187)
  ·
    refine ⟨167198288146858896074952281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111465525431239264049968187 167198288146858896074952281)
    ·
      refine ⟨125398716110144172056214211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167198288146858896074952281 125398716110144172056214211)
      ·
        refine ⟨188098074165216258084321317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125398716110144172056214211 188098074165216258084321317)
        ·
          refine ⟨35268388905978048390810247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188098074165216258084321317 35268388905978048390810247)
          ·
            refine ⟨52902583358967072586215371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35268388905978048390810247 52902583358967072586215371)
            ·
              refine ⟨79353875038450608879323057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52902583358967072586215371 79353875038450608879323057)
              ·
                refine ⟨59515406278837956659492293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79353875038450608879323057 59515406278837956659492293)
                ·
                  refine ⟨11159138677282116873654805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59515406278837956659492293 11159138677282116873654805)
                  ·
                    refine ⟨523084625497599228452569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11159138677282116873654805 523084625497599228452569)
                    ·
                      rfl

theorem cell23_3056111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_3056111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056111 prefixEnd_3056111 := by exact prefixLift 3056111
  have htrace : WordTrace (prefixWord ++ tailWord_3056111) baseStart_3056111 baseEnd_3056111 := by
    simpa [prefixWord, tailWord_3056111, baseEnd_3056111] using wordTrace_append hprefix tailTrace_3056111
  have hstable : (prefixWord ++ tailWord_3056111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056111).length < 2 ^ (prefixWord ++ tailWord_3056111).sum := by decide
  have hdescent : baseEnd_3056111 < baseStart_3056111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056130 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3056130 : Nat := 118140960795 + 3056130 * 2 ^ 59
def prefixEnd_3056130 : Nat := 4983230072969 + 3 ^ 40 * 3056130 * 2
def baseEnd_3056130 : Nat := 1569263632625233111020121

theorem tailTrace_3056130 : CollatzResearch.WordTrace tailWord_3056130 prefixEnd_3056130 1569263632625233111020121 := by
  unfold tailWord_3056130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27866554604542607573727461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74310812278780286863273229 27866554604542607573727461)
  ·
    refine ⟨5224978988351738920073899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27866554604542607573727461 5224978988351738920073899)
    ·
      refine ⟨7837468482527608380110849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5224978988351738920073899 7837468482527608380110849)
      ·
        refine ⟨5878101361895706285083137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7837468482527608380110849 5878101361895706285083137)
        ·
          refine ⟨4408576021421779713812353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5878101361895706285083137 4408576021421779713812353)
          ·
            refine ⟨3306432016066334785359265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4408576021421779713812353 3306432016066334785359265)
            ·
              refine ⟨2479824012049751089019449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306432016066334785359265 2479824012049751089019449)
              ·
                refine ⟨1859868009037313316764587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479824012049751089019449 1859868009037313316764587)
                ·
                  refine ⟨2789802013555969975146881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859868009037313316764587 2789802013555969975146881)
                  ·
                    refine ⟨2092351510166977481360161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789802013555969975146881 2092351510166977481360161)
                    ·
                      refine ⟨1569263632625233111020121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092351510166977481360161 1569263632625233111020121)
                      ·
                        rfl

theorem cell23_3056130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3056130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056130 prefixEnd_3056130 := by exact prefixLift 3056130
  have htrace : WordTrace (prefixWord ++ tailWord_3056130) baseStart_3056130 baseEnd_3056130 := by
    simpa [prefixWord, tailWord_3056130, baseEnd_3056130] using wordTrace_append hprefix tailTrace_3056130
  have hstable : (prefixWord ++ tailWord_3056130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056130).length < 2 ^ (prefixWord ++ tailWord_3056130).sum := by decide
  have hdescent : baseEnd_3056130 < baseStart_3056130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056138 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3056138 : Nat := 118140960795 + 3056138 * 2 ^ 59
def prefixEnd_3056138 : Nat := 4983230072969 + 3 ^ 40 * 3056138 * 2
def baseEnd_3056138 : Nat := 1569267740470469079720083

theorem tailTrace_3056138 : CollatzResearch.WordTrace tailWord_3056138 prefixEnd_3056138 1569267740470469079720083 := by
  unfold tailWord_3056138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27866627550535361915300267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74311006801427631774134045 27866627550535361915300267)
  ·
    refine ⟨41799941325803042872950401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27866627550535361915300267 41799941325803042872950401)
    ·
      refine ⟨31349955994352282154712801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41799941325803042872950401 31349955994352282154712801)
      ·
        refine ⟨23512466995764211616034601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31349955994352282154712801 23512466995764211616034601)
        ·
          refine ⟨17634350246823158712025951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23512466995764211616034601 17634350246823158712025951)
          ·
            refine ⟨26451525370234738068038927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17634350246823158712025951 26451525370234738068038927)
            ·
              refine ⟨39677288055352107102058391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26451525370234738068038927 39677288055352107102058391)
              ·
                refine ⟨59515932083028160653087587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39677288055352107102058391 59515932083028160653087587)
                ·
                  refine ⟨89273898124542240979631381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59515932083028160653087587 89273898124542240979631381)
                  ·
                    refine ⟨4184713974587917545920221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89273898124542240979631381 4184713974587917545920221)
                    ·
                      refine ⟨1569267740470469079720083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4184713974587917545920221 1569267740470469079720083)
                      ·
                        rfl

theorem cell23_3056138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3056138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056138 prefixEnd_3056138 := by exact prefixLift 3056138
  have htrace : WordTrace (prefixWord ++ tailWord_3056138) baseStart_3056138 baseEnd_3056138 := by
    simpa [prefixWord, tailWord_3056138, baseEnd_3056138] using wordTrace_append hprefix tailTrace_3056138
  have hstable : (prefixWord ++ tailWord_3056138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056138).length < 2 ^ (prefixWord ++ tailWord_3056138).sum := by decide
  have hdescent : baseEnd_3056138 < baseStart_3056138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056152 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3056152 : Nat := 118140960795 + 3056152 * 2 ^ 59
def prefixEnd_3056152 : Nat := 4983230072969 + 3 ^ 40 * 3056152 * 2
def baseEnd_3056152 : Nat := 1569274929199632024945019

theorem tailTrace_3056152 : CollatzResearch.WordTrace tailWord_3056152 prefixEnd_3056152 1569274929199632024945019 := by
  unfold tailWord_3056152
  simp only [CollatzResearch.WordTrace]
  refine ⟨55733510412045364026105355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74311347216060485368140473 55733510412045364026105355)
  ·
    refine ⟨83600265618068046039158033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55733510412045364026105355 83600265618068046039158033)
    ·
      refine ⟨62700199213551034529368525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83600265618068046039158033 62700199213551034529368525)
      ·
        refine ⟨23512574705081637948513197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62700199213551034529368525 23512574705081637948513197)
        ·
          refine ⟨8817215514405614230692449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23512574705081637948513197 8817215514405614230692449)
          ·
            refine ⟨6612911635804210673019337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8817215514405614230692449 6612911635804210673019337)
            ·
              refine ⟨4959683726853158004764503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6612911635804210673019337 4959683726853158004764503)
              ·
                refine ⟨7439525590279737007146755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959683726853158004764503 7439525590279737007146755)
                ·
                  refine ⟨11159288385419605510720133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7439525590279737007146755 11159288385419605510720133)
                  ·
                    refine ⟨2092366572266176033260025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11159288385419605510720133 2092366572266176033260025)
                    ·
                      refine ⟨1569274929199632024945019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092366572266176033260025 1569274929199632024945019)
                      ·
                        rfl

theorem cell23_3056152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3056152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056152 prefixEnd_3056152 := by exact prefixLift 3056152
  have htrace : WordTrace (prefixWord ++ tailWord_3056152) baseStart_3056152 baseEnd_3056152 := by
    simpa [prefixWord, tailWord_3056152, baseEnd_3056152] using wordTrace_append hprefix tailTrace_3056152
  have hstable : (prefixWord ++ tailWord_3056152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056152).length < 2 ^ (prefixWord ++ tailWord_3056152).sum := by decide
  have hdescent : baseEnd_3056152 < baseStart_3056152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056173 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3056173 : Nat := 118140960795 + 3056173 * 2 ^ 59
def prefixEnd_3056173 : Nat := 4983230072969 + 3 ^ 40 * 3056173 * 2
def baseEnd_3056173 : Nat := 1569285712293376442782423

theorem tailTrace_3056173 : CollatzResearch.WordTrace tailWord_3056173 prefixEnd_3056173 1569285712293376442782423 := by
  unfold tailWord_3056173
  simp only [CollatzResearch.WordTrace]
  refine ⟨111467786757014648638725173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74311857838009765759150115 111467786757014648638725173)
  ·
    refine ⟨10450105008470123309880485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111467786757014648638725173 10450105008470123309880485)
    ·
      refine ⟨1959394689088148120602591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10450105008470123309880485 1959394689088148120602591)
      ·
        refine ⟨2939092033632222180903887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959394689088148120602591 2939092033632222180903887)
        ·
          refine ⟨4408638050448333271355831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939092033632222180903887 4408638050448333271355831)
          ·
            refine ⟨6612957075672499907033747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408638050448333271355831 6612957075672499907033747)
            ·
              refine ⟨9919435613508749860550621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6612957075672499907033747 9919435613508749860550621)
              ·
                refine ⟨3719788355065781197706483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9919435613508749860550621 3719788355065781197706483)
                ·
                  refine ⟨5579682532598671796559725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719788355065781197706483 5579682532598671796559725)
                  ·
                    refine ⟨2092380949724501923709897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5579682532598671796559725 2092380949724501923709897)
                    ·
                      refine ⟨1569285712293376442782423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092380949724501923709897 1569285712293376442782423)
                      ·
                        rfl

theorem cell23_3056173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3056173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056173 prefixEnd_3056173 := by exact prefixLift 3056173
  have htrace : WordTrace (prefixWord ++ tailWord_3056173) baseStart_3056173 baseEnd_3056173 := by
    simpa [prefixWord, tailWord_3056173, baseEnd_3056173] using wordTrace_append hprefix tailTrace_3056173
  have hstable : (prefixWord ++ tailWord_3056173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056173).length < 2 ^ (prefixWord ++ tailWord_3056173).sum := by decide
  have hdescent : baseEnd_3056173 < baseStart_3056173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056205 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3056205 : Nat := 118140960795 + 3056205 * 2 ^ 59
def prefixEnd_3056205 : Nat := 4983230072969 + 3 ^ 40 * 3056205 * 2
def baseEnd_3056205 : Nat := 523100714558106772527425

theorem tailTrace_3056205 : CollatzResearch.WordTrace tailWord_3056205 prefixEnd_3056205 523100714558106772527425 := by
  unfold tailWord_3056205
  simp only [CollatzResearch.WordTrace]
  refine ⟨111468953892898718103890069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74312635928599145402593379 111468953892898718103890069)
  ·
    refine ⟨5225107213729627411119847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111468953892898718103890069 5225107213729627411119847)
    ·
      refine ⟨7837660820594441116679771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225107213729627411119847 7837660820594441116679771)
      ·
        refine ⟨11756491230891661675019657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7837660820594441116679771 11756491230891661675019657)
        ·
          refine ⟨8817368423168746256264743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11756491230891661675019657 8817368423168746256264743)
          ·
            refine ⟨13226052634753119384397115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817368423168746256264743 13226052634753119384397115)
            ·
              refine ⟨19839078952129679076595673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13226052634753119384397115 19839078952129679076595673)
              ·
                refine ⟨14879309214097259307446755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19839078952129679076595673 14879309214097259307446755)
                ·
                  refine ⟨22318963821145888961170133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14879309214097259307446755 22318963821145888961170133)
                  ·
                    refine ⟨523100714558106772527425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22318963821145888961170133 523100714558106772527425)
                    ·
                      rfl

theorem cell23_3056205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3056205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056205 prefixEnd_3056205 := by exact prefixLift 3056205
  have htrace : WordTrace (prefixWord ++ tailWord_3056205) baseStart_3056205 baseEnd_3056205 := by
    simpa [prefixWord, tailWord_3056205, baseEnd_3056205] using wordTrace_append hprefix tailTrace_3056205
  have hstable : (prefixWord ++ tailWord_3056205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056205).length < 2 ^ (prefixWord ++ tailWord_3056205).sum := by decide
  have hdescent : baseEnd_3056205 < baseStart_3056205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056208 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_3056208 : Nat := 118140960795 + 3056208 * 2 ^ 59
def prefixEnd_3056208 : Nat := 4983230072969 + 3 ^ 40 * 3056208 * 2
def baseEnd_3056208 : Nat := 1569303684116283805844761

theorem tailTrace_3056208 : CollatzResearch.WordTrace tailWord_3056208 prefixEnd_3056208 1569303684116283805844761 := by
  unfold tailWord_3056208
  simp only [CollatzResearch.WordTrace]
  refine ⟨55734531655943924808124639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74312708874591899744166185 55734531655943924808124639)
  ·
    refine ⟨83601797483915887212186959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55734531655943924808124639 83601797483915887212186959)
    ·
      refine ⟨125402696225873830818280439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83601797483915887212186959 125402696225873830818280439)
      ·
        refine ⟨188104044338810746227420659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125402696225873830818280439 188104044338810746227420659)
        ·
          refine ⟨282156066508216119341130989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188104044338810746227420659 282156066508216119341130989)
          ·
            refine ⟨105808524940581044752924121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282156066508216119341130989 105808524940581044752924121)
            ·
              refine ⟨79356393705435783564693091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105808524940581044752924121 79356393705435783564693091)
              ·
                refine ⟨119034590558153675347039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79356393705435783564693091 119034590558153675347039637)
                ·
                  refine ⟨5579746432413453531892483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119034590558153675347039637 5579746432413453531892483)
                  ·
                    refine ⟨8369619648620180297838725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5579746432413453531892483 8369619648620180297838725)
                    ·
                      refine ⟨1569303684116283805844761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8369619648620180297838725 1569303684116283805844761)
                      ·
                        rfl

theorem cell23_3056208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_3056208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056208 prefixEnd_3056208 := by exact prefixLift 3056208
  have htrace : WordTrace (prefixWord ++ tailWord_3056208) baseStart_3056208 baseEnd_3056208 := by
    simpa [prefixWord, tailWord_3056208, baseEnd_3056208] using wordTrace_append hprefix tailTrace_3056208
  have hstable : (prefixWord ++ tailWord_3056208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056208).length < 2 ^ (prefixWord ++ tailWord_3056208).sum := by decide
  have hdescent : baseEnd_3056208 < baseStart_3056208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056226 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_3056226 : Nat := 118140960795 + 3056226 * 2 ^ 59
def prefixEnd_3056226 : Nat := 4983230072969 + 3 ^ 40 * 3056226 * 2
def baseEnd_3056226 : Nat := 174368102974229415046631

theorem tailTrace_3056226 : CollatzResearch.WordTrace tailWord_3056226 prefixEnd_3056226 174368102974229415046631 := by
  unfold tailWord_3056226
  simp only [CollatzResearch.WordTrace]
  refine ⟨27867429956455659672601133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74313146550548425793603021 27867429956455659672601133)
  ·
    refine ⟨10450286233670872377225425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27867429956455659672601133 10450286233670872377225425)
    ·
      refine ⟨7837714675253154282919069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10450286233670872377225425 7837714675253154282919069)
      ·
        refine ⟨2939143003219932856094651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7837714675253154282919069 2939143003219932856094651)
        ·
          refine ⟨4408714504829899284141977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939143003219932856094651 4408714504829899284141977)
          ·
            refine ⟨3306535878622424463106483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4408714504829899284141977 3306535878622424463106483)
            ·
              refine ⟨4959803817933636694659725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306535878622424463106483 4959803817933636694659725)
              ·
                refine ⟨1859926431725113760497397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959803817933636694659725 1859926431725113760497397)
                ·
                  refine ⟨174368102974229415046631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859926431725113760497397 174368102974229415046631)
                  ·
                    rfl

theorem cell23_3056226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_3056226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056226 prefixEnd_3056226 := by exact prefixLift 3056226
  have htrace : WordTrace (prefixWord ++ tailWord_3056226) baseStart_3056226 baseEnd_3056226 := by
    simpa [prefixWord, tailWord_3056226, baseEnd_3056226] using wordTrace_append hprefix tailTrace_3056226
  have hstable : (prefixWord ++ tailWord_3056226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056226).length < 2 ^ (prefixWord ++ tailWord_3056226).sum := by decide
  have hdescent : baseEnd_3056226 < baseStart_3056226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056242 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3056242 : Nat := 118140960795 + 3056242 * 2 ^ 59
def prefixEnd_3056242 : Nat := 4983230072969 + 3 ^ 40 * 3056242 * 2
def baseEnd_3056242 : Nat := 1569321142458536672819605

theorem tailTrace_3056242 : CollatzResearch.WordTrace tailWord_3056242 prefixEnd_3056242 1569321142458536672819605 := by
  unfold tailWord_3056242
  simp only [CollatzResearch.WordTrace]
  refine ⟨27867575848441168355746745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74313535595843115615324653 27867575848441168355746745)
  ·
    refine ⟨20900681886330876266810059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27867575848441168355746745 20900681886330876266810059)
    ·
      refine ⟨31351022829496314400215089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20900681886330876266810059 31351022829496314400215089)
      ·
        refine ⟨23513267122122235800161317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31351022829496314400215089 23513267122122235800161317)
        ·
          refine ⟨4408737585397919212530247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23513267122122235800161317 4408737585397919212530247)
          ·
            refine ⟨6613106378096878818795371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408737585397919212530247 6613106378096878818795371)
            ·
              refine ⟨9919659567145318228193057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6613106378096878818795371 9919659567145318228193057)
              ·
                refine ⟨7439744675358988671144793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9919659567145318228193057 7439744675358988671144793)
                ·
                  refine ⟨5579808506519241503358595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7439744675358988671144793 5579808506519241503358595)
                  ·
                    refine ⟨8369712759778862255037893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5579808506519241503358595 8369712759778862255037893)
                    ·
                      refine ⟨1569321142458536672819605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8369712759778862255037893 1569321142458536672819605)
                      ·
                        rfl

theorem cell23_3056242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3056242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056242 prefixEnd_3056242 := by exact prefixLift 3056242
  have htrace : WordTrace (prefixWord ++ tailWord_3056242) baseStart_3056242 baseEnd_3056242 := by
    simpa [prefixWord, tailWord_3056242, baseEnd_3056242] using wordTrace_append hprefix tailTrace_3056242
  have hstable : (prefixWord ++ tailWord_3056242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056242).length < 2 ^ (prefixWord ++ tailWord_3056242).sum := by decide
  have hdescent : baseEnd_3056242 < baseStart_3056242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056252 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_3056252 : Nat := 118140960795 + 3056252 * 2 ^ 59
def prefixEnd_3056252 : Nat := 4983230072969 + 3 ^ 40 * 3056252 * 2
def baseEnd_3056252 : Nat := 523108759088360544564853

theorem tailTrace_3056252 : CollatzResearch.WordTrace tailWord_3056252 prefixEnd_3056252 523108759088360544564853 := by
  unfold tailWord_3056252
  simp only [CollatzResearch.WordTrace]
  refine ⟨55735334061864222565425505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74313778749152296753900673 55735334061864222565425505)
  ·
    refine ⟨41801500546398166924069129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55735334061864222565425505 41801500546398166924069129)
    ·
      refine ⟨31351125409798625193051847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41801500546398166924069129 31351125409798625193051847)
      ·
        refine ⟨47026688114697937789577771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31351125409798625193051847 47026688114697937789577771)
        ·
          refine ⟨70540032172046906684366657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47026688114697937789577771 70540032172046906684366657)
          ·
            refine ⟨52905024129035180013274993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70540032172046906684366657 52905024129035180013274993)
            ·
              refine ⟨39678768096776385009956245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52905024129035180013274993 39678768096776385009956245)
              ·
                refine ⟨1859942254536393047341699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39678768096776385009956245 1859942254536393047341699)
                ·
                  refine ⟨2789913381804589571012549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859942254536393047341699 2789913381804589571012549)
                  ·
                    refine ⟨523108759088360544564853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789913381804589571012549 523108759088360544564853)
                    ·
                      rfl

theorem cell23_3056252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_3056252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056252 prefixEnd_3056252 := by exact prefixLift 3056252
  have htrace : WordTrace (prefixWord ++ tailWord_3056252) baseStart_3056252 baseEnd_3056252 := by
    simpa [prefixWord, tailWord_3056252, baseEnd_3056252] using wordTrace_append hprefix tailTrace_3056252
  have hstable : (prefixWord ++ tailWord_3056252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056252).length < 2 ^ (prefixWord ++ tailWord_3056252).sum := by decide
  have hdescent : baseEnd_3056252 < baseStart_3056252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056315 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 6, 2]
def baseStart_3056315 : Nat := 118140960795 + 3056315 * 2 ^ 59
def prefixEnd_3056315 : Nat := 4983230072969 + 3 ^ 40 * 3056315 * 2
def baseEnd_3056315 : Nat := 1569358626546314887206769

theorem tailTrace_3056315 : CollatzResearch.WordTrace tailWord_3056315 prefixEnd_3056315 1569358626546314887206769 := by
  unfold tailWord_3056315
  simp only [CollatzResearch.WordTrace]
  refine ⟨111472965922500206890394399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74315310615000137926929599 111472965922500206890394399)
  ·
    refine ⟨167209448883750310335591599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111472965922500206890394399 167209448883750310335591599)
    ·
      refine ⟨250814173325625465503387399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167209448883750310335591599 250814173325625465503387399)
      ·
        refine ⟨376221259988438198255081099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250814173325625465503387399 376221259988438198255081099)
        ·
          refine ⟨564331889982657297382621649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376221259988438198255081099 564331889982657297382621649)
          ·
            refine ⟨423248917486992973036966237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564331889982657297382621649 423248917486992973036966237)
            ·
              refine ⟨158718344057622364888862339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423248917486992973036966237 158718344057622364888862339)
              ·
                refine ⟨238077516086433547333293509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158718344057622364888862339 238077516086433547333293509)
                ·
                  refine ⟨44639534266206290124992533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238077516086433547333293509 44639534266206290124992533)
                  ·
                    refine ⟨2092478168728419849609025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44639534266206290124992533 2092478168728419849609025)
                    ·
                      refine ⟨1569358626546314887206769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092478168728419849609025 1569358626546314887206769)
                      ·
                        rfl

theorem cell23_3056315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6, 2].length) (baseStart_3056315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056315 prefixEnd_3056315 := by exact prefixLift 3056315
  have htrace : WordTrace (prefixWord ++ tailWord_3056315) baseStart_3056315 baseEnd_3056315 := by
    simpa [prefixWord, tailWord_3056315, baseEnd_3056315] using wordTrace_append hprefix tailTrace_3056315
  have hstable : (prefixWord ++ tailWord_3056315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056315).length < 2 ^ (prefixWord ++ tailWord_3056315).sum := by decide
  have hdescent : baseEnd_3056315 < baseStart_3056315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056332 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3056332 : Nat := 118140960795 + 3056332 * 2 ^ 59
def prefixEnd_3056332 : Nat := 4983230072969 + 3 ^ 40 * 3056332 * 2
def baseEnd_3056332 : Nat := 1569367355717441320694191

theorem tailTrace_3056332 : CollatzResearch.WordTrace tailWord_3056332 prefixEnd_3056332 1569367355717441320694191 := by
  unfold tailWord_3056332
  simp only [CollatzResearch.WordTrace]
  refine ⟨55736792981719309396881625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74315723975625745862508833 55736792981719309396881625)
  ·
    refine ⟨41802594736289482047661219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55736792981719309396881625 41802594736289482047661219)
    ·
      refine ⟨62703892104434223071491829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41802594736289482047661219 62703892104434223071491829)
      ·
        refine ⟨5878489884790708412952359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62703892104434223071491829 5878489884790708412952359)
        ·
          refine ⟨8817734827186062619428539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878489884790708412952359 8817734827186062619428539)
          ·
            refine ⟨13226602240779093929142809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817734827186062619428539 13226602240779093929142809)
            ·
              refine ⟨9919951680584320446857107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13226602240779093929142809 9919951680584320446857107)
              ·
                refine ⟨14879927520876480670285661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9919951680584320446857107 14879927520876480670285661)
                ·
                  refine ⟨5579972820328680251357123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14879927520876480670285661 5579972820328680251357123)
                  ·
                    refine ⟨8369959230493020377035685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5579972820328680251357123 8369959230493020377035685)
                    ·
                      refine ⟨1569367355717441320694191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8369959230493020377035685 1569367355717441320694191)
                      ·
                        rfl

theorem cell23_3056332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3056332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056332 prefixEnd_3056332 := by exact prefixLift 3056332
  have htrace : WordTrace (prefixWord ++ tailWord_3056332) baseStart_3056332 baseEnd_3056332 := by
    simpa [prefixWord, tailWord_3056332, baseEnd_3056332] using wordTrace_append hprefix tailTrace_3056332
  have hstable : (prefixWord ++ tailWord_3056332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056332).length < 2 ^ (prefixWord ++ tailWord_3056332).sum := by decide
  have hdescent : baseEnd_3056332 < baseStart_3056332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056345 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_3056345 : Nat := 118140960795 + 3056345 * 2 ^ 59
def prefixEnd_3056345 : Nat := 4983230072969 + 3 ^ 40 * 3056345 * 2
def baseEnd_3056345 : Nat := 1569374030965949769831631

theorem tailTrace_3056345 : CollatzResearch.WordTrace tailWord_3056345 prefixEnd_3056345 1569374030965949769831631 := by
  unfold tailWord_3056345
  simp only [CollatzResearch.WordTrace]
  refine ⟨111474060112391522013986489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74316040074927681342657659 111474060112391522013986489)
  ·
    refine ⟨83605545084293641510489867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111474060112391522013986489 83605545084293641510489867)
    ·
      refine ⟨125408317626440462265734801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83605545084293641510489867 125408317626440462265734801)
      ·
        refine ⟨94056238219830346699301101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125408317626440462265734801 94056238219830346699301101)
        ·
          refine ⟨35271089332436380012237913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94056238219830346699301101 35271089332436380012237913)
          ·
            refine ⟨26453316999327285009178435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35271089332436380012237913 26453316999327285009178435)
            ·
              refine ⟨39679975498990927513767653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26453316999327285009178435 39679975498990927513767653)
              ·
                refine ⟨7439995406060798908831435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39679975498990927513767653 7439995406060798908831435)
                ·
                  refine ⟨11159993109091198363247153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7439995406060798908831435 11159993109091198363247153)
                  ·
                    refine ⟨8369994831818398772435365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11159993109091198363247153 8369994831818398772435365)
                    ·
                      refine ⟨1569374030965949769831631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8369994831818398772435365 1569374030965949769831631)
                      ·
                        rfl

theorem cell23_3056345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_3056345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056345 prefixEnd_3056345 := by exact prefixLift 3056345
  have htrace : WordTrace (prefixWord ++ tailWord_3056345) baseStart_3056345 baseEnd_3056345 := by
    simpa [prefixWord, tailWord_3056345, baseEnd_3056345] using wordTrace_append hprefix tailTrace_3056345
  have hstable : (prefixWord ++ tailWord_3056345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056345).length < 2 ^ (prefixWord ++ tailWord_3056345).sum := by decide
  have hdescent : baseEnd_3056345 < baseStart_3056345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056355 : List Nat := [1, 1, 1, 7, 1, 2, 10]
def baseStart_3056355 : Nat := 118140960795 + 3056355 * 2 ^ 59
def prefixEnd_3056355 : Nat := 4983230072969 + 3 ^ 40 * 3056355 * 2
def baseEnd_3056355 : Nat := 19375051429290058403785

theorem tailTrace_3056355 : CollatzResearch.WordTrace tailWord_3056355 prefixEnd_3056355 19375051429290058403785 := by
  unfold tailWord_3056355
  simp only [CollatzResearch.WordTrace]
  refine ⟨111474424842355293721850519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74316283228236862481233679 111474424842355293721850519)
  ·
    refine ⟨167211637263532940582775779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111474424842355293721850519 167211637263532940582775779)
    ·
      refine ⟨250817455895299410874163669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167211637263532940582775779 250817455895299410874163669)
      ·
        refine ⟨5878534122546079942363211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 250817455895299410874163669 5878534122546079942363211)
        ·
          refine ⟨8817801183819119913544817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878534122546079942363211 8817801183819119913544817)
          ·
            refine ⟨6613350887864339935158613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8817801183819119913544817 6613350887864339935158613)
            ·
              refine ⟨19375051429290058403785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6613350887864339935158613 19375051429290058403785)
              ·
                rfl

theorem cell23_3056355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 10].length) (baseStart_3056355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056355 prefixEnd_3056355 := by exact prefixLift 3056355
  have htrace : WordTrace (prefixWord ++ tailWord_3056355) baseStart_3056355 baseEnd_3056355 := by
    simpa [prefixWord, tailWord_3056355, baseEnd_3056355] using wordTrace_append hprefix tailTrace_3056355
  have hstable : (prefixWord ++ tailWord_3056355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056355).length < 2 ^ (prefixWord ++ tailWord_3056355).sum := by decide
  have hdescent : baseEnd_3056355 < baseStart_3056355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056366 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_3056366 : Nat := 118140960795 + 3056366 * 2 ^ 59
def prefixEnd_3056366 : Nat := 4983230072969 + 3 ^ 40 * 3056366 * 2
def baseEnd_3056366 : Nat := 1569384814059694187669035

theorem tailTrace_3056366 : CollatzResearch.WordTrace tailWord_3056366 prefixEnd_3056366 1569384814059694187669035 := by
  unfold tailWord_3056366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934353255664430325062619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74316550696876961733667301 13934353255664430325062619)
  ·
    refine ⟨20901529883496645487593929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13934353255664430325062619 20901529883496645487593929)
    ·
      refine ⟨15676147412622484115695447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20901529883496645487593929 15676147412622484115695447)
      ·
        refine ⟨23514221118933726173543171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15676147412622484115695447 23514221118933726173543171)
        ·
          refine ⟨35271331678400589260314757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23514221118933726173543171 35271331678400589260314757)
          ·
            refine ⟨6613374689700110486309017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35271331678400589260314757 6613374689700110486309017)
            ·
              refine ⟨4960031017275082864731763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613374689700110486309017 4960031017275082864731763)
              ·
                refine ⟨7440046525912624297097645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960031017275082864731763 7440046525912624297097645)
                ·
                  refine ⟨2790017447217234111411617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7440046525912624297097645 2790017447217234111411617)
                  ·
                    refine ⟨2092513085412925583558713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2790017447217234111411617 2092513085412925583558713)
                    ·
                      refine ⟨1569384814059694187669035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092513085412925583558713 1569384814059694187669035)
                      ·
                        rfl

theorem cell23_3056366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_3056366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056366 prefixEnd_3056366 := by exact prefixLift 3056366
  have htrace : WordTrace (prefixWord ++ tailWord_3056366) baseStart_3056366 baseEnd_3056366 := by
    simpa [prefixWord, tailWord_3056366, baseEnd_3056366] using wordTrace_append hprefix tailTrace_3056366
  have hstable : (prefixWord ++ tailWord_3056366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056366).length < 2 ^ (prefixWord ++ tailWord_3056366).sum := by decide
  have hdescent : baseEnd_3056366 < baseStart_3056366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056386 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3056386 : Nat := 118140960795 + 3056386 * 2 ^ 59
def prefixEnd_3056386 : Nat := 4983230072969 + 3 ^ 40 * 3056386 * 2
def baseEnd_3056386 : Nat := 1569395083672784109418943

theorem tailTrace_3056386 : CollatzResearch.WordTrace tailWord_3056386 prefixEnd_3056386 1569395083672784109418943 := by
  unfold tailWord_3056386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27868888876310746504057253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74317037003495324010819341 27868888876310746504057253)
  ·
    refine ⟨5225416664308264969510735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27868888876310746504057253 5225416664308264969510735)
    ·
      refine ⟨7838124996462397454266103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225416664308264969510735 7838124996462397454266103)
      ·
        refine ⟨11757187494693596181399155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7838124996462397454266103 11757187494693596181399155)
        ·
          refine ⟨17635781242040394272098733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757187494693596181399155 17635781242040394272098733)
          ·
            refine ⟨6613417965765147852037025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17635781242040394272098733 6613417965765147852037025)
            ·
              refine ⟨4960063474323860889027769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613417965765147852037025 4960063474323860889027769)
              ·
                refine ⟨3720047605742895666770827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4960063474323860889027769 3720047605742895666770827)
                ·
                  refine ⟨5580071408614343500156241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720047605742895666770827 5580071408614343500156241)
                  ·
                    refine ⟨4185053556460757625117181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5580071408614343500156241 4185053556460757625117181)
                    ·
                      refine ⟨1569395083672784109418943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4185053556460757625117181 1569395083672784109418943)
                      ·
                        rfl

theorem cell23_3056386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3056386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056386 prefixEnd_3056386 := by exact prefixLift 3056386
  have htrace : WordTrace (prefixWord ++ tailWord_3056386) baseStart_3056386 baseEnd_3056386 := by
    simpa [prefixWord, tailWord_3056386, baseEnd_3056386] using wordTrace_append hprefix tailTrace_3056386
  have hstable : (prefixWord ++ tailWord_3056386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056386).length < 2 ^ (prefixWord ++ tailWord_3056386).sum := by decide
  have hdescent : baseEnd_3056386 < baseStart_3056386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056425 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_3056425 : Nat := 118140960795 + 3056425 * 2 ^ 59
def prefixEnd_3056425 : Nat := 4983230072969 + 3 ^ 40 * 3056425 * 2
def baseEnd_3056425 : Nat := 1569415109418309456831263

theorem tailTrace_3056425 : CollatzResearch.WordTrace tailWord_3056425 prefixEnd_3056425 1569415109418309456831263 := by
  unfold tailWord_3056425
  simp only [CollatzResearch.WordTrace]
  refine ⟨111476977952101695676898729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74317985301401130451265819 111476977952101695676898729)
  ·
    refine ⟨83607733464076271757674047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111476977952101695676898729 83607733464076271757674047)
    ·
      refine ⟨125411600196114407636511071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83607733464076271757674047 125411600196114407636511071)
      ·
        refine ⟨188117400294171611454766607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125411600196114407636511071 188117400294171611454766607)
        ·
          refine ⟨282176100441257417182149911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188117400294171611454766607 282176100441257417182149911)
          ·
            refine ⟨423264150661886125773224867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282176100441257417182149911 423264150661886125773224867)
            ·
              refine ⟨634896225992829188659837301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423264150661886125773224867 634896225992829188659837301)
              ·
                refine ⟨59521521186827736436859747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 634896225992829188659837301 59521521186827736436859747)
                ·
                  refine ⟨89282281780241604655289621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59521521186827736436859747 89282281780241604655289621)
                  ·
                    refine ⟨4185106958448825218216701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89282281780241604655289621 4185106958448825218216701)
                    ·
                      refine ⟨1569415109418309456831263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4185106958448825218216701 1569415109418309456831263)
                      ·
                        rfl

theorem cell23_3056425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_3056425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056425 prefixEnd_3056425 := by exact prefixLift 3056425
  have htrace : WordTrace (prefixWord ++ tailWord_3056425) baseStart_3056425 baseEnd_3056425 := by
    simpa [prefixWord, tailWord_3056425, baseEnd_3056425] using wordTrace_append hprefix tailTrace_3056425
  have hstable : (prefixWord ++ tailWord_3056425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056425).length < 2 ^ (prefixWord ++ tailWord_3056425).sum := by decide
  have hdescent : baseEnd_3056425 < baseStart_3056425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056475 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 10, 5]
def baseStart_3056475 : Nat := 118140960795 + 3056475 * 2 ^ 59
def prefixEnd_3056475 : Nat := 4983230072969 + 3 ^ 40 * 3056475 * 2
def baseEnd_3056475 : Nat := 523146927817011420402011

theorem tailTrace_3056475 : CollatzResearch.WordTrace tailWord_3056475 prefixEnd_3056475 523146927817011420402011 := by
  unfold tailWord_3056475
  simp only [CollatzResearch.WordTrace]
  refine ⟨111478801601920554216218879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74319201067947036144145919 111478801601920554216218879)
  ·
    refine ⟨167218202402880831324328319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111478801601920554216218879 167218202402880831324328319)
    ·
      refine ⟨250827303604321246986492479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167218202402880831324328319 250827303604321246986492479)
      ·
        refine ⟨376240955406481870479738719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250827303604321246986492479 376240955406481870479738719)
        ·
          refine ⟨564361433109722805719608079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376240955406481870479738719 564361433109722805719608079)
          ·
            refine ⟨846542149664584208579412119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564361433109722805719608079 846542149664584208579412119)
            ·
              refine ⟨1269813224496876312869118179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846542149664584208579412119 1269813224496876312869118179)
              ·
                refine ⟨1904719836745314469303677269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269813224496876312869118179 1904719836745314469303677269)
                ·
                  refine ⟨5580233896714788484288117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1904719836745314469303677269 5580233896714788484288117)
                  ·
                    refine ⟨523146927817011420402011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5580233896714788484288117 523146927817011420402011)
                    ·
                      rfl

theorem cell23_3056475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 5].length) (baseStart_3056475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056475 prefixEnd_3056475 := by exact prefixLift 3056475
  have htrace : WordTrace (prefixWord ++ tailWord_3056475) baseStart_3056475 baseEnd_3056475 := by
    simpa [prefixWord, tailWord_3056475, baseEnd_3056475] using wordTrace_append hprefix tailTrace_3056475
  have hstable : (prefixWord ++ tailWord_3056475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056475).length < 2 ^ (prefixWord ++ tailWord_3056475).sum := by decide
  have hdescent : baseEnd_3056475 < baseStart_3056475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056512 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_3056512 : Nat := 118140960795 + 3056512 * 2 ^ 59
def prefixEnd_3056512 : Nat := 4983230072969 + 3 ^ 40 * 3056512 * 2
def baseEnd_3056512 : Nat := 1569459782235250616443363

theorem tailTrace_3056512 : CollatzResearch.WordTrace tailWord_3056512 prefixEnd_3056512 1569459782235250616443363 := by
  unfold tailWord_3056512
  simp only [CollatzResearch.WordTrace]
  refine ⟨55740075551393254767657895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74320100735191006356877193 55740075551393254767657895)
  ·
    refine ⟨83610113327089882151486843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55740075551393254767657895 83610113327089882151486843)
    ·
      refine ⟨125415169990634823227230265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83610113327089882151486843 125415169990634823227230265)
      ·
        refine ⟨94061377492976117420422699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125415169990634823227230265 94061377492976117420422699)
        ·
          refine ⟨141092066239464176130634049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94061377492976117420422699 141092066239464176130634049)
          ·
            refine ⟨105819049679598132097975537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141092066239464176130634049 105819049679598132097975537)
            ·
              refine ⟨79364287259698599073481653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105819049679598132097975537 79364287259698599073481653)
              ·
                refine ⟨7440401930596743663138905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79364287259698599073481653 7440401930596743663138905)
                ·
                  refine ⟨5580301447947557747354179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7440401930596743663138905 5580301447947557747354179)
                  ·
                    refine ⟨8370452171921336621031269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5580301447947557747354179 8370452171921336621031269)
                    ·
                      refine ⟨1569459782235250616443363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8370452171921336621031269 1569459782235250616443363)
                      ·
                        rfl

theorem cell23_3056512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_3056512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056512 prefixEnd_3056512 := by exact prefixLift 3056512
  have htrace : WordTrace (prefixWord ++ tailWord_3056512) baseStart_3056512 baseEnd_3056512 := by
    simpa [prefixWord, tailWord_3056512, baseEnd_3056512] using wordTrace_append hprefix tailTrace_3056512
  have hstable : (prefixWord ++ tailWord_3056512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056512).length < 2 ^ (prefixWord ++ tailWord_3056512).sum := by decide
  have hdescent : baseEnd_3056512 < baseStart_3056512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056546 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_3056546 : Nat := 118140960795 + 3056546 * 2 ^ 59
def prefixEnd_3056546 : Nat := 4983230072969 + 3 ^ 40 * 3056546 * 2
def baseEnd_3056546 : Nat := 1569477240577503483418207

theorem tailTrace_3056546 : CollatzResearch.WordTrace tailWord_3056546 prefixEnd_3056546 1569477240577503483418207 := by
  unfold tailWord_3056546
  simp only [CollatzResearch.WordTrace]
  refine ⟨27870347796165833335513373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74320927456442222228035661 27870347796165833335513373)
  ·
    refine ⟨10451380423562187500817515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27870347796165833335513373 10451380423562187500817515)
    ·
      refine ⟨15677070635343281251226273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10451380423562187500817515 15677070635343281251226273)
      ·
        refine ⟨11757802976507460938419705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15677070635343281251226273 11757802976507460938419705)
        ·
          refine ⟨8818352232380595703814779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11757802976507460938419705 8818352232380595703814779)
          ·
            refine ⟨13227528348570893555722169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818352232380595703814779 13227528348570893555722169)
            ·
              refine ⟨9920646261428170166791627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13227528348570893555722169 9920646261428170166791627)
              ·
                refine ⟨14880969392142255250187441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9920646261428170166791627 14880969392142255250187441)
                ·
                  refine ⟨11160727044106691437640581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14880969392142255250187441 11160727044106691437640581)
                  ·
                    refine ⟨2092636320770004644557609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11160727044106691437640581 2092636320770004644557609)
                    ·
                      refine ⟨1569477240577503483418207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092636320770004644557609 1569477240577503483418207)
                      ·
                        rfl

theorem cell23_3056546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_3056546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056546 prefixEnd_3056546 := by exact prefixLift 3056546
  have htrace : WordTrace (prefixWord ++ tailWord_3056546) baseStart_3056546 baseEnd_3056546 := by
    simpa [prefixWord, tailWord_3056546, baseEnd_3056546] using wordTrace_append hprefix tailTrace_3056546
  have hstable : (prefixWord ++ tailWord_3056546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056546).length < 2 ^ (prefixWord ++ tailWord_3056546).sum := by decide
  have hdescent : baseEnd_3056546 < baseStart_3056546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056676 : List Nat := [2, 3, 1, 4, 1, 2, 3, 7]
def baseStart_3056676 : Nat := 118140960795 + 3056676 * 2 ^ 59
def prefixEnd_3056676 : Nat := 4983230072969 + 3 ^ 40 * 3056676 * 2
def baseEnd_3056676 : Nat := 58131259002318073140467

theorem tailTrace_3056676 : CollatzResearch.WordTrace tailWord_3056676 prefixEnd_3056676 58131259002318073140467 := by
  unfold tailWord_3056676
  simp only [CollatzResearch.WordTrace]
  refine ⟨55743066337096182772142941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74324088449461577029523921 55743066337096182772142941)
  ·
    refine ⟨20903649876411068539553603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55743066337096182772142941 20903649876411068539553603)
    ·
      refine ⟨31355474814616602809330405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20903649876411068539553603 31355474814616602809330405)
      ·
        refine ⟨5879151527740613026749451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31355474814616602809330405 5879151527740613026749451)
        ·
          refine ⟨8818727291610919540124177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879151527740613026749451 8818727291610919540124177)
          ·
            refine ⟨6614045468708189655093133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8818727291610919540124177 6614045468708189655093133)
            ·
              refine ⟨2480267050765571120659925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6614045468708189655093133 2480267050765571120659925)
              ·
                refine ⟨58131259002318073140467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2480267050765571120659925 58131259002318073140467)
                ·
                  rfl

theorem cell23_3056676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 7].length) (baseStart_3056676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056676 prefixEnd_3056676 := by exact prefixLift 3056676
  have htrace : WordTrace (prefixWord ++ tailWord_3056676) baseStart_3056676 baseEnd_3056676 := by
    simpa [prefixWord, tailWord_3056676, baseEnd_3056676] using wordTrace_append hprefix tailTrace_3056676
  have hstable : (prefixWord ++ tailWord_3056676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056676).length < 2 ^ (prefixWord ++ tailWord_3056676).sum := by decide
  have hdescent : baseEnd_3056676 < baseStart_3056676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056686 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3056686 : Nat := 118140960795 + 3056686 * 2 ^ 59
def prefixEnd_3056686 : Nat := 4983230072969 + 3 ^ 40 * 3056686 * 2
def baseEnd_3056686 : Nat := 1569549127869132935667563

theorem tailTrace_3056686 : CollatzResearch.WordTrace tailWord_3056686 prefixEnd_3056686 1569549127869132935667563 := by
  unfold tailWord_3056686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13935812175519517156518739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74324331602770758168099941 13935812175519517156518739)
  ·
    refine ⟨20903718263279275734778109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13935812175519517156518739 20903718263279275734778109)
    ·
      refine ⟨7838894348729728400541791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20903718263279275734778109 7838894348729728400541791)
      ·
        refine ⟨11758341523094592600812687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7838894348729728400541791 11758341523094592600812687)
        ·
          refine ⟨17637512284641888901219031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11758341523094592600812687 17637512284641888901219031)
          ·
            refine ⟨26456268426962833351828547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17637512284641888901219031 26456268426962833351828547)
            ·
              refine ⟨39684402640444250027742821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26456268426962833351828547 39684402640444250027742821)
              ·
                refine ⟨7440825495083296880201779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39684402640444250027742821 7440825495083296880201779)
                ·
                  refine ⟨11161238242624945320302669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440825495083296880201779 11161238242624945320302669)
                  ·
                    refine ⟨4185464340984354495113501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11161238242624945320302669 4185464340984354495113501)
                    ·
                      refine ⟨1569549127869132935667563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4185464340984354495113501 1569549127869132935667563)
                      ·
                        rfl

theorem cell23_3056686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3056686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056686 prefixEnd_3056686 := by exact prefixLift 3056686
  have htrace : WordTrace (prefixWord ++ tailWord_3056686) baseStart_3056686 baseEnd_3056686 := by
    simpa [prefixWord, tailWord_3056686, baseEnd_3056686] using wordTrace_append hprefix tailTrace_3056686
  have hstable : (prefixWord ++ tailWord_3056686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056686).length < 2 ^ (prefixWord ++ tailWord_3056686).sum := by decide
  have hdescent : baseEnd_3056686 < baseStart_3056686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056743 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_3056743 : Nat := 118140960795 + 3056743 * 2 ^ 59
def prefixEnd_3056743 : Nat := 4983230072969 + 3 ^ 40 * 3056743 * 2
def baseEnd_3056743 : Nat := 1569578396266439212654801

theorem tailTrace_3056743 : CollatzResearch.WordTrace tailWord_3056743 prefixEnd_3056743 1569578396266439212654801 := by
  unfold tailWord_3056743
  simp only [CollatzResearch.WordTrace]
  refine ⟨111488576364949635986974883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74325717576633090657983255 111488576364949635986974883)
  ·
    refine ⟨167232864547424453980462325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111488576364949635986974883 167232864547424453980462325)
    ·
      refine ⟨15678081051321042560668343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167232864547424453980462325 15678081051321042560668343)
      ·
        refine ⟨23517121576981563841002515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15678081051321042560668343 23517121576981563841002515)
        ·
          refine ⟨35275682365472345761503773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23517121576981563841002515 35275682365472345761503773)
          ·
            refine ⟨13228380887052129660563915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35275682365472345761503773 13228380887052129660563915)
            ·
              refine ⟨19842571330578194490845873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13228380887052129660563915 19842571330578194490845873)
              ·
                refine ⟨14881928497933645868134405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19842571330578194490845873 14881928497933645868134405)
                ·
                  refine ⟨2790361593362558600275201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14881928497933645868134405 2790361593362558600275201)
                  ·
                    refine ⟨2092771195021918950206401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2790361593362558600275201 2092771195021918950206401)
                    ·
                      refine ⟨1569578396266439212654801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092771195021918950206401 1569578396266439212654801)
                      ·
                        rfl

theorem cell23_3056743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_3056743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056743 prefixEnd_3056743 := by exact prefixLift 3056743
  have htrace : WordTrace (prefixWord ++ tailWord_3056743) baseStart_3056743 baseEnd_3056743 := by
    simpa [prefixWord, tailWord_3056743, baseEnd_3056743] using wordTrace_append hprefix tailTrace_3056743
  have hstable : (prefixWord ++ tailWord_3056743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056743).length < 2 ^ (prefixWord ++ tailWord_3056743).sum := by decide
  have hdescent : baseEnd_3056743 < baseStart_3056743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056746 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3056746 : Nat := 118140960795 + 3056746 * 2 ^ 59
def prefixEnd_3056746 : Nat := 4983230072969 + 3 ^ 40 * 3056746 * 2
def baseEnd_3056746 : Nat := 1569579936708402700917287

theorem tailTrace_3056746 : CollatzResearch.WordTrace tailWord_3056746 prefixEnd_3056746 1569579936708402700917287 := by
  unfold tailWord_3056746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27872171445984691874833523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74325790522625844999556061 27872171445984691874833523)
  ·
    refine ⟨41808257168977037812250285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27872171445984691874833523 41808257168977037812250285)
    ·
      refine ⟨15678096438366389179593857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41808257168977037812250285 15678096438366389179593857)
      ·
        refine ⟨11758572328774791884695393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15678096438366389179593857 11758572328774791884695393)
        ·
          refine ⟨8818929246581093913521545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11758572328774791884695393 8818929246581093913521545)
          ·
            refine ⟨6614196934935820435141159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8818929246581093913521545 6614196934935820435141159)
            ·
              refine ⟨9921295402403730652711739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614196934935820435141159 9921295402403730652711739)
              ·
                refine ⟨14881943103605595979067609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9921295402403730652711739 14881943103605595979067609)
                ·
                  refine ⟨11161457327704196984300707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14881943103605595979067609 11161457327704196984300707)
                  ·
                    refine ⟨16742185991556295476451061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11161457327704196984300707 16742185991556295476451061)
                    ·
                      refine ⟨1569579936708402700917287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16742185991556295476451061 1569579936708402700917287)
                      ·
                        rfl

theorem cell23_3056746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3056746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056746 prefixEnd_3056746 := by exact prefixLift 3056746
  have htrace : WordTrace (prefixWord ++ tailWord_3056746) baseStart_3056746 baseEnd_3056746 := by
    simpa [prefixWord, tailWord_3056746, baseEnd_3056746] using wordTrace_append hprefix tailTrace_3056746
  have hstable : (prefixWord ++ tailWord_3056746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056746).length < 2 ^ (prefixWord ++ tailWord_3056746).sum := by decide
  have hdescent : baseEnd_3056746 < baseStart_3056746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056777 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 2, 2, 2]
def baseStart_3056777 : Nat := 118140960795 + 3056777 * 2 ^ 59
def prefixEnd_3056777 : Nat := 4983230072969 + 3 ^ 40 * 3056777 * 2
def baseEnd_3056777 : Nat := 1569595854608692079629645

theorem tailTrace_3056777 : CollatzResearch.WordTrace tailWord_3056777 prefixEnd_3056777 1569595854608692079629645 := by
  unfold tailWord_3056777
  simp only [CollatzResearch.WordTrace]
  refine ⟨111489816446826459793712585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74326544297884306529141723 111489816446826459793712585)
  ·
    refine ⟨83617362335119844845284439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111489816446826459793712585 83617362335119844845284439)
    ·
      refine ⟨125426043502679767267926659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83617362335119844845284439 125426043502679767267926659)
      ·
        refine ⟨188139065254019650901889989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125426043502679767267926659 188139065254019650901889989)
        ·
          refine ⟨35276074735128684544104373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188139065254019650901889989 35276074735128684544104373)
          ·
            refine ⟨3307132006418314176009785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35276074735128684544104373 3307132006418314176009785)
            ·
              refine ⟨2480349004813735632007339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3307132006418314176009785 2480349004813735632007339)
              ·
                refine ⟨3720523507220603448011009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480349004813735632007339 3720523507220603448011009)
                ·
                  refine ⟨2790392630415452586008257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720523507220603448011009 2790392630415452586008257)
                  ·
                    refine ⟨2092794472811589439506193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2790392630415452586008257 2092794472811589439506193)
                    ·
                      refine ⟨1569595854608692079629645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092794472811589439506193 1569595854608692079629645)
                      ·
                        rfl

theorem cell23_3056777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 2, 2].length) (baseStart_3056777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056777 prefixEnd_3056777 := by exact prefixLift 3056777
  have htrace : WordTrace (prefixWord ++ tailWord_3056777) baseStart_3056777 baseEnd_3056777 := by
    simpa [prefixWord, tailWord_3056777, baseEnd_3056777] using wordTrace_append hprefix tailTrace_3056777
  have hstable : (prefixWord ++ tailWord_3056777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056777).length < 2 ^ (prefixWord ++ tailWord_3056777).sum := by decide
  have hdescent : baseEnd_3056777 < baseStart_3056777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056796 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_3056796 : Nat := 118140960795 + 3056796 * 2 ^ 59
def prefixEnd_3056796 : Nat := 4983230072969 + 3 ^ 40 * 3056796 * 2
def baseEnd_3056796 : Nat := 523201870247042501764019

theorem tailTrace_3056796 : CollatzResearch.WordTrace tailWord_3056796 prefixEnd_3056796 523201870247042501764019 := by
  unfold tailWord_3056796
  simp only [CollatzResearch.WordTrace]
  refine ⟨55745254716878813019327121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74327006289171750692436161 55745254716878813019327121)
  ·
    refine ⟨41808941037659109764495341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55745254716878813019327121 41808941037659109764495341)
    ·
      refine ⟨15678352889122166161685753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41808941037659109764495341 15678352889122166161685753)
      ·
        refine ⟨11758764666841624621264315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15678352889122166161685753 11758764666841624621264315)
        ·
          refine ⟨17638147000262436931896473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11758764666841624621264315 17638147000262436931896473)
          ·
            refine ⟨13228610250196827698922355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17638147000262436931896473 13228610250196827698922355)
            ·
              refine ⟨19842915375295241548383533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13228610250196827698922355 19842915375295241548383533)
              ·
                refine ⟨7441093265735715580643825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19842915375295241548383533 7441093265735715580643825)
                ·
                  refine ⟨5580819949301786685482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7441093265735715580643825 5580819949301786685482869)
                  ·
                    refine ⟨523201870247042501764019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5580819949301786685482869 523201870247042501764019)
                    ·
                      rfl

theorem cell23_3056796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_3056796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056796 prefixEnd_3056796 := by exact prefixLift 3056796
  have htrace : WordTrace (prefixWord ++ tailWord_3056796) baseStart_3056796 baseEnd_3056796 := by
    simpa [prefixWord, tailWord_3056796, baseEnd_3056796] using wordTrace_append hprefix tailTrace_3056796
  have hstable : (prefixWord ++ tailWord_3056796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056796).length < 2 ^ (prefixWord ++ tailWord_3056796).sum := by decide
  have hdescent : baseEnd_3056796 < baseStart_3056796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056816 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 4, 4, 2]
def baseStart_3056816 : Nat := 118140960795 + 3056816 * 2 ^ 59
def prefixEnd_3056816 : Nat := 4983230072969 + 3 ^ 40 * 3056816 * 2
def baseEnd_3056816 : Nat := 1569615880354217427041965

theorem tailTrace_3056816 : CollatzResearch.WordTrace tailWord_3056816 prefixEnd_3056816 1569615880354217427041965 := by
  unfold tailWord_3056816
  simp only [CollatzResearch.WordTrace]
  refine ⟨55745619446842584727191151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74327492595790112969588201 55745619446842584727191151)
  ·
    refine ⟨83618429170263877090786727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55745619446842584727191151 83618429170263877090786727)
    ·
      refine ⟨125427643755395815636180091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83618429170263877090786727 125427643755395815636180091)
      ·
        refine ⟨188141465633093723454270137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125427643755395815636180091 188141465633093723454270137)
        ·
          refine ⟨141106099224820292590702603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188141465633093723454270137 141106099224820292590702603)
          ·
            refine ⟨211659148837230438886053905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141106099224820292590702603 211659148837230438886053905)
            ·
              refine ⟨158744361627922829164540429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211659148837230438886053905 158744361627922829164540429)
              ·
                refine ⟨59529135610471060936702661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158744361627922829164540429 59529135610471060936702661)
                ·
                  refine ⟨11161712926963323925631749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59529135610471060936702661 11161712926963323925631749)
                  ·
                    refine ⟨2092821173805623236055953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11161712926963323925631749 2092821173805623236055953)
                    ·
                      refine ⟨1569615880354217427041965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2092821173805623236055953 1569615880354217427041965)
                      ·
                        rfl

theorem cell23_3056816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 4, 2].length) (baseStart_3056816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056816 prefixEnd_3056816 := by exact prefixLift 3056816
  have htrace : WordTrace (prefixWord ++ tailWord_3056816) baseStart_3056816 baseEnd_3056816 := by
    simpa [prefixWord, tailWord_3056816, baseEnd_3056816] using wordTrace_append hprefix tailTrace_3056816
  have hstable : (prefixWord ++ tailWord_3056816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056816).length < 2 ^ (prefixWord ++ tailWord_3056816).sum := by decide
  have hdescent : baseEnd_3056816 < baseStart_3056816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056826 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_3056826 : Nat := 118140960795 + 3056826 * 2 ^ 59
def prefixEnd_3056826 : Nat := 4983230072969 + 3 ^ 40 * 3056826 * 2
def baseEnd_3056826 : Nat := 523207005053587462638973

theorem tailTrace_3056826 : CollatzResearch.WordTrace tailWord_3056826 prefixEnd_3056826 523207005053587462638973 := by
  unfold tailWord_3056826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27872900905912235290561583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74327735749099294108164221 27872900905912235290561583)
  ·
    refine ⟨41809351358868352935842375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27872900905912235290561583 41809351358868352935842375)
    ·
      refine ⟨62714027038302529403763563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41809351358868352935842375 62714027038302529403763563)
      ·
        refine ⟨94071040557453794105645345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62714027038302529403763563 94071040557453794105645345)
        ·
          refine ⟨70553280418090345579234009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94071040557453794105645345 70553280418090345579234009)
          ·
            refine ⟨52914960313567759184425507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70553280418090345579234009 52914960313567759184425507)
            ·
              refine ⟨79372440470351638776638261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52914960313567759184425507 79372440470351638776638261)
              ·
                refine ⟨7441166294095466135309837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79372440470351638776638261 7441166294095466135309837)
                ·
                  refine ⟨2790437360285799800741189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7441166294095466135309837 2790437360285799800741189)
                  ·
                    refine ⟨523207005053587462638973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790437360285799800741189 523207005053587462638973)
                    ·
                      rfl

theorem cell23_3056826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_3056826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056826 prefixEnd_3056826 := by exact prefixLift 3056826
  have htrace : WordTrace (prefixWord ++ tailWord_3056826) baseStart_3056826 baseEnd_3056826 := by
    simpa [prefixWord, tailWord_3056826, baseEnd_3056826] using wordTrace_append hprefix tailTrace_3056826
  have hstable : (prefixWord ++ tailWord_3056826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056826).length < 2 ^ (prefixWord ++ tailWord_3056826).sum := by decide
  have hdescent : baseEnd_3056826 < baseStart_3056826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056853 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3056853 : Nat := 118140960795 + 3056853 * 2 ^ 59
def prefixEnd_3056853 : Nat := 4983230072969 + 3 ^ 40 * 3056853 * 2
def baseEnd_3056853 : Nat := 1569634879138433782279295

theorem tailTrace_3056853 : CollatzResearch.WordTrace tailWord_3056853 prefixEnd_3056853 1569634879138433782279295 := by
  unfold tailWord_3056853
  simp only [CollatzResearch.WordTrace]
  refine ⟨111492588394551124773479213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74328392263034083182319475 111492588394551124773479213)
  ·
    refine ⟨41809720647956671790054705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111492588394551124773479213 41809720647956671790054705)
    ·
      refine ⟨31357290485967503842541029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41809720647956671790054705 31357290485967503842541029)
      ·
        refine ⟨5879491966118906970476443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31357290485967503842541029 5879491966118906970476443)
        ·
          refine ⟨8819237949178360455714665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879491966118906970476443 8819237949178360455714665)
          ·
            refine ⟨6614428461883770341785999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8819237949178360455714665 6614428461883770341785999)
            ·
              refine ⟨9921642692825655512678999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614428461883770341785999 9921642692825655512678999)
              ·
                refine ⟨14882464039238483269018499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9921642692825655512678999 14882464039238483269018499)
                ·
                  refine ⟨22323696058857724903527749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14882464039238483269018499 22323696058857724903527749)
                  ·
                    refine ⟨4185693011035823419411453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22323696058857724903527749 4185693011035823419411453)
                    ·
                      refine ⟨1569634879138433782279295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4185693011035823419411453 1569634879138433782279295)
                      ·
                        rfl

theorem cell23_3056853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3056853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056853 prefixEnd_3056853 := by exact prefixLift 3056853
  have htrace : WordTrace (prefixWord ++ tailWord_3056853) baseStart_3056853 baseEnd_3056853 := by
    simpa [prefixWord, tailWord_3056853, baseEnd_3056853] using wordTrace_append hprefix tailTrace_3056853
  have hstable : (prefixWord ++ tailWord_3056853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056853).length < 2 ^ (prefixWord ++ tailWord_3056853).sum := by decide
  have hdescent : baseEnd_3056853 < baseStart_3056853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056883 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 3]
def baseStart_3056883 : Nat := 118140960795 + 3056883 * 2 ^ 59
def prefixEnd_3056883 : Nat := 4983230072969 + 3 ^ 40 * 3056883 * 2
def baseEnd_3056883 : Nat := 1569650283558068664904157

theorem tailTrace_3056883 : CollatzResearch.WordTrace tailWord_3056883 prefixEnd_3056883 1569650283558068664904157 := by
  unfold tailWord_3056883
  simp only [CollatzResearch.WordTrace]
  refine ⟨111493682584442439897071303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74329121722961626598047535 111493682584442439897071303)
  ·
    refine ⟨167240523876663659845606955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111493682584442439897071303 167240523876663659845606955)
    ·
      refine ⟨250860785814995489768410433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167240523876663659845606955 250860785814995489768410433)
      ·
        refine ⟨188145589361246617326307825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250860785814995489768410433 188145589361246617326307825)
        ·
          refine ⟨141109192020934962994730869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188145589361246617326307825 141109192020934962994730869)
          ·
            refine ⟨13228986751962652780756019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141109192020934962994730869 13228986751962652780756019)
            ·
              refine ⟨19843480127943979171134029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13228986751962652780756019 19843480127943979171134029)
              ·
                refine ⟨7441305047978992189175261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19843480127943979171134029 7441305047978992189175261)
                ·
                  refine ⟨2790489392992122070940723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7441305047978992189175261 2790489392992122070940723)
                  ·
                    refine ⟨4185734089488183106411085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2790489392992122070940723 4185734089488183106411085)
                    ·
                      refine ⟨1569650283558068664904157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4185734089488183106411085 1569650283558068664904157)
                      ·
                        rfl

theorem cell23_3056883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_3056883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056883 prefixEnd_3056883 := by exact prefixLift 3056883
  have htrace : WordTrace (prefixWord ++ tailWord_3056883) baseStart_3056883 baseEnd_3056883 := by
    simpa [prefixWord, tailWord_3056883, baseEnd_3056883] using wordTrace_append hprefix tailTrace_3056883
  have hstable : (prefixWord ++ tailWord_3056883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056883).length < 2 ^ (prefixWord ++ tailWord_3056883).sum := by decide
  have hdescent : baseEnd_3056883 < baseStart_3056883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056900 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3056900 : Nat := 118140960795 + 3056900 * 2 ^ 59
def prefixEnd_3056900 : Nat := 4983230072969 + 3 ^ 40 * 3056900 * 2
def baseEnd_3056900 : Nat := 1569659012729195098391579

theorem tailTrace_3056900 : CollatzResearch.WordTrace tailWord_3056900 prefixEnd_3056900 1569659012729195098391579 := by
  unfold tailWord_3056900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55747151312690425900220077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74329535083587234533626769 55747151312690425900220077)
  ·
    refine ⟨20905181742258909712582529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55747151312690425900220077 20905181742258909712582529)
    ·
      refine ⟨15678886306694182284436897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20905181742258909712582529 15678886306694182284436897)
      ·
        refine ⟨11759164730020636713327673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15678886306694182284436897 11759164730020636713327673)
        ·
          refine ⟨8819373547515477534995755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11759164730020636713327673 8819373547515477534995755)
          ·
            refine ⟨13229060321273216302493633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819373547515477534995755 13229060321273216302493633)
            ·
              refine ⟨9921795240954912226870225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13229060321273216302493633 9921795240954912226870225)
              ·
                refine ⟨7441346430716184170152669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9921795240954912226870225 7441346430716184170152669)
                ·
                  refine ⟨2790504911518569063807251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7441346430716184170152669 2790504911518569063807251)
                  ·
                    refine ⟨4185757367277853595710877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2790504911518569063807251 4185757367277853595710877)
                    ·
                      refine ⟨1569659012729195098391579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4185757367277853595710877 1569659012729195098391579)
                      ·
                        rfl

theorem cell23_3056900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3056900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056900 prefixEnd_3056900 := by exact prefixLift 3056900
  have htrace : WordTrace (prefixWord ++ tailWord_3056900) baseStart_3056900 baseEnd_3056900 := by
    simpa [prefixWord, tailWord_3056900, baseEnd_3056900] using wordTrace_append hprefix tailTrace_3056900
  have hstable : (prefixWord ++ tailWord_3056900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056900).length < 2 ^ (prefixWord ++ tailWord_3056900).sum := by decide
  have hdescent : baseEnd_3056900 < baseStart_3056900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056933 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_3056933 : Nat := 118140960795 + 3056933 * 2 ^ 59
def prefixEnd_3056933 : Nat := 4983230072969 + 3 ^ 40 * 3056933 * 2
def baseEnd_3056933 : Nat := 523225319196931156426309

theorem tailTrace_3056933 : CollatzResearch.WordTrace tailWord_3056933 prefixEnd_3056933 523225319196931156426309 := by
  unfold tailWord_3056933
  simp only [CollatzResearch.WordTrace]
  refine ⟨111495506234261298436391453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74330337489507532290927635 111495506234261298436391453)
  ·
    refine ⟨41810814837847986913646795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111495506234261298436391453 41810814837847986913646795)
    ·
      refine ⟨62716222256771980370470193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41810814837847986913646795 62716222256771980370470193)
      ·
        refine ⟨47037166692578985277852645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62716222256771980370470193 47037166692578985277852645)
        ·
          refine ⟨8819468754858559739597371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47037166692578985277852645 8819468754858559739597371)
          ·
            refine ⟨13229203132287839609396057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819468754858559739597371 13229203132287839609396057)
            ·
              refine ⟨9921902349215879707047043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13229203132287839609396057 9921902349215879707047043)
              ·
                refine ⟨14882853523823819560570565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9921902349215879707047043 14882853523823819560570565)
                ·
                  refine ⟨2790535035716966167606981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14882853523823819560570565 2790535035716966167606981)
                  ·
                    refine ⟨523225319196931156426309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790535035716966167606981 523225319196931156426309)
                    ·
                      rfl

theorem cell23_3056933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_3056933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056933 prefixEnd_3056933 := by exact prefixLift 3056933
  have htrace : WordTrace (prefixWord ++ tailWord_3056933) baseStart_3056933 baseEnd_3056933 := by
    simpa [prefixWord, tailWord_3056933, baseEnd_3056933] using wordTrace_append hprefix tailTrace_3056933
  have hstable : (prefixWord ++ tailWord_3056933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056933).length < 2 ^ (prefixWord ++ tailWord_3056933).sum := by decide
  have hdescent : baseEnd_3056933 < baseStart_3056933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056946 : List Nat := [3, 2, 1, 1, 4, 1, 1, 10]
def baseStart_3056946 : Nat := 118140960795 + 3056946 * 2 ^ 59
def prefixEnd_3056946 : Nat := 4983230072969 + 3 ^ 40 * 3056946 * 2
def baseEnd_3056946 : Nat := 58136393808863034015421

theorem tailTrace_3056946 : CollatzResearch.WordTrace tailWord_3056946 prefixEnd_3056946 58136393808863034015421 := by
  unfold tailWord_3056946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27873995095803550414153673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74330653588809467771076461 27873995095803550414153673)
  ·
    refine ⟨20905496321852662810615255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27873995095803550414153673 20905496321852662810615255)
    ·
      refine ⟨31358244482778994215922883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20905496321852662810615255 31358244482778994215922883)
      ·
        refine ⟨47037366724168491323884325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31358244482778994215922883 47037366724168491323884325)
        ·
          refine ⟨8819506260781592123228311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47037366724168491323884325 8819506260781592123228311)
          ·
            refine ⟨13229259391172388184842467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819506260781592123228311 13229259391172388184842467)
            ·
              refine ⟨19843889086758582277263701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13229259391172388184842467 19843889086758582277263701)
              ·
                refine ⟨58136393808863034015421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19843889086758582277263701 58136393808863034015421)
                ·
                  rfl

theorem cell23_3056946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_3056946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056946 prefixEnd_3056946 := by exact prefixLift 3056946
  have htrace : WordTrace (prefixWord ++ tailWord_3056946) baseStart_3056946 baseEnd_3056946 := by
    simpa [prefixWord, tailWord_3056946, baseEnd_3056946] using wordTrace_append hprefix tailTrace_3056946
  have hstable : (prefixWord ++ tailWord_3056946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056946).length < 2 ^ (prefixWord ++ tailWord_3056946).sum := by decide
  have hdescent : baseEnd_3056946 < baseStart_3056946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3056986 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_3056986 : Nat := 118140960795 + 3056986 * 2 ^ 59
def prefixEnd_3056986 : Nat := 4983230072969 + 3 ^ 40 * 3056986 * 2
def baseEnd_3056986 : Nat := 1569703172065481761916183

theorem tailTrace_3056986 : CollatzResearch.WordTrace tailWord_3056986 prefixEnd_3056986 1569703172065481761916183 := by
  unfold tailWord_3056986
  simp only [CollatzResearch.WordTrace]
  refine ⟨27874359825767322122017703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74331626202046192325380541 27874359825767322122017703)
  ·
    refine ⟨41811539738650983183026555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27874359825767322122017703 41811539738650983183026555)
    ·
      refine ⟨62717309607976474774539833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41811539738650983183026555 62717309607976474774539833)
      ·
        refine ⟨47037982205982356080904875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62717309607976474774539833 47037982205982356080904875)
        ·
          refine ⟨70556973308973534121357313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47037982205982356080904875 70556973308973534121357313)
          ·
            refine ⟨52917729981730150591017985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70556973308973534121357313 52917729981730150591017985)
            ·
              refine ⟨39688297486297612943263489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52917729981730150591017985 39688297486297612943263489)
              ·
                refine ⟨29766223114723209707447617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39688297486297612943263489 29766223114723209707447617)
                ·
                  refine ⟨22324667336042407280585713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29766223114723209707447617 22324667336042407280585713)
                  ·
                    refine ⟨16743500502031805460439285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22324667336042407280585713 16743500502031805460439285)
                    ·
                      refine ⟨1569703172065481761916183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16743500502031805460439285 1569703172065481761916183)
                      ·
                        rfl

theorem cell23_3056986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_3056986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3056986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3056986 prefixEnd_3056986 := by exact prefixLift 3056986
  have htrace : WordTrace (prefixWord ++ tailWord_3056986) baseStart_3056986 baseEnd_3056986 := by
    simpa [prefixWord, tailWord_3056986, baseEnd_3056986] using wordTrace_append hprefix tailTrace_3056986
  have hstable : (prefixWord ++ tailWord_3056986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3056986).length < 2 ^ (prefixWord ++ tailWord_3056986).sum := by decide
  have hdescent : baseEnd_3056986 < baseStart_3056986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3056986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057036 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 9]
def baseStart_3057036 : Nat := 118140960795 + 3057036 * 2 ^ 59
def prefixEnd_3057036 : Nat := 4983230072969 + 3 ^ 40 * 3057036 * 2
def baseEnd_3057036 : Nat := 174414316233134062921217

theorem tailTrace_3057036 : CollatzResearch.WordTrace tailWord_3057036 prefixEnd_3057036 174414316233134062921217 := by
  unfold tailWord_3057036
  simp only [CollatzResearch.WordTrace]
  refine ⟨55749631476444073513695481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74332841968592098018260641 55749631476444073513695481)
  ·
    refine ⟨41812223607333055135271611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55749631476444073513695481 41812223607333055135271611)
    ·
      refine ⟨62718335410999582702907417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41812223607333055135271611 62718335410999582702907417)
      ·
        refine ⟨47038751558249687027180563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62718335410999582702907417 47038751558249687027180563)
        ·
          refine ⟨70558127337374530540770845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47038751558249687027180563 70558127337374530540770845)
          ·
            refine ⟨26459297751515448952789067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70558127337374530540770845 26459297751515448952789067)
            ·
              refine ⟨39688946627273173429183601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26459297751515448952789067 39688946627273173429183601)
              ·
                refine ⟨29766709970454880071887701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39688946627273173429183601 29766709970454880071887701)
                ·
                  refine ⟨174414316233134062921217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29766709970454880071887701 174414316233134062921217)
                  ·
                    rfl

theorem cell23_3057036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_3057036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057036 prefixEnd_3057036 := by exact prefixLift 3057036
  have htrace : WordTrace (prefixWord ++ tailWord_3057036) baseStart_3057036 baseEnd_3057036 := by
    simpa [prefixWord, tailWord_3057036, baseEnd_3057036] using wordTrace_append hprefix tailTrace_3057036
  have hstable : (prefixWord ++ tailWord_3057036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057036).length < 2 ^ (prefixWord ++ tailWord_3057036).sum := by decide
  have hdescent : baseEnd_3057036 < baseStart_3057036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057053 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 7]
def baseStart_3057053 : Nat := 118140960795 + 3057053 * 2 ^ 59
def prefixEnd_3057053 : Nat := 4983230072969 + 3 ^ 40 * 3057053 * 2
def baseEnd_3057053 : Nat := 174415286141036999975375

theorem tailTrace_3057053 : CollatzResearch.WordTrace tailWord_3057053 prefixEnd_3057053 174415286141036999975375 := by
  unfold tailWord_3057053
  simp only [CollatzResearch.WordTrace]
  refine ⟨111499882993826558930759813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74333255329217705953839875 111499882993826558930759813)
  ·
    refine ⟨20906228061342479799517465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111499882993826558930759813 20906228061342479799517465)
    ·
      refine ⟨15679671046006859849638099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20906228061342479799517465 15679671046006859849638099)
      ·
        refine ⟨23519506569010289774457149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15679671046006859849638099 23519506569010289774457149)
        ·
          refine ⟨8819814963378858665421431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23519506569010289774457149 8819814963378858665421431)
          ·
            refine ⟨13229722445068287998132147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819814963378858665421431 13229722445068287998132147)
            ·
              refine ⟨19844583667602431997198221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13229722445068287998132147 19844583667602431997198221)
              ·
                refine ⟨7441718875350911998949333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19844583667602431997198221 7441718875350911998949333)
                ·
                  refine ⟨174415286141036999975375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7441718875350911998949333 174415286141036999975375)
                  ·
                    rfl

theorem cell23_3057053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_3057053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057053 prefixEnd_3057053 := by exact prefixLift 3057053
  have htrace : WordTrace (prefixWord ++ tailWord_3057053) baseStart_3057053 baseEnd_3057053 := by
    simpa [prefixWord, tailWord_3057053, baseEnd_3057053] using wordTrace_append hprefix tailTrace_3057053
  have hstable : (prefixWord ++ tailWord_3057053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057053).length < 2 ^ (prefixWord ++ tailWord_3057053).sum := by decide
  have hdescent : baseEnd_3057053 < baseStart_3057053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057100 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_3057100 : Nat := 118140960795 + 3057100 * 2 ^ 59
def prefixEnd_3057100 : Nat := 4983230072969 + 3 ^ 40 * 3057100 * 2
def baseEnd_3057100 : Nat := 523253902953364771963553

theorem tailTrace_3057100 : CollatzResearch.WordTrace tailWord_3057100 prefixEnd_3057100 523253902953364771963553 := by
  unfold tailWord_3057100
  simp only [CollatzResearch.WordTrace]
  refine ⟨55750798612328142978860377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74334398149770857305147169 55750798612328142978860377)
  ·
    refine ⟨41813098959246107234145283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55750798612328142978860377 41813098959246107234145283)
    ·
      refine ⟨62719648438869160851217925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41813098959246107234145283 62719648438869160851217925)
      ·
        refine ⟨11759934082287967659603361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62719648438869160851217925 11759934082287967659603361)
        ·
          refine ⟨8819950561715975744702521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11759934082287967659603361 8819950561715975744702521)
          ·
            refine ⟨6614962921286981808526891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8819950561715975744702521 6614962921286981808526891)
            ·
              refine ⟨9922444381930472712790337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614962921286981808526891 9922444381930472712790337)
              ·
                refine ⟨7441833286447854534592753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9922444381930472712790337 7441833286447854534592753)
                ·
                  refine ⟨5581374964835890900944565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7441833286447854534592753 5581374964835890900944565)
                  ·
                    refine ⟨523253902953364771963553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5581374964835890900944565 523253902953364771963553)
                    ·
                      rfl

theorem cell23_3057100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_3057100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057100 prefixEnd_3057100 := by exact prefixLift 3057100
  have htrace : WordTrace (prefixWord ++ tailWord_3057100) baseStart_3057100 baseEnd_3057100 := by
    simpa [prefixWord, tailWord_3057100, baseEnd_3057100] using wordTrace_append hprefix tailTrace_3057100
  have hstable : (prefixWord ++ tailWord_3057100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057100).length < 2 ^ (prefixWord ++ tailWord_3057100).sum := by decide
  have hdescent : baseEnd_3057100 < baseStart_3057100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057103 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_3057103 : Nat := 118140960795 + 3057103 * 2 ^ 59
def prefixEnd_3057103 : Nat := 4983230072969 + 3 ^ 40 * 3057103 * 2
def baseEnd_3057103 : Nat := 1569763249302057804153145

theorem tailTrace_3057103 : CollatzResearch.WordTrace tailWord_3057103 prefixEnd_3057103 1569763249302057804153145 := by
  unfold tailWord_3057103
  simp only [CollatzResearch.WordTrace]
  refine ⟨111501706643645417470079963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74334471095763611646719975 111501706643645417470079963)
  ·
    refine ⟨167252559965468126205119945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111501706643645417470079963 167252559965468126205119945)
    ·
      refine ⟨125439419974101094653839959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167252559965468126205119945 125439419974101094653839959)
      ·
        refine ⟨188159129961151641980759939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125439419974101094653839959 188159129961151641980759939)
        ·
          refine ⟨282238694941727462971139909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188159129961151641980759939 282238694941727462971139909)
          ·
            refine ⟨52919755301573899307088733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282238694941727462971139909 52919755301573899307088733)
            ·
              refine ⟨19844908238090212240158275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52919755301573899307088733 19844908238090212240158275)
              ·
                refine ⟨29767362357135318360237413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19844908238090212240158275 29767362357135318360237413)
                ·
                  refine ⟨5581380441962872192544515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29767362357135318360237413 5581380441962872192544515)
                  ·
                    refine ⟨8372070662944308288816773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581380441962872192544515 8372070662944308288816773)
                    ·
                      refine ⟨1569763249302057804153145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8372070662944308288816773 1569763249302057804153145)
                      ·
                        rfl

theorem cell23_3057103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_3057103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057103 prefixEnd_3057103 := by exact prefixLift 3057103
  have htrace : WordTrace (prefixWord ++ tailWord_3057103) baseStart_3057103 baseEnd_3057103 := by
    simpa [prefixWord, tailWord_3057103, baseEnd_3057103] using wordTrace_append hprefix tailTrace_3057103
  have hstable : (prefixWord ++ tailWord_3057103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057103).length < 2 ^ (prefixWord ++ tailWord_3057103).sum := by decide
  have hdescent : baseEnd_3057103 < baseStart_3057103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057110 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3057110 : Nat := 118140960795 + 3057110 * 2 ^ 59
def prefixEnd_3057110 : Nat := 4983230072969 + 3 ^ 40 * 3057110 * 2
def baseEnd_3057110 : Nat := 1569766843666639276765613

theorem tailTrace_3057110 : CollatzResearch.WordTrace tailWord_3057110 prefixEnd_3057110 1569766843666639276765613 := by
  unfold tailWord_3057110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6968872622163753604099049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74334641303080038443723189 6968872622163753604099049)
  ·
    refine ⟨5226654466622815203074287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6968872622163753604099049 5226654466622815203074287)
    ·
      refine ⟨7839981699934222804611431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5226654466622815203074287 7839981699934222804611431)
      ·
        refine ⟨11759972549901334206917147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7839981699934222804611431 11759972549901334206917147)
        ·
          refine ⟨17639958824852001310375721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11759972549901334206917147 17639958824852001310375721)
          ·
            refine ⟨13229969118639000982781791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17639958824852001310375721 13229969118639000982781791)
            ·
              refine ⟨19844953677958501474172687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13229969118639000982781791 19844953677958501474172687)
              ·
                refine ⟨29767430516937752211259031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19844953677958501474172687 29767430516937752211259031)
                ·
                  refine ⟨44651145775406628316888547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29767430516937752211259031 44651145775406628316888547)
                  ·
                    refine ⟨66976718663109942475332821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44651145775406628316888547 66976718663109942475332821)
                    ·
                      refine ⟨1569766843666639276765613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66976718663109942475332821 1569766843666639276765613)
                      ·
                        rfl

theorem cell23_3057110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3057110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057110 prefixEnd_3057110 := by exact prefixLift 3057110
  have htrace : WordTrace (prefixWord ++ tailWord_3057110) baseStart_3057110 baseEnd_3057110 := by
    simpa [prefixWord, tailWord_3057110, baseEnd_3057110] using wordTrace_append hprefix tailTrace_3057110
  have hstable : (prefixWord ++ tailWord_3057110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057110).length < 2 ^ (prefixWord ++ tailWord_3057110).sum := by decide
  have hdescent : baseEnd_3057110 < baseStart_3057110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057164 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_3057164 : Nat := 118140960795 + 3057164 * 2 ^ 59
def prefixEnd_3057164 : Nat := 4983230072969 + 3 ^ 40 * 3057164 * 2
def baseEnd_3057164 : Nat := 523264857207327355163455

theorem tailTrace_3057164 : CollatzResearch.WordTrace tailWord_3057164 prefixEnd_3057164 523264857207327355163455 := by
  unfold tailWord_3057164
  simp only [CollatzResearch.WordTrace]
  refine ⟨55751965748212212444025273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74335954330949616592033697 55751965748212212444025273)
  ·
    refine ⟨41813974311159159333018955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55751965748212212444025273 41813974311159159333018955)
    ·
      refine ⟨62720961466738738999528433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41813974311159159333018955 62720961466738738999528433)
      ·
        refine ⟨47040721100054054249646325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62720961466738738999528433 47040721100054054249646325)
        ·
          refine ⟨4410067603130067585904343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47040721100054054249646325 4410067603130067585904343)
          ·
            refine ⟨6615101404695101378856515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410067603130067585904343 6615101404695101378856515)
            ·
              refine ⟨9922652107042652068284773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615101404695101378856515 9922652107042652068284773)
              ·
                refine ⟨1860497270070497262803395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9922652107042652068284773 1860497270070497262803395)
                ·
                  refine ⟨2790745905105745894205093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860497270070497262803395 2790745905105745894205093)
                  ·
                    refine ⟨523264857207327355163455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790745905105745894205093 523264857207327355163455)
                    ·
                      rfl

theorem cell23_3057164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_3057164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057164 prefixEnd_3057164 := by exact prefixLift 3057164
  have htrace : WordTrace (prefixWord ++ tailWord_3057164) baseStart_3057164 baseEnd_3057164 := by
    simpa [prefixWord, tailWord_3057164, baseEnd_3057164] using wordTrace_append hprefix tailTrace_3057164
  have hstable : (prefixWord ++ tailWord_3057164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057164).length < 2 ^ (prefixWord ++ tailWord_3057164).sum := by decide
  have hdescent : baseEnd_3057164 < baseStart_3057164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057207 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 1, 5]
def baseStart_3057207 : Nat := 118140960795 + 3057207 * 2 ^ 59
def prefixEnd_3057207 : Nat := 4983230072969 + 3 ^ 40 * 3057207 * 2
def baseEnd_3057207 : Nat := 523272217096708465750889

theorem tailTrace_3057207 : CollatzResearch.WordTrace tailWord_3057207 prefixEnd_3057207 523272217096708465750889 := by
  unfold tailWord_3057207
  simp only [CollatzResearch.WordTrace]
  refine ⟨111505499835268643231865875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74336999890179095487910583 111505499835268643231865875)
  ·
    refine ⟨167258249752902964847798813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111505499835268643231865875 167258249752902964847798813)
    ·
      refine ⟨62721843657338611817924555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167258249752902964847798813 62721843657338611817924555)
      ·
        refine ⟨94082765486007917726886833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62721843657338611817924555 94082765486007917726886833)
        ·
          refine ⟨70562074114505938295165125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94082765486007917726886833 70562074114505938295165125)
          ·
            refine ⟨13230388896469863430343461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70562074114505938295165125 13230388896469863430343461)
            ·
              refine ⟨2480697918088099393189399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13230388896469863430343461 2480697918088099393189399)
              ·
                refine ⟨3721046877132149089784099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480697918088099393189399 3721046877132149089784099)
                ·
                  refine ⟨5581570315698223634676149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721046877132149089784099 5581570315698223634676149)
                  ·
                    refine ⟨523272217096708465750889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5581570315698223634676149 523272217096708465750889)
                    ·
                      rfl

theorem cell23_3057207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_3057207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057207 prefixEnd_3057207 := by exact prefixLift 3057207
  have htrace : WordTrace (prefixWord ++ tailWord_3057207) baseStart_3057207 baseEnd_3057207 := by
    simpa [prefixWord, tailWord_3057207, baseEnd_3057207] using wordTrace_append hprefix tailTrace_3057207
  have hstable : (prefixWord ++ tailWord_3057207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057207).length < 2 ^ (prefixWord ++ tailWord_3057207).sum := by decide
  have hdescent : baseEnd_3057207 < baseStart_3057207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057233 : List Nat := [1, 2, 2, 1, 3, 2, 2, 10]
def baseStart_3057233 : Nat := 118140960795 + 3057233 * 2 ^ 59
def prefixEnd_3057233 : Nat := 4983230072969 + 3 ^ 40 * 3057233 * 2
def baseEnd_3057233 : Nat := 58141851918042307241761

theorem tailTrace_3057233 : CollatzResearch.WordTrace tailWord_3057233 prefixEnd_3057233 58141851918042307241761 := by
  unfold tailWord_3057233
  simp only [CollatzResearch.WordTrace]
  refine ⟨111506448133174449672312353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74337632088782966448208235 111506448133174449672312353)
  ·
    refine ⟨83629836099880837254234265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111506448133174449672312353 83629836099880837254234265)
    ·
      refine ⟨62722377074910627940675699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83629836099880837254234265 62722377074910627940675699)
      ·
        refine ⟨94083565612365941911013549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62722377074910627940675699 94083565612365941911013549)
        ·
          refine ⟨35281337104637228216630081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94083565612365941911013549 35281337104637228216630081)
          ·
            refine ⟨26461002828477921162472561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35281337104637228216630081 26461002828477921162472561)
            ·
              refine ⟨19845752121358440871854421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26461002828477921162472561 19845752121358440871854421)
              ·
                refine ⟨58141851918042307241761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19845752121358440871854421 58141851918042307241761)
                ·
                  rfl

theorem cell23_3057233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 10].length) (baseStart_3057233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057233 prefixEnd_3057233 := by exact prefixLift 3057233
  have htrace : WordTrace (prefixWord ++ tailWord_3057233) baseStart_3057233 baseEnd_3057233 := by
    simpa [prefixWord, tailWord_3057233, baseEnd_3057233] using wordTrace_append hprefix tailTrace_3057233
  have hstable : (prefixWord ++ tailWord_3057233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057233).length < 2 ^ (prefixWord ++ tailWord_3057233).sum := by decide
  have hdescent : baseEnd_3057233 < baseStart_3057233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057244 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3057244 : Nat := 118140960795 + 3057244 * 2 ^ 59
def prefixEnd_3057244 : Nat := 4983230072969 + 3 ^ 40 * 3057244 * 2
def baseEnd_3057244 : Nat := 1569835650074341752489997

theorem tailTrace_3057244 : CollatzResearch.WordTrace tailWord_3057244 prefixEnd_3057244 1569835650074341752489997 := by
  unfold tailWord_3057244
  simp only [CollatzResearch.WordTrace]
  refine ⟨55753424668067299275481393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74337899557423065700641857 55753424668067299275481393)
  ·
    refine ⟨41815068501050474456611045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55753424668067299275481393 41815068501050474456611045)
    ·
      refine ⟨7840325343946963960614571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41815068501050474456611045 7840325343946963960614571)
      ·
        refine ⟨11760488015920445940921857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7840325343946963960614571 11760488015920445940921857)
        ·
          refine ⟨8820366011940334455691393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11760488015920445940921857 8820366011940334455691393)
          ·
            refine ⟨6615274508955250841768545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8820366011940334455691393 6615274508955250841768545)
            ·
              refine ⟨4961455881716438131326409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6615274508955250841768545 4961455881716438131326409)
              ·
                refine ⟨3721091911287328598494807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4961455881716438131326409 3721091911287328598494807)
                ·
                  refine ⟨5581637866930992897742211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721091911287328598494807 5581637866930992897742211)
                  ·
                    refine ⟨8372456800396489346613317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581637866930992897742211 8372456800396489346613317)
                    ·
                      refine ⟨1569835650074341752489997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8372456800396489346613317 1569835650074341752489997)
                      ·
                        rfl

theorem cell23_3057244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3057244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057244 prefixEnd_3057244 := by exact prefixLift 3057244
  have htrace : WordTrace (prefixWord ++ tailWord_3057244) baseStart_3057244 baseEnd_3057244 := by
    simpa [prefixWord, tailWord_3057244, baseEnd_3057244] using wordTrace_append hprefix tailTrace_3057244
  have hstable : (prefixWord ++ tailWord_3057244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057244).length < 2 ^ (prefixWord ++ tailWord_3057244).sum := by decide
  have hdescent : baseEnd_3057244 < baseStart_3057244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057260 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_3057260 : Nat := 118140960795 + 3057260 * 2 ^ 59
def prefixEnd_3057260 : Nat := 4983230072969 + 3 ^ 40 * 3057260 * 2
def baseEnd_3057260 : Nat := 1569843865764813689889923

theorem tailTrace_3057260 : CollatzResearch.WordTrace tailWord_3057260 prefixEnd_3057260 1569843865764813689889923 := by
  unfold tailWord_3057260
  simp only [CollatzResearch.WordTrace]
  refine ⟨55753716452038316641772617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74338288602717755522363489 55753716452038316641772617)
  ·
    refine ⟨41815287339028737481329463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55753716452038316641772617 41815287339028737481329463)
    ·
      refine ⟨62722931008543106221994195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41815287339028737481329463 62722931008543106221994195)
      ·
        refine ⟨94084396512814659332991293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62722931008543106221994195 94084396512814659332991293)
        ·
          refine ⟨35281648692305497249871735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94084396512814659332991293 35281648692305497249871735)
          ·
            refine ⟨52922473038458245874807603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35281648692305497249871735 52922473038458245874807603)
            ·
              refine ⟨79383709557687368812211405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52922473038458245874807603 79383709557687368812211405)
              ·
                refine ⟨29768891084132763304579277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79383709557687368812211405 29768891084132763304579277)
                ·
                  refine ⟨11163334156549786239217229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29768891084132763304579277 11163334156549786239217229)
                  ·
                    refine ⟨4186250308706169839706461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11163334156549786239217229 4186250308706169839706461)
                    ·
                      refine ⟨1569843865764813689889923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4186250308706169839706461 1569843865764813689889923)
                      ·
                        rfl

theorem cell23_3057260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_3057260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057260 prefixEnd_3057260 := by exact prefixLift 3057260
  have htrace : WordTrace (prefixWord ++ tailWord_3057260) baseStart_3057260 baseEnd_3057260 := by
    simpa [prefixWord, tailWord_3057260, baseEnd_3057260] using wordTrace_append hprefix tailTrace_3057260
  have hstable : (prefixWord ++ tailWord_3057260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057260).length < 2 ^ (prefixWord ++ tailWord_3057260).sum := by decide
  have hdescent : baseEnd_3057260 < baseStart_3057260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057263 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 9]
def baseStart_3057263 : Nat := 118140960795 + 3057263 * 2 ^ 59
def prefixEnd_3057263 : Nat := 4983230072969 + 3 ^ 40 * 3057263 * 2
def baseEnd_3057263 : Nat := 523281802068925726050803

theorem tailTrace_3057263 : CollatzResearch.WordTrace tailWord_3057263 prefixEnd_3057263 523281802068925726050803 := by
  unfold tailWord_3057263
  simp only [CollatzResearch.WordTrace]
  refine ⟨111507542323065764795904443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74338361548710509863936295 111507542323065764795904443)
  ·
    refine ⟨167261313484598647193856665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111507542323065764795904443 167261313484598647193856665)
    ·
      refine ⟨125445985113448985395392499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167261313484598647193856665 125445985113448985395392499)
      ·
        refine ⟨188168977670173478093088749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125445985113448985395392499 188168977670173478093088749)
        ·
          refine ⟨70563366626315054284908281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188168977670173478093088749 70563366626315054284908281)
          ·
            refine ⟨52922524969736290713681211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70563366626315054284908281 52922524969736290713681211)
            ·
              refine ⟨79383787454604436070521817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52922524969736290713681211 79383787454604436070521817)
              ·
                refine ⟨59537840590953327052891363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79383787454604436070521817 59537840590953327052891363)
                ·
                  refine ⟨89306760886429990579337045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59537840590953327052891363 89306760886429990579337045)
                  ·
                    refine ⟨523281802068925726050803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 89306760886429990579337045 523281802068925726050803)
                    ·
                      rfl

theorem cell23_3057263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_3057263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057263 prefixEnd_3057263 := by exact prefixLift 3057263
  have htrace : WordTrace (prefixWord ++ tailWord_3057263) baseStart_3057263 baseEnd_3057263 := by
    simpa [prefixWord, tailWord_3057263, baseEnd_3057263] using wordTrace_append hprefix tailTrace_3057263
  have hstable : (prefixWord ++ tailWord_3057263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057263).length < 2 ^ (prefixWord ++ tailWord_3057263).sum := by decide
  have hdescent : baseEnd_3057263 < baseStart_3057263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057288 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 2, 4]
def baseStart_3057288 : Nat := 118140960795 + 3057288 * 2 ^ 59
def prefixEnd_3057288 : Nat := 4983230072969 + 3 ^ 40 * 3057288 * 2
def baseEnd_3057288 : Nat := 523286081074379860113265

theorem tailTrace_3057288 : CollatzResearch.WordTrace tailWord_3057288 prefixEnd_3057288 523286081074379860113265 := by
  unfold tailWord_3057288
  simp only [CollatzResearch.WordTrace]
  refine ⟨55754227073987597032782259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74338969431983462710376345 55754227073987597032782259)
  ·
    refine ⟨83631340610981395549173389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55754227073987597032782259 83631340610981395549173389)
    ·
      refine ⟨31361752729118023330940021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83631340610981395549173389 31361752729118023330940021)
      ·
        refine ⟨2940164318354814687275627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31361752729118023330940021 2940164318354814687275627)
        ·
          refine ⟨4410246477532222030913441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940164318354814687275627 4410246477532222030913441)
          ·
            refine ⟨3307684858149166523185081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4410246477532222030913441 3307684858149166523185081)
            ·
              refine ⟨2480763643611874892388811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3307684858149166523185081 2480763643611874892388811)
              ·
                refine ⟨3721145465417812338583217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480763643611874892388811 3721145465417812338583217)
                ·
                  refine ⟨2790859099063359253937413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3721145465417812338583217 2790859099063359253937413)
                  ·
                    refine ⟨523286081074379860113265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790859099063359253937413 523286081074379860113265)
                    ·
                      rfl

theorem cell23_3057288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_3057288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057288 prefixEnd_3057288 := by exact prefixLift 3057288
  have htrace : WordTrace (prefixWord ++ tailWord_3057288) baseStart_3057288 baseEnd_3057288 := by
    simpa [prefixWord, tailWord_3057288, baseEnd_3057288] using wordTrace_append hprefix tailTrace_3057288
  have hstable : (prefixWord ++ tailWord_3057288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057288).length < 2 ^ (prefixWord ++ tailWord_3057288).sum := by decide
  have hdescent : baseEnd_3057288 < baseStart_3057288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057298 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_3057298 : Nat := 118140960795 + 3057298 * 2 ^ 59
def prefixEnd_3057298 : Nat := 4983230072969 + 3 ^ 40 * 3057298 * 2
def baseEnd_3057298 : Nat := 1569863378029684541214749

theorem tailTrace_3057298 : CollatzResearch.WordTrace tailWord_3057298 prefixEnd_3057298 1569863378029684541214749 := by
  unfold tailWord_3057298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27877204719484741443357137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74339212585292643848952365 27877204719484741443357137)
  ·
    refine ⟨20907903539613556082517853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27877204719484741443357137 20907903539613556082517853)
    ·
      refine ⟨7840463827355083530944195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20907903539613556082517853 7840463827355083530944195)
      ·
        refine ⟨11760695741032625296416293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7840463827355083530944195 11760695741032625296416293)
        ·
          refine ⟨2205130451443617243078055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11760695741032625296416293 2205130451443617243078055)
          ·
            refine ⟨3307695677165425864617083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205130451443617243078055 3307695677165425864617083)
            ·
              refine ⟨4961543515748138796925625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307695677165425864617083 4961543515748138796925625)
              ·
                refine ⟨3721157636811104097694219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4961543515748138796925625 3721157636811104097694219)
                ·
                  refine ⟨5581736455216656146541329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721157636811104097694219 5581736455216656146541329)
                  ·
                    refine ⟨4186302341412492109905997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5581736455216656146541329 4186302341412492109905997)
                    ·
                      refine ⟨1569863378029684541214749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4186302341412492109905997 1569863378029684541214749)
                      ·
                        rfl

theorem cell23_3057298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_3057298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057298 prefixEnd_3057298 := by exact prefixLift 3057298
  have htrace : WordTrace (prefixWord ++ tailWord_3057298) baseStart_3057298 baseEnd_3057298 := by
    simpa [prefixWord, tailWord_3057298, baseEnd_3057298] using wordTrace_append hprefix tailTrace_3057298
  have hstable : (prefixWord ++ tailWord_3057298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057298).length < 2 ^ (prefixWord ++ tailWord_3057298).sum := by decide
  have hdescent : baseEnd_3057298 < baseStart_3057298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057304 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3057304 : Nat := 118140960795 + 3057304 * 2 ^ 59
def prefixEnd_3057304 : Nat := 4983230072969 + 3 ^ 40 * 3057304 * 2
def baseEnd_3057304 : Nat := 1569866458913611517739721

theorem tailTrace_3057304 : CollatzResearch.WordTrace tailWord_3057304 prefixEnd_3057304 1569866458913611517739721 := by
  unfold tailWord_3057304
  simp only [CollatzResearch.WordTrace]
  refine ⟨55754518857958614399073483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74339358477278152532097977 55754518857958614399073483)
  ·
    refine ⟨83631778286937921598610225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55754518857958614399073483 83631778286937921598610225)
    ·
      refine ⟨62723833715203441198957669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83631778286937921598610225 62723833715203441198957669)
      ·
        refine ⟨11760718821600645224804563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62723833715203441198957669 11760718821600645224804563)
        ·
          refine ⟨17641078232400967837206845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11760718821600645224804563 17641078232400967837206845)
          ·
            refine ⟨6615404337150362938952567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17641078232400967837206845 6615404337150362938952567)
            ·
              refine ⟨9923106505725544408428851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615404337150362938952567 9923106505725544408428851)
              ·
                refine ⟨14884659758588316612643277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9923106505725544408428851 14884659758588316612643277)
                ·
                  refine ⟨5581747409470618729741229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14884659758588316612643277 5581747409470618729741229)
                  ·
                    refine ⟨2093155278551482023652961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5581747409470618729741229 2093155278551482023652961)
                    ·
                      refine ⟨1569866458913611517739721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093155278551482023652961 1569866458913611517739721)
                      ·
                        rfl

theorem cell23_3057304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3057304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057304 prefixEnd_3057304 := by exact prefixLift 3057304
  have htrace : WordTrace (prefixWord ++ tailWord_3057304) baseStart_3057304 baseEnd_3057304 := by
    simpa [prefixWord, tailWord_3057304, baseEnd_3057304] using wordTrace_append hprefix tailTrace_3057304
  have hstable : (prefixWord ++ tailWord_3057304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057304).length < 2 ^ (prefixWord ++ tailWord_3057304).sum := by decide
  have hdescent : baseEnd_3057304 < baseStart_3057304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3057317 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 3, 4, 2]
def baseStart_3057317 : Nat := 118140960795 + 3057317 * 2 ^ 59
def prefixEnd_3057317 : Nat := 4983230072969 + 3 ^ 40 * 3057317 * 2
def baseEnd_3057317 : Nat := 1569873134162119966877161

theorem tailTrace_3057317 : CollatzResearch.WordTrace tailWord_3057317 prefixEnd_3057317 1569873134162119966877161 := by
  unfold tailWord_3057317
  simp only [CollatzResearch.WordTrace]
  refine ⟨111509511864870132018370205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74339674576580088012246803 111509511864870132018370205)
  ·
    refine ⟨41816066949326299506888827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111509511864870132018370205 41816066949326299506888827)
    ·
      refine ⟨62724100423989449260333241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41816066949326299506888827 62724100423989449260333241)
      ·
        refine ⟨47043075317992086945249931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62724100423989449260333241 47043075317992086945249931)
        ·
          refine ⟨70564612976988130417874897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47043075317992086945249931 70564612976988130417874897)
          ·
            refine ⟨52923459732741097813406173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70564612976988130417874897 52923459732741097813406173)
            ·
              refine ⟨19846297399777911680027315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52923459732741097813406173 19846297399777911680027315)
              ·
                refine ⟨29769446099666867520040973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19846297399777911680027315 29769446099666867520040973)
                ·
                  refine ⟨11163542287375075320015365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29769446099666867520040973 11163542287375075320015365)
                  ·
                    refine ⟨2093164178882826622502881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11163542287375075320015365 2093164178882826622502881)
                    ·
                      refine ⟨1569873134162119966877161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2093164178882826622502881 1569873134162119966877161)
                      ·
                        rfl

theorem cell23_3057317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_3057317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3057317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3057317 prefixEnd_3057317 := by exact prefixLift 3057317
  have htrace : WordTrace (prefixWord ++ tailWord_3057317) baseStart_3057317 baseEnd_3057317 := by
    simpa [prefixWord, tailWord_3057317, baseEnd_3057317] using wordTrace_append hprefix tailTrace_3057317
  have hstable : (prefixWord ++ tailWord_3057317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3057317).length < 2 ^ (prefixWord ++ tailWord_3057317).sum := by decide
  have hdescent : baseEnd_3057317 < baseStart_3057317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3057317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
