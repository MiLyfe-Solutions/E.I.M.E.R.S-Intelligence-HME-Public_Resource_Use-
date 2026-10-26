import V185TrunkScan23Chunk0324

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1922033 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_1922033 : Nat := 118140960795 + 1922033 * 2 ^ 59
def prefixEnd_1922033 : Nat := 4983230072969 + 3 ^ 40 * 1922033 * 2
def baseEnd_1922033 : Nat := 328975587601061256916079

theorem tailTrace_1922033 : CollatzResearch.WordTrace tailWord_1922033 prefixEnd_1922033 328975587601061256916079 := by
  unfold tailWord_1922033
  simp only [CollatzResearch.WordTrace]
  refine ⟨70102302645810172947626753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46734868430540115298417835 70102302645810172947626753)
  ·
    refine ⟨52576726984357629710720065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70102302645810172947626753 52576726984357629710720065)
    ·
      refine ⟨39432545238268222283040049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52576726984357629710720065 39432545238268222283040049)
      ·
        refine ⟨29574408928701166712280037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39432545238268222283040049 29574408928701166712280037)
        ·
          refine ⟨5545201674131468758552507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29574408928701166712280037 5545201674131468758552507)
          ·
            refine ⟨8317802511197203137828761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545201674131468758552507 8317802511197203137828761)
            ·
              refine ⟨6238351883397902353371571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8317802511197203137828761 6238351883397902353371571)
              ·
                refine ⟨9357527825096853530057357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238351883397902353371571 9357527825096853530057357)
                ·
                  refine ⟨3509072934411320073771509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9357527825096853530057357 3509072934411320073771509)
                  ·
                    refine ⟨328975587601061256916079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3509072934411320073771509 328975587601061256916079)
                    ·
                      rfl

theorem cell23_1922033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_1922033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922033 prefixEnd_1922033 := by exact prefixLift 1922033
  have htrace : WordTrace (prefixWord ++ tailWord_1922033) baseStart_1922033 baseEnd_1922033 := by
    simpa [prefixWord, tailWord_1922033, baseEnd_1922033] using wordTrace_append hprefix tailTrace_1922033
  have hstable : (prefixWord ++ tailWord_1922033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922033).length < 2 ^ (prefixWord ++ tailWord_1922033).sum := by decide
  have hdescent : baseEnd_1922033 < baseStart_1922033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922034 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1922034 : Nat := 118140960795 + 1922034 * 2 ^ 59
def prefixEnd_1922034 : Nat := 4983230072969 + 3 ^ 40 * 1922034 * 2
def baseEnd_1922034 : Nat := 986927276283838266835733

theorem tailTrace_1922034 : CollatzResearch.WordTrace tailWord_1922034 prefixEnd_1922034 986927276283838266835733 := by
  unfold tailWord_1922034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17525584779701637529603289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46734892745871033412275437 17525584779701637529603289)
  ·
    refine ⟨13144188584776228147202467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17525584779701637529603289 13144188584776228147202467)
    ·
      refine ⟨19716282877164342220803701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13144188584776228147202467 19716282877164342220803701)
      ·
        refine ⟨1848401519734157083200347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19716282877164342220803701 1848401519734157083200347)
        ·
          refine ⟨2772602279601235624800521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848401519734157083200347 2772602279601235624800521)
          ·
            refine ⟨2079451709700926718600391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772602279601235624800521 2079451709700926718600391)
            ·
              refine ⟨3119177564551390077900587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079451709700926718600391 3119177564551390077900587)
              ·
                refine ⟨4678766346827085116850881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119177564551390077900587 4678766346827085116850881)
                ·
                  refine ⟨3509074760120313837638161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678766346827085116850881 3509074760120313837638161)
                  ·
                    refine ⟨2631806070090235378228621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509074760120313837638161 2631806070090235378228621)
                    ·
                      refine ⟨986927276283838266835733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631806070090235378228621 986927276283838266835733)
                      ·
                        rfl

theorem cell23_1922034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1922034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922034 prefixEnd_1922034 := by exact prefixLift 1922034
  have htrace : WordTrace (prefixWord ++ tailWord_1922034) baseStart_1922034 baseEnd_1922034 := by
    simpa [prefixWord, tailWord_1922034, baseEnd_1922034] using wordTrace_append hprefix tailTrace_1922034
  have hstable : (prefixWord ++ tailWord_1922034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922034).length < 2 ^ (prefixWord ++ tailWord_1922034).sum := by decide
  have hdescent : baseEnd_1922034 < baseStart_1922034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922073 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_1922073 : Nat := 118140960795 + 1922073 * 2 ^ 59
def prefixEnd_1922073 : Nat := 4983230072969 + 3 ^ 40 * 1922073 * 2
def baseEnd_1922073 : Nat := 986947302029363614248053

theorem tailTrace_1922073 : CollatzResearch.WordTrace tailWord_1922073 prefixEnd_1922073 986947302029363614248053 := by
  unfold tailWord_1922073
  simp only [CollatzResearch.WordTrace]
  refine ⟨70103761565665259779082873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46735841043776839852721915 70103761565665259779082873)
  ·
    refine ⟨52577821174248944834312155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70103761565665259779082873 52577821174248944834312155)
    ·
      refine ⟨78866731761373417251468233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52577821174248944834312155 78866731761373417251468233)
      ·
        refine ⟨59150048821030062938601175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78866731761373417251468233 59150048821030062938601175)
        ·
          refine ⟨88725073231545094407901763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59150048821030062938601175 88725073231545094407901763)
          ·
            refine ⟨133087609847317641611852645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88725073231545094407901763 133087609847317641611852645)
            ·
              refine ⟨24953926846372057802222371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133087609847317641611852645 24953926846372057802222371)
              ·
                refine ⟨37430890269558086703333557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24953926846372057802222371 37430890269558086703333557)
                ·
                  refine ⟨3509145962771070628437521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37430890269558086703333557 3509145962771070628437521)
                  ·
                    refine ⟨2631859472078302971328141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509145962771070628437521 2631859472078302971328141)
                    ·
                      refine ⟨986947302029363614248053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631859472078302971328141 986947302029363614248053)
                      ·
                        rfl

theorem cell23_1922073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_1922073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922073 prefixEnd_1922073 := by exact prefixLift 1922073
  have htrace : WordTrace (prefixWord ++ tailWord_1922073) baseStart_1922073 baseEnd_1922073 := by
    simpa [prefixWord, tailWord_1922073, baseEnd_1922073] using wordTrace_append hprefix tailTrace_1922073
  have hstable : (prefixWord ++ tailWord_1922073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922073).length < 2 ^ (prefixWord ++ tailWord_1922073).sum := by decide
  have hdescent : baseEnd_1922073 < baseStart_1922073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922083 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1922083 : Nat := 118140960795 + 1922083 * 2 ^ 59
def prefixEnd_1922083 : Nat := 4983230072969 + 3 ^ 40 * 1922083 * 2
def baseEnd_1922083 : Nat := 986952436835908575123007

theorem tailTrace_1922083 : CollatzResearch.WordTrace tailWord_1922083 prefixEnd_1922083 986952436835908575123007 := by
  unfold tailWord_1922083
  simp only [CollatzResearch.WordTrace]
  refine ⟨70104126295629031486946903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46736084197086020991297935 70104126295629031486946903)
  ·
    refine ⟨105156189443443547230420355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70104126295629031486946903 105156189443443547230420355)
    ·
      refine ⟨157734284165165320845630533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105156189443443547230420355 157734284165165320845630533)
      ·
        refine ⟨29575178280968497658555725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157734284165165320845630533 29575178280968497658555725)
        ·
          refine ⟨11090691855363186621958397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29575178280968497658555725 11090691855363186621958397)
          ·
            refine ⟨4159009445761194983234399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11090691855363186621958397 4159009445761194983234399)
            ·
              refine ⟨6238514168641792474851599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159009445761194983234399 6238514168641792474851599)
              ·
                refine ⟨9357771252962688712277399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238514168641792474851599 9357771252962688712277399)
                ·
                  refine ⟨14036656879444033068416099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9357771252962688712277399 14036656879444033068416099)
                  ·
                    refine ⟨21054985319166049602624149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14036656879444033068416099 21054985319166049602624149)
                    ·
                      refine ⟨986952436835908575123007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21054985319166049602624149 986952436835908575123007)
                      ·
                        rfl

theorem cell23_1922083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1922083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922083 prefixEnd_1922083 := by exact prefixLift 1922083
  have htrace : WordTrace (prefixWord ++ tailWord_1922083) baseStart_1922083 baseEnd_1922083 := by
    simpa [prefixWord, tailWord_1922083, baseEnd_1922083] using wordTrace_append hprefix tailTrace_1922083
  have hstable : (prefixWord ++ tailWord_1922083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922083).length < 2 ^ (prefixWord ++ tailWord_1922083).sum := by decide
  have hdescent : baseEnd_1922083 < baseStart_1922083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922087 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1922087 : Nat := 118140960795 + 1922087 * 2 ^ 59
def prefixEnd_1922087 : Nat := 4983230072969 + 3 ^ 40 * 1922087 * 2
def baseEnd_1922087 : Nat := 986954490758526559472989

theorem tailTrace_1922087 : CollatzResearch.WordTrace tailWord_1922087 prefixEnd_1922087 986954490758526559472989 := by
  unfold tailWord_1922087
  simp only [CollatzResearch.WordTrace]
  refine ⟨70104272187614540170092515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46736181458409693446728343 70104272187614540170092515)
  ·
    refine ⟨105156408281421810255138773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70104272187614540170092515 105156408281421810255138773)
    ·
      refine ⟨2464603319095823677854815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 105156408281421810255138773 2464603319095823677854815)
      ·
        refine ⟨3696904978643735516782223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464603319095823677854815 3696904978643735516782223)
        ·
          refine ⟨5545357467965603275173335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696904978643735516782223 5545357467965603275173335)
          ·
            refine ⟨8318036201948404912760003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545357467965603275173335 8318036201948404912760003)
            ·
              refine ⟨12477054302922607369140005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318036201948404912760003 12477054302922607369140005)
              ·
                refine ⟨2339447681797988881713751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12477054302922607369140005 2339447681797988881713751)
                ·
                  refine ⟨3509171522696983322570627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339447681797988881713751 3509171522696983322570627)
                  ·
                    refine ⟨5263757284045474983855941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509171522696983322570627 5263757284045474983855941)
                    ·
                      refine ⟨986954490758526559472989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5263757284045474983855941 986954490758526559472989)
                      ·
                        rfl

theorem cell23_1922087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1922087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922087 prefixEnd_1922087 := by exact prefixLift 1922087
  have htrace : WordTrace (prefixWord ++ tailWord_1922087) baseStart_1922087 baseEnd_1922087 := by
    simpa [prefixWord, tailWord_1922087, baseEnd_1922087] using wordTrace_append hprefix tailTrace_1922087
  have hstable : (prefixWord ++ tailWord_1922087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922087).length < 2 ^ (prefixWord ++ tailWord_1922087).sum := by decide
  have hdescent : baseEnd_1922087 < baseStart_1922087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922103 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1922103 : Nat := 118140960795 + 1922103 * 2 ^ 59
def prefixEnd_1922103 : Nat := 4983230072969 + 3 ^ 40 * 1922103 * 2
def baseEnd_1922103 : Nat := 986962706448998496872915

theorem tailTrace_1922103 : CollatzResearch.WordTrace tailWord_1922103 prefixEnd_1922103 986962706448998496872915 := by
  unfold tailWord_1922103
  simp only [CollatzResearch.WordTrace]
  refine ⟨70104855755556574902674963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46736570503704383268449975 70104855755556574902674963)
  ·
    refine ⟨105157283633334862354012445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70104855755556574902674963 105157283633334862354012445)
    ·
      refine ⟨39433981362500573382754667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105157283633334862354012445 39433981362500573382754667)
      ·
        refine ⟨59150972043750860074132001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39433981362500573382754667 59150972043750860074132001)
        ·
          refine ⟨44363229032813145055599001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59150972043750860074132001 44363229032813145055599001)
          ·
            refine ⟨33272421774609858791699251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44363229032813145055599001 33272421774609858791699251)
            ·
              refine ⟨49908632661914788187548877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33272421774609858791699251 49908632661914788187548877)
              ·
                refine ⟨18715737248218045570330829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49908632661914788187548877 18715737248218045570330829)
                ·
                  refine ⟨7018401468081767088874061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18715737248218045570330829 7018401468081767088874061)
                  ·
                    refine ⟨2631900550530662658327773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7018401468081767088874061 2631900550530662658327773)
                    ·
                      refine ⟨986962706448998496872915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631900550530662658327773 986962706448998496872915)
                      ·
                        rfl

theorem cell23_1922103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1922103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922103 prefixEnd_1922103 := by exact prefixLift 1922103
  have htrace : WordTrace (prefixWord ++ tailWord_1922103) baseStart_1922103 baseEnd_1922103 := by
    simpa [prefixWord, tailWord_1922103, baseEnd_1922103] using wordTrace_append hprefix tailTrace_1922103
  have hstable : (prefixWord ++ tailWord_1922103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922103).length < 2 ^ (prefixWord ++ tailWord_1922103).sum := by decide
  have hdescent : baseEnd_1922103 < baseStart_1922103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922110 : List Nat := [4, 2, 1, 3, 1, 3, 9]
def baseStart_1922110 : Nat := 118140960795 + 1922110 * 2 ^ 59
def prefixEnd_1922110 : Nat := 4983230072969 + 3 ^ 40 * 1922110 * 2
def baseEnd_1922110 : Nat := 12184769145846666289943

theorem tailTrace_1922110 : CollatzResearch.WordTrace tailWord_1922110 prefixEnd_1922110 12184769145846666289943 := by
  unfold tailWord_1922110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763138883316401887272473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46736740711020810065453189 8763138883316401887272473)
  ·
    refine ⟨6572354162487301415454355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8763138883316401887272473 6572354162487301415454355)
    ·
      refine ⟨9858531243730952123181533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572354162487301415454355 9858531243730952123181533)
      ·
        refine ⟨3696949216399107046193075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9858531243730952123181533 3696949216399107046193075)
        ·
          refine ⟨5545423824598660569289613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696949216399107046193075 5545423824598660569289613)
          ·
            refine ⟨2079533934224497713483605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5545423824598660569289613 2079533934224497713483605)
            ·
              refine ⟨12184769145846666289943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2079533934224497713483605 12184769145846666289943)
              ·
                rfl

theorem cell23_1922110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 9].length) (baseStart_1922110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922110 prefixEnd_1922110 := by exact prefixLift 1922110
  have htrace : WordTrace (prefixWord ++ tailWord_1922110) baseStart_1922110 baseEnd_1922110 := by
    simpa [prefixWord, tailWord_1922110, baseEnd_1922110] using wordTrace_append hprefix tailTrace_1922110
  have hstable : (prefixWord ++ tailWord_1922110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922110).length < 2 ^ (prefixWord ++ tailWord_1922110).sum := by decide
  have hdescent : baseEnd_1922110 < baseStart_1922110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922120 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_1922120 : Nat := 118140960795 + 1922120 * 2 ^ 59
def prefixEnd_1922120 : Nat := 4983230072969 + 3 ^ 40 * 1922120 * 2
def baseEnd_1922120 : Nat := 986971435620124930360337

theorem tailTrace_1922120 : CollatzResearch.WordTrace tailWord_1922120 prefixEnd_1922120 986971435620124930360337 := by
  unfold tailWord_1922120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052737898247493403021907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46736983864329991204029209 35052737898247493403021907)
  ·
    refine ⟨52579106847371240104532861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35052737898247493403021907 52579106847371240104532861)
    ·
      refine ⟨19717165067764215039199823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52579106847371240104532861 19717165067764215039199823)
      ·
        refine ⟨29575747601646322558799735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717165067764215039199823 29575747601646322558799735)
        ·
          refine ⟨44363621402469483838199603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29575747601646322558799735 44363621402469483838199603)
          ·
            refine ⟨66545432103704225757299405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44363621402469483838199603 66545432103704225757299405)
            ·
              refine ⟨24954537038889084658987277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66545432103704225757299405 24954537038889084658987277)
              ·
                refine ⟨9357951389583406747120229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24954537038889084658987277 9357951389583406747120229)
                ·
                  refine ⟨1754615885546888765085043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9357951389583406747120229 1754615885546888765085043)
                  ·
                    refine ⟨2631923828320333147627565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1754615885546888765085043 2631923828320333147627565)
                    ·
                      refine ⟨986971435620124930360337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631923828320333147627565 986971435620124930360337)
                      ·
                        rfl

theorem cell23_1922120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_1922120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922120 prefixEnd_1922120 := by exact prefixLift 1922120
  have htrace : WordTrace (prefixWord ++ tailWord_1922120) baseStart_1922120 baseEnd_1922120 := by
    simpa [prefixWord, tailWord_1922120, baseEnd_1922120] using wordTrace_append hprefix tailTrace_1922120
  have hstable : (prefixWord ++ tailWord_1922120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922120).length < 2 ^ (prefixWord ++ tailWord_1922120).sum := by decide
  have hdescent : baseEnd_1922120 < baseStart_1922120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922141 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1922141 : Nat := 118140960795 + 1922141 * 2 ^ 59
def prefixEnd_1922141 : Nat := 4983230072969 + 3 ^ 40 * 1922141 * 2
def baseEnd_1922141 : Nat := 986982218713869348197741

theorem tailTrace_1922141 : CollatzResearch.WordTrace tailWord_1922141 prefixEnd_1922141 986982218713869348197741 := by
  unfold tailWord_1922141
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106241729418907392558277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46737494486279271595038851 70106241729418907392558277)
  ·
    refine ⟨13144920324266045136104677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70106241729418907392558277 13144920324266045136104677)
    ·
      refine ⟨2464672560799883463019627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13144920324266045136104677 2464672560799883463019627)
      ·
        refine ⟨3697008841199825194529441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464672560799883463019627 3697008841199825194529441)
        ·
          refine ⟨2772756630899868895897081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3697008841199825194529441 2772756630899868895897081)
          ·
            refine ⟨2079567473174901671922811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772756630899868895897081 2079567473174901671922811)
            ·
              refine ⟨3119351209762352507884217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079567473174901671922811 3119351209762352507884217)
              ·
                refine ⟨2339513407321764380913163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119351209762352507884217 2339513407321764380913163)
                ·
                  refine ⟨3509270110982646571369745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339513407321764380913163 3509270110982646571369745)
                  ·
                    refine ⟨2631952583236984928527309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509270110982646571369745 2631952583236984928527309)
                    ·
                      refine ⟨986982218713869348197741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631952583236984928527309 986982218713869348197741)
                      ·
                        rfl

theorem cell23_1922141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1922141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922141 prefixEnd_1922141 := by exact prefixLift 1922141
  have htrace : WordTrace (prefixWord ++ tailWord_1922141) baseStart_1922141 baseEnd_1922141 := by
    simpa [prefixWord, tailWord_1922141, baseEnd_1922141] using wordTrace_append hprefix tailTrace_1922141
  have hstable : (prefixWord ++ tailWord_1922141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922141).length < 2 ^ (prefixWord ++ tailWord_1922141).sum := by decide
  have hdescent : baseEnd_1922141 < baseStart_1922141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922163 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 3]
def baseStart_1922163 : Nat := 118140960795 + 1922163 * 2 ^ 59
def prefixEnd_1922163 : Nat := 4983230072969 + 3 ^ 40 * 1922163 * 2
def baseEnd_1922163 : Nat := 986993515288268262122639

theorem tailTrace_1922163 : CollatzResearch.WordTrace tailWord_1922163 prefixEnd_1922163 986993515288268262122639 := by
  unfold tailWord_1922163
  simp only [CollatzResearch.WordTrace]
  refine ⟨70107044135339205149859143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46738029423559470099906095 70107044135339205149859143)
  ·
    refine ⟨105160566203008807724788715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70107044135339205149859143 105160566203008807724788715)
    ·
      refine ⟨157740849304513211587183073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105160566203008807724788715 157740849304513211587183073)
      ·
        refine ⟨118305636978384908690387305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157740849304513211587183073 118305636978384908690387305)
        ·
          refine ⟨88729227733788681517790479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118305636978384908690387305 88729227733788681517790479)
          ·
            refine ⟨133093841600683022276685719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88729227733788681517790479 133093841600683022276685719)
            ·
              refine ⟨199640762401024533415028579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133093841600683022276685719 199640762401024533415028579)
              ·
                refine ⟨299461143601536800122542869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199640762401024533415028579 299461143601536800122542869)
                ·
                  refine ⟨14037241106322037505744197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 299461143601536800122542869 14037241106322037505744197)
                  ·
                    refine ⟨2631982707435382032327037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14037241106322037505744197 2631982707435382032327037)
                    ·
                      refine ⟨986993515288268262122639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631982707435382032327037 986993515288268262122639)
                      ·
                        rfl

theorem cell23_1922163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_1922163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922163 prefixEnd_1922163 := by exact prefixLift 1922163
  have htrace : WordTrace (prefixWord ++ tailWord_1922163) baseStart_1922163 baseEnd_1922163 := by
    simpa [prefixWord, tailWord_1922163, baseEnd_1922163] using wordTrace_append hprefix tailTrace_1922163
  have hstable : (prefixWord ++ tailWord_1922163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922163).length < 2 ^ (prefixWord ++ tailWord_1922163).sum := by decide
  have hdescent : baseEnd_1922163 < baseStart_1922163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922180 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1922180 : Nat := 118140960795 + 1922180 * 2 ^ 59
def prefixEnd_1922180 : Nat := 4983230072969 + 3 ^ 40 * 1922180 * 2
def baseEnd_1922180 : Nat := 987002244459394695610061

theorem tailTrace_1922180 : CollatzResearch.WordTrace tailWord_1922180 prefixEnd_1922180 987002244459394695610061 := by
  unfold tailWord_1922180
  simp only [CollatzResearch.WordTrace]
  refine ⟨35053832088138808526613997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46738442784185078035485329 35053832088138808526613997)
  ·
    refine ⟨13145187033052053197480249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35053832088138808526613997 13145187033052053197480249)
    ·
      refine ⟨9858890274789039898110187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13145187033052053197480249 9858890274789039898110187)
      ·
        refine ⟨14788335412183559847165281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858890274789039898110187 14788335412183559847165281)
        ·
          refine ⟨11091251559137669885373961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14788335412183559847165281 11091251559137669885373961)
          ·
            refine ⟨8318438669353252414030471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091251559137669885373961 8318438669353252414030471)
            ·
              refine ⟨12477658004029878621045707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318438669353252414030471 12477658004029878621045707)
              ·
                refine ⟨18716487006044817931568561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477658004029878621045707 18716487006044817931568561)
                ·
                  refine ⟨14037365254533613448676421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18716487006044817931568561 14037365254533613448676421)
                  ·
                    refine ⟨2632005985225052521626829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14037365254533613448676421 2632005985225052521626829)
                    ·
                      refine ⟨987002244459394695610061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2632005985225052521626829 987002244459394695610061)
                      ·
                        rfl

theorem cell23_1922180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1922180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922180 prefixEnd_1922180 := by exact prefixLift 1922180
  have htrace : WordTrace (prefixWord ++ tailWord_1922180) baseStart_1922180 baseEnd_1922180 := by
    simpa [prefixWord, tailWord_1922180, baseEnd_1922180] using wordTrace_append hprefix tailTrace_1922180
  have hstable : (prefixWord ++ tailWord_1922180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922180).length < 2 ^ (prefixWord ++ tailWord_1922180).sum := by decide
  have hdescent : baseEnd_1922180 < baseStart_1922180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922183 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 7]
def baseStart_1922183 : Nat := 118140960795 + 1922183 * 2 ^ 59
def prefixEnd_1922183 : Nat := 4983230072969 + 3 ^ 40 * 1922183 * 2
def baseEnd_1922183 : Nat := 109667087211262020430283

theorem tailTrace_1922183 : CollatzResearch.WordTrace tailWord_1922183 prefixEnd_1922183 109667087211262020430283 := by
  unfold tailWord_1922183
  simp only [CollatzResearch.WordTrace]
  refine ⟨70107773595266748565587203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46738515730177832377058135 70107773595266748565587203)
  ·
    refine ⟨105161660392900122848380805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70107773595266748565587203 105161660392900122848380805)
    ·
      refine ⟨19717811323668773034071401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105161660392900122848380805 19717811323668773034071401)
      ·
        refine ⟨14788358492751579775553551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19717811323668773034071401 14788358492751579775553551)
        ·
          refine ⟨22182537739127369663330327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14788358492751579775553551 22182537739127369663330327)
          ·
            refine ⟨33273806608691054494995491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22182537739127369663330327 33273806608691054494995491)
            ·
              refine ⟨49910709913036581742493237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33273806608691054494995491 49910709913036581742493237)
              ·
                refine ⟨4679129054347179538358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49910709913036581742493237 4679129054347179538358741)
                ·
                  refine ⟨109667087211262020430283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4679129054347179538358741 109667087211262020430283)
                  ·
                    rfl

theorem cell23_1922183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 7].length) (baseStart_1922183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922183 prefixEnd_1922183 := by exact prefixLift 1922183
  have htrace : WordTrace (prefixWord ++ tailWord_1922183) baseStart_1922183 baseEnd_1922183 := by
    simpa [prefixWord, tailWord_1922183, baseEnd_1922183] using wordTrace_append hprefix tailTrace_1922183
  have hstable : (prefixWord ++ tailWord_1922183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922183).length < 2 ^ (prefixWord ++ tailWord_1922183).sum := by decide
  have hdescent : baseEnd_1922183 < baseStart_1922183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922190 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1922190 : Nat := 118140960795 + 1922190 * 2 ^ 59
def prefixEnd_1922190 : Nat := 4983230072969 + 3 ^ 40 * 1922190 * 2
def baseEnd_1922190 : Nat := 987007379265939656485015

theorem tailTrace_1922190 : CollatzResearch.WordTrace tailWord_1922190 prefixEnd_1922190 987007379265939656485015 := by
  unfold tailWord_1922190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763503613280173595136503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46738685937494259174061349 8763503613280173595136503)
  ·
    refine ⟨13145255419920260392704755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8763503613280173595136503 13145255419920260392704755)
    ·
      refine ⟨19717883129880390589057133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145255419920260392704755 19717883129880390589057133)
      ·
        refine ⟨7394206173705146470896425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19717883129880390589057133 7394206173705146470896425)
        ·
          refine ⟨5545654630278859853172319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7394206173705146470896425 5545654630278859853172319)
          ·
            refine ⟨8318481945418289779758479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545654630278859853172319 8318481945418289779758479)
            ·
              refine ⟨12477722918127434669637719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318481945418289779758479 12477722918127434669637719)
              ·
                refine ⟨18716584377191152004456579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477722918127434669637719 18716584377191152004456579)
                ·
                  refine ⟨28074876565786728006684869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18716584377191152004456579 28074876565786728006684869)
                  ·
                    refine ⟨5264039356085011501253413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28074876565786728006684869 5264039356085011501253413)
                    ·
                      refine ⟨987007379265939656485015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5264039356085011501253413 987007379265939656485015)
                      ·
                        rfl

theorem cell23_1922190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1922190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922190 prefixEnd_1922190 := by exact prefixLift 1922190
  have htrace : WordTrace (prefixWord ++ tailWord_1922190) baseStart_1922190 baseEnd_1922190 := by
    simpa [prefixWord, tailWord_1922190, baseEnd_1922190] using wordTrace_append hprefix tailTrace_1922190
  have hstable : (prefixWord ++ tailWord_1922190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922190).length < 2 ^ (prefixWord ++ tailWord_1922190).sum := by decide
  have hdescent : baseEnd_1922190 < baseStart_1922190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922194 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1922194 : Nat := 118140960795 + 1922194 * 2 ^ 59
def prefixEnd_1922194 : Nat := 4983230072969 + 3 ^ 40 * 1922194 * 2
def baseEnd_1922194 : Nat := 987009433188557640834997

theorem tailTrace_1922194 : CollatzResearch.WordTrace tailWord_1922194 prefixEnd_1922194 987009433188557640834997 := by
  unfold tailWord_1922194
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527043699556724361059409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46738783198817931629491757 17527043699556724361059409)
  ·
    refine ⟨13145282774667543270794557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17527043699556724361059409 13145282774667543270794557)
    ·
      refine ⟨4929481040500328726547959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13145282774667543270794557 4929481040500328726547959)
      ·
        refine ⟨7394221560750493089821939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929481040500328726547959 7394221560750493089821939)
        ·
          refine ⟨11091332341125739634732909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394221560750493089821939 11091332341125739634732909)
          ·
            refine ⟨4159249627922152363024841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11091332341125739634732909 4159249627922152363024841)
            ·
              refine ⟨3119437220941614272268631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159249627922152363024841 3119437220941614272268631)
              ·
                refine ⟨4679155831412421408402947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119437220941614272268631 4679155831412421408402947)
                ·
                  refine ⟨7018733747118632112604421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679155831412421408402947 7018733747118632112604421)
                  ·
                    refine ⟨1316012577584743521113329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018733747118632112604421 1316012577584743521113329)
                    ·
                      refine ⟨987009433188557640834997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316012577584743521113329 987009433188557640834997)
                      ·
                        rfl

theorem cell23_1922194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1922194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922194 prefixEnd_1922194 := by exact prefixLift 1922194
  have htrace : WordTrace (prefixWord ++ tailWord_1922194) baseStart_1922194 baseEnd_1922194 := by
    simpa [prefixWord, tailWord_1922194, baseEnd_1922194] using wordTrace_append hprefix tailTrace_1922194
  have hstable : (prefixWord ++ tailWord_1922194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922194).length < 2 ^ (prefixWord ++ tailWord_1922194).sum := by decide
  have hdescent : baseEnd_1922194 < baseStart_1922194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922200 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 7]
def baseStart_1922200 : Nat := 118140960795 + 1922200 * 2 ^ 59
def prefixEnd_1922200 : Nat := 4983230072969 + 3 ^ 40 * 1922200 * 2
def baseEnd_1922200 : Nat := 109668057119164957484441

theorem tailTrace_1922200 : CollatzResearch.WordTrace tailWord_1922200 prefixEnd_1922200 109668057119164957484441 := by
  unfold tailWord_1922200
  simp only [CollatzResearch.WordTrace]
  refine ⟨35054196818102580234478027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46738929090803440312637369 35054196818102580234478027)
  ·
    refine ⟨52581295227153870351717041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35054196818102580234478027 52581295227153870351717041)
    ·
      refine ⟨39435971420365402763787781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52581295227153870351717041 39435971420365402763787781)
      ·
        refine ⟨7394244641318513018210209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39435971420365402763787781 7394244641318513018210209)
        ·
          refine ⟨5545683480988884763657657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7394244641318513018210209 5545683480988884763657657)
          ·
            refine ⟨4159262610741663572743243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5545683480988884763657657 4159262610741663572743243)
            ·
              refine ⟨6238893916112495359114865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159262610741663572743243 6238893916112495359114865)
              ·
                refine ⟨4679170437084371519336149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238893916112495359114865 4679170437084371519336149)
                ·
                  refine ⟨109668057119164957484441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4679170437084371519336149 109668057119164957484441)
                  ·
                    rfl

theorem cell23_1922200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_1922200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922200 prefixEnd_1922200 := by exact prefixLift 1922200
  have htrace : WordTrace (prefixWord ++ tailWord_1922200) baseStart_1922200 baseEnd_1922200 := by
    simpa [prefixWord, tailWord_1922200, baseEnd_1922200] using wordTrace_append hprefix tailTrace_1922200
  have hstable : (prefixWord ++ tailWord_1922200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922200).length < 2 ^ (prefixWord ++ tailWord_1922200).sum := by decide
  have hdescent : baseEnd_1922200 < baseStart_1922200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922220 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 7, 2]
def baseStart_1922220 : Nat := 118140960795 + 1922220 * 2 ^ 59
def prefixEnd_1922220 : Nat := 4983230072969 + 3 ^ 40 * 1922220 * 2
def baseEnd_1922220 : Nat := 987022783685574539109877

theorem tailTrace_1922220 : CollatzResearch.WordTrace tailWord_1922220 prefixEnd_1922220 987022783685574539109877 := by
  unfold tailWord_1922220
  simp only [CollatzResearch.WordTrace]
  refine ⟨35054561548066351942342057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46739415397421802589789409 35054561548066351942342057)
  ·
    refine ⟨26290921161049763956756543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35054561548066351942342057 26290921161049763956756543)
    ·
      refine ⟨39436381741574645935134815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26290921161049763956756543 39436381741574645935134815)
      ·
        refine ⟨59154572612361968902702223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39436381741574645935134815 59154572612361968902702223)
        ·
          refine ⟨88731858918542953354053335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59154572612361968902702223 88731858918542953354053335)
          ·
            refine ⟨133097788377814430031080003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88731858918542953354053335 133097788377814430031080003)
            ·
              refine ⟨199646682566721645046620005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133097788377814430031080003 199646682566721645046620005)
              ·
                refine ⟨37433752981260308446241251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199646682566721645046620005 37433752981260308446241251)
                ·
                  refine ⟨56150629471890462669361877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37433752981260308446241251 56150629471890462669361877)
                  ·
                    refine ⟨1316030378247432718813169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56150629471890462669361877 1316030378247432718813169)
                    ·
                      refine ⟨987022783685574539109877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316030378247432718813169 987022783685574539109877)
                      ·
                        rfl

theorem cell23_1922220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_1922220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922220 prefixEnd_1922220 := by exact prefixLift 1922220
  have htrace : WordTrace (prefixWord ++ tailWord_1922220) baseStart_1922220 baseEnd_1922220 := by
    simpa [prefixWord, tailWord_1922220, baseEnd_1922220] using wordTrace_append hprefix tailTrace_1922220
  have hstable : (prefixWord ++ tailWord_1922220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922220).length < 2 ^ (prefixWord ++ tailWord_1922220).sum := by decide
  have hdescent : baseEnd_1922220 < baseStart_1922220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922223 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_1922223 : Nat := 118140960795 + 1922223 * 2 ^ 59
def prefixEnd_1922223 : Nat := 4983230072969 + 3 ^ 40 * 1922223 * 2
def baseEnd_1922223 : Nat := 987024324127538027372363

theorem tailTrace_1922223 : CollatzResearch.WordTrace tailWord_1922223 prefixEnd_1922223 987024324127538027372363 := by
  unfold tailWord_1922223
  simp only [CollatzResearch.WordTrace]
  refine ⟨70109232515121835397043323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46739488343414556931362215 70109232515121835397043323)
  ·
    refine ⟨105163848772682753095564985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70109232515121835397043323 105163848772682753095564985)
    ·
      refine ⟨78872886579512064821673739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105163848772682753095564985 78872886579512064821673739)
      ·
        refine ⟨118309329869268097232510609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78872886579512064821673739 118309329869268097232510609)
        ·
          refine ⟨88731997401951072924382957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118309329869268097232510609 88731997401951072924382957)
          ·
            refine ⟨33274499025731652346643609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88731997401951072924382957 33274499025731652346643609)
            ·
              refine ⟨24955874269298739259982707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33274499025731652346643609 24955874269298739259982707)
              ·
                refine ⟨37433811403948108889974061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24955874269298739259982707 37433811403948108889974061)
                ·
                  refine ⟨14037679276480540833740273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37433811403948108889974061 14037679276480540833740273)
                  ·
                    refine ⟨10528259457360405625305205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14037679276480540833740273 10528259457360405625305205)
                    ·
                      refine ⟨987024324127538027372363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10528259457360405625305205 987024324127538027372363)
                      ·
                        rfl

theorem cell23_1922223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_1922223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922223 prefixEnd_1922223 := by exact prefixLift 1922223
  have htrace : WordTrace (prefixWord ++ tailWord_1922223) baseStart_1922223 baseEnd_1922223 := by
    simpa [prefixWord, tailWord_1922223, baseEnd_1922223] using wordTrace_append hprefix tailTrace_1922223
  have hstable : (prefixWord ++ tailWord_1922223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922223).length < 2 ^ (prefixWord ++ tailWord_1922223).sum := by decide
  have hdescent : baseEnd_1922223 < baseStart_1922223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922250 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1922250 : Nat := 118140960795 + 1922250 * 2 ^ 59
def prefixEnd_1922250 : Nat := 4983230072969 + 3 ^ 40 * 1922250 * 2
def baseEnd_1922250 : Nat := 987038188105209421734739

theorem tailTrace_1922250 : CollatzResearch.WordTrace tailWord_1922250 prefixEnd_1922250 987038188105209421734739 := by
  unfold tailWord_1922250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527554321506004752069051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46740144857349346005517469 17527554321506004752069051)
  ·
    refine ⟨26291331482259007128103577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17527554321506004752069051 26291331482259007128103577)
    ·
      refine ⟨19718498611694255346077683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26291331482259007128103577 19718498611694255346077683)
      ·
        refine ⟨29577747917541383019116525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19718498611694255346077683 29577747917541383019116525)
        ·
          refine ⟨11091655469078018632168697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29577747917541383019116525 11091655469078018632168697)
          ·
            refine ⟨8318741601808513974126523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091655469078018632168697 8318741601808513974126523)
            ·
              refine ⟨12478112402712770961189785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318741601808513974126523 12478112402712770961189785)
              ·
                refine ⟨9358584302034578220892339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478112402712770961189785 9358584302034578220892339)
                ·
                  refine ⟨14037876453051867331338509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358584302034578220892339 14037876453051867331338509)
                  ·
                    refine ⟨5264203669894450249251941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14037876453051867331338509 5264203669894450249251941)
                    ·
                      refine ⟨987038188105209421734739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5264203669894450249251941 987038188105209421734739)
                      ·
                        rfl

theorem cell23_1922250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1922250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922250 prefixEnd_1922250 := by exact prefixLift 1922250
  have htrace : WordTrace (prefixWord ++ tailWord_1922250) baseStart_1922250 baseEnd_1922250 := by
    simpa [prefixWord, tailWord_1922250, baseEnd_1922250] using wordTrace_append hprefix tailTrace_1922250
  have hstable : (prefixWord ++ tailWord_1922250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922250).length < 2 ^ (prefixWord ++ tailWord_1922250).sum := by decide
  have hdescent : baseEnd_1922250 < baseStart_1922250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922307 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 6]
def baseStart_1922307 : Nat := 118140960795 + 1922307 * 2 ^ 59
def prefixEnd_1922307 : Nat := 4983230072969 + 3 ^ 40 * 1922307 * 2
def baseEnd_1922307 : Nat := 109674161833612855413553

theorem tailTrace_1922307 : CollatzResearch.WordTrace tailWord_1922307 prefixEnd_1922307 109674161833612855413553 := by
  unfold tailWord_1922307
  simp only [CollatzResearch.WordTrace]
  refine ⟨70112296246817517743101175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46741530831211678495400783 70112296246817517743101175)
  ·
    refine ⟨105168444370226276614651763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70112296246817517743101175 105168444370226276614651763)
    ·
      refine ⟨157752666555339414921977645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105168444370226276614651763 157752666555339414921977645)
      ·
        refine ⟨59157249958252280595741617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157752666555339414921977645 59157249958252280595741617)
        ·
          refine ⟨44367937468689210446806213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59157249958252280595741617 44367937468689210446806213)
          ·
            refine ⟨8318988275379226958776165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44367937468689210446806213 8318988275379226958776165)
            ·
              refine ⟨1559810301633605054770531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8318988275379226958776165 1559810301633605054770531)
              ·
                refine ⟨2339715452450407582155797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559810301633605054770531 2339715452450407582155797)
                ·
                  refine ⟨109674161833612855413553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2339715452450407582155797 109674161833612855413553)
                  ·
                    rfl

theorem cell23_1922307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 6].length) (baseStart_1922307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922307 prefixEnd_1922307 := by exact prefixLift 1922307
  have htrace : WordTrace (prefixWord ++ tailWord_1922307) baseStart_1922307 baseEnd_1922307 := by
    simpa [prefixWord, tailWord_1922307, baseEnd_1922307] using wordTrace_append hprefix tailTrace_1922307
  have hstable : (prefixWord ++ tailWord_1922307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922307).length < 2 ^ (prefixWord ++ tailWord_1922307).sum := by decide
  have hdescent : baseEnd_1922307 < baseStart_1922307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922357 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1922357 : Nat := 118140960795 + 1922357 * 2 ^ 59
def prefixEnd_1922357 : Nat := 4983230072969 + 3 ^ 40 * 1922357 * 2
def baseEnd_1922357 : Nat := 987093130535240503096747

theorem tailTrace_1922357 : CollatzResearch.WordTrace tailWord_1922357 prefixEnd_1922357 987093130535240503096747 := by
  unfold tailWord_1922357
  simp only [CollatzResearch.WordTrace]
  refine ⟨70114119896636376282421325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46742746597757584188280883 70114119896636376282421325)
  ·
    refine ⟨26292794961238641105907997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70114119896636376282421325 26292794961238641105907997)
    ·
      refine ⟨9859798110464490414715499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26292794961238641105907997 9859798110464490414715499)
      ·
        refine ⟨14789697165696735622073249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859798110464490414715499 14789697165696735622073249)
        ·
          refine ⟨11092272874272551716554937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14789697165696735622073249 11092272874272551716554937)
          ·
            refine ⟨8319204655704413787416203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11092272874272551716554937 8319204655704413787416203)
            ·
              refine ⟨12478806983556620681124305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319204655704413787416203 12478806983556620681124305)
              ·
                refine ⟨9359105237667465510843229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478806983556620681124305 9359105237667465510843229)
                ·
                  refine ⟨3509664464125299566566211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9359105237667465510843229 3509664464125299566566211)
                  ·
                    refine ⟨5264496696187949349849317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509664464125299566566211 5264496696187949349849317)
                    ·
                      refine ⟨987093130535240503096747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5264496696187949349849317 987093130535240503096747)
                      ·
                        rfl

theorem cell23_1922357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1922357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922357 prefixEnd_1922357 := by exact prefixLift 1922357
  have htrace : WordTrace (prefixWord ++ tailWord_1922357) baseStart_1922357 baseEnd_1922357 := by
    simpa [prefixWord, tailWord_1922357, baseEnd_1922357] using wordTrace_append hprefix tailTrace_1922357
  have hstable : (prefixWord ++ tailWord_1922357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922357).length < 2 ^ (prefixWord ++ tailWord_1922357).sum := by decide
  have hdescent : baseEnd_1922357 < baseStart_1922357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922360 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1922360 : Nat := 118140960795 + 1922360 * 2 ^ 59
def prefixEnd_1922360 : Nat := 4983230072969 + 3 ^ 40 * 1922360 * 2
def baseEnd_1922360 : Nat := 987094670977203991359233

theorem tailTrace_1922360 : CollatzResearch.WordTrace tailWord_1922360 prefixEnd_1922360 987094670977203991359233 := by
  unfold tailWord_1922360
  simp only [CollatzResearch.WordTrace]
  refine ⟨35057114657812753897390267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46742819543750338529853689 35057114657812753897390267)
  ·
    refine ⟨52585671986719130846085401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35057114657812753897390267 52585671986719130846085401)
    ·
      refine ⟨39439253990039348134564051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52585671986719130846085401 39439253990039348134564051)
      ·
        refine ⟨59158880985059022201846077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39439253990039348134564051 59158880985059022201846077)
        ·
          refine ⟨22184580369397133325692279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59158880985059022201846077 22184580369397133325692279)
          ·
            refine ⟨33276870554095699988538419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22184580369397133325692279 33276870554095699988538419)
            ·
              refine ⟨49915305831143549982807629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33276870554095699988538419 49915305831143549982807629)
              ·
                refine ⟨18718239686678831243552861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49915305831143549982807629 18718239686678831243552861)
                ·
                  refine ⟨7019339882504561716332323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18718239686678831243552861 7019339882504561716332323)
                  ·
                    refine ⟨10529009823756842574498485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019339882504561716332323 10529009823756842574498485)
                    ·
                      refine ⟨987094670977203991359233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10529009823756842574498485 987094670977203991359233)
                      ·
                        rfl

theorem cell23_1922360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1922360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922360 prefixEnd_1922360 := by exact prefixLift 1922360
  have htrace : WordTrace (prefixWord ++ tailWord_1922360) baseStart_1922360 baseEnd_1922360 := by
    simpa [prefixWord, tailWord_1922360, baseEnd_1922360] using wordTrace_append hprefix tailTrace_1922360
  have hstable : (prefixWord ++ tailWord_1922360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922360).length < 2 ^ (prefixWord ++ tailWord_1922360).sum := by decide
  have hdescent : baseEnd_1922360 < baseStart_1922360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922367 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 1, 6]
def baseStart_1922367 : Nat := 118140960795 + 1922367 * 2 ^ 59
def prefixEnd_1922367 : Nat := 4983230072969 + 3 ^ 40 * 1922367 * 2
def baseEnd_1922367 : Nat := 329032755113928487990567

theorem tailTrace_1922367 : CollatzResearch.WordTrace tailWord_1922367 prefixEnd_1922367 329032755113928487990567 := by
  unfold tailWord_1922367
  simp only [CollatzResearch.WordTrace]
  refine ⟨70114484626600147990285355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46742989751066765326856903 70114484626600147990285355)
  ·
    refine ⟨105171726939900221985428033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70114484626600147990285355 105171726939900221985428033)
    ·
      refine ⟨78878795204925166489071025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105171726939900221985428033 78878795204925166489071025)
      ·
        refine ⟨59159096403693874866803269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78878795204925166489071025 59159096403693874866803269)
        ·
          refine ⟨11092330575692601537525613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59159096403693874866803269 11092330575692601537525613)
          ·
            refine ⟨4159623965884725576572105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11092330575692601537525613 4159623965884725576572105)
            ·
              refine ⟨3119717974413544182429079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159623965884725576572105 3119717974413544182429079)
              ·
                refine ⟨4679576961620316273643619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119717974413544182429079 4679576961620316273643619)
                ·
                  refine ⟨7019365442430474410465429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679576961620316273643619 7019365442430474410465429)
                  ·
                    refine ⟨329032755113928487990567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7019365442430474410465429 329032755113928487990567)
                    ·
                      rfl

theorem cell23_1922367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_1922367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922367 prefixEnd_1922367 := by exact prefixLift 1922367
  have htrace : WordTrace (prefixWord ++ tailWord_1922367) baseStart_1922367 baseEnd_1922367 := by
    simpa [prefixWord, tailWord_1922367, baseEnd_1922367] using wordTrace_append hprefix tailTrace_1922367
  have hstable : (prefixWord ++ tailWord_1922367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922367).length < 2 ^ (prefixWord ++ tailWord_1922367).sum := by decide
  have hdescent : baseEnd_1922367 < baseStart_1922367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922377 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_1922377 : Nat := 118140960795 + 1922377 * 2 ^ 59
def prefixEnd_1922377 : Nat := 4983230072969 + 3 ^ 40 * 1922377 * 2
def baseEnd_1922377 : Nat := 987103400148330424846655

theorem tailTrace_1922377 : CollatzResearch.WordTrace tailWord_1922377 prefixEnd_1922377 987103400148330424846655 := by
  unfold tailWord_1922377
  simp only [CollatzResearch.WordTrace]
  refine ⟨70114849356563919698149385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46743232904375946465432923 70114849356563919698149385)
  ·
    refine ⟨52586137017422939773612039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70114849356563919698149385 52586137017422939773612039)
    ·
      refine ⟨78879205526134409660418059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52586137017422939773612039 78879205526134409660418059)
      ·
        refine ⟨118318808289201614490627089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78879205526134409660418059 118318808289201614490627089)
        ·
          refine ⟨88739106216901210867970317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118318808289201614490627089 88739106216901210867970317)
          ·
            refine ⟨33277164831337954075488869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88739106216901210867970317 33277164831337954075488869)
            ·
              refine ⟨6239468405875866389154163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33277164831337954075488869 6239468405875866389154163)
              ·
                refine ⟨9359202608813799583731245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239468405875866389154163 9359202608813799583731245)
                ·
                  refine ⟨3509700978305174843899217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9359202608813799583731245 3509700978305174843899217)
                  ·
                    refine ⟨2632275733728881132924413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509700978305174843899217 2632275733728881132924413)
                    ·
                      refine ⟨987103400148330424846655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2632275733728881132924413 987103400148330424846655)
                      ·
                        rfl

theorem cell23_1922377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_1922377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922377 prefixEnd_1922377 := by exact prefixLift 1922377
  have htrace : WordTrace (prefixWord ++ tailWord_1922377) baseStart_1922377 baseEnd_1922377 := by
    simpa [prefixWord, tailWord_1922377, baseEnd_1922377] using wordTrace_append hprefix tailTrace_1922377
  have hstable : (prefixWord ++ tailWord_1922377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922377).length < 2 ^ (prefixWord ++ tailWord_1922377).sum := by decide
  have hdescent : baseEnd_1922377 < baseStart_1922377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922391 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 1, 1, 4]
def baseStart_1922391 : Nat := 118140960795 + 1922391 * 2 ^ 59
def prefixEnd_1922391 : Nat := 4983230072969 + 3 ^ 40 * 1922391 * 2
def baseEnd_1922391 : Nat := 987110588877493370071591

theorem tailTrace_1922391 : CollatzResearch.WordTrace tailWord_1922391 prefixEnd_1922391 987110588877493370071591 := by
  unfold tailWord_1922391
  simp only [CollatzResearch.WordTrace]
  refine ⟨70115359978513200089159027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46743573319008800059439351 70115359978513200089159027)
  ·
    refine ⟨105173039967769800133738541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70115359978513200089159027 105173039967769800133738541)
    ·
      refine ⟨39439889987913675050151953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105173039967769800133738541 39439889987913675050151953)
      ·
        refine ⟨29579917490935256287613965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39439889987913675050151953 29579917490935256287613965)
        ·
          refine ⟨11092469059100721107855237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29579917490935256287613965 11092469059100721107855237)
          ·
            refine ⟨2079837948581385207722857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11092469059100721107855237 2079837948581385207722857)
            ·
              refine ⟨1559878461436038905792143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079837948581385207722857 1559878461436038905792143)
              ·
                refine ⟨2339817692154058358688215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559878461436038905792143 2339817692154058358688215)
                ·
                  refine ⟨3509726538231087538032323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339817692154058358688215 3509726538231087538032323)
                  ·
                    refine ⟨5264589807346631307048485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509726538231087538032323 5264589807346631307048485)
                    ·
                      refine ⟨987110588877493370071591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5264589807346631307048485 987110588877493370071591)
                      ·
                        rfl

theorem cell23_1922391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_1922391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922391 prefixEnd_1922391 := by exact prefixLift 1922391
  have htrace : WordTrace (prefixWord ++ tailWord_1922391) baseStart_1922391 baseEnd_1922391 := by
    simpa [prefixWord, tailWord_1922391, baseEnd_1922391] using wordTrace_append hprefix tailTrace_1922391
  have hstable : (prefixWord ++ tailWord_1922391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922391).length < 2 ^ (prefixWord ++ tailWord_1922391).sum := by decide
  have hdescent : baseEnd_1922391 < baseStart_1922391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922408 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1922408 : Nat := 118140960795 + 1922408 * 2 ^ 59
def prefixEnd_1922408 : Nat := 4983230072969 + 3 ^ 40 * 1922408 * 2
def baseEnd_1922408 : Nat := 987119318048619803559013

theorem tailTrace_1922408 : CollatzResearch.WordTrace tailWord_1922408 prefixEnd_1922408 987119318048619803559013 := by
  unfold tailWord_1922408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35057990009725805996263939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46743986679634407995018585 35057990009725805996263939)
  ·
    refine ⟨52586985014588708994395909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35057990009725805996263939 52586985014588708994395909)
    ·
      refine ⟨9860059690235382936449233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52586985014588708994395909 9860059690235382936449233)
      ·
        refine ⟨7395044767676537202336925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9860059690235382936449233 7395044767676537202336925)
        ·
          refine ⟨2773141787878701450876347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7395044767676537202336925 2773141787878701450876347)
          ·
            refine ⟨4159712681818052176314521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773141787878701450876347 4159712681818052176314521)
            ·
              refine ⟨3119784511363539132235891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159712681818052176314521 3119784511363539132235891)
              ·
                refine ⟨4679676767045308698353837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119784511363539132235891 4679676767045308698353837)
                ·
                  refine ⟨1754878787641990761882689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4679676767045308698353837 1754878787641990761882689)
                  ·
                    refine ⟨1316159090731493071412017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1754878787641990761882689 1316159090731493071412017)
                    ·
                      refine ⟨987119318048619803559013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316159090731493071412017 987119318048619803559013)
                      ·
                        rfl

theorem cell23_1922408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1922408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922408 prefixEnd_1922408 := by exact prefixLift 1922408
  have htrace : WordTrace (prefixWord ++ tailWord_1922408) baseStart_1922408 baseEnd_1922408 := by
    simpa [prefixWord, tailWord_1922408, baseEnd_1922408] using wordTrace_append hprefix tailTrace_1922408
  have hstable : (prefixWord ++ tailWord_1922408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922408).length < 2 ^ (prefixWord ++ tailWord_1922408).sum := by decide
  have hdescent : baseEnd_1922408 < baseStart_1922408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922421 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1922421 : Nat := 118140960795 + 1922421 * 2 ^ 59
def prefixEnd_1922421 : Nat := 4983230072969 + 3 ^ 40 * 1922421 * 2
def baseEnd_1922421 : Nat := 987125993297128252696453

theorem tailTrace_1922421 : CollatzResearch.WordTrace tailWord_1922421 prefixEnd_1922421 987125993297128252696453 := by
  unfold tailWord_1922421
  simp only [CollatzResearch.WordTrace]
  refine ⟨70116454168404515212751117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46744302778936343475167411 70116454168404515212751117)
  ·
    refine ⟨26293670313151693204781669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70116454168404515212751117 26293670313151693204781669)
    ·
      refine ⟨4930063183715942475896563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26293670313151693204781669 4930063183715942475896563)
      ·
        refine ⟨7395094775573913713844845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4930063183715942475896563 7395094775573913713844845)
        ·
          refine ⟨2773160540840217642691817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7395094775573913713844845 2773160540840217642691817)
          ·
            refine ⟨2079870405630163232018863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773160540840217642691817 2079870405630163232018863)
            ·
              refine ⟨3119805608445244848028295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079870405630163232018863 3119805608445244848028295)
              ·
                refine ⟨4679708412667867272042443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119805608445244848028295 4679708412667867272042443)
                ·
                  refine ⟨7019562619001800908063665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679708412667867272042443 7019562619001800908063665)
                  ·
                    refine ⟨5264671964251350681047749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019562619001800908063665 5264671964251350681047749)
                    ·
                      refine ⟨987125993297128252696453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5264671964251350681047749 987125993297128252696453)
                      ·
                        rfl

theorem cell23_1922421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1922421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922421 prefixEnd_1922421 := by exact prefixLift 1922421
  have htrace : WordTrace (prefixWord ++ tailWord_1922421) baseStart_1922421 baseEnd_1922421 := by
    simpa [prefixWord, tailWord_1922421, baseEnd_1922421] using wordTrace_append hprefix tailTrace_1922421
  have hstable : (prefixWord ++ tailWord_1922421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922421).length < 2 ^ (prefixWord ++ tailWord_1922421).sum := by decide
  have hdescent : baseEnd_1922421 < baseStart_1922421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922467 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1922467 : Nat := 118140960795 + 1922467 * 2 ^ 59
def prefixEnd_1922467 : Nat := 4983230072969 + 3 ^ 40 * 1922467 * 2
def baseEnd_1922467 : Nat := 987149613407235072721241

theorem tailTrace_1922467 : CollatzResearch.WordTrace tailWord_1922467 prefixEnd_1922467 987149613407235072721241 := by
  unfold tailWord_1922467
  simp only [CollatzResearch.WordTrace]
  refine ⟨70118131926237865068925655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46745421284158576712617103 70118131926237865068925655)
  ·
    refine ⟨105177197889356797603388483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70118131926237865068925655 105177197889356797603388483)
    ·
      refine ⟨157765796834035196405082725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105177197889356797603388483 157765796834035196405082725)
      ·
        refine ⟨29581086906381599325953011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157765796834035196405082725 29581086906381599325953011)
        ·
          refine ⟨44371630359572398988929517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29581086906381599325953011 44371630359572398988929517)
          ·
            refine ⟨16639361384839649620848569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44371630359572398988929517 16639361384839649620848569)
            ·
              refine ⟨12479521038629737215636427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16639361384839649620848569 12479521038629737215636427)
              ·
                refine ⟨18719281557944605823454641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12479521038629737215636427 18719281557944605823454641)
                ·
                  refine ⟨14039461168458454367590981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18719281557944605823454641 14039461168458454367590981)
                  ·
                    refine ⟨2632398969085960193923309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14039461168458454367590981 2632398969085960193923309)
                    ·
                      refine ⟨987149613407235072721241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2632398969085960193923309 987149613407235072721241)
                      ·
                        rfl

theorem cell23_1922467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1922467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922467 prefixEnd_1922467 := by exact prefixLift 1922467
  have htrace : WordTrace (prefixWord ++ tailWord_1922467) baseStart_1922467 baseEnd_1922467 := by
    simpa [prefixWord, tailWord_1922467, baseEnd_1922467] using wordTrace_append hprefix tailTrace_1922467
  have hstable : (prefixWord ++ tailWord_1922467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922467).length < 2 ^ (prefixWord ++ tailWord_1922467).sum := by decide
  have hdescent : baseEnd_1922467 < baseStart_1922467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922504 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 5]
def baseStart_1922504 : Nat := 118140960795 + 1922504 * 2 ^ 59
def prefixEnd_1922504 : Nat := 4983230072969 + 3 ^ 40 * 1922504 * 2
def baseEnd_1922504 : Nat := 109685401354605714217619

theorem tailTrace_1922504 : CollatzResearch.WordTrace tailWord_1922504 prefixEnd_1922504 109685401354605714217619 := by
  unfold tailWord_1922504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35059740713551910194011283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46746320951402546925348377 35059740713551910194011283)
  ·
    refine ⟨52589611070327865291016925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35059740713551910194011283 52589611070327865291016925)
    ·
      refine ⟨19721104151372949484131347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52589611070327865291016925 19721104151372949484131347)
      ·
        refine ⟨29581656227059424226197021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19721104151372949484131347 29581656227059424226197021)
        ·
          refine ⟨11093121085147284084823883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29581656227059424226197021 11093121085147284084823883)
          ·
            refine ⟨16639681627720926127235825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11093121085147284084823883 16639681627720926127235825)
            ·
              refine ⟨12479761220790694595426869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16639681627720926127235825 12479761220790694595426869)
              ·
                refine ⟨1169977614449127618321269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12479761220790694595426869 1169977614449127618321269)
                ·
                  refine ⟨109685401354605714217619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169977614449127618321269 109685401354605714217619)
                  ·
                    rfl

theorem cell23_1922504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 5].length) (baseStart_1922504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922504 prefixEnd_1922504 := by exact prefixLift 1922504
  have htrace : WordTrace (prefixWord ++ tailWord_1922504) baseStart_1922504 baseEnd_1922504 := by
    simpa [prefixWord, tailWord_1922504, baseEnd_1922504] using wordTrace_append hprefix tailTrace_1922504
  have hstable : (prefixWord ++ tailWord_1922504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922504).length < 2 ^ (prefixWord ++ tailWord_1922504).sum := by decide
  have hdescent : baseEnd_1922504 < baseStart_1922504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922521 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 5]
def baseStart_1922521 : Nat := 118140960795 + 1922521 * 2 ^ 59
def prefixEnd_1922521 : Nat := 4983230072969 + 3 ^ 40 * 1922521 * 2
def baseEnd_1922521 : Nat := 109686371262508651271777

theorem tailTrace_1922521 : CollatzResearch.WordTrace tailWord_1922521 prefixEnd_1922521 109686371262508651271777 := by
  unfold tailWord_1922521
  simp only [CollatzResearch.WordTrace]
  refine ⟨70120101468042232291391417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46746734312028154860927611 70120101468042232291391417)
  ·
    refine ⟨52590076101031674218543563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70120101468042232291391417 52590076101031674218543563)
    ·
      refine ⟨78885114151547511327815345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52590076101031674218543563 78885114151547511327815345)
      ·
        refine ⟨59163835613660633495861509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78885114151547511327815345 59163835613660633495861509)
        ·
          refine ⟨11093219177561368780474033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59163835613660633495861509 11093219177561368780474033)
          ·
            refine ⟨8319914383171026585355525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093219177561368780474033 8319914383171026585355525)
            ·
              refine ⟨1559983946844567484754161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8319914383171026585355525 1559983946844567484754161)
              ·
                refine ⟨1169987960133425613565621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559983946844567484754161 1169987960133425613565621)
                ·
                  refine ⟨109686371262508651271777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169987960133425613565621 109686371262508651271777)
                  ·
                    rfl

theorem cell23_1922521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 5].length) (baseStart_1922521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922521 prefixEnd_1922521 := by exact prefixLift 1922521
  have htrace : WordTrace (prefixWord ++ tailWord_1922521) baseStart_1922521 baseEnd_1922521 := by
    simpa [prefixWord, tailWord_1922521, baseEnd_1922521] using wordTrace_append hprefix tailTrace_1922521
  have hstable : (prefixWord ++ tailWord_1922521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922521).length < 2 ^ (prefixWord ++ tailWord_1922521).sum := by decide
  have hdescent : baseEnd_1922521 < baseStart_1922521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922527 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1922527 : Nat := 118140960795 + 1922527 * 2 ^ 59
def prefixEnd_1922527 : Nat := 4983230072969 + 3 ^ 40 * 1922527 * 2
def baseEnd_1922527 : Nat := 987180422246504837970965

theorem tailTrace_1922527 : CollatzResearch.WordTrace tailWord_1922527 prefixEnd_1922527 987180422246504837970965 := by
  unfold tailWord_1922527
  simp only [CollatzResearch.WordTrace]
  refine ⟨70120320306020495316109835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46746880204013663544073223 70120320306020495316109835)
  ·
    refine ⟨105180480459030742974164753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70120320306020495316109835 105180480459030742974164753)
    ·
      refine ⟨78885360344273057230623565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105180480459030742974164753 78885360344273057230623565)
      ·
        refine ⟨29582010129102396461483837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78885360344273057230623565 29582010129102396461483837)
        ·
          refine ⟨11093253798413398673056439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29582010129102396461483837 11093253798413398673056439)
          ·
            refine ⟨16639880697620098009584659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11093253798413398673056439 16639880697620098009584659)
            ·
              refine ⟨24959821046430147014376989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16639880697620098009584659 24959821046430147014376989)
              ·
                refine ⟨9359932892411305130391371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24959821046430147014376989 9359932892411305130391371)
                ·
                  refine ⟨14039899338616957695587057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359932892411305130391371 14039899338616957695587057)
                  ·
                    refine ⟨10529924503962718271690293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14039899338616957695587057 10529924503962718271690293)
                    ·
                      refine ⟨987180422246504837970965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10529924503962718271690293 987180422246504837970965)
                      ·
                        rfl

theorem cell23_1922527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1922527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922527 prefixEnd_1922527 := by exact prefixLift 1922527
  have htrace : WordTrace (prefixWord ++ tailWord_1922527) baseStart_1922527 baseEnd_1922527 := by
    simpa [prefixWord, tailWord_1922527, baseEnd_1922527] using wordTrace_append hprefix tailTrace_1922527
  have hstable : (prefixWord ++ tailWord_1922527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922527).length < 2 ^ (prefixWord ++ tailWord_1922527).sum := by decide
  have hdescent : baseEnd_1922527 < baseStart_1922527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922554 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2]
def baseStart_1922554 : Nat := 118140960795 + 1922554 * 2 ^ 59
def prefixEnd_1922554 : Nat := 4983230072969 + 3 ^ 40 * 1922554 * 2
def baseEnd_1922554 : Nat := 987194286224176232333341

theorem tailTrace_1922554 : CollatzResearch.WordTrace tailWord_1922554 prefixEnd_1922554 987194286224176232333341 := by
  unfold tailWord_1922554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530326269230669731835679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46747536717948452618228477 17530326269230669731835679)
  ·
    refine ⟨26295489403846004597753519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17530326269230669731835679 26295489403846004597753519)
    ·
      refine ⟨39443234105769006896630279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26295489403846004597753519 39443234105769006896630279)
      ·
        refine ⟨59164851158653510344945419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39443234105769006896630279 59164851158653510344945419)
        ·
          refine ⟨88747276737980265517418129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59164851158653510344945419 88747276737980265517418129)
          ·
            refine ⟨66560457553485199138063597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88747276737980265517418129 66560457553485199138063597)
            ·
              refine ⟨24960171582556949676773849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66560457553485199138063597 24960171582556949676773849)
              ·
                refine ⟨18720128686917712257580387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24960171582556949676773849 18720128686917712257580387)
                ·
                  refine ⟨28080193030376568386370581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18720128686917712257580387 28080193030376568386370581)
                  ·
                    refine ⟨1316259048298901643111121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28080193030376568386370581 1316259048298901643111121)
                    ·
                      refine ⟨987194286224176232333341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316259048298901643111121 987194286224176232333341)
                      ·
                        rfl

theorem cell23_1922554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_1922554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922554 prefixEnd_1922554 := by exact prefixLift 1922554
  have htrace : WordTrace (prefixWord ++ tailWord_1922554) baseStart_1922554 baseEnd_1922554 := by
    simpa [prefixWord, tailWord_1922554, baseEnd_1922554] using wordTrace_append hprefix tailTrace_1922554
  have hstable : (prefixWord ++ tailWord_1922554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922554).length < 2 ^ (prefixWord ++ tailWord_1922554).sum := by decide
  have hdescent : baseEnd_1922554 < baseStart_1922554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922566 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1922566 : Nat := 118140960795 + 1922566 * 2 ^ 59
def prefixEnd_1922566 : Nat := 4983230072969 + 3 ^ 40 * 1922566 * 2
def baseEnd_1922566 : Nat := 987200447992030185383287

theorem tailTrace_1922566 : CollatzResearch.WordTrace tailWord_1922566 prefixEnd_1922566 987200447992030185383287 := by
  unfold tailWord_1922566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191304461027475155524361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46747828501919469984519701 2191304461027475155524361)
  ·
    refine ⟨1643478345770606366643271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2191304461027475155524361 1643478345770606366643271)
    ·
      refine ⟨2465217518655909549964907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643478345770606366643271 2465217518655909549964907)
      ·
        refine ⟨3697826277983864324947361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465217518655909549964907 3697826277983864324947361)
        ·
          refine ⟨2773369708487898243710521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3697826277983864324947361 2773369708487898243710521)
          ·
            refine ⟨2080027281365923682782891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773369708487898243710521 2080027281365923682782891)
            ·
              refine ⟨3120040922048885524174337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080027281365923682782891 3120040922048885524174337)
              ·
                refine ⟨2340030691536664143130753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120040922048885524174337 2340030691536664143130753)
                ·
                  refine ⟨1755023018652498107348065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340030691536664143130753 1755023018652498107348065)
                  ·
                    refine ⟨1316267263989373580511049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755023018652498107348065 1316267263989373580511049)
                    ·
                      refine ⟨987200447992030185383287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316267263989373580511049 987200447992030185383287)
                      ·
                        rfl

theorem cell23_1922566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1922566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922566 prefixEnd_1922566 := by exact prefixLift 1922566
  have htrace : WordTrace (prefixWord ++ tailWord_1922566) baseStart_1922566 baseEnd_1922566 := by
    simpa [prefixWord, tailWord_1922566, baseEnd_1922566] using wordTrace_append hprefix tailTrace_1922566
  have hstable : (prefixWord ++ tailWord_1922566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922566).length < 2 ^ (prefixWord ++ tailWord_1922566).sum := by decide
  have hdescent : baseEnd_1922566 < baseStart_1922566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922577 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 8]
def baseStart_1922577 : Nat := 118140960795 + 1922577 * 2 ^ 59
def prefixEnd_1922577 : Nat := 4983230072969 + 3 ^ 40 * 1922577 * 2
def baseEnd_1922577 : Nat := 109689566253247738038415

theorem tailTrace_1922577 : CollatzResearch.WordTrace tailWord_1922577 prefixEnd_1922577 109689566253247738038415 := by
  unfold tailWord_1922577
  simp only [CollatzResearch.WordTrace]
  refine ⟨70122143955839353855429985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46748095970559569236953323 70122143955839353855429985)
  ·
    refine ⟨52591607966879515391572489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70122143955839353855429985 52591607966879515391572489)
    ·
      refine ⟨39443705975159636543679367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52591607966879515391572489 39443705975159636543679367)
      ·
        refine ⟨59165558962739454815519051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39443705975159636543679367 59165558962739454815519051)
        ·
          refine ⟨88748338444109182223278577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59165558962739454815519051 88748338444109182223278577)
          ·
            refine ⟨66561253833081886667458933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88748338444109182223278577 66561253833081886667458933)
            ·
              refine ⟨6240117546851426875074275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66561253833081886667458933 6240117546851426875074275)
              ·
                refine ⟨9360176320277140312611413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240117546851426875074275 9360176320277140312611413)
                ·
                  refine ⟨109689566253247738038415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9360176320277140312611413 109689566253247738038415)
                  ·
                    rfl

theorem cell23_1922577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_1922577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922577 prefixEnd_1922577 := by exact prefixLift 1922577
  have htrace : WordTrace (prefixWord ++ tailWord_1922577) baseStart_1922577 baseEnd_1922577 := by
    simpa [prefixWord, tailWord_1922577, baseEnd_1922577] using wordTrace_append hprefix tailTrace_1922577
  have hstable : (prefixWord ++ tailWord_1922577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922577).length < 2 ^ (prefixWord ++ tailWord_1922577).sum := by decide
  have hdescent : baseEnd_1922577 < baseStart_1922577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922581 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_1922581 : Nat := 118140960795 + 1922581 * 2 ^ 59
def prefixEnd_1922581 : Nat := 4983230072969 + 3 ^ 40 * 1922581 * 2
def baseEnd_1922581 : Nat := 329069383400615875565239

theorem tailTrace_1922581 : CollatzResearch.WordTrace tailWord_1922581 prefixEnd_1922581 329069383400615875565239 := by
  unfold tailWord_1922581
  simp only [CollatzResearch.WordTrace]
  refine ⟨70122289847824862538575597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46748193231883241692383731 70122289847824862538575597)
  ·
    refine ⟨26295858692934323451965849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70122289847824862538575597 26295858692934323451965849)
    ·
      refine ⟨19721894019700742588974387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26295858692934323451965849 19721894019700742588974387)
      ·
        refine ⟨29582841029551113883461581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19721894019700742588974387 29582841029551113883461581)
        ·
          refine ⟨11093565386081667706298093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29582841029551113883461581 11093565386081667706298093)
          ·
            refine ⟨4160087019780625389861785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11093565386081667706298093 4160087019780625389861785)
            ·
              refine ⟨3120065264835469042396339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160087019780625389861785 3120065264835469042396339)
              ·
                refine ⟨4680097897253203563594509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120065264835469042396339 4680097897253203563594509)
                ·
                  refine ⟨1755036711469951336347941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4680097897253203563594509 1755036711469951336347941)
                  ·
                    refine ⟨329069383400615875565239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755036711469951336347941 329069383400615875565239)
                    ·
                      rfl

theorem cell23_1922581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_1922581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922581 prefixEnd_1922581 := by exact prefixLift 1922581
  have htrace : WordTrace (prefixWord ++ tailWord_1922581) baseStart_1922581 baseEnd_1922581 := by
    simpa [prefixWord, tailWord_1922581, baseEnd_1922581] using wordTrace_append hprefix tailTrace_1922581
  have hstable : (prefixWord ++ tailWord_1922581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922581).length < 2 ^ (prefixWord ++ tailWord_1922581).sum := by decide
  have hdescent : baseEnd_1922581 < baseStart_1922581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922594 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_1922594 : Nat := 118140960795 + 1922594 * 2 ^ 59
def prefixEnd_1922594 : Nat := 4983230072969 + 3 ^ 40 * 1922594 * 2
def baseEnd_1922594 : Nat := 109690536161150675092573

theorem tailTrace_1922594 : CollatzResearch.WordTrace tailWord_1922594 prefixEnd_1922594 109690536161150675092573 := by
  unfold tailWord_1922594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530690999194441439699709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46748509331185177172532557 17530690999194441439699709)
  ·
    refine ⟨6574009124697915539887391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17530690999194441439699709 6574009124697915539887391)
    ·
      refine ⟨9861013687046873309831087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574009124697915539887391 9861013687046873309831087)
      ·
        refine ⟨14791520530570309964746631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9861013687046873309831087 14791520530570309964746631)
        ·
          refine ⟨22187280795855464947119947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14791520530570309964746631 22187280795855464947119947)
          ·
            refine ⟨33280921193783197420679921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22187280795855464947119947 33280921193783197420679921)
            ·
              refine ⟨24960690895337398065509941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33280921193783197420679921 24960690895337398065509941)
              ·
                refine ⟨2340064771437881068641557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24960690895337398065509941 2340064771437881068641557)
                ·
                  refine ⟨109690536161150675092573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2340064771437881068641557 109690536161150675092573)
                  ·
                    rfl

theorem cell23_1922594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_1922594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922594 prefixEnd_1922594 := by exact prefixLift 1922594
  have htrace : WordTrace (prefixWord ++ tailWord_1922594) baseStart_1922594 baseEnd_1922594 := by
    simpa [prefixWord, tailWord_1922594, baseEnd_1922594] using wordTrace_append hprefix tailTrace_1922594
  have hstable : (prefixWord ++ tailWord_1922594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922594).length < 2 ^ (prefixWord ++ tailWord_1922594).sum := by decide
  have hdescent : baseEnd_1922594 < baseStart_1922594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922597 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1922597 : Nat := 118140960795 + 1922597 * 2 ^ 59
def prefixEnd_1922597 : Nat := 4983230072969 + 3 ^ 40 * 1922597 * 2
def baseEnd_1922597 : Nat := 987216365892319564095643

theorem tailTrace_1922597 : CollatzResearch.WordTrace tailWord_1922597 prefixEnd_1922597 987216365892319564095643 := by
  unfold tailWord_1922597
  simp only [CollatzResearch.WordTrace]
  refine ⟨70122873415766897271158045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46748582277177931514105363 70122873415766897271158045)
  ·
    refine ⟨26296077530912586476684267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70122873415766897271158045 26296077530912586476684267)
    ·
      refine ⟨39444116296368879715026401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26296077530912586476684267 39444116296368879715026401)
      ·
        refine ⟨29583087222276659786269801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39444116296368879715026401 29583087222276659786269801)
        ·
          refine ⟨22187315416707494839702351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29583087222276659786269801 22187315416707494839702351)
          ·
            refine ⟨33280973125061242259553527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22187315416707494839702351 33280973125061242259553527)
            ·
              refine ⟨49921459687591863389330291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33280973125061242259553527 49921459687591863389330291)
              ·
                refine ⟨74882189531387795083995437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49921459687591863389330291 74882189531387795083995437)
                ·
                  refine ⟨28080821074270423156498289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74882189531387795083995437 28080821074270423156498289)
                  ·
                    refine ⟨21060615805702817367373717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28080821074270423156498289 21060615805702817367373717)
                    ·
                      refine ⟨987216365892319564095643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21060615805702817367373717 987216365892319564095643)
                      ·
                        rfl

theorem cell23_1922597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1922597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922597 prefixEnd_1922597 := by exact prefixLift 1922597
  have htrace : WordTrace (prefixWord ++ tailWord_1922597) baseStart_1922597 baseEnd_1922597 := by
    simpa [prefixWord, tailWord_1922597, baseEnd_1922597] using wordTrace_append hprefix tailTrace_1922597
  have hstable : (prefixWord ++ tailWord_1922597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922597).length < 2 ^ (prefixWord ++ tailWord_1922597).sum := by decide
  have hdescent : baseEnd_1922597 < baseStart_1922597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922661 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1922661 : Nat := 118140960795 + 1922661 * 2 ^ 59
def prefixEnd_1922661 : Nat := 4983230072969 + 3 ^ 40 * 1922661 * 2
def baseEnd_1922661 : Nat := 987249228654207313695349

theorem tailTrace_1922661 : CollatzResearch.WordTrace tailWord_1922661 prefixEnd_1922661 987249228654207313695349 := by
  unfold tailWord_1922661
  simp only [CollatzResearch.WordTrace]
  refine ⟨70125207687535036201487837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46750138458356690800991891 70125207687535036201487837)
  ·
    refine ⟨26296952882825638575557939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70125207687535036201487837 26296952882825638575557939)
    ·
      refine ⟨39445429324238457863336909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26296952882825638575557939 39445429324238457863336909)
      ·
        refine ⟨14792035996589421698751341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39445429324238457863336909 14792035996589421698751341)
        ·
          refine ⟨5547013498721033137031753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14792035996589421698751341 5547013498721033137031753)
          ·
            refine ⟨4160260124040774852773815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547013498721033137031753 4160260124040774852773815)
            ·
              refine ⟨6240390186061162279160723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160260124040774852773815 6240390186061162279160723)
              ·
                refine ⟨9360585279091743418741085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240390186061162279160723 9360585279091743418741085)
                ·
                  refine ⟨3510219479659403782027907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9360585279091743418741085 3510219479659403782027907)
                  ·
                    refine ⟨5265329219489105673041861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3510219479659403782027907 5265329219489105673041861)
                    ·
                      refine ⟨987249228654207313695349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5265329219489105673041861 987249228654207313695349)
                      ·
                        rfl

theorem cell23_1922661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1922661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922661 prefixEnd_1922661 := by exact prefixLift 1922661
  have htrace : WordTrace (prefixWord ++ tailWord_1922661) baseStart_1922661 baseEnd_1922661 := by
    simpa [prefixWord, tailWord_1922661, baseEnd_1922661] using wordTrace_append hprefix tailTrace_1922661
  have hstable : (prefixWord ++ tailWord_1922661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922661).length < 2 ^ (prefixWord ++ tailWord_1922661).sum := by decide
  have hdescent : baseEnd_1922661 < baseStart_1922661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922711 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1922711 : Nat := 118140960795 + 1922711 * 2 ^ 59
def prefixEnd_1922711 : Nat := 4983230072969 + 3 ^ 40 * 1922711 * 2
def baseEnd_1922711 : Nat := 987274902686932118070119

theorem tailTrace_1922711 : CollatzResearch.WordTrace tailWord_1922711 prefixEnd_1922711 987274902686932118070119 := by
  unfold tailWord_1922711
  simp only [CollatzResearch.WordTrace]
  refine ⟨70127031337353894740807987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46751354224902596493871991 70127031337353894740807987)
  ·
    refine ⟨105190547006030842111211981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70127031337353894740807987 105190547006030842111211981)
    ·
      refine ⟨39446455127261565791704493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105190547006030842111211981 39446455127261565791704493)
      ·
        refine ⟨14792420672723087171889185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39446455127261565791704493 14792420672723087171889185)
        ·
          refine ⟨11094315504542315378916889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14792420672723087171889185 11094315504542315378916889)
          ·
            refine ⟨8320736628406736534187667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11094315504542315378916889 8320736628406736534187667)
            ·
              refine ⟨12481104942610104801281501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320736628406736534187667 12481104942610104801281501)
              ·
                refine ⟨4680414353478789300480563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12481104942610104801281501 4680414353478789300480563)
                ·
                  refine ⟨7020621530218183950720845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680414353478789300480563 7020621530218183950720845)
                  ·
                    refine ⟨2632733073831818981520317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7020621530218183950720845 2632733073831818981520317)
                    ·
                      refine ⟨987274902686932118070119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2632733073831818981520317 987274902686932118070119)
                      ·
                        rfl

theorem cell23_1922711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1922711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922711 prefixEnd_1922711 := by exact prefixLift 1922711
  have htrace : WordTrace (prefixWord ++ tailWord_1922711) baseStart_1922711 baseEnd_1922711 := by
    simpa [prefixWord, tailWord_1922711, baseEnd_1922711] using wordTrace_append hprefix tailTrace_1922711
  have hstable : (prefixWord ++ tailWord_1922711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922711).length < 2 ^ (prefixWord ++ tailWord_1922711).sum := by decide
  have hdescent : baseEnd_1922711 < baseStart_1922711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922718 : List Nat := [4, 3, 1, 1, 1, 3, 3, 7]
def baseStart_1922718 : Nat := 118140960795 + 1922718 * 2 ^ 59
def prefixEnd_1922718 : Nat := 4983230072969 + 3 ^ 40 * 1922718 * 2
def baseEnd_1922718 : Nat := 36565870261167170025281

theorem tailTrace_1922718 : CollatzResearch.WordTrace tailWord_1922718 prefixEnd_1922718 36565870261167170025281 := by
  unfold tailWord_1922718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765910831041066867039101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46751524432219023290875205 8765910831041066867039101)
  ·
    refine ⟨3287216561640400075139663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8765910831041066867039101 3287216561640400075139663)
    ·
      refine ⟨4930824842460600112709495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287216561640400075139663 4930824842460600112709495)
      ·
        refine ⟨7396237263690900169064243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4930824842460600112709495 7396237263690900169064243)
        ·
          refine ⟨11094355895536350253596365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396237263690900169064243 11094355895536350253596365)
          ·
            refine ⟨4160383460826131345098637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11094355895536350253596365 4160383460826131345098637)
            ·
              refine ⟨1560143797809799254411989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4160383460826131345098637 1560143797809799254411989)
              ·
                refine ⟨36565870261167170025281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1560143797809799254411989 36565870261167170025281)
                ·
                  rfl

theorem cell23_1922718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_1922718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922718 prefixEnd_1922718 := by exact prefixLift 1922718
  have htrace : WordTrace (prefixWord ++ tailWord_1922718) baseStart_1922718 baseEnd_1922718 := by
    simpa [prefixWord, tailWord_1922718, baseEnd_1922718] using wordTrace_append hprefix tailTrace_1922718
  have hstable : (prefixWord ++ tailWord_1922718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922718).length < 2 ^ (prefixWord ++ tailWord_1922718).sum := by decide
  have hdescent : baseEnd_1922718 < baseStart_1922718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922762 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_1922762 : Nat := 118140960795 + 1922762 * 2 ^ 59
def prefixEnd_1922762 : Nat := 4983230072969 + 3 ^ 40 * 1922762 * 2
def baseEnd_1922762 : Nat := 987301090200311418532385

theorem tailTrace_1922762 : CollatzResearch.WordTrace tailWord_1922762 prefixEnd_1922762 987301090200311418532385 := by
  unfold tailWord_1922762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532222865042282612728635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46752594306779420300609693 17532222865042282612728635)
  ·
    refine ⟨26298334297563423919092953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17532222865042282612728635 26298334297563423919092953)
    ·
      refine ⟨19723750723172567939319715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26298334297563423919092953 19723750723172567939319715)
      ·
        refine ⟨29585626084758851908979573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19723750723172567939319715 29585626084758851908979573)
        ·
          refine ⟨2773652445446142366466835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29585626084758851908979573 2773652445446142366466835)
          ·
            refine ⟨4160478668169213549700253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773652445446142366466835 4160478668169213549700253)
            ·
              refine ⟨1560179500563455081137595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4160478668169213549700253 1560179500563455081137595)
              ·
                refine ⟨2340269250845182621706393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560179500563455081137595 2340269250845182621706393)
                ·
                  refine ⟨1755201938133886966279795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340269250845182621706393 1755201938133886966279795)
                  ·
                    refine ⟨2632802907200830449419693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1755201938133886966279795 2632802907200830449419693)
                    ·
                      refine ⟨987301090200311418532385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2632802907200830449419693 987301090200311418532385)
                      ·
                        rfl

theorem cell23_1922762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_1922762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922762 prefixEnd_1922762 := by exact prefixLift 1922762
  have htrace : WordTrace (prefixWord ++ tailWord_1922762) baseStart_1922762 baseEnd_1922762 := by
    simpa [prefixWord, tailWord_1922762, baseEnd_1922762] using wordTrace_append hprefix tailTrace_1922762
  have hstable : (prefixWord ++ tailWord_1922762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922762).length < 2 ^ (prefixWord ++ tailWord_1922762).sum := by decide
  have hdescent : baseEnd_1922762 < baseStart_1922762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922772 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1922772 : Nat := 118140960795 + 1922772 * 2 ^ 59
def prefixEnd_1922772 : Nat := 4983230072969 + 3 ^ 40 * 1922772 * 2
def baseEnd_1922772 : Nat := 987306225006856379407339

theorem tailTrace_1922772 : CollatzResearch.WordTrace tailWord_1922772 prefixEnd_1922772 987306225006856379407339 := by
  unfold tailWord_1922772
  simp only [CollatzResearch.WordTrace]
  refine ⟨35064628095066451079389285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46752837460088601439185713 35064628095066451079389285)
  ·
    refine ⟨6574617767824959577385491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35064628095066451079389285 6574617767824959577385491)
    ·
      refine ⟨9861926651737439366078237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574617767824959577385491 9861926651737439366078237)
      ·
        refine ⟨3698222494401539762279339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9861926651737439366078237 3698222494401539762279339)
        ·
          refine ⟨5547333741602309643419009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698222494401539762279339 5547333741602309643419009)
          ·
            refine ⟨4160500306201732232564257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547333741602309643419009 4160500306201732232564257)
            ·
              refine ⟨3120375229651299174423193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160500306201732232564257 3120375229651299174423193)
              ·
                refine ⟨2340281422238474380817395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120375229651299174423193 2340281422238474380817395)
                ·
                  refine ⟨3510422133357711571226093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340281422238474380817395 3510422133357711571226093)
                  ·
                    refine ⟨1316408300009141839209785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510422133357711571226093 1316408300009141839209785)
                    ·
                      refine ⟨987306225006856379407339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316408300009141839209785 987306225006856379407339)
                      ·
                        rfl

theorem cell23_1922772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1922772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922772 prefixEnd_1922772 := by exact prefixLift 1922772
  have htrace : WordTrace (prefixWord ++ tailWord_1922772) baseStart_1922772 baseEnd_1922772 := by
    simpa [prefixWord, tailWord_1922772, baseEnd_1922772] using wordTrace_append hprefix tailTrace_1922772
  have hstable : (prefixWord ++ tailWord_1922772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922772).length < 2 ^ (prefixWord ++ tailWord_1922772).sum := by decide
  have hdescent : baseEnd_1922772 < baseStart_1922772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922818 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1922818 : Nat := 118140960795 + 1922818 * 2 ^ 59
def prefixEnd_1922818 : Nat := 4983230072969 + 3 ^ 40 * 1922818 * 2
def baseEnd_1922818 : Nat := 987329845116963199432127

theorem tailTrace_1922818 : CollatzResearch.WordTrace tailWord_1922818 prefixEnd_1922818 987329845116963199432127 := by
  unfold tailWord_1922818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532733486991563003738277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46753955965310834676635405 17532733486991563003738277)
  ·
    refine ⟨3287387528810918063200927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17532733486991563003738277 3287387528810918063200927)
    ·
      refine ⟨4931081293216377094801391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287387528810918063200927 4931081293216377094801391)
      ·
        refine ⟨7396621939824565642202087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931081293216377094801391 7396621939824565642202087)
        ·
          refine ⟨11094932909736848463303131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396621939824565642202087 11094932909736848463303131)
          ·
            refine ⟨16642399364605272694954697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094932909736848463303131 16642399364605272694954697)
            ·
              refine ⟨12481799523453954521216023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16642399364605272694954697 12481799523453954521216023)
              ·
                refine ⟨18722699285180931781824035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12481799523453954521216023 18722699285180931781824035)
                ·
                  refine ⟨28084048927771397672736053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18722699285180931781824035 28084048927771397672736053)
                  ·
                    refine ⟨2632879586978568531819005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28084048927771397672736053 2632879586978568531819005)
                    ·
                      refine ⟨987329845116963199432127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2632879586978568531819005 987329845116963199432127)
                      ·
                        rfl

theorem cell23_1922818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1922818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922818 prefixEnd_1922818 := by exact prefixLift 1922818
  have htrace : WordTrace (prefixWord ++ tailWord_1922818) baseStart_1922818 baseEnd_1922818 := by
    simpa [prefixWord, tailWord_1922818, baseEnd_1922818] using wordTrace_append hprefix tailTrace_1922818
  have hstable : (prefixWord ++ tailWord_1922818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922818).length < 2 ^ (prefixWord ++ tailWord_1922818).sum := by decide
  have hdescent : baseEnd_1922818 < baseStart_1922818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922892 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 2, 1, 4]
def baseStart_1922892 : Nat := 118140960795 + 1922892 * 2 ^ 59
def prefixEnd_1922892 : Nat := 4983230072969 + 3 ^ 40 * 1922892 * 2
def baseEnd_1922892 : Nat := 987367842685395909906787

theorem tailTrace_1922892 : CollatzResearch.WordTrace tailWord_1922892 prefixEnd_1922892 987367842685395909906787 := by
  unfold tailWord_1922892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35066816474849081326573465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46755755299798775102097953 35066816474849081326573465)
  ·
    refine ⟨26300112356136810994930099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35066816474849081326573465 26300112356136810994930099)
    ·
      refine ⟨39450168534205216492395149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26300112356136810994930099 39450168534205216492395149)
      ·
        refine ⟨14793813200326956184648181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39450168534205216492395149 14793813200326956184648181)
        ·
          refine ⟨1386919987530652142310767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14793813200326956184648181 1386919987530652142310767)
          ·
            refine ⟨2080379981295978213466151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386919987530652142310767 2080379981295978213466151)
            ·
              refine ⟨3120569971943967320199227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080379981295978213466151 3120569971943967320199227)
              ·
                refine ⟨4680854957915950980298841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120569971943967320199227 4680854957915950980298841)
                ·
                  refine ⟨3510641218436963235224131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4680854957915950980298841 3510641218436963235224131)
                  ·
                    refine ⟨5265961827655444852836197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3510641218436963235224131 5265961827655444852836197)
                    ·
                      refine ⟨987367842685395909906787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5265961827655444852836197 987367842685395909906787)
                      ·
                        rfl

theorem cell23_1922892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_1922892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922892 prefixEnd_1922892 := by exact prefixLift 1922892
  have htrace : WordTrace (prefixWord ++ tailWord_1922892) baseStart_1922892 baseEnd_1922892 := by
    simpa [prefixWord, tailWord_1922892, baseEnd_1922892] using wordTrace_append hprefix tailTrace_1922892
  have hstable : (prefixWord ++ tailWord_1922892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922892).length < 2 ^ (prefixWord ++ tailWord_1922892).sum := by decide
  have hdescent : baseEnd_1922892 < baseStart_1922892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922915 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 6]
def baseStart_1922915 : Nat := 118140960795 + 1922915 * 2 ^ 59
def prefixEnd_1922915 : Nat := 4983230072969 + 3 ^ 40 * 1922915 * 2
def baseEnd_1922915 : Nat := 109708850304494368879909

theorem tailTrace_1922915 : CollatzResearch.WordTrace tailWord_1922915 prefixEnd_1922915 109708850304494368879909 := by
  unfold tailWord_1922915
  simp only [CollatzResearch.WordTrace]
  refine ⟨70134471828614837581234199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46756314552409891720822799 70134471828614837581234199)
  ·
    refine ⟨105201707742922256371851299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70134471828614837581234199 105201707742922256371851299)
    ·
      refine ⟨157802561614383384557776949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105201707742922256371851299 157802561614383384557776949)
      ·
        refine ⟨14793990151348442302291589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157802561614383384557776949 14793990151348442302291589)
        ·
          refine ⟨2773873153377832931679673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14793990151348442302291589 2773873153377832931679673)
          ·
            refine ⟨2080404865033374698759755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773873153377832931679673 2080404865033374698759755)
            ·
              refine ⟨3120607297550062048139633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080404865033374698759755 3120607297550062048139633)
              ·
                refine ⟨2340455473162546536104725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120607297550062048139633 2340455473162546536104725)
                ·
                  refine ⟨109708850304494368879909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2340455473162546536104725 109708850304494368879909)
                  ·
                    rfl

theorem cell23_1922915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 6].length) (baseStart_1922915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922915 prefixEnd_1922915 := by exact prefixLift 1922915
  have htrace : WordTrace (prefixWord ++ tailWord_1922915) baseStart_1922915 baseEnd_1922915 := by
    simpa [prefixWord, tailWord_1922915, baseEnd_1922915] using wordTrace_append hprefix tailTrace_1922915
  have hstable : (prefixWord ++ tailWord_1922915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922915).length < 2 ^ (prefixWord ++ tailWord_1922915).sum := by decide
  have hdescent : baseEnd_1922915 < baseStart_1922915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922925 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1922925 : Nat := 118140960795 + 1922925 * 2 ^ 59
def prefixEnd_1922925 : Nat := 4983230072969 + 3 ^ 40 * 1922925 * 2
def baseEnd_1922925 : Nat := 987384787546994280794135

theorem tailTrace_1922925 : CollatzResearch.WordTrace tailWord_1922925 prefixEnd_1922925 987384787546994280794135 := by
  unfold tailWord_1922925
  simp only [CollatzResearch.WordTrace]
  refine ⟨70134836558578609289098229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46756557705719072859398819 70134836558578609289098229)
  ·
    refine ⟨6575140927366744620852959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70134836558578609289098229 6575140927366744620852959)
    ·
      refine ⟨9862711391050116931279439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575140927366744620852959 9862711391050116931279439)
      ·
        refine ⟨14794067086575175396919159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862711391050116931279439 14794067086575175396919159)
        ·
          refine ⟨22191100629862763095378739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794067086575175396919159 22191100629862763095378739)
          ·
            refine ⟨33286650944794144643068109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22191100629862763095378739 33286650944794144643068109)
            ·
              refine ⟨12482494104297804241150541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33286650944794144643068109 12482494104297804241150541)
              ·
                refine ⟨4680935289111676590431453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12482494104297804241150541 4680935289111676590431453)
                ·
                  refine ⟨1755350733416878721411795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4680935289111676590431453 1755350733416878721411795)
                  ·
                    refine ⟨2633026100125318082117693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1755350733416878721411795 2633026100125318082117693)
                    ·
                      refine ⟨987384787546994280794135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2633026100125318082117693 987384787546994280794135)
                      ·
                        rfl

theorem cell23_1922925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1922925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922925 prefixEnd_1922925 := by exact prefixLift 1922925
  have htrace : WordTrace (prefixWord ++ tailWord_1922925) baseStart_1922925 baseEnd_1922925 := by
    simpa [prefixWord, tailWord_1922925, baseEnd_1922925] using wordTrace_append hprefix tailTrace_1922925
  have hstable : (prefixWord ++ tailWord_1922925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922925).length < 2 ^ (prefixWord ++ tailWord_1922925).sum := by decide
  have hdescent : baseEnd_1922925 < baseStart_1922925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922948 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1922948 : Nat := 118140960795 + 1922948 * 2 ^ 59
def prefixEnd_1922948 : Nat := 4983230072969 + 3 ^ 40 * 1922948 * 2
def baseEnd_1922948 : Nat := 987396597602047690806529

theorem tailTrace_1922948 : CollatzResearch.WordTrace tailWord_1922948 prefixEnd_1922948 987396597602047690806529 := by
  unfold tailWord_1922948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35067837718747642108592749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46757116958330189478123665 35067837718747642108592749)
  ·
    refine ⟨13150439144530365790722281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35067837718747642108592749 13150439144530365790722281)
    ·
      refine ⟨9862829358397774343041711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13150439144530365790722281 9862829358397774343041711)
      ·
        refine ⟨14794244037596661514562567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862829358397774343041711 14794244037596661514562567)
        ·
          refine ⟨22191366056394992271843851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794244037596661514562567 22191366056394992271843851)
          ·
            refine ⟨33287049084592488407765777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22191366056394992271843851 33287049084592488407765777)
            ·
              refine ⟨24965286813444366305824333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33287049084592488407765777 24965286813444366305824333)
              ·
                refine ⟨9361982555041637364684125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24965286813444366305824333 9361982555041637364684125)
                ·
                  refine ⟨3510743458140614011756547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9361982555041637364684125 3510743458140614011756547)
                  ·
                    refine ⟨5266115187210921017634821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3510743458140614011756547 5266115187210921017634821)
                    ·
                      refine ⟨987396597602047690806529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5266115187210921017634821 987396597602047690806529)
                      ·
                        rfl

theorem cell23_1922948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1922948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922948 prefixEnd_1922948 := by exact prefixLift 1922948
  have htrace : WordTrace (prefixWord ++ tailWord_1922948) baseStart_1922948 baseEnd_1922948 := by
    simpa [prefixWord, tailWord_1922948, baseEnd_1922948] using wordTrace_append hprefix tailTrace_1922948
  have hstable : (prefixWord ++ tailWord_1922948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922948).length < 2 ^ (prefixWord ++ tailWord_1922948).sum := by decide
  have hdescent : baseEnd_1922948 < baseStart_1922948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922991 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_1922991 : Nat := 118140960795 + 1922991 * 2 ^ 59
def prefixEnd_1922991 : Nat := 4983230072969 + 3 ^ 40 * 1922991 * 2
def baseEnd_1922991 : Nat := 987418677270191022568831

theorem tailTrace_1922991 : CollatzResearch.WordTrace tailWord_1922991 prefixEnd_1922991 987418677270191022568831 := by
  unfold tailWord_1922991
  simp only [CollatzResearch.WordTrace]
  refine ⟨70137243776339502561000827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46758162517559668374000551 70137243776339502561000827)
  ·
    refine ⟨105205865664509253841501241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70137243776339502561000827 105205865664509253841501241)
    ·
      refine ⟨78904399248381940381125931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105205865664509253841501241 78904399248381940381125931)
      ·
        refine ⟨118356598872572910571688897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78904399248381940381125931 118356598872572910571688897)
        ·
          refine ⟨88767449154429682928766673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118356598872572910571688897 88767449154429682928766673)
          ·
            refine ⟨66575586865822262196575005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88767449154429682928766673 66575586865822262196575005)
            ·
              refine ⟨24965845074683348323715627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66575586865822262196575005 24965845074683348323715627)
              ·
                refine ⟨37448767612025022485573441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24965845074683348323715627 37448767612025022485573441)
                ·
                  refine ⟨28086575709018766864180081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37448767612025022485573441 28086575709018766864180081)
                  ·
                    refine ⟨21064931781764075148135061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28086575709018766864180081 21064931781764075148135061)
                    ·
                      refine ⟨987418677270191022568831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21064931781764075148135061 987418677270191022568831)
                      ·
                        rfl

theorem cell23_1922991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_1922991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922991 prefixEnd_1922991 := by exact prefixLift 1922991
  have htrace : WordTrace (prefixWord ++ tailWord_1922991) baseStart_1922991 baseEnd_1922991 := by
    simpa [prefixWord, tailWord_1922991, baseEnd_1922991] using wordTrace_append hprefix tailTrace_1922991
  have hstable : (prefixWord ++ tailWord_1922991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922991).length < 2 ^ (prefixWord ++ tailWord_1922991).sum := by decide
  have hdescent : baseEnd_1922991 < baseStart_1922991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922996 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1922996 : Nat := 118140960795 + 1922996 * 2 ^ 59
def prefixEnd_1922996 : Nat := 4983230072969 + 3 ^ 40 * 1922996 * 2
def baseEnd_1922996 : Nat := 329140414891154501002103

theorem tailTrace_1922996 : CollatzResearch.WordTrace tailWord_1922996 prefixEnd_1922996 329140414891154501002103 := by
  unfold tailWord_1922996
  simp only [CollatzResearch.WordTrace]
  refine ⟨35068713070660694207466421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46758284094214258943288561 35068713070660694207466421)
  ·
    refine ⟨3287691850374440081949977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35068713070660694207466421 3287691850374440081949977)
    ·
      refine ⟨2465768887780830061462483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3287691850374440081949977 2465768887780830061462483)
      ·
        refine ⟨3698653331671245092193725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465768887780830061462483 3698653331671245092193725)
        ·
          refine ⟨1386994999376716909572647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3698653331671245092193725 1386994999376716909572647)
          ·
            refine ⟨2080492499065075364358971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386994999376716909572647 2080492499065075364358971)
            ·
              refine ⟨3120738748597613046538457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080492499065075364358971 3120738748597613046538457)
              ·
                refine ⟨2340554061448209784903843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120738748597613046538457 2340554061448209784903843)
                ·
                  refine ⟨3510831092172314677355765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340554061448209784903843 3510831092172314677355765)
                  ·
                    refine ⟨329140414891154501002103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3510831092172314677355765 329140414891154501002103)
                    ·
                      rfl

theorem cell23_1922996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1922996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1922996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1922996 prefixEnd_1922996 := by exact prefixLift 1922996
  have htrace : WordTrace (prefixWord ++ tailWord_1922996) baseStart_1922996 baseEnd_1922996 := by
    simpa [prefixWord, tailWord_1922996, baseEnd_1922996] using wordTrace_append hprefix tailTrace_1922996
  have hstable : (prefixWord ++ tailWord_1922996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922996).length < 2 ^ (prefixWord ++ tailWord_1922996).sum := by decide
  have hdescent : baseEnd_1922996 < baseStart_1922996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923032 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_1923032 : Nat := 118140960795 + 1923032 * 2 ^ 59
def prefixEnd_1923032 : Nat := 4983230072969 + 3 ^ 40 * 1923032 * 2
def baseEnd_1923032 : Nat := 987439729977025362156143

theorem tailTrace_1923032 : CollatzResearch.WordTrace tailWord_1923032 prefixEnd_1923032 987439729977025362156143 := by
  unfold tailWord_1923032
  simp only [CollatzResearch.WordTrace]
  refine ⟨35069369584595483281621675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46759159446127311042162233 35069369584595483281621675)
  ·
    refine ⟨52604054376893224922432513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35069369584595483281621675 52604054376893224922432513)
    ·
      refine ⟨39453040782669918691824385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52604054376893224922432513 39453040782669918691824385)
      ·
        refine ⟨29589780587002439018868289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39453040782669918691824385 29589780587002439018868289)
        ·
          refine ⟨22192335440251829264151217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29589780587002439018868289 22192335440251829264151217)
          ·
            refine ⟨16644251580188871948113413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22192335440251829264151217 16644251580188871948113413)
            ·
              refine ⟨3120797171285413490271265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16644251580188871948113413 3120797171285413490271265)
              ·
                refine ⟨2340597878464060117703449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120797171285413490271265 2340597878464060117703449)
                ·
                  refine ⟨1755448408848045088277587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340597878464060117703449 1755448408848045088277587)
                  ·
                    refine ⟨2633172613272067632416381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1755448408848045088277587 2633172613272067632416381)
                    ·
                      refine ⟨987439729977025362156143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2633172613272067632416381 987439729977025362156143)
                      ·
                        rfl

theorem cell23_1923032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_1923032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923032 prefixEnd_1923032 := by exact prefixLift 1923032
  have htrace : WordTrace (prefixWord ++ tailWord_1923032) baseStart_1923032 baseEnd_1923032 := by
    simpa [prefixWord, tailWord_1923032, baseEnd_1923032] using wordTrace_append hprefix tailTrace_1923032
  have hstable : (prefixWord ++ tailWord_1923032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923032).length < 2 ^ (prefixWord ++ tailWord_1923032).sum := by decide
  have hdescent : baseEnd_1923032 < baseStart_1923032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923033 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 1, 2, 2]
def baseStart_1923033 : Nat := 118140960795 + 1923033 * 2 ^ 59
def prefixEnd_1923033 : Nat := 4983230072969 + 3 ^ 40 * 1923033 * 2
def baseEnd_1923033 : Nat := 987440243457679858243639

theorem tailTrace_1923033 : CollatzResearch.WordTrace tailWord_1923033 prefixEnd_1923033 987440243457679858243639 := by
  unfold tailWord_1923033
  simp only [CollatzResearch.WordTrace]
  refine ⟨70138775642187343734029753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46759183761458229156019835 70138775642187343734029753)
  ·
    refine ⟨52604081731640507800522315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70138775642187343734029753 52604081731640507800522315)
    ·
      refine ⟨78906122597460761700783473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52604081731640507800522315 78906122597460761700783473)
      ·
        refine ⟨59179591948095571275587605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78906122597460761700783473 59179591948095571275587605)
        ·
          refine ⟨2774043372566979903543169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59179591948095571275587605 2774043372566979903543169)
          ·
            refine ⟨2080532529425234927657377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774043372566979903543169 2080532529425234927657377)
            ·
              refine ⟨1560399397068926195743033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080532529425234927657377 1560399397068926195743033)
              ·
                refine ⟨1170299547801694646807275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560399397068926195743033 1170299547801694646807275)
                ·
                  refine ⟨1755449321702541970210913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170299547801694646807275 1755449321702541970210913)
                  ·
                    refine ⟨1316586991276906477658185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755449321702541970210913 1316586991276906477658185)
                    ·
                      refine ⟨987440243457679858243639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316586991276906477658185 987440243457679858243639)
                      ·
                        rfl

theorem cell23_1923033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_1923033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923033 prefixEnd_1923033 := by exact prefixLift 1923033
  have htrace : WordTrace (prefixWord ++ tailWord_1923033) baseStart_1923033 baseEnd_1923033 := by
    simpa [prefixWord, tailWord_1923033, baseEnd_1923033] using wordTrace_append hprefix tailTrace_1923033
  have hstable : (prefixWord ++ tailWord_1923033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923033).length < 2 ^ (prefixWord ++ tailWord_1923033).sum := by decide
  have hdescent : baseEnd_1923033 < baseStart_1923033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923068 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1923068 : Nat := 118140960795 + 1923068 * 2 ^ 59
def prefixEnd_1923068 : Nat := 4983230072969 + 3 ^ 40 * 1923068 * 2
def baseEnd_1923068 : Nat := 987458215280587221305977

theorem tailTrace_1923068 : CollatzResearch.WordTrace tailWord_1923068 prefixEnd_1923068 987458215280587221305977 := by
  unfold tailWord_1923068
  simp only [CollatzResearch.WordTrace]
  refine ⟨35070026098530272355776929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46760034798040363141035905 35070026098530272355776929)
  ·
    refine ⟨26302519573897704266832697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35070026098530272355776929 26302519573897704266832697)
    ·
      refine ⟨19726889680423278200124523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26302519573897704266832697 19726889680423278200124523)
      ·
        refine ⟨29590334520634917300186785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19726889680423278200124523 29590334520634917300186785)
        ·
          refine ⟨22192750890476187975140089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29590334520634917300186785 22192750890476187975140089)
          ·
            refine ⟨16644563167857140981355067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22192750890476187975140089 16644563167857140981355067)
            ·
              refine ⟨24966844751785711472032601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644563167857140981355067 24966844751785711472032601)
              ·
                refine ⟨18725133563839283604024451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24966844751785711472032601 18725133563839283604024451)
                ·
                  refine ⟨28087700345758925406036677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18725133563839283604024451 28087700345758925406036677)
                  ·
                    refine ⟨5266443814829798513631877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28087700345758925406036677 5266443814829798513631877)
                    ·
                      refine ⟨987458215280587221305977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5266443814829798513631877 987458215280587221305977)
                      ·
                        rfl

theorem cell23_1923068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1923068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923068 prefixEnd_1923068 := by exact prefixLift 1923068
  have htrace : WordTrace (prefixWord ++ tailWord_1923068) baseStart_1923068 baseEnd_1923068 := by
    simpa [prefixWord, tailWord_1923068, baseEnd_1923068] using wordTrace_append hprefix tailTrace_1923068
  have hstable : (prefixWord ++ tailWord_1923068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923068).length < 2 ^ (prefixWord ++ tailWord_1923068).sum := by decide
  have hdescent : baseEnd_1923068 < baseStart_1923068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923076 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1923076 : Nat := 118140960795 + 1923076 * 2 ^ 59
def prefixEnd_1923076 : Nat := 4983230072969 + 3 ^ 40 * 1923076 * 2
def baseEnd_1923076 : Nat := 987462323125823190005941

theorem tailTrace_1923076 : CollatzResearch.WordTrace tailWord_1923076 prefixEnd_1923076 987462323125823190005941 := by
  unfold tailWord_1923076
  simp only [CollatzResearch.WordTrace]
  refine ⟨35070171990515781038922541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46760229320687708051896721 35070171990515781038922541)
  ·
    refine ⟨13151314496443417889595953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35070171990515781038922541 13151314496443417889595953)
    ·
      refine ⟨9863485872332563417196965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13151314496443417889595953 9863485872332563417196965)
      ·
        refine ⟨1849403601062355640724431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9863485872332563417196965 1849403601062355640724431)
        ·
          refine ⟨2774105401593533461086647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849403601062355640724431 2774105401593533461086647)
          ·
            refine ⟨4161158102390300191629971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774105401593533461086647 4161158102390300191629971)
            ·
              refine ⟨6241737153585450287444957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161158102390300191629971 6241737153585450287444957)
              ·
                refine ⟨2340651432594543857791859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6241737153585450287444957 2340651432594543857791859)
                ·
                  refine ⟨3510977148891815786687789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340651432594543857791859 3510977148891815786687789)
                  ·
                    refine ⟨1316616430834430920007921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510977148891815786687789 1316616430834430920007921)
                    ·
                      refine ⟨987462323125823190005941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316616430834430920007921 987462323125823190005941)
                      ·
                        rfl

theorem cell23_1923076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1923076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923076 prefixEnd_1923076 := by exact prefixLift 1923076
  have htrace : WordTrace (prefixWord ++ tailWord_1923076) baseStart_1923076 baseEnd_1923076 := by
    simpa [prefixWord, tailWord_1923076, baseEnd_1923076] using wordTrace_append hprefix tailTrace_1923076
  have hstable : (prefixWord ++ tailWord_1923076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923076).length < 2 ^ (prefixWord ++ tailWord_1923076).sum := by decide
  have hdescent : baseEnd_1923076 < baseStart_1923076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923088 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_1923088 : Nat := 118140960795 + 1923088 * 2 ^ 59
def prefixEnd_1923088 : Nat := 4983230072969 + 3 ^ 40 * 1923088 * 2
def baseEnd_1923088 : Nat := 987468484893677143055885

theorem tailTrace_1923088 : CollatzResearch.WordTrace tailWord_1923088 prefixEnd_1923088 987468484893677143055885 := by
  unfold tailWord_1923088
  simp only [CollatzResearch.WordTrace]
  refine ⟨35070390828494044063640959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46760521104658725418187945 35070390828494044063640959)
  ·
    refine ⟨52605586242741066095461439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35070390828494044063640959 52605586242741066095461439)
    ·
      refine ⟨78908379364111599143192159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52605586242741066095461439 78908379364111599143192159)
      ·
        refine ⟨118362569046167398714788239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78908379364111599143192159 118362569046167398714788239)
        ·
          refine ⟨177543853569251098072182359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118362569046167398714788239 177543853569251098072182359)
          ·
            refine ⟨266315780353876647108273539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177543853569251098072182359 266315780353876647108273539)
            ·
              refine ⟨399473670530814970662410309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266315780353876647108273539 399473670530814970662410309)
              ·
                refine ⟨74901313224527806999201933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399473670530814970662410309 74901313224527806999201933)
                ·
                  refine ⟨28087992459197927624700725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74901313224527806999201933 28087992459197927624700725)
                  ·
                    refine ⟨2633249293049805714815693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28087992459197927624700725 2633249293049805714815693)
                    ·
                      refine ⟨987468484893677143055885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2633249293049805714815693 987468484893677143055885)
                      ·
                        rfl

theorem cell23_1923088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_1923088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923088 prefixEnd_1923088 := by exact prefixLift 1923088
  have htrace : WordTrace (prefixWord ++ tailWord_1923088) baseStart_1923088 baseEnd_1923088 := by
    simpa [prefixWord, tailWord_1923088, baseEnd_1923088] using wordTrace_append hprefix tailTrace_1923088
  have hstable : (prefixWord ++ tailWord_1923088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923088).length < 2 ^ (prefixWord ++ tailWord_1923088).sum := by decide
  have hdescent : baseEnd_1923088 < baseStart_1923088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923106 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_1923106 : Nat := 118140960795 + 1923106 * 2 ^ 59
def prefixEnd_1923106 : Nat := 4983230072969 + 3 ^ 40 * 1923106 * 2
def baseEnd_1923106 : Nat := 987477727545458072630803

theorem tailTrace_1923106 : CollatzResearch.WordTrace tailWord_1923106 prefixEnd_1923106 987477727545458072630803 := by
  unfold tailWord_1923106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535359542730719300359293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46760958780615251467624781 17535359542730719300359293)
  ·
    refine ⟨6575759828524019737634735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17535359542730719300359293 6575759828524019737634735)
    ·
      refine ⟨9863639742786029606452103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575759828524019737634735 9863639742786029606452103)
      ·
        refine ⟨14795459614179044409678155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863639742786029606452103 14795459614179044409678155)
        ·
          refine ⟨22193189421268566614517233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14795459614179044409678155 22193189421268566614517233)
          ·
            refine ⟨16644892065951424960887925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22193189421268566614517233 16644892065951424960887925)
            ·
              refine ⟨1560458631182946090083243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16644892065951424960887925 1560458631182946090083243)
              ·
                refine ⟨2340687946774419135124865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560458631182946090083243 2340687946774419135124865)
                ·
                  refine ⟨1755515960080814351343649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340687946774419135124865 1755515960080814351343649)
                  ·
                    refine ⟨1316636970060610763507737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755515960080814351343649 1316636970060610763507737)
                    ·
                      refine ⟨987477727545458072630803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316636970060610763507737 987477727545458072630803)
                      ·
                        rfl

theorem cell23_1923106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_1923106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923106 prefixEnd_1923106 := by exact prefixLift 1923106
  have htrace : WordTrace (prefixWord ++ tailWord_1923106) baseStart_1923106 baseEnd_1923106 := by
    simpa [prefixWord, tailWord_1923106, baseEnd_1923106] using wordTrace_append hprefix tailTrace_1923106
  have hstable : (prefixWord ++ tailWord_1923106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923106).length < 2 ^ (prefixWord ++ tailWord_1923106).sum := by decide
  have hdescent : baseEnd_1923106 < baseStart_1923106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923129 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 5]
def baseStart_1923129 : Nat := 118140960795 + 1923129 * 2 ^ 59
def prefixEnd_1923129 : Nat := 4983230072969 + 3 ^ 40 * 1923129 * 2
def baseEnd_1923129 : Nat := 109721059733390164738133

theorem tailTrace_1923129 : CollatzResearch.WordTrace tailWord_1923129 prefixEnd_1923129 109721059733390164738133 := by
  unfold tailWord_1923129
  simp only [CollatzResearch.WordTrace]
  refine ⟨70142277049839552129524441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46761518033226368086349627 70142277049839552129524441)
  ·
    refine ⟨52606707787379664097143331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70142277049839552129524441 52606707787379664097143331)
    ·
      refine ⟨78910061681069496145714997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52606707787379664097143331 78910061681069496145714997)
      ·
        refine ⟨7397818282600265263660781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78910061681069496145714997 7397818282600265263660781)
        ·
          refine ⟨2774181855975099473872793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7397818282600265263660781 2774181855975099473872793)
          ·
            refine ⟨2080636391981324605404595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774181855975099473872793 2080636391981324605404595)
            ·
              refine ⟨3120954587971986908106893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080636391981324605404595 3120954587971986908106893)
              ·
                refine ⟨1170357970489495090540085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3120954587971986908106893 1170357970489495090540085)
                ·
                  refine ⟨109721059733390164738133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1170357970489495090540085 109721059733390164738133)
                  ·
                    rfl

theorem cell23_1923129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 5].length) (baseStart_1923129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923129 prefixEnd_1923129 := by exact prefixLift 1923129
  have htrace : WordTrace (prefixWord ++ tailWord_1923129) baseStart_1923129 baseEnd_1923129 := by
    simpa [prefixWord, tailWord_1923129, baseEnd_1923129] using wordTrace_append hprefix tailTrace_1923129
  have hstable : (prefixWord ++ tailWord_1923129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923129).length < 2 ^ (prefixWord ++ tailWord_1923129).sum := by decide
  have hdescent : baseEnd_1923129 < baseStart_1923129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923145 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_1923145 : Nat := 118140960795 + 1923145 * 2 ^ 59
def prefixEnd_1923145 : Nat := 4983230072969 + 3 ^ 40 * 1923145 * 2
def baseEnd_1923145 : Nat := 987497753290983420043123

theorem tailTrace_1923145 : CollatzResearch.WordTrace tailWord_1923145 prefixEnd_1923145 987497753290983420043123 := by
  unfold tailWord_1923145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70142860617781586862106889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46761907078521057908071259 70142860617781586862106889)
  ·
    refine ⟨52607145463336190146580167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70142860617781586862106889 52607145463336190146580167)
    ·
      refine ⟨78910718195004285219870251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52607145463336190146580167 78910718195004285219870251)
      ·
        refine ⟨118366077292506427829805377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78910718195004285219870251 118366077292506427829805377)
        ·
          refine ⟨88774557969379820872354033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118366077292506427829805377 88774557969379820872354033)
          ·
            refine ⟨66580918477034865654265525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88774557969379820872354033 66580918477034865654265525)
            ·
              refine ⟨6241961107222018655087393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66580918477034865654265525 6241961107222018655087393)
              ·
                refine ⟨4681470830416513991315545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6241961107222018655087393 4681470830416513991315545)
                ·
                  refine ⟨3511103122812385493486659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4681470830416513991315545 3511103122812385493486659)
                  ·
                    refine ⟨5266654684218578240229989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3511103122812385493486659 5266654684218578240229989)
                    ·
                      refine ⟨987497753290983420043123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5266654684218578240229989 987497753290983420043123)
                      ·
                        rfl

theorem cell23_1923145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_1923145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923145 prefixEnd_1923145 := by exact prefixLift 1923145
  have htrace : WordTrace (prefixWord ++ tailWord_1923145) baseStart_1923145 baseEnd_1923145 := by
    simpa [prefixWord, tailWord_1923145, baseEnd_1923145] using wordTrace_append hprefix tailTrace_1923145
  have hstable : (prefixWord ++ tailWord_1923145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923145).length < 2 ^ (prefixWord ++ tailWord_1923145).sum := by decide
  have hdescent : baseEnd_1923145 < baseStart_1923145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923229 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1923229 : Nat := 118140960795 + 1923229 * 2 ^ 59
def prefixEnd_1923229 : Nat := 4983230072969 + 3 ^ 40 * 1923229 * 2
def baseEnd_1923229 : Nat := 987540885665961091392737

theorem tailTrace_1923229 : CollatzResearch.WordTrace tailWord_1923229 prefixEnd_1923229 987540885665961091392737 := by
  unfold tailWord_1923229
  simp only [CollatzResearch.WordTrace]
  refine ⟨70145924349477269208164741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46763949566318179472109827 70145924349477269208164741)
  ·
    refine ⟨13152360815526987976530889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70145924349477269208164741 13152360815526987976530889)
    ·
      refine ⟨9864270611645240982398167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13152360815526987976530889 9864270611645240982398167)
      ·
        refine ⟨14796405917467861473597251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864270611645240982398167 14796405917467861473597251)
        ·
          refine ⟨22194608876201792210395877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796405917467861473597251 22194608876201792210395877)
          ·
            refine ⟨4161489164287836039449227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22194608876201792210395877 4161489164287836039449227)
            ·
              refine ⟨6242233746431754059173841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161489164287836039449227 6242233746431754059173841)
              ·
                refine ⟨4681675309823815544380381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6242233746431754059173841 4681675309823815544380381)
                ·
                  refine ⟨1755628241183930829142643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4681675309823815544380381 1755628241183930829142643)
                  ·
                    refine ⟨2633442361775896243713965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1755628241183930829142643 2633442361775896243713965)
                    ·
                      refine ⟨987540885665961091392737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2633442361775896243713965 987540885665961091392737)
                      ·
                        rfl

theorem cell23_1923229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1923229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923229 prefixEnd_1923229 := by exact prefixLift 1923229
  have htrace : WordTrace (prefixWord ++ tailWord_1923229) baseStart_1923229 baseEnd_1923229 := by
    simpa [prefixWord, tailWord_1923229, baseEnd_1923229] using wordTrace_append hprefix tailTrace_1923229
  have hstable : (prefixWord ++ tailWord_1923229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923229).length < 2 ^ (prefixWord ++ tailWord_1923229).sum := by decide
  have hdescent : baseEnd_1923229 < baseStart_1923229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923249 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 1, 5]
def baseStart_1923249 : Nat := 118140960795 + 1923249 * 2 ^ 59
def prefixEnd_1923249 : Nat := 4983230072969 + 3 ^ 40 * 1923249 * 2
def baseEnd_1923249 : Nat := 329183718426350337714215

theorem tailTrace_1923249 : CollatzResearch.WordTrace tailWord_1923249 prefixEnd_1923249 329183718426350337714215 := by
  unfold tailWord_1923249
  simp only [CollatzResearch.WordTrace]
  refine ⟨70146653809404812623892801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46764435872936541749261867 70146653809404812623892801)
  ·
    refine ⟨52609990357053609467919601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70146653809404812623892801 52609990357053609467919601)
    ·
      refine ⟨39457492767790207100939701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52609990357053609467919601 39457492767790207100939701)
      ·
        refine ⟨3699139946980331915713097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39457492767790207100939701 3699139946980331915713097)
        ·
          refine ⟨2774354960235248936784823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3699139946980331915713097 2774354960235248936784823)
          ·
            refine ⟨4161532440352873405177235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774354960235248936784823 4161532440352873405177235)
            ·
              refine ⟨6242298660529310107765853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161532440352873405177235 6242298660529310107765853)
              ·
                refine ⟨2340861997698491290412195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6242298660529310107765853 2340861997698491290412195)
                ·
                  refine ⟨3511292996547736935618293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340861997698491290412195 3511292996547736935618293)
                  ·
                    refine ⟨329183718426350337714215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3511292996547736935618293 329183718426350337714215)
                    ·
                      rfl

theorem cell23_1923249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_1923249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923249 prefixEnd_1923249 := by exact prefixLift 1923249
  have htrace : WordTrace (prefixWord ++ tailWord_1923249) baseStart_1923249 baseEnd_1923249 := by
    simpa [prefixWord, tailWord_1923249, baseEnd_1923249] using wordTrace_append hprefix tailTrace_1923249
  have hstable : (prefixWord ++ tailWord_1923249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923249).length < 2 ^ (prefixWord ++ tailWord_1923249).sum := by decide
  have hdescent : baseEnd_1923249 < baseStart_1923249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923269 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 3, 2, 2]
def baseStart_1923269 : Nat := 118140960795 + 1923269 * 2 ^ 59
def prefixEnd_1923269 : Nat := 4983230072969 + 3 ^ 40 * 1923269 * 2
def baseEnd_1923269 : Nat := 987561424892140934892553

theorem tailTrace_1923269 : CollatzResearch.WordTrace tailWord_1923269 prefixEnd_1923269 987561424892140934892553 := by
  unfold tailWord_1923269
  simp only [CollatzResearch.WordTrace]
  refine ⟨70147383269332356039620861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46764922179554904026413907 70147383269332356039620861)
  ·
    refine ⟨26305268725999633514857823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70147383269332356039620861 26305268725999633514857823)
    ·
      refine ⟨39457903088999450272286735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26305268725999633514857823 39457903088999450272286735)
      ·
        refine ⟨59186854633499175408430103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39457903088999450272286735 59186854633499175408430103)
        ·
          refine ⟨88780281950248763112645155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59186854633499175408430103 88780281950248763112645155)
          ·
            refine ⟨133170422925373144668967733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88780281950248763112645155 133170422925373144668967733)
            ·
              refine ⟨12484727149253732312715725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133170422925373144668967733 12484727149253732312715725)
              ·
                refine ⟨4681772680970149617268397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12484727149253732312715725 4681772680970149617268397)
                ·
                  refine ⟨1755664755363806106475649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4681772680970149617268397 1755664755363806106475649)
                  ·
                    refine ⟨1316748566522854579856737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755664755363806106475649 1316748566522854579856737)
                    ·
                      refine ⟨987561424892140934892553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316748566522854579856737 987561424892140934892553)
                      ·
                        rfl

theorem cell23_1923269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_1923269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923269 prefixEnd_1923269 := by exact prefixLift 1923269
  have htrace : WordTrace (prefixWord ++ tailWord_1923269) baseStart_1923269 baseEnd_1923269 := by
    simpa [prefixWord, tailWord_1923269, baseEnd_1923269] using wordTrace_append hprefix tailTrace_1923269
  have hstable : (prefixWord ++ tailWord_1923269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923269).length < 2 ^ (prefixWord ++ tailWord_1923269).sum := by decide
  have hdescent : baseEnd_1923269 < baseStart_1923269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923279 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 2, 4]
def baseStart_1923279 : Nat := 118140960795 + 1923279 * 2 ^ 59
def prefixEnd_1923279 : Nat := 4983230072969 + 3 ^ 40 * 1923279 * 2
def baseEnd_1923279 : Nat := 329188853232895298589169

theorem tailTrace_1923279 : CollatzResearch.WordTrace tailWord_1923279 prefixEnd_1923279 329188853232895298589169 := by
  unfold tailWord_1923279
  simp only [CollatzResearch.WordTrace]
  refine ⟨70147747999296127747484891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46765165332864085164989927 70147747999296127747484891)
  ·
    refine ⟨105221621998944191621227337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70147747999296127747484891 105221621998944191621227337)
    ·
      refine ⟨78916216499208143715920503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105221621998944191621227337 78916216499208143715920503)
      ·
        refine ⟨118374324748812215573880755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78916216499208143715920503 118374324748812215573880755)
        ·
          refine ⟨177561487123218323360821133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118374324748812215573880755 177561487123218323360821133)
          ·
            refine ⟨66585557671206871260307925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177561487123218323360821133 66585557671206871260307925)
            ·
              refine ⟨1560599007918911045163467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66585557671206871260307925 1560599007918911045163467)
              ·
                refine ⟨2340898511878366567745201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560599007918911045163467 2340898511878366567745201)
                ·
                  refine ⟨1755673883908774925808901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340898511878366567745201 1755673883908774925808901)
                  ·
                    refine ⟨329188853232895298589169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755673883908774925808901 329188853232895298589169)
                    ·
                      rfl

theorem cell23_1923279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 4].length) (baseStart_1923279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923279 prefixEnd_1923279 := by exact prefixLift 1923279
  have htrace : WordTrace (prefixWord ++ tailWord_1923279) baseStart_1923279 baseEnd_1923279 := by
    simpa [prefixWord, tailWord_1923279, baseEnd_1923279] using wordTrace_append hprefix tailTrace_1923279
  have hstable : (prefixWord ++ tailWord_1923279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923279).length < 2 ^ (prefixWord ++ tailWord_1923279).sum := by decide
  have hdescent : baseEnd_1923279 < baseStart_1923279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923282 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1923282 : Nat := 118140960795 + 1923282 * 2 ^ 59
def prefixEnd_1923282 : Nat := 4983230072969 + 3 ^ 40 * 1923282 * 2
def baseEnd_1923282 : Nat := 987568100140649384029993

theorem tailTrace_1923282 : CollatzResearch.WordTrace tailWord_1923282 prefixEnd_1923282 987568100140649384029993 := by
  unfold tailWord_1923282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536964354571314814961025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46765238278856839506562733 17536964354571314814961025)
  ·
    refine ⟨13152723265928486111220769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17536964354571314814961025 13152723265928486111220769)
    ·
      refine ⟨9864542449446364583415577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13152723265928486111220769 9864542449446364583415577)
      ·
        refine ⟨7398406837084773437561683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9864542449446364583415577 7398406837084773437561683)
        ·
          refine ⟨11097610255627160156342525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398406837084773437561683 11097610255627160156342525)
          ·
            refine ⟨4161603845860185058628447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11097610255627160156342525 4161603845860185058628447)
            ·
              refine ⟨6242405768790277587942671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161603845860185058628447 6242405768790277587942671)
              ·
                refine ⟨9363608653185416381914007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242405768790277587942671 9363608653185416381914007)
                ·
                  refine ⟨14045412979778124572871011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9363608653185416381914007 14045412979778124572871011)
                  ·
                    refine ⟨21068119469667186859306517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14045412979778124572871011 21068119469667186859306517)
                    ·
                      refine ⟨987568100140649384029993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21068119469667186859306517 987568100140649384029993)
                      ·
                        rfl

theorem cell23_1923282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1923282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923282 prefixEnd_1923282 := by exact prefixLift 1923282
  have htrace : WordTrace (prefixWord ++ tailWord_1923282) baseStart_1923282 baseEnd_1923282 := by
    simpa [prefixWord, tailWord_1923282, baseEnd_1923282] using wordTrace_append hprefix tailTrace_1923282
  have hstable : (prefixWord ++ tailWord_1923282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923282).length < 2 ^ (prefixWord ++ tailWord_1923282).sum := by decide
  have hdescent : baseEnd_1923282 < baseStart_1923282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923286 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1923286 : Nat := 118140960795 + 1923286 * 2 ^ 59
def prefixEnd_1923286 : Nat := 4983230072969 + 3 ^ 40 * 1923286 * 2
def baseEnd_1923286 : Nat := 987570154063267368379975

theorem tailTrace_1923286 : CollatzResearch.WordTrace tailWord_1923286 prefixEnd_1923286 987570154063267368379975 := by
  unfold tailWord_1923286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384250206891922996436857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46765335540180511961993141 4384250206891922996436857)
  ·
    refine ⟨3288187655168942247327643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4384250206891922996436857 3288187655168942247327643)
    ·
      refine ⟨4932281482753413370991465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288187655168942247327643 4932281482753413370991465)
      ·
        refine ⟨3699211112065060028243599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4932281482753413370991465 3699211112065060028243599)
        ·
          refine ⟨5548816668097590042365399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699211112065060028243599 5548816668097590042365399)
          ·
            refine ⟨8323225002146385063548099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548816668097590042365399 8323225002146385063548099)
            ·
              refine ⟨12484837503219577595322149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323225002146385063548099 12484837503219577595322149)
              ·
                refine ⟨2340907031853670799122903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12484837503219577595322149 2340907031853670799122903)
                ·
                  refine ⟨3511360547780506198684355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340907031853670799122903 3511360547780506198684355)
                  ·
                    refine ⟨5267040821670759298026533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3511360547780506198684355 5267040821670759298026533)
                    ·
                      refine ⟨987570154063267368379975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5267040821670759298026533 987570154063267368379975)
                      ·
                        rfl

theorem cell23_1923286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1923286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923286 prefixEnd_1923286 := by exact prefixLift 1923286
  have htrace : WordTrace (prefixWord ++ tailWord_1923286) baseStart_1923286 baseEnd_1923286 := by
    simpa [prefixWord, tailWord_1923286, baseEnd_1923286] using wordTrace_append hprefix tailTrace_1923286
  have hstable : (prefixWord ++ tailWord_1923286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923286).length < 2 ^ (prefixWord ++ tailWord_1923286).sum := by decide
  have hdescent : baseEnd_1923286 < baseStart_1923286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923309 : List Nat := [1, 5, 1, 2, 4, 1, 9]
def baseStart_1923309 : Nat := 118140960795 + 1923309 * 2 ^ 59
def prefixEnd_1923309 : Nat := 4983230072969 + 3 ^ 40 * 1923309 * 2
def baseEnd_1923309 : Nat := 12192369927386676276449

theorem tailTrace_1923309 : CollatzResearch.WordTrace tailWord_1923309 prefixEnd_1923309 12192369927386676276449 := by
  unfold tailWord_1923309
  simp only [CollatzResearch.WordTrace]
  refine ⟨70148842189187442871076981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46765894792791628580717987 70148842189187442871076981)
  ·
    refine ⟨6576453955236322769163467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70148842189187442871076981 6576453955236322769163467)
    ·
      refine ⟨9864680932854484153745201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6576453955236322769163467 9864680932854484153745201)
      ·
        refine ⟨7398510699640863115308901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9864680932854484153745201 7398510699640863115308901)
        ·
          refine ⟨1387220756182661834120419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7398510699640863115308901 1387220756182661834120419)
          ·
            refine ⟨2080831134273992751180629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387220756182661834120419 2080831134273992751180629)
            ·
              refine ⟨12192369927386676276449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2080831134273992751180629 12192369927386676276449)
              ·
                rfl

theorem cell23_1923309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 9].length) (baseStart_1923309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923309 prefixEnd_1923309 := by exact prefixLift 1923309
  have htrace : WordTrace (prefixWord ++ tailWord_1923309) baseStart_1923309 baseEnd_1923309 := by
    simpa [prefixWord, tailWord_1923309, baseEnd_1923309] using wordTrace_append hprefix tailTrace_1923309
  have hstable : (prefixWord ++ tailWord_1923309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923309).length < 2 ^ (prefixWord ++ tailWord_1923309).sum := by decide
  have hdescent : baseEnd_1923309 < baseStart_1923309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923315 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_1923315 : Nat := 118140960795 + 1923315 * 2 ^ 59
def prefixEnd_1923315 : Nat := 4983230072969 + 3 ^ 40 * 1923315 * 2
def baseEnd_1923315 : Nat := 987585045002247754917341

theorem tailTrace_1923315 : CollatzResearch.WordTrace tailWord_1923315 prefixEnd_1923315 987585045002247754917341 := by
  unfold tailWord_1923315
  simp only [CollatzResearch.WordTrace]
  refine ⟨70149061027165705895795399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46766040684777137263863599 70149061027165705895795399)
  ·
    refine ⟨105223591540748558843693099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70149061027165705895795399 105223591540748558843693099)
    ·
      refine ⟨157835387311122838265539649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105223591540748558843693099 157835387311122838265539649)
      ·
        refine ⟨118376540483342128699154737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157835387311122838265539649 118376540483342128699154737)
        ·
          refine ⟨88782405362506596524366053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118376540483342128699154737 88782405362506596524366053)
          ·
            refine ⟨16646701005469986848318635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88782405362506596524366053 16646701005469986848318635)
            ·
              refine ⟨24970051508204980272477953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16646701005469986848318635 24970051508204980272477953)
              ·
                refine ⟨18727538631153735204358465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24970051508204980272477953 18727538631153735204358465)
                ·
                  refine ⟨14045653973365301403268849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18727538631153735204358465 14045653973365301403268849)
                  ·
                    refine ⟨10534240480023976052451637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14045653973365301403268849 10534240480023976052451637)
                    ·
                      refine ⟨987585045002247754917341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10534240480023976052451637 987585045002247754917341)
                      ·
                        rfl

theorem cell23_1923315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_1923315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923315 prefixEnd_1923315 := by exact prefixLift 1923315
  have htrace : WordTrace (prefixWord ++ tailWord_1923315) baseStart_1923315 baseEnd_1923315 := by
    simpa [prefixWord, tailWord_1923315, baseEnd_1923315] using wordTrace_append hprefix tailTrace_1923315
  have hstable : (prefixWord ++ tailWord_1923315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923315).length < 2 ^ (prefixWord ++ tailWord_1923315).sum := by decide
  have hdescent : baseEnd_1923315 < baseStart_1923315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923329 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_1923329 : Nat := 118140960795 + 1923329 * 2 ^ 59
def prefixEnd_1923329 : Nat := 4983230072969 + 3 ^ 40 * 1923329 * 2
def baseEnd_1923329 : Nat := 987592233731410700142277

theorem tailTrace_1923329 : CollatzResearch.WordTrace tailWord_1923329 prefixEnd_1923329 987592233731410700142277 := by
  unfold tailWord_1923329
  simp only [CollatzResearch.WordTrace]
  refine ⟨70149571649114986286805041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46766381099409990857870027 70149571649114986286805041)
  ·
    refine ⟨52612178736836239715103781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70149571649114986286805041 52612178736836239715103781)
    ·
      refine ⟨9864783513156794946581959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52612178736836239715103781 9864783513156794946581959)
      ·
        refine ⟨14797175269735192419872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864783513156794946581959 14797175269735192419872939)
        ·
          refine ⟨22195762904602788629809409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14797175269735192419872939 22195762904602788629809409)
          ·
            refine ⟨16646822178452091472357057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22195762904602788629809409 16646822178452091472357057)
            ·
              refine ⟨12485116633839068604267793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16646822178452091472357057 12485116633839068604267793)
              ·
                refine ⟨9363837475379301453200845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12485116633839068604267793 9363837475379301453200845)
                ·
                  refine ⟨3511439053267238044950317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9363837475379301453200845 3511439053267238044950317)
                  ·
                    refine ⟨1316789644975214266856369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511439053267238044950317 1316789644975214266856369)
                    ·
                      refine ⟨987592233731410700142277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316789644975214266856369 987592233731410700142277)
                      ·
                        rfl

theorem cell23_1923329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_1923329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923329 prefixEnd_1923329 := by exact prefixLift 1923329
  have htrace : WordTrace (prefixWord ++ tailWord_1923329) baseStart_1923329 baseEnd_1923329 := by
    simpa [prefixWord, tailWord_1923329, baseEnd_1923329] using wordTrace_append hprefix tailTrace_1923329
  have hstable : (prefixWord ++ tailWord_1923329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923329).length < 2 ^ (prefixWord ++ tailWord_1923329).sum := by decide
  have hdescent : baseEnd_1923329 < baseStart_1923329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923336 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1923336 : Nat := 118140960795 + 1923336 * 2 ^ 59
def prefixEnd_1923336 : Nat := 4983230072969 + 3 ^ 40 * 1923336 * 2
def baseEnd_1923336 : Nat := 987595828095992172754745

theorem tailTrace_1923336 : CollatzResearch.WordTrace tailWord_1923336 prefixEnd_1923336 987595828095992172754745 := by
  unfold tailWord_1923336
  simp only [CollatzResearch.WordTrace]
  refine ⟨35074913480044813241154931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46766551306726417654873241 35074913480044813241154931)
  ·
    refine ⟨52612370220067219861732397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35074913480044813241154931 52612370220067219861732397)
    ·
      refine ⟨19729638832525207448149649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52612370220067219861732397 19729638832525207448149649)
      ·
        refine ⟨14797229124393905586112237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19729638832525207448149649 14797229124393905586112237)
        ·
          refine ⟨5548960921647714594792089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14797229124393905586112237 5548960921647714594792089)
          ·
            refine ⟨4161720691235785946094067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5548960921647714594792089 4161720691235785946094067)
            ·
              refine ⟨6242581036853678919141101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161720691235785946094067 6242581036853678919141101)
              ·
                refine ⟨2340967888820129594677913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6242581036853678919141101 2340967888820129594677913)
                ·
                  refine ⟨1755725916615097196008435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340967888820129594677913 1755725916615097196008435)
                  ·
                    refine ⟨2633588874922645794012653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1755725916615097196008435 2633588874922645794012653)
                    ·
                      refine ⟨987595828095992172754745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2633588874922645794012653 987595828095992172754745)
                      ·
                        rfl

theorem cell23_1923336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1923336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923336 prefixEnd_1923336 := by exact prefixLift 1923336
  have htrace : WordTrace (prefixWord ++ tailWord_1923336) baseStart_1923336 baseEnd_1923336 := by
    simpa [prefixWord, tailWord_1923336, baseEnd_1923336] using wordTrace_append hprefix tailTrace_1923336
  have hstable : (prefixWord ++ tailWord_1923336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923336).length < 2 ^ (prefixWord ++ tailWord_1923336).sum := by decide
  have hdescent : baseEnd_1923336 < baseStart_1923336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923359 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 3, 4, 2]
def baseStart_1923359 : Nat := 118140960795 + 1923359 * 2 ^ 59
def prefixEnd_1923359 : Nat := 4983230072969 + 3 ^ 40 * 1923359 * 2
def baseEnd_1923359 : Nat := 987607638151045582767139

theorem tailTrace_1923359 : CollatzResearch.WordTrace tailWord_1923359 prefixEnd_1923359 987607638151045582767139 := by
  unfold tailWord_1923359
  simp only [CollatzResearch.WordTrace]
  refine ⟨70150665839006301410397131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46767110559337534273598087 70150665839006301410397131)
  ·
    refine ⟨105225998758509452115595697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70150665839006301410397131 105225998758509452115595697)
    ·
      refine ⟨78919499068882089086696773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105225998758509452115595697 78919499068882089086696773)
      ·
        refine ⟨14797406075415391703755645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78919499068882089086696773 14797406075415391703755645)
        ·
          refine ⟨5549027278280771888908367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14797406075415391703755645 5549027278280771888908367)
          ·
            refine ⟨8323540917421157833362551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5549027278280771888908367 8323540917421157833362551)
            ·
              refine ⟨12485311376131736750043827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323540917421157833362551 12485311376131736750043827)
              ·
                refine ⟨18727967064197605125065741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485311376131736750043827 18727967064197605125065741)
                ·
                  refine ⟨7022987649074101921899653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18727967064197605125065741 7022987649074101921899653)
                  ·
                    refine ⟨1316810184201394110356185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7022987649074101921899653 1316810184201394110356185)
                    ·
                      refine ⟨987607638151045582767139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316810184201394110356185 987607638151045582767139)
                      ·
                        rfl

theorem cell23_1923359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_1923359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923359 prefixEnd_1923359 := by exact prefixLift 1923359
  have htrace : WordTrace (prefixWord ++ tailWord_1923359) baseStart_1923359 baseEnd_1923359 := by
    simpa [prefixWord, tailWord_1923359, baseEnd_1923359] using wordTrace_append hprefix tailTrace_1923359
  have hstable : (prefixWord ++ tailWord_1923359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923359).length < 2 ^ (prefixWord ++ tailWord_1923359).sum := by decide
  have hdescent : baseEnd_1923359 < baseStart_1923359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923375 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_1923375 : Nat := 118140960795 + 1923375 * 2 ^ 59
def prefixEnd_1923375 : Nat := 4983230072969 + 3 ^ 40 * 1923375 * 2
def baseEnd_1923375 : Nat := 987615853841517520167065

theorem tailTrace_1923375 : CollatzResearch.WordTrace tailWord_1923375 prefixEnd_1923375 987615853841517520167065 := by
  unfold tailWord_1923375
  simp only [CollatzResearch.WordTrace]
  refine ⟨70151249406948336142979579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46767499604632224095319719 70151249406948336142979579)
  ·
    refine ⟨105226874110422504214469369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70151249406948336142979579 105226874110422504214469369)
    ·
      refine ⟨78920155582816878160852027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105226874110422504214469369 78920155582816878160852027)
      ·
        refine ⟨118380233374225317241278041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78920155582816878160852027 118380233374225317241278041)
        ·
          refine ⟨88785175030668987930958531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118380233374225317241278041 88785175030668987930958531)
          ·
            refine ⟨133177762546003481896437797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88785175030668987930958531 133177762546003481896437797)
            ·
              refine ⟨24970830477375652855582087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133177762546003481896437797 24970830477375652855582087)
              ·
                refine ⟨37456245716063479283373131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24970830477375652855582087 37456245716063479283373131)
                ·
                  refine ⟨56184368574095218925059697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37456245716063479283373131 56184368574095218925059697)
                  ·
                    refine ⟨42138276430571414193794773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56184368574095218925059697 42138276430571414193794773)
                    ·
                      refine ⟨987615853841517520167065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42138276430571414193794773 987615853841517520167065)
                      ·
                        rfl

theorem cell23_1923375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_1923375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923375 prefixEnd_1923375 := by exact prefixLift 1923375
  have htrace : WordTrace (prefixWord ++ tailWord_1923375) baseStart_1923375 baseEnd_1923375 := by
    simpa [prefixWord, tailWord_1923375, baseEnd_1923375] using wordTrace_append hprefix tailTrace_1923375
  have hstable : (prefixWord ++ tailWord_1923375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923375).length < 2 ^ (prefixWord ++ tailWord_1923375).sum := by decide
  have hdescent : baseEnd_1923375 < baseStart_1923375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923393 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1923393 : Nat := 118140960795 + 1923393 * 2 ^ 59
def prefixEnd_1923393 : Nat := 4983230072969 + 3 ^ 40 * 1923393 * 2
def baseEnd_1923393 : Nat := 987625096493298449741983

theorem tailTrace_1923393 : CollatzResearch.WordTrace tailWord_1923393 prefixEnd_1923393 987625096493298449741983 := by
  unfold tailWord_1923393
  simp only [CollatzResearch.WordTrace]
  refine ⟨70151905920883125217134833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46767937280588750144756555 70151905920883125217134833)
  ·
    refine ⟨52613929440662343912851125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70151905920883125217134833 52613929440662343912851125)
    ·
      refine ⟨4932555885062094741829793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52613929440662343912851125 4932555885062094741829793)
      ·
        refine ⟨3699416913796571056372345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4932555885062094741829793 3699416913796571056372345)
        ·
          refine ⟨2774562685347428292279259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3699416913796571056372345 2774562685347428292279259)
          ·
            refine ⟨4161844028021142438418889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774562685347428292279259 4161844028021142438418889)
            ·
              refine ⟨3121383021015856828814167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161844028021142438418889 3121383021015856828814167)
              ·
                refine ⟨4682074531523785243221251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121383021015856828814167 4682074531523785243221251)
                ·
                  refine ⟨7023111797285677864831877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682074531523785243221251 7023111797285677864831877)
                  ·
                    refine ⟨1316833461991064599655977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023111797285677864831877 1316833461991064599655977)
                    ·
                      refine ⟨987625096493298449741983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316833461991064599655977 987625096493298449741983)
                      ·
                        rfl

theorem cell23_1923393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1923393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923393 prefixEnd_1923393 := by exact prefixLift 1923393
  have htrace : WordTrace (prefixWord ++ tailWord_1923393) baseStart_1923393 baseEnd_1923393 := by
    simpa [prefixWord, tailWord_1923393, baseEnd_1923393] using wordTrace_append hprefix tailTrace_1923393
  have hstable : (prefixWord ++ tailWord_1923393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923393).length < 2 ^ (prefixWord ++ tailWord_1923393).sum := by decide
  have hdescent : baseEnd_1923393 < baseStart_1923393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923492 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1923492 : Nat := 118140960795 + 1923492 * 2 ^ 59
def prefixEnd_1923492 : Nat := 4983230072969 + 3 ^ 40 * 1923492 * 2
def baseEnd_1923492 : Nat := 987675931078093562404027

theorem tailTrace_1923492 : CollatzResearch.WordTrace tailWord_1923492 prefixEnd_1923492 987675931078093562404027 := by
  unfold tailWord_1923492
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077758373762232562494365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46770344498349643416659153 35077758373762232562494365)
  ·
    refine ⟨13154159390160837210935387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35077758373762232562494365 13154159390160837210935387)
    ·
      refine ⟨19731239085241255816403081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13154159390160837210935387 19731239085241255816403081)
      ·
        refine ⟨14798429313930941862302311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19731239085241255816403081 14798429313930941862302311)
        ·
          refine ⟨22197643970896412793453467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798429313930941862302311 22197643970896412793453467)
          ·
            refine ⟨33296465956344619190180201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22197643970896412793453467 33296465956344619190180201)
            ·
              refine ⟨24972349467258464392635151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33296465956344619190180201 24972349467258464392635151)
              ·
                refine ⟨37458524200887696588952727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24972349467258464392635151 37458524200887696588952727)
                ·
                  refine ⟨56187786301331544883429091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37458524200887696588952727 56187786301331544883429091)
                  ·
                    refine ⟨84281679451997317325143637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56187786301331544883429091 84281679451997317325143637)
                    ·
                      refine ⟨987675931078093562404027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 84281679451997317325143637 987675931078093562404027)
                      ·
                        rfl

theorem cell23_1923492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1923492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923492 prefixEnd_1923492 := by exact prefixLift 1923492
  have htrace : WordTrace (prefixWord ++ tailWord_1923492) baseStart_1923492 baseEnd_1923492 := by
    simpa [prefixWord, tailWord_1923492, baseEnd_1923492] using wordTrace_append hprefix tailTrace_1923492
  have hstable : (prefixWord ++ tailWord_1923492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923492).length < 2 ^ (prefixWord ++ tailWord_1923492).sum := by decide
  have hdescent : baseEnd_1923492 < baseStart_1923492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923493 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_1923493 : Nat := 118140960795 + 1923493 * 2 ^ 59
def prefixEnd_1923493 : Nat := 4983230072969 + 3 ^ 40 * 1923493 * 2
def baseEnd_1923493 : Nat := 329225481519582686163841

theorem tailTrace_1923493 : CollatzResearch.WordTrace tailWord_1923493 prefixEnd_1923493 329225481519582686163841 := by
  unfold tailWord_1923493
  simp only [CollatzResearch.WordTrace]
  refine ⟨70155553220520842295775133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46770368813680561530516755 70155553220520842295775133)
  ·
    refine ⟨26308332457695315860915675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70155553220520842295775133 26308332457695315860915675)
    ·
      refine ⟨39462498686542973791373513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26308332457695315860915675 39462498686542973791373513)
      ·
        refine ⟨29596874014907230343530135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39462498686542973791373513 29596874014907230343530135)
        ·
          refine ⟨44395311022360845515295203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29596874014907230343530135 44395311022360845515295203)
          ·
            refine ⟨66592966533541268272942805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44395311022360845515295203 66592966533541268272942805)
            ·
              refine ⟨1560772653129873475147097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66592966533541268272942805 1560772653129873475147097)
              ·
                refine ⟨1170579489847405106360323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560772653129873475147097 1170579489847405106360323)
                ·
                  refine ⟨1755869234771107659540485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170579489847405106360323 1755869234771107659540485)
                  ·
                    refine ⟨329225481519582686163841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755869234771107659540485 329225481519582686163841)
                    ·
                      rfl

theorem cell23_1923493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_1923493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923493 prefixEnd_1923493 := by exact prefixLift 1923493
  have htrace : WordTrace (prefixWord ++ tailWord_1923493) baseStart_1923493 baseEnd_1923493 := by
    simpa [prefixWord, tailWord_1923493, baseEnd_1923493] using wordTrace_append hprefix tailTrace_1923493
  have hstable : (prefixWord ++ tailWord_1923493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923493).length < 2 ^ (prefixWord ++ tailWord_1923493).sum := by decide
  have hdescent : baseEnd_1923493 < baseStart_1923493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 6, 2]
def baseStart_1923539 : Nat := 118140960795 + 1923539 * 2 ^ 59
def prefixEnd_1923539 : Nat := 4983230072969 + 3 ^ 40 * 1923539 * 2
def baseEnd_1923539 : Nat := 987700064668854878516311

theorem tailTrace_1923539 : CollatzResearch.WordTrace tailWord_1923539 prefixEnd_1923539 987700064668854878516311 := by
  unfold tailWord_1923539
  simp only [CollatzResearch.WordTrace]
  refine ⟨70157230978354192151949671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46771487318902794767966447 70157230978354192151949671)
  ·
    refine ⟨105235846467531288227924507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70157230978354192151949671 105235846467531288227924507)
    ·
      refine ⟨157853769701296932341886761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105235846467531288227924507 157853769701296932341886761)
      ·
        refine ⟨118390327275972699256415071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157853769701296932341886761 118390327275972699256415071)
        ·
          refine ⟨177585490913959048884622607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118390327275972699256415071 177585490913959048884622607)
          ·
            refine ⟨266378236370938573326933911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177585490913959048884622607 266378236370938573326933911)
            ·
              refine ⟨399567354556407859990400867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266378236370938573326933911 399567354556407859990400867)
              ·
                refine ⟨599351031834611789985601301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399567354556407859990400867 599351031834611789985601301)
                ·
                  refine ⟨28094579617247427655575061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 599351031834611789985601301 28094579617247427655575061)
                  ·
                    refine ⟨1316933419558473171355081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28094579617247427655575061 1316933419558473171355081)
                    ·
                      refine ⟨987700064668854878516311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316933419558473171355081 987700064668854878516311)
                      ·
                        rfl

theorem cell23_1923539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6, 2].length) (baseStart_1923539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923539 prefixEnd_1923539 := by exact prefixLift 1923539
  have htrace : WordTrace (prefixWord ++ tailWord_1923539) baseStart_1923539 baseEnd_1923539 := by
    simpa [prefixWord, tailWord_1923539, baseEnd_1923539] using wordTrace_append hprefix tailTrace_1923539
  have hstable : (prefixWord ++ tailWord_1923539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923539).length < 2 ^ (prefixWord ++ tailWord_1923539).sum := by decide
  have hdescent : baseEnd_1923539 < baseStart_1923539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923549 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1923549 : Nat := 118140960795 + 1923549 * 2 ^ 59
def prefixEnd_1923549 : Nat := 4983230072969 + 3 ^ 40 * 1923549 * 2
def baseEnd_1923549 : Nat := 329235066491799946463755

theorem tailTrace_1923549 : CollatzResearch.WordTrace tailWord_1923549 prefixEnd_1923549 329235066491799946463755 := by
  unfold tailWord_1923549
  simp only [CollatzResearch.WordTrace]
  refine ⟨70157595708317963859813701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46771730472211975906542467 70157595708317963859813701)
  ·
    refine ⟨13154549195309618223715069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70157595708317963859813701 13154549195309618223715069)
    ·
      refine ⟨4932955948241106833893151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13154549195309618223715069 4932955948241106833893151)
      ·
        refine ⟨7399433922361660250839727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932955948241106833893151 7399433922361660250839727)
        ·
          refine ⟨11099150883542490376259591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399433922361660250839727 11099150883542490376259591)
          ·
            refine ⟨16648726325313735564389387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099150883542490376259591 16648726325313735564389387)
            ·
              refine ⟨24973089487970603346584081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16648726325313735564389387 24973089487970603346584081)
              ·
                refine ⟨18729817115977952509938061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24973089487970603346584081 18729817115977952509938061)
                ·
                  refine ⟨7023681418491732191226773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18729817115977952509938061 7023681418491732191226773)
                  ·
                    refine ⟨329235066491799946463755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7023681418491732191226773 329235066491799946463755)
                    ·
                      rfl

theorem cell23_1923549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1923549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923549 prefixEnd_1923549 := by exact prefixLift 1923549
  have htrace : WordTrace (prefixWord ++ tailWord_1923549) baseStart_1923549 baseEnd_1923549 := by
    simpa [prefixWord, tailWord_1923549, baseEnd_1923549] using wordTrace_append hprefix tailTrace_1923549
  have hstable : (prefixWord ++ tailWord_1923549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923549).length < 2 ^ (prefixWord ++ tailWord_1923549).sum := by decide
  have hdescent : baseEnd_1923549 < baseStart_1923549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923559 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1923559 : Nat := 118140960795 + 1923559 * 2 ^ 59
def prefixEnd_1923559 : Nat := 4983230072969 + 3 ^ 40 * 1923559 * 2
def baseEnd_1923559 : Nat := 987710334281944800266219

theorem tailTrace_1923559 : CollatzResearch.WordTrace tailWord_1923559 prefixEnd_1923559 987710334281944800266219 := by
  unfold tailWord_1923559
  simp only [CollatzResearch.WordTrace]
  refine ⟨70157960438281735567677731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46771973625521157045118487 70157960438281735567677731)
  ·
    refine ⟨105236940657422603351516597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70157960438281735567677731 105236940657422603351516597)
    ·
      refine ⟨9865963186633369064204681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105236940657422603351516597 9865963186633369064204681)
      ·
        refine ⟨7399472389975026798153511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9865963186633369064204681 7399472389975026798153511)
        ·
          refine ⟨11099208584962540197230267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399472389975026798153511 11099208584962540197230267)
          ·
            refine ⟨16648812877443810295845401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099208584962540197230267 16648812877443810295845401)
            ·
              refine ⟨12486609658082857721884051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16648812877443810295845401 12486609658082857721884051)
              ·
                refine ⟨18729914487124286582826077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12486609658082857721884051 18729914487124286582826077)
                ·
                  refine ⟨7023717932671607468559779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18729914487124286582826077 7023717932671607468559779)
                  ·
                    refine ⟨10535576899007411202839669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023717932671607468559779 10535576899007411202839669)
                    ·
                      refine ⟨987710334281944800266219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10535576899007411202839669 987710334281944800266219)
                      ·
                        rfl

theorem cell23_1923559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1923559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923559 prefixEnd_1923559 := by exact prefixLift 1923559
  have htrace : WordTrace (prefixWord ++ tailWord_1923559) baseStart_1923559 baseEnd_1923559 := by
    simpa [prefixWord, tailWord_1923559, baseEnd_1923559] using wordTrace_append hprefix tailTrace_1923559
  have hstable : (prefixWord ++ tailWord_1923559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923559).length < 2 ^ (prefixWord ++ tailWord_1923559).sum := by decide
  have hdescent : baseEnd_1923559 < baseStart_1923559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923566 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1923566 : Nat := 118140960795 + 1923566 * 2 ^ 59
def prefixEnd_1923566 : Nat := 4983230072969 + 3 ^ 40 * 1923566 * 2
def baseEnd_1923566 : Nat := 329237976215508757626229

theorem tailTrace_1923566 : CollatzResearch.WordTrace tailWord_1923566 prefixEnd_1923566 329237976215508757626229 := by
  unfold tailWord_1923566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769776968657046970397819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46772143832837583842121701 8769776968657046970397819)
  ·
    refine ⟨13154665452985570455596729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8769776968657046970397819 13154665452985570455596729)
    ·
      refine ⟨9865999089739177841697547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13154665452985570455596729 9865999089739177841697547)
      ·
        refine ⟨14798998634608766762546321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9865999089739177841697547 14798998634608766762546321)
        ·
          refine ⟨11099248975956575071909741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14798998634608766762546321 11099248975956575071909741)
          ·
            refine ⟨4162218365983715651966153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11099248975956575071909741 4162218365983715651966153)
            ·
              refine ⟨3121663774487786738974615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162218365983715651966153 3121663774487786738974615)
              ·
                refine ⟨4682495661731680108461923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121663774487786738974615 4682495661731680108461923)
                ·
                  refine ⟨7023743492597520162692885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682495661731680108461923 7023743492597520162692885)
                  ·
                    refine ⟨329237976215508757626229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7023743492597520162692885 329237976215508757626229)
                    ·
                      rfl

theorem cell23_1923566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1923566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923566 prefixEnd_1923566 := by exact prefixLift 1923566
  have htrace : WordTrace (prefixWord ++ tailWord_1923566) baseStart_1923566 baseEnd_1923566 := by
    simpa [prefixWord, tailWord_1923566, baseEnd_1923566] using wordTrace_append hprefix tailTrace_1923566
  have hstable : (prefixWord ++ tailWord_1923566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923566).length < 2 ^ (prefixWord ++ tailWord_1923566).sum := by decide
  have hdescent : baseEnd_1923566 < baseStart_1923566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923576 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_1923576 : Nat := 118140960795 + 1923576 * 2 ^ 59
def prefixEnd_1923576 : Nat := 4983230072969 + 3 ^ 40 * 1923576 * 2
def baseEnd_1923576 : Nat := 987719063453071233753641

theorem tailTrace_1923576 : CollatzResearch.WordTrace tailWord_1923576 prefixEnd_1923576 987719063453071233753641 := by
  unfold tailWord_1923576
  simp only [CollatzResearch.WordTrace]
  refine ⟨35079290239610073735523291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46772386986146764980697721 35079290239610073735523291)
  ·
    refine ⟨52618935359415110603284937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35079290239610073735523291 52618935359415110603284937)
    ·
      refine ⟨39464201519561332952463703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52618935359415110603284937 39464201519561332952463703)
      ·
        refine ⟨59196302279341999428695555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39464201519561332952463703 59196302279341999428695555)
        ·
          refine ⟨88794453419012999143043333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59196302279341999428695555 88794453419012999143043333)
          ·
            refine ⟨16648960016064937339320625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88794453419012999143043333 16648960016064937339320625)
            ·
              refine ⟨12486720012048703004490469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16648960016064937339320625 12486720012048703004490469)
              ·
                refine ⟨2341260002259131813341963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12486720012048703004490469 2341260002259131813341963)
                ·
                  refine ⟨3511890003388697720012945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341260002259131813341963 3511890003388697720012945)
                  ·
                    refine ⟨2633917502541523290009709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3511890003388697720012945 2633917502541523290009709)
                    ·
                      refine ⟨987719063453071233753641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2633917502541523290009709 987719063453071233753641)
                      ·
                        rfl

theorem cell23_1923576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_1923576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923576 prefixEnd_1923576 := by exact prefixLift 1923576
  have htrace : WordTrace (prefixWord ++ tailWord_1923576) baseStart_1923576 baseEnd_1923576 := by
    simpa [prefixWord, tailWord_1923576, baseEnd_1923576] using wordTrace_append hprefix tailTrace_1923576
  have hstable : (prefixWord ++ tailWord_1923576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923576).length < 2 ^ (prefixWord ++ tailWord_1923576).sum := by decide
  have hdescent : baseEnd_1923576 < baseStart_1923576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923607 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1923607 : Nat := 118140960795 + 1923607 * 2 ^ 59
def prefixEnd_1923607 : Nat := 4983230072969 + 3 ^ 40 * 1923607 * 2
def baseEnd_1923607 : Nat := 987734981353360612465999

theorem tailTrace_1923607 : CollatzResearch.WordTrace tailWord_1923607 prefixEnd_1923607 987734981353360612465999 := by
  unfold tailWord_1923607
  simp only [CollatzResearch.WordTrace]
  refine ⟨70159711142107839765425075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46773140761405226510283383 70159711142107839765425075)
  ·
    refine ⟨105239566713161759648137613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70159711142107839765425075 105239566713161759648137613)
    ·
      refine ⟨39464837517435659868051605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105239566713161759648137613 39464837517435659868051605)
      ·
        refine ⟨1849914258629796556314919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39464837517435659868051605 1849914258629796556314919)
        ·
          refine ⟨2774871387944694834472379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849914258629796556314919 2774871387944694834472379)
          ·
            refine ⟨4162307081917042251708569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774871387944694834472379 4162307081917042251708569)
            ·
              refine ⟨3121730311437781688781427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162307081917042251708569 3121730311437781688781427)
              ·
                refine ⟨4682595467156672533172141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121730311437781688781427 4682595467156672533172141)
                ·
                  refine ⟨1755973300183752199939553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4682595467156672533172141 1755973300183752199939553)
                  ·
                    refine ⟨1316979975137814149954665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1755973300183752199939553 1316979975137814149954665)
                    ·
                      refine ⟨987734981353360612465999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316979975137814149954665 987734981353360612465999)
                      ·
                        rfl

theorem cell23_1923607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1923607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923607 prefixEnd_1923607 := by exact prefixLift 1923607
  have htrace : WordTrace (prefixWord ++ tailWord_1923607) baseStart_1923607 baseEnd_1923607 := by
    simpa [prefixWord, tailWord_1923607, baseEnd_1923607] using wordTrace_append hprefix tailTrace_1923607
  have hstable : (prefixWord ++ tailWord_1923607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923607).length < 2 ^ (prefixWord ++ tailWord_1923607).sum := by decide
  have hdescent : baseEnd_1923607 < baseStart_1923607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923620 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1923620 : Nat := 118140960795 + 1923620 * 2 ^ 59
def prefixEnd_1923620 : Nat := 4983230072969 + 3 ^ 40 * 1923620 * 2
def baseEnd_1923620 : Nat := 987741656601869061603439

theorem tailTrace_1923620 : CollatzResearch.WordTrace tailWord_1923620 prefixEnd_1923620 987741656601869061603439 := by
  unfold tailWord_1923620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35080092645530371492824157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46773456860707161990432209 35080092645530371492824157)
  ·
    refine ⟨13155034742073889309809059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35080092645530371492824157 13155034742073889309809059)
    ·
      refine ⟨19732552113110833964713589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13155034742073889309809059 19732552113110833964713589)
      ·
        refine ⟨1849926760604140684191899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19732552113110833964713589 1849926760604140684191899)
        ·
          refine ⟨2774890140906211026287849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849926760604140684191899 2774890140906211026287849)
          ·
            refine ⟨2081167605679658269715887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774890140906211026287849 2081167605679658269715887)
            ·
              refine ⟨3121751408519487404573831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081167605679658269715887 3121751408519487404573831)
              ·
                refine ⟨4682627112779231106860747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121751408519487404573831 4682627112779231106860747)
                ·
                  refine ⟨7023940669168846660291121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682627112779231106860747 7023940669168846660291121)
                  ·
                    refine ⟨5267955501876634995218341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7023940669168846660291121 5267955501876634995218341)
                    ·
                      refine ⟨987741656601869061603439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5267955501876634995218341 987741656601869061603439)
                      ·
                        rfl

theorem cell23_1923620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1923620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923620 prefixEnd_1923620 := by exact prefixLift 1923620
  have htrace : WordTrace (prefixWord ++ tailWord_1923620) baseStart_1923620 baseEnd_1923620 := by
    simpa [prefixWord, tailWord_1923620, baseEnd_1923620] using wordTrace_append hprefix tailTrace_1923620
  have hstable : (prefixWord ++ tailWord_1923620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923620).length < 2 ^ (prefixWord ++ tailWord_1923620).sum := by decide
  have hdescent : baseEnd_1923620 < baseStart_1923620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923630 : List Nat := [4, 1, 3, 1, 4, 1, 2, 7]
def baseStart_1923630 : Nat := 118140960795 + 1923630 * 2 ^ 59
def prefixEnd_1923630 : Nat := 4983230072969 + 3 ^ 40 * 1923630 * 2
def baseEnd_1923630 : Nat := 36583214496607926758459

theorem tailTrace_1923630 : CollatzResearch.WordTrace tailWord_1923630 prefixEnd_1923630 36583214496607926758459 := by
  unfold tailWord_1923630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770068752628064336689043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46773700014016343129008229 8770068752628064336689043)
  ·
    refine ⟨13155103128942096505033565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770068752628064336689043 13155103128942096505033565)
    ·
      refine ⟨4933163673353286189387587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13155103128942096505033565 4933163673353286189387587)
      ·
        refine ⟨7399745510029929284081381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4933163673353286189387587 7399745510029929284081381)
        ·
          refine ⟨1387452283130611740765259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7399745510029929284081381 1387452283130611740765259)
          ·
            refine ⟨2081178424695917611147889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387452283130611740765259 2081178424695917611147889)
            ·
              refine ⟨1560883818521938208360917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081178424695917611147889 1560883818521938208360917)
              ·
                refine ⟨36583214496607926758459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1560883818521938208360917 36583214496607926758459)
                ·
                  rfl

theorem cell23_1923630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_1923630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923630 prefixEnd_1923630 := by exact prefixLift 1923630
  have htrace : WordTrace (prefixWord ++ tailWord_1923630) baseStart_1923630 baseEnd_1923630 := by
    simpa [prefixWord, tailWord_1923630, baseEnd_1923630] using wordTrace_append hprefix tailTrace_1923630
  have hstable : (prefixWord ++ tailWord_1923630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923630).length < 2 ^ (prefixWord ++ tailWord_1923630).sum := by decide
  have hdescent : baseEnd_1923630 < baseStart_1923630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923633 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 1, 3, 2]
def baseStart_1923633 : Nat := 118140960795 + 1923633 * 2 ^ 59
def prefixEnd_1923633 : Nat := 4983230072969 + 3 ^ 40 * 1923633 * 2
def baseEnd_1923633 : Nat := 987748331850377510740879

theorem tailTrace_1923633 : CollatzResearch.WordTrace tailWord_1923633 prefixEnd_1923633 987748331850377510740879 := by
  unfold tailWord_1923633
  simp only [CollatzResearch.WordTrace]
  refine ⟨70160659440013646205871553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46773772960009097470581035 70160659440013646205871553)
  ·
    refine ⟨52620494580010234654403665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70160659440013646205871553 52620494580010234654403665)
    ·
      refine ⟨39465370935007675990802749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52620494580010234654403665 39465370935007675990802749)
      ·
        refine ⟨14799514100627878496551031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39465370935007675990802749 14799514100627878496551031)
        ·
          refine ⟨22199271150941817744826547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14799514100627878496551031 22199271150941817744826547)
          ·
            refine ⟨33298906726412726617239821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22199271150941817744826547 33298906726412726617239821)
            ·
              refine ⟨12487090022404772481464933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33298906726412726617239821 12487090022404772481464933)
              ·
                refine ⟨2341329379200894840274675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12487090022404772481464933 2341329379200894840274675)
                ·
                  refine ⟨3511994068801342260412013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341329379200894840274675 3511994068801342260412013)
                  ·
                    refine ⟨1316997775800503347654505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511994068801342260412013 1316997775800503347654505)
                    ·
                      refine ⟨987748331850377510740879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1316997775800503347654505 987748331850377510740879)
                      ·
                        rfl

theorem cell23_1923633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_1923633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923633 prefixEnd_1923633 := by exact prefixLift 1923633
  have htrace : WordTrace (prefixWord ++ tailWord_1923633) baseStart_1923633 baseEnd_1923633 := by
    simpa [prefixWord, tailWord_1923633, baseEnd_1923633] using wordTrace_append hprefix tailTrace_1923633
  have hstable : (prefixWord ++ tailWord_1923633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923633).length < 2 ^ (prefixWord ++ tailWord_1923633).sum := by decide
  have hdescent : baseEnd_1923633 < baseStart_1923633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923659 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4]
def baseStart_1923659 : Nat := 118140960795 + 1923659 * 2 ^ 59
def prefixEnd_1923659 : Nat := 4983230072969 + 3 ^ 40 * 1923659 * 2
def baseEnd_1923659 : Nat := 987761682347394409015759

theorem tailTrace_1923659 : CollatzResearch.WordTrace tailWord_1923659 prefixEnd_1923659 987761682347394409015759 := by
  unfold tailWord_1923659
  simp only [CollatzResearch.WordTrace]
  refine ⟨70161607737919452646318031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46774405158612968430878687 70161607737919452646318031)
  ·
    refine ⟨105242411606879178969477047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70161607737919452646318031 105242411606879178969477047)
    ·
      refine ⟨157863617410318768454215571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105242411606879178969477047 157863617410318768454215571)
      ·
        refine ⟨236795426115478152681323357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157863617410318768454215571 236795426115478152681323357)
        ·
          refine ⟨88798284793304307255496259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236795426115478152681323357 88798284793304307255496259)
          ·
            refine ⟨133197427189956460883244389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88798284793304307255496259 133197427189956460883244389)
            ·
              refine ⟨24974517598116836415608323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133197427189956460883244389 24974517598116836415608323)
              ·
                refine ⟨37461776397175254623412485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24974517598116836415608323 37461776397175254623412485)
                ·
                  refine ⟨7024083074470360241889841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37461776397175254623412485 7024083074470360241889841)
                  ·
                    refine ⟨5268062305852770181417381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024083074470360241889841 5268062305852770181417381)
                    ·
                      refine ⟨987761682347394409015759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5268062305852770181417381 987761682347394409015759)
                      ·
                        rfl

theorem cell23_1923659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_1923659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923659 prefixEnd_1923659 := by exact prefixLift 1923659
  have htrace : WordTrace (prefixWord ++ tailWord_1923659) baseStart_1923659 baseEnd_1923659 := by
    simpa [prefixWord, tailWord_1923659, baseEnd_1923659] using wordTrace_append hprefix tailTrace_1923659
  have hstable : (prefixWord ++ tailWord_1923659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923659).length < 2 ^ (prefixWord ++ tailWord_1923659).sum := by decide
  have hdescent : baseEnd_1923659 < baseStart_1923659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923663 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 4, 2, 2]
def baseStart_1923663 : Nat := 118140960795 + 1923663 * 2 ^ 59
def prefixEnd_1923663 : Nat := 4983230072969 + 3 ^ 40 * 1923663 * 2
def baseEnd_1923663 : Nat := 987763736270012393365741

theorem tailTrace_1923663 : CollatzResearch.WordTrace tailWord_1923663 prefixEnd_1923663 987763736270012393365741 := by
  unfold tailWord_1923663
  simp only [CollatzResearch.WordTrace]
  refine ⟨70161753629904961329463643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46774502419936640886309095 70161753629904961329463643)
  ·
    refine ⟨105242630444857441994195465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70161753629904961329463643 105242630444857441994195465)
    ·
      refine ⟨78931972833643081495646599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105242630444857441994195465 78931972833643081495646599)
      ·
        refine ⟨118397959250464622243469899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78931972833643081495646599 118397959250464622243469899)
        ·
          refine ⟨177596938875696933365204849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118397959250464622243469899 177596938875696933365204849)
          ·
            refine ⟨133197704156772700023903637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177596938875696933365204849 133197704156772700023903637)
            ·
              refine ⟨6243642382348720313620483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133197704156772700023903637 6243642382348720313620483)
              ·
                refine ⟨9365463573523080470430725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243642382348720313620483 9365463573523080470430725)
                ·
                  refine ⟨1756024420035577588205761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9365463573523080470430725 1756024420035577588205761)
                  ·
                    refine ⟨1317018315026683191154321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1756024420035577588205761 1317018315026683191154321)
                    ·
                      refine ⟨987763736270012393365741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317018315026683191154321 987763736270012393365741)
                      ·
                        rfl

theorem cell23_1923663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 2, 2].length) (baseStart_1923663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923663 prefixEnd_1923663 := by exact prefixLift 1923663
  have htrace : WordTrace (prefixWord ++ tailWord_1923663) baseStart_1923663 baseEnd_1923663 := by
    simpa [prefixWord, tailWord_1923663, baseEnd_1923663] using wordTrace_append hprefix tailTrace_1923663
  have hstable : (prefixWord ++ tailWord_1923663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923663).length < 2 ^ (prefixWord ++ tailWord_1923663).sum := by decide
  have hdescent : baseEnd_1923663 < baseStart_1923663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923666 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1923666 : Nat := 118140960795 + 1923666 * 2 ^ 59
def prefixEnd_1923666 : Nat := 4983230072969 + 3 ^ 40 * 1923666 * 2
def baseEnd_1923666 : Nat := 987765276711975881628227

theorem tailTrace_1923666 : CollatzResearch.WordTrace tailWord_1923666 prefixEnd_1923666 987765276711975881628227 := by
  unfold tailWord_1923666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17540465762223523210455713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46774575365929395227881901 17540465762223523210455713)
  ·
    refine ⟨13155349321667642407841785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17540465762223523210455713 13155349321667642407841785)
    ·
      refine ⟨9866511991250731805881339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13155349321667642407841785 9866511991250731805881339)
      ·
        refine ⟨14799767986876097708822009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9866511991250731805881339 14799767986876097708822009)
        ·
          refine ⟨11099825990157073281616507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14799767986876097708822009 11099825990157073281616507)
          ·
            refine ⟨16649738985235609922424761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099825990157073281616507 16649738985235609922424761)
            ·
              refine ⟨12487304238926707441818571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16649738985235609922424761 12487304238926707441818571)
              ·
                refine ⟨18730956358390061162727857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12487304238926707441818571 18730956358390061162727857)
                ·
                  refine ⟨14048217268792545872045893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18730956358390061162727857 14048217268792545872045893)
                  ·
                    refine ⟨2634040737898602351008605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14048217268792545872045893 2634040737898602351008605)
                    ·
                      refine ⟨987765276711975881628227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634040737898602351008605 987765276711975881628227)
                      ·
                        rfl

theorem cell23_1923666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1923666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923666 prefixEnd_1923666 := by exact prefixLift 1923666
  have htrace : WordTrace (prefixWord ++ tailWord_1923666) baseStart_1923666 baseEnd_1923666 := by
    simpa [prefixWord, tailWord_1923666, baseEnd_1923666] using wordTrace_append hprefix tailTrace_1923666
  have hstable : (prefixWord ++ tailWord_1923666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923666).length < 2 ^ (prefixWord ++ tailWord_1923666).sum := by decide
  have hdescent : baseEnd_1923666 < baseStart_1923666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923726 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1923726 : Nat := 118140960795 + 1923726 * 2 ^ 59
def prefixEnd_1923726 : Nat := 4983230072969 + 3 ^ 40 * 1923726 * 2
def baseEnd_1923726 : Nat := 987796085551245646877951

theorem tailTrace_1923726 : CollatzResearch.WordTrace tailWord_1923726 prefixEnd_1923726 987796085551245646877951 := by
  unfold tailWord_1923726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770506428584590386125879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46776034285784482059338021 8770506428584590386125879)
  ·
    refine ⟨13155759642876885579188819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770506428584590386125879 13155759642876885579188819)
    ·
      refine ⟨19733639464315328368783229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13155759642876885579188819 19733639464315328368783229)
      ·
        refine ⟨7400114799118248138293711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19733639464315328368783229 7400114799118248138293711)
        ·
          refine ⟨11100172198677372207440567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400114799118248138293711 11100172198677372207440567)
          ·
            refine ⟨16650258298016058311160851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100172198677372207440567 16650258298016058311160851)
            ·
              refine ⟨24975387447024087466741277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16650258298016058311160851 24975387447024087466741277)
              ·
                refine ⟨9365770292634032800027979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24975387447024087466741277 9365770292634032800027979)
                ·
                  refine ⟨14048655438951049200041969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365770292634032800027979 14048655438951049200041969)
                  ·
                    refine ⟨10536491579213286900031477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14048655438951049200041969 10536491579213286900031477)
                    ·
                      refine ⟨987796085551245646877951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10536491579213286900031477 987796085551245646877951)
                      ·
                        rfl

theorem cell23_1923726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1923726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923726 prefixEnd_1923726 := by exact prefixLift 1923726
  have htrace : WordTrace (prefixWord ++ tailWord_1923726) baseStart_1923726 baseEnd_1923726 := by
    simpa [prefixWord, tailWord_1923726, baseEnd_1923726] using wordTrace_append hprefix tailTrace_1923726
  have hstable : (prefixWord ++ tailWord_1923726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923726).length < 2 ^ (prefixWord ++ tailWord_1923726).sum := by decide
  have hdescent : baseEnd_1923726 < baseStart_1923726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923736 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1923736 : Nat := 118140960795 + 1923736 * 2 ^ 59
def prefixEnd_1923736 : Nat := 4983230072969 + 3 ^ 40 * 1923736 * 2
def baseEnd_1923736 : Nat := 987801220357790607752905

theorem tailTrace_1923736 : CollatzResearch.WordTrace tailWord_1923736 prefixEnd_1923736 987801220357790607752905 := by
  unfold tailWord_1923736
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082208079320247398435531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46776277439093663197914041 35082208079320247398435531)
  ·
    refine ⟨52623312118980371097653297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35082208079320247398435531 52623312118980371097653297)
    ·
      refine ⟨39467484089235278323239973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52623312118980371097653297 39467484089235278323239973)
      ·
        refine ⟨7400153266731614685607495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39467484089235278323239973 7400153266731614685607495)
        ·
          refine ⟨11100229900097422028411243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400153266731614685607495 11100229900097422028411243)
          ·
            refine ⟨16650344850146133042616865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100229900097422028411243 16650344850146133042616865)
            ·
              refine ⟨12487758637609599781962649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16650344850146133042616865 12487758637609599781962649)
              ·
                refine ⟨9365818978207199836471987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12487758637609599781962649 9365818978207199836471987)
                ·
                  refine ⟨14048728467310799754707981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365818978207199836471987 14048728467310799754707981)
                  ·
                    refine ⟨5268273175241549908015493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14048728467310799754707981 5268273175241549908015493)
                    ·
                      refine ⟨987801220357790607752905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5268273175241549908015493 987801220357790607752905)
                      ·
                        rfl

theorem cell23_1923736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1923736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923736 prefixEnd_1923736 := by exact prefixLift 1923736
  have htrace : WordTrace (prefixWord ++ tailWord_1923736) baseStart_1923736 baseEnd_1923736 := by
    simpa [prefixWord, tailWord_1923736, baseEnd_1923736] using wordTrace_append hprefix tailTrace_1923736
  have hstable : (prefixWord ++ tailWord_1923736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923736).length < 2 ^ (prefixWord ++ tailWord_1923736).sum := by decide
  have hdescent : baseEnd_1923736 < baseStart_1923736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923776 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 8]
def baseStart_1923776 : Nat := 118140960795 + 1923776 * 2 ^ 59
def prefixEnd_1923776 : Nat := 4983230072969 + 3 ^ 40 * 1923776 * 2
def baseEnd_1923776 : Nat := 109757973287107827916969

theorem tailTrace_1923776 : CollatzResearch.WordTrace tailWord_1923776 prefixEnd_1923776 109757973287107827916969 := by
  unfold tailWord_1923776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082937539247790814163591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46777250052330387752218121 35082937539247790814163591)
  ·
    refine ⟨52624406308871686221245387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35082937539247790814163591 52624406308871686221245387)
    ·
      refine ⟨78936609463307529331868081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52624406308871686221245387 78936609463307529331868081)
      ·
        refine ⟨59202457097480646998901061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78936609463307529331868081 59202457097480646998901061)
        ·
          refine ⟨11100460705777621312293949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59202457097480646998901061 11100460705777621312293949)
          ·
            refine ⟨4162672764666607992110231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11100460705777621312293949 4162672764666607992110231)
            ·
              refine ⟨6244009146999911988165347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162672764666607992110231 6244009146999911988165347)
              ·
                refine ⟨9366013720499867982248021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244009146999911988165347 9366013720499867982248021)
                ·
                  refine ⟨109757973287107827916969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9366013720499867982248021 109757973287107827916969)
                  ·
                    rfl

theorem cell23_1923776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_1923776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923776 prefixEnd_1923776 := by exact prefixLift 1923776
  have htrace : WordTrace (prefixWord ++ tailWord_1923776) baseStart_1923776 baseEnd_1923776 := by
    simpa [prefixWord, tailWord_1923776, baseEnd_1923776] using wordTrace_append hprefix tailTrace_1923776
  have hstable : (prefixWord ++ tailWord_1923776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923776).length < 2 ^ (prefixWord ++ tailWord_1923776).sum := by decide
  have hdescent : baseEnd_1923776 < baseStart_1923776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923780 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1923780 : Nat := 118140960795 + 1923780 * 2 ^ 59
def prefixEnd_1923780 : Nat := 4983230072969 + 3 ^ 40 * 1923780 * 2
def baseEnd_1923780 : Nat := 329274604502196145200901

theorem tailTrace_1923780 : CollatzResearch.WordTrace tailWord_1923780 prefixEnd_1923780 329274604502196145200901 := by
  unfold tailWord_1923780
  simp only [CollatzResearch.WordTrace]
  refine ⟨35083010485240545155736397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46777347313654060207648529 35083010485240545155736397)
  ·
    refine ⟨13156128931965204433401149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35083010485240545155736397 13156128931965204433401149)
    ·
      refine ⟨4933548349486951662525431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13156128931965204433401149 4933548349486951662525431)
      ·
        refine ⟨7400322524230427493788147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4933548349486951662525431 7400322524230427493788147)
        ·
          refine ⟨11100483786345641240682221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400322524230427493788147 11100483786345641240682221)
          ·
            refine ⟨4162681419879615465255833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11100483786345641240682221 4162681419879615465255833)
            ·
              refine ⟨3122011064909711598941875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162681419879615465255833 3122011064909711598941875)
              ·
                refine ⟨4683016597364567398412813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122011064909711598941875 4683016597364567398412813)
                ·
                  refine ⟨1756131224011712774404805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4683016597364567398412813 1756131224011712774404805)
                  ·
                    refine ⟨329274604502196145200901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756131224011712774404805 329274604502196145200901)
                    ·
                      rfl

theorem cell23_1923780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1923780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923780 prefixEnd_1923780 := by exact prefixLift 1923780
  have htrace : WordTrace (prefixWord ++ tailWord_1923780) baseStart_1923780 baseEnd_1923780 := by
    simpa [prefixWord, tailWord_1923780, baseEnd_1923780] using wordTrace_append hprefix tailTrace_1923780
  have hstable : (prefixWord ++ tailWord_1923780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923780).length < 2 ^ (prefixWord ++ tailWord_1923780).sum := by decide
  have hdescent : baseEnd_1923780 < baseStart_1923780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923793 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 6]
def baseStart_1923793 : Nat := 118140960795 + 1923793 * 2 ^ 59
def prefixEnd_1923793 : Nat := 4983230072969 + 3 ^ 40 * 1923793 * 2
def baseEnd_1923793 : Nat := 109758943195010764971127

theorem tailTrace_1923793 : CollatzResearch.WordTrace tailWord_1923793 prefixEnd_1923793 109758943195010764971127 := by
  unfold tailWord_1923793
  simp only [CollatzResearch.WordTrace]
  refine ⟨70166495119433993531696033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46777663412955995687797355 70166495119433993531696033)
  ·
    refine ⟨52624871339575495148772025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70166495119433993531696033 52624871339575495148772025)
    ·
      refine ⟨39468653504681621361579019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52624871339575495148772025 39468653504681621361579019)
      ·
        refine ⟨59202980257022432042368529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39468653504681621361579019 59202980257022432042368529)
        ·
          refine ⟨44402235192766824031776397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59202980257022432042368529 44402235192766824031776397)
          ·
            refine ⟨16650838197287559011916149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44402235192766824031776397 16650838197287559011916149)
            ·
              refine ⟨1561016080995708657367139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16650838197287559011916149 1561016080995708657367139)
              ·
                refine ⟨2341524121493562986050709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561016080995708657367139 2341524121493562986050709)
                ·
                  refine ⟨109758943195010764971127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2341524121493562986050709 109758943195010764971127)
                  ·
                    rfl

theorem cell23_1923793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 6].length) (baseStart_1923793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923793 prefixEnd_1923793 := by exact prefixLift 1923793
  have htrace : WordTrace (prefixWord ++ tailWord_1923793) baseStart_1923793 baseEnd_1923793 := by
    simpa [prefixWord, tailWord_1923793, baseEnd_1923793] using wordTrace_append hprefix tailTrace_1923793
  have hstable : (prefixWord ++ tailWord_1923793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923793).length < 2 ^ (prefixWord ++ tailWord_1923793).sum := by decide
  have hdescent : baseEnd_1923793 < baseStart_1923793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923823 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 1, 5]
def baseStart_1923823 : Nat := 118140960795 + 1923823 * 2 ^ 59
def prefixEnd_1923823 : Nat := 4983230072969 + 3 ^ 40 * 1923823 * 2
def baseEnd_1923823 : Nat := 329281964391577255788335

theorem tailTrace_1923823 : CollatzResearch.WordTrace tailWord_1923823 prefixEnd_1923823 329281964391577255788335 := by
  unfold tailWord_1923823
  simp only [CollatzResearch.WordTrace]
  refine ⟨70167589309325308655288123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46778392872883539103525415 70167589309325308655288123)
  ·
    refine ⟨105251383963987962982932185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70167589309325308655288123 105251383963987962982932185)
    ·
      refine ⟨78938537972990972237199139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105251383963987962982932185 78938537972990972237199139)
      ·
        refine ⟨118407806959486458355798709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78938537972990972237199139 118407806959486458355798709)
        ·
          refine ⟨11100731902451855470856129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118407806959486458355798709 11100731902451855470856129)
          ·
            refine ⟨8325548926838891603142097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11100731902451855470856129 8325548926838891603142097)
            ·
              refine ⟨6244161695129168702356573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325548926838891603142097 6244161695129168702356573)
              ·
                refine ⟨2341560635673438263383715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6244161695129168702356573 2341560635673438263383715)
                ·
                  refine ⟨3512340953510157395075573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341560635673438263383715 3512340953510157395075573)
                  ·
                    refine ⟨329281964391577255788335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3512340953510157395075573 329281964391577255788335)
                    ·
                      rfl

theorem cell23_1923823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_1923823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923823 prefixEnd_1923823 := by exact prefixLift 1923823
  have htrace : WordTrace (prefixWord ++ tailWord_1923823) baseStart_1923823 baseEnd_1923823 := by
    simpa [prefixWord, tailWord_1923823, baseEnd_1923823] using wordTrace_append hprefix tailTrace_1923823
  have hstable : (prefixWord ++ tailWord_1923823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923823).length < 2 ^ (prefixWord ++ tailWord_1923823).sum := by decide
  have hdescent : baseEnd_1923823 < baseStart_1923823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923866 : List Nat := [3, 1, 1, 3, 2, 1, 1, 11]
def baseStart_1923866 : Nat := 118140960795 + 1923866 * 2 ^ 59
def prefixEnd_1923866 : Nat := 4983230072969 + 3 ^ 40 * 1923866 * 2
def baseEnd_1923866 : Nat := 36587702697884262930641

theorem tailTrace_1923866 : CollatzResearch.WordTrace tailWord_1923866 prefixEnd_1923866 36587702697884262930641 := by
  unfold tailWord_1923866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17542289412042381749775863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46779438432113017999402301 17542289412042381749775863)
  ·
    refine ⟨26313434118063572624663795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17542289412042381749775863 26313434118063572624663795)
    ·
      refine ⟨39470151177095358936995693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26313434118063572624663795 39470151177095358936995693)
      ·
        refine ⟨14801306691410759601373385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39470151177095358936995693 14801306691410759601373385)
        ·
          refine ⟨11100980018558069701030039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14801306691410759601373385 11100980018558069701030039)
          ·
            refine ⟨16651470027837104551545059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100980018558069701030039 16651470027837104551545059)
            ·
              refine ⟨24977205041755656827317589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16651470027837104551545059 24977205041755656827317589)
              ·
                refine ⟨36587702697884262930641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24977205041755656827317589 36587702697884262930641)
                ·
                  rfl

theorem cell23_1923866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_1923866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923866 prefixEnd_1923866 := by exact prefixLift 1923866
  have htrace : WordTrace (prefixWord ++ tailWord_1923866) baseStart_1923866 baseEnd_1923866 := by
    simpa [prefixWord, tailWord_1923866, baseEnd_1923866] using wordTrace_append hprefix tailTrace_1923866
  have hstable : (prefixWord ++ tailWord_1923866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923866).length < 2 ^ (prefixWord ++ tailWord_1923866).sum := by decide
  have hdescent : baseEnd_1923866 < baseStart_1923866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923873 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1923873 : Nat := 118140960795 + 1923873 * 2 ^ 59
def prefixEnd_1923873 : Nat := 4983230072969 + 3 ^ 40 * 1923873 * 2
def baseEnd_1923873 : Nat := 987871567207456571739775

theorem tailTrace_1923873 : CollatzResearch.WordTrace tailWord_1923873 prefixEnd_1923873 987871567207456571739775 := by
  unfold tailWord_1923873
  simp only [CollatzResearch.WordTrace]
  refine ⟨70169412959144167194608273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46779608639429444796405515 70169412959144167194608273)
  ·
    refine ⟨52627059719358125395956205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70169412959144167194608273 52627059719358125395956205)
    ·
      refine ⟨19735147394759297023483577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52627059719358125395956205 19735147394759297023483577)
      ·
        refine ⟨14801360546069472767612683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19735147394759297023483577 14801360546069472767612683)
        ·
          refine ⟨22202040819104209151419025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801360546069472767612683 22202040819104209151419025)
          ·
            refine ⟨16651530614328156863564269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22202040819104209151419025 16651530614328156863564269)
            ·
              refine ⟨6244323980373058823836601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16651530614328156863564269 6244323980373058823836601)
              ·
                refine ⟨4683242985279794117877451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6244323980373058823836601 4683242985279794117877451)
                ·
                  refine ⟨7024864477919691176816177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683242985279794117877451 7024864477919691176816177)
                  ·
                    refine ⟨5268648358439768382612133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024864477919691176816177 5268648358439768382612133)
                    ·
                      refine ⟨987871567207456571739775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5268648358439768382612133 987871567207456571739775)
                      ·
                        rfl

theorem cell23_1923873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1923873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923873 prefixEnd_1923873 := by exact prefixLift 1923873
  have htrace : WordTrace (prefixWord ++ tailWord_1923873) baseStart_1923873 baseEnd_1923873 := by
    simpa [prefixWord, tailWord_1923873, baseEnd_1923873] using wordTrace_append hprefix tailTrace_1923873
  have hstable : (prefixWord ++ tailWord_1923873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923873).length < 2 ^ (prefixWord ++ tailWord_1923873).sum := by decide
  have hdescent : baseEnd_1923873 < baseStart_1923873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923896 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_1923896 : Nat := 118140960795 + 1923896 * 2 ^ 59
def prefixEnd_1923896 : Nat := 4983230072969 + 3 ^ 40 * 1923896 * 2
def baseEnd_1923896 : Nat := 329294459087503327250723

theorem tailTrace_1923896 : CollatzResearch.WordTrace tailWord_1923896 prefixEnd_1923896 329294459087503327250723 := by
  unfold tailWord_1923896
  simp only [CollatzResearch.WordTrace]
  refine ⟨35085125919030421061347771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46780167892040561415130361 35085125919030421061347771)
  ·
    refine ⟨52627688878545631592021657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35085125919030421061347771 52627688878545631592021657)
    ·
      refine ⟨39470766658909223694016243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52627688878545631592021657 39470766658909223694016243)
      ·
        refine ⟨59206149988363835541024365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39470766658909223694016243 59206149988363835541024365)
        ·
          refine ⟨22202306245636438327884137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59206149988363835541024365 22202306245636438327884137)
          ·
            refine ⟨16651729684227328745913103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22202306245636438327884137 16651729684227328745913103)
            ·
              refine ⟨24977594526340993118869655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16651729684227328745913103 24977594526340993118869655)
              ·
                refine ⟨37466391789511489678304483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24977594526340993118869655 37466391789511489678304483)
                ·
                  refine ⟨56199587684267234517456725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37466391789511489678304483 56199587684267234517456725)
                  ·
                    refine ⟨329294459087503327250723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 56199587684267234517456725 329294459087503327250723)
                    ·
                      rfl

theorem cell23_1923896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_1923896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923896 prefixEnd_1923896 := by exact prefixLift 1923896
  have htrace : WordTrace (prefixWord ++ tailWord_1923896) baseStart_1923896 baseEnd_1923896 := by
    simpa [prefixWord, tailWord_1923896, baseEnd_1923896] using wordTrace_append hprefix tailTrace_1923896
  have hstable : (prefixWord ++ tailWord_1923896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923896).length < 2 ^ (prefixWord ++ tailWord_1923896).sum := by decide
  have hdescent : baseEnd_1923896 < baseStart_1923896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923917 : List Nat := [1, 6, 1, 2, 2, 1, 3, 7]
def baseStart_1923917 : Nat := 118140960795 + 1923917 * 2 ^ 59
def prefixEnd_1923917 : Nat := 4983230072969 + 3 ^ 40 * 1923917 * 2
def baseEnd_1923917 : Nat := 36588672605787199984799

theorem tailTrace_1923917 : CollatzResearch.WordTrace tailWord_1923917 prefixEnd_1923917 36588672605787199984799 := by
  unfold tailWord_1923917
  simp only [CollatzResearch.WordTrace]
  refine ⟨70171017770984762709210005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46780678513989841806140003 70171017770984762709210005)
  ·
    refine ⟨3289266458014910751994219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70171017770984762709210005 3289266458014910751994219)
    ·
      refine ⟨4933899687022366127991329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3289266458014910751994219 4933899687022366127991329)
      ·
        refine ⟨3700424765266774595993497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4933899687022366127991329 3700424765266774595993497)
        ·
          refine ⟨2775318573950080946995123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700424765266774595993497 2775318573950080946995123)
          ·
            refine ⟨4162977860925121420492685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775318573950080946995123 4162977860925121420492685)
            ·
              refine ⟨1561116697846920532684757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4162977860925121420492685 1561116697846920532684757)
              ·
                refine ⟨36588672605787199984799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1561116697846920532684757 36588672605787199984799)
                ·
                  rfl

theorem cell23_1923917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 7].length) (baseStart_1923917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923917 prefixEnd_1923917 := by exact prefixLift 1923917
  have htrace : WordTrace (prefixWord ++ tailWord_1923917) baseStart_1923917 baseEnd_1923917 := by
    simpa [prefixWord, tailWord_1923917, baseEnd_1923917] using wordTrace_append hprefix tailTrace_1923917
  have hstable : (prefixWord ++ tailWord_1923917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923917).length < 2 ^ (prefixWord ++ tailWord_1923917).sum := by decide
  have hdescent : baseEnd_1923917 < baseStart_1923917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923920 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 3, 3, 2]
def baseStart_1923920 : Nat := 118140960795 + 1923920 * 2 ^ 59
def prefixEnd_1923920 : Nat := 4983230072969 + 3 ^ 40 * 1923920 * 2
def baseEnd_1923920 : Nat := 987895700798217887852059

theorem tailTrace_1923920 : CollatzResearch.WordTrace tailWord_1923920 prefixEnd_1923920 987895700798217887852059 := by
  unfold tailWord_1923920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35085563594986947110784607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46780751459982596147712809 35085563594986947110784607)
  ·
    refine ⟨52628345392480420666176911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35085563594986947110784607 52628345392480420666176911)
    ·
      refine ⟨78942518088720630999265367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52628345392480420666176911 78942518088720630999265367)
      ·
        refine ⟨118413777133080946498898051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78942518088720630999265367 118413777133080946498898051)
        ·
          refine ⟨177620665699621419748347077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118413777133080946498898051 177620665699621419748347077)
          ·
            refine ⟨33303874818679016202815077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177620665699621419748347077 33303874818679016202815077)
            ·
              refine ⟨6244476528502315538027827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33303874818679016202815077 6244476528502315538027827)
              ·
                refine ⟨9366714792753473307041741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244476528502315538027827 9366714792753473307041741)
                ·
                  refine ⟨3512518047282552490140653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9366714792753473307041741 3512518047282552490140653)
                  ·
                    refine ⟨1317194267730957183802745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512518047282552490140653 1317194267730957183802745)
                    ·
                      refine ⟨987895700798217887852059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317194267730957183802745 987895700798217887852059)
                      ·
                        rfl

theorem cell23_1923920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 3, 2].length) (baseStart_1923920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923920 prefixEnd_1923920 := by exact prefixLift 1923920
  have htrace : WordTrace (prefixWord ++ tailWord_1923920) baseStart_1923920 baseEnd_1923920 := by
    simpa [prefixWord, tailWord_1923920, baseEnd_1923920] using wordTrace_append hprefix tailTrace_1923920
  have hstable : (prefixWord ++ tailWord_1923920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923920).length < 2 ^ (prefixWord ++ tailWord_1923920).sum := by decide
  have hdescent : baseEnd_1923920 < baseStart_1923920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923943 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1923943 : Nat := 118140960795 + 1923943 * 2 ^ 59
def prefixEnd_1923943 : Nat := 4983230072969 + 3 ^ 40 * 1923943 * 2
def baseEnd_1923943 : Nat := 329302503617757099288151

theorem tailTrace_1923943 : CollatzResearch.WordTrace tailWord_1923943 prefixEnd_1923943 329302503617757099288151 := by
  unfold tailWord_1923943
  simp only [CollatzResearch.WordTrace]
  refine ⟨70171966068890569149656483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46781310712593712766437655 70171966068890569149656483)
  ·
    refine ⟨105257949103335853724484725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70171966068890569149656483 105257949103335853724484725)
    ·
      refine ⟨9867932728437736286670443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105257949103335853724484725 9867932728437736286670443)
      ·
        refine ⟨14801899092656604430005665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9867932728437736286670443 14801899092656604430005665)
        ·
          refine ⟨11101424319492453322504249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14801899092656604430005665 11101424319492453322504249)
          ·
            refine ⟨8326068239619339991878187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11101424319492453322504249 8326068239619339991878187)
            ·
              refine ⟨12489102359429009987817281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326068239619339991878187 12489102359429009987817281)
              ·
                refine ⟨9366826769571757490862961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12489102359429009987817281 9366826769571757490862961)
                ·
                  refine ⟨7025120077178818118147221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9366826769571757490862961 7025120077178818118147221)
                  ·
                    refine ⟨329302503617757099288151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7025120077178818118147221 329302503617757099288151)
                    ·
                      rfl

theorem cell23_1923943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1923943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923943 prefixEnd_1923943 := by exact prefixLift 1923943
  have htrace : WordTrace (prefixWord ++ tailWord_1923943) baseStart_1923943 baseEnd_1923943 := by
    simpa [prefixWord, tailWord_1923943, baseEnd_1923943] using wordTrace_append hprefix tailTrace_1923943
  have hstable : (prefixWord ++ tailWord_1923943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923943).length < 2 ^ (prefixWord ++ tailWord_1923943).sum := by decide
  have hdescent : baseEnd_1923943 < baseStart_1923943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923944 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1923944 : Nat := 118140960795 + 1923944 * 2 ^ 59
def prefixEnd_1923944 : Nat := 4983230072969 + 3 ^ 40 * 1923944 * 2
def baseEnd_1923944 : Nat := 987908024333925793951949

theorem tailTrace_1923944 : CollatzResearch.WordTrace tailWord_1923944 prefixEnd_1923944 987908024333925793951949 := by
  unfold tailWord_1923944
  simp only [CollatzResearch.WordTrace]
  refine ⟨35086001270943473160221443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46781335027924630880295257 35086001270943473160221443)
  ·
    refine ⟨52629001906415209740332165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35086001270943473160221443 52629001906415209740332165)
    ·
      refine ⟨9867937857452851826312281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52629001906415209740332165 9867937857452851826312281)
      ·
        refine ⟨7400953393089638869734211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9867937857452851826312281 7400953393089638869734211)
        ·
          refine ⟨11101430089634458304601317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400953393089638869734211 11101430089634458304601317)
          ·
            refine ⟨2081518141806460932112747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11101430089634458304601317 2081518141806460932112747)
            ·
              refine ⟨3122277212709691398169121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081518141806460932112747 3122277212709691398169121)
              ·
                refine ⟨2341707909532268548626841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3122277212709691398169121 2341707909532268548626841)
                ·
                  refine ⟨1756280932149201411470131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341707909532268548626841 1756280932149201411470131)
                  ·
                    refine ⟨2634421398223802117205197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1756280932149201411470131 2634421398223802117205197)
                    ·
                      refine ⟨987908024333925793951949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634421398223802117205197 987908024333925793951949)
                      ·
                        rfl

theorem cell23_1923944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1923944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923944 prefixEnd_1923944 := by exact prefixLift 1923944
  have htrace : WordTrace (prefixWord ++ tailWord_1923944) baseStart_1923944 baseEnd_1923944 := by
    simpa [prefixWord, tailWord_1923944, baseEnd_1923944] using wordTrace_append hprefix tailTrace_1923944
  have hstable : (prefixWord ++ tailWord_1923944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923944).length < 2 ^ (prefixWord ++ tailWord_1923944).sum := by decide
  have hdescent : baseEnd_1923944 < baseStart_1923944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923963 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4]
def baseStart_1923963 : Nat := 118140960795 + 1923963 * 2 ^ 59
def prefixEnd_1923963 : Nat := 4983230072969 + 3 ^ 40 * 1923963 * 2
def baseEnd_1923963 : Nat := 987917780466361219614361

theorem tailTrace_1923963 : CollatzResearch.WordTrace tailWord_1923963 prefixEnd_1923963 987917780466361219614361 := by
  unfold tailWord_1923963
  simp only [CollatzResearch.WordTrace]
  refine ⟨70172695528818112565384543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46781797019212075043589695 70172695528818112565384543)
  ·
    refine ⟨105259043293227168848076815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70172695528818112565384543 105259043293227168848076815)
    ·
      refine ⟨157888564939840753272115223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105259043293227168848076815 157888564939840753272115223)
      ·
        refine ⟨236832847409761129908172835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157888564939840753272115223 236832847409761129908172835)
        ·
          refine ⟨355249271114641694862259253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236832847409761129908172835 355249271114641694862259253)
          ·
            refine ⟨33304619166997658893336805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355249271114641694862259253 33304619166997658893336805)
            ·
              refine ⟨6244616093812061042500651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33304619166997658893336805 6244616093812061042500651)
              ·
                refine ⟨9366924140718091563750977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244616093812061042500651 9366924140718091563750977)
                ·
                  refine ⟨7025193105538568672813233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9366924140718091563750977 7025193105538568672813233)
                  ·
                    refine ⟨5268894829153926504609925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025193105538568672813233 5268894829153926504609925)
                    ·
                      refine ⟨987917780466361219614361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5268894829153926504609925 987917780466361219614361)
                      ·
                        rfl

theorem cell23_1923963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_1923963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923963 prefixEnd_1923963 := by exact prefixLift 1923963
  have htrace : WordTrace (prefixWord ++ tailWord_1923963) baseStart_1923963 baseEnd_1923963 := by
    simpa [prefixWord, tailWord_1923963, baseEnd_1923963] using wordTrace_append hprefix tailTrace_1923963
  have hstable : (prefixWord ++ tailWord_1923963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923963).length < 2 ^ (prefixWord ++ tailWord_1923963).sum := by decide
  have hdescent : baseEnd_1923963 < baseStart_1923963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923967 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 2, 2, 2]
def baseStart_1923967 : Nat := 118140960795 + 1923967 * 2 ^ 59
def prefixEnd_1923967 : Nat := 4983230072969 + 3 ^ 40 * 1923967 * 2
def baseEnd_1923967 : Nat := 987919834388979203964343

theorem tailTrace_1923967 : CollatzResearch.WordTrace tailWord_1923967 prefixEnd_1923967 987919834388979203964343 := by
  unfold tailWord_1923967
  simp only [CollatzResearch.WordTrace]
  refine ⟨70172841420803621248530155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46781894280535747499020103 70172841420803621248530155)
  ·
    refine ⟨105259262131205431872795233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70172841420803621248530155 105259262131205431872795233)
    ·
      refine ⟨78944446598404073904596425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105259262131205431872795233 78944446598404073904596425)
      ·
        refine ⟨59208334948803055428447319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78944446598404073904596425 59208334948803055428447319)
        ·
          refine ⟨88812502423204583142670979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59208334948803055428447319 88812502423204583142670979)
          ·
            refine ⟨133218753634806874714006469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88812502423204583142670979 133218753634806874714006469)
            ·
              refine ⟨24978516306526289008876213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133218753634806874714006469 24978516306526289008876213)
              ·
                refine ⟨2341735903736839594582145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24978516306526289008876213 2341735903736839594582145)
                ·
                  refine ⟨1756301927802629695936609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341735903736839594582145 1756301927802629695936609)
                  ·
                    refine ⟨1317226445851972271952457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1756301927802629695936609 1317226445851972271952457)
                    ·
                      refine ⟨987919834388979203964343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317226445851972271952457 987919834388979203964343)
                      ·
                        rfl

theorem cell23_1923967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_1923967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923967 prefixEnd_1923967 := by exact prefixLift 1923967
  have htrace : WordTrace (prefixWord ++ tailWord_1923967) baseStart_1923967 baseEnd_1923967 := by
    simpa [prefixWord, tailWord_1923967, baseEnd_1923967] using wordTrace_append hprefix tailTrace_1923967
  have hstable : (prefixWord ++ tailWord_1923967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923967).length < 2 ^ (prefixWord ++ tailWord_1923967).sum := by decide
  have hdescent : baseEnd_1923967 < baseStart_1923967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923973 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 7]
def baseStart_1923973 : Nat := 118140960795 + 1923973 * 2 ^ 59
def prefixEnd_1923973 : Nat := 4983230072969 + 3 ^ 40 * 1923973 * 2
def baseEnd_1923973 : Nat := 109769212808100686721035

theorem tailTrace_1923973 : CollatzResearch.WordTrace tailWord_1923973 prefixEnd_1923973 109769212808100686721035 := by
  unfold tailWord_1923973
  simp only [CollatzResearch.WordTrace]
  refine ⟨70173060258781884273248573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46782040172521256182165715 70173060258781884273248573)
  ·
    refine ⟨26314897597043206602468215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70173060258781884273248573 26314897597043206602468215)
    ·
      refine ⟨39472346395564809903702323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26314897597043206602468215 39472346395564809903702323)
      ·
        refine ⟨59208519593347214855553485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39472346395564809903702323 59208519593347214855553485)
        ·
          refine ⟨22203194847505205570832557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59208519593347214855553485 22203194847505205570832557)
          ·
            refine ⟨8326198067814452089062209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22203194847505205570832557 8326198067814452089062209)
            ·
              refine ⟨6244648550860839066796657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8326198067814452089062209 6244648550860839066796657)
              ·
                refine ⟨4683486413145629300097493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6244648550860839066796657 4683486413145629300097493)
                ·
                  refine ⟨109769212808100686721035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4683486413145629300097493 109769212808100686721035)
                  ·
                    rfl

theorem cell23_1923973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_1923973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1923973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1923973 prefixEnd_1923973 := by exact prefixLift 1923973
  have htrace : WordTrace (prefixWord ++ tailWord_1923973) baseStart_1923973 baseEnd_1923973 := by
    simpa [prefixWord, tailWord_1923973, baseEnd_1923973] using wordTrace_append hprefix tailTrace_1923973
  have hstable : (prefixWord ++ tailWord_1923973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923973).length < 2 ^ (prefixWord ++ tailWord_1923973).sum := by decide
  have hdescent : baseEnd_1923973 < baseStart_1923973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924003 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 4, 5]
def baseStart_1924003 : Nat := 118140960795 + 1924003 * 2 ^ 59
def prefixEnd_1924003 : Nat := 4983230072969 + 3 ^ 40 * 1924003 * 2
def baseEnd_1924003 : Nat := 329312773230847021038059

theorem tailTrace_1924003 : CollatzResearch.WordTrace tailWord_1924003 prefixEnd_1924003 329312773230847021038059 := by
  unfold tailWord_1924003
  simp only [CollatzResearch.WordTrace]
  refine ⟨70174154448673199396840663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46782769632448799597893775 70174154448673199396840663)
  ·
    refine ⟨105261231673009799095260995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70174154448673199396840663 105261231673009799095260995)
    ·
      refine ⟨157891847509514698642891493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105261231673009799095260995 157891847509514698642891493)
      ·
        refine ⟨29604721408034005995542155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157891847509514698642891493 29604721408034005995542155)
        ·
          refine ⟨44407082112051008993313233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29604721408034005995542155 44407082112051008993313233)
          ·
            refine ⟨33305311584038256744984925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44407082112051008993313233 33305311584038256744984925)
            ·
              refine ⟨12489491844014346279369347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33305311584038256744984925 12489491844014346279369347)
              ·
                refine ⟨18734237766021519419054021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489491844014346279369347 18734237766021519419054021)
                ·
                  refine ⟨3512669581129034891072629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18734237766021519419054021 3512669581129034891072629)
                  ·
                    refine ⟨329312773230847021038059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3512669581129034891072629 329312773230847021038059)
                    ·
                      rfl

theorem cell23_1924003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 5].length) (baseStart_1924003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924003 prefixEnd_1924003 := by exact prefixLift 1924003
  have htrace : WordTrace (prefixWord ++ tailWord_1924003) baseStart_1924003 baseEnd_1924003 := by
    simpa [prefixWord, tailWord_1924003, baseEnd_1924003] using wordTrace_append hprefix tailTrace_1924003
  have hstable : (prefixWord ++ tailWord_1924003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924003).length < 2 ^ (prefixWord ++ tailWord_1924003).sum := by decide
  have hdescent : baseEnd_1924003 < baseStart_1924003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924007 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 7]
def baseStart_1924007 : Nat := 118140960795 + 1924007 * 2 ^ 59
def prefixEnd_1924007 : Nat := 4983230072969 + 3 ^ 40 * 1924007 * 2
def baseEnd_1924007 : Nat := 109771152623906560829351

theorem tailTrace_1924007 : CollatzResearch.WordTrace tailWord_1924007 prefixEnd_1924007 109771152623906560829351 := by
  unfold tailWord_1924007
  simp only [CollatzResearch.WordTrace]
  refine ⟨70174300340658708079986275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46782866893772472053324183 70174300340658708079986275)
  ·
    refine ⟨105261450510988062119979413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70174300340658708079986275 105261450510988062119979413)
    ·
      refine ⟨4934130492702565411874035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105261450510988062119979413 4934130492702565411874035)
      ·
        refine ⟨7401195739053848117811053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934130492702565411874035 7401195739053848117811053)
        ·
          refine ⟨2775448402145193044179145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7401195739053848117811053 2775448402145193044179145)
          ·
            refine ⟨2081586301608894783134359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775448402145193044179145 2081586301608894783134359)
            ·
              refine ⟨3122379452413342174701539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081586301608894783134359 3122379452413342174701539)
              ·
                refine ⟨4683569178620013262052309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122379452413342174701539 4683569178620013262052309)
                ·
                  refine ⟨109771152623906560829351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4683569178620013262052309 109771152623906560829351)
                  ·
                    rfl

theorem cell23_1924007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 7].length) (baseStart_1924007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924007 prefixEnd_1924007 := by exact prefixLift 1924007
  have htrace : WordTrace (prefixWord ++ tailWord_1924007) baseStart_1924007 baseEnd_1924007 := by
    simpa [prefixWord, tailWord_1924007, baseEnd_1924007] using wordTrace_append hprefix tailTrace_1924007
  have hstable : (prefixWord ++ tailWord_1924007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924007).length < 2 ^ (prefixWord ++ tailWord_1924007).sum := by decide
  have hdescent : baseEnd_1924007 < baseStart_1924007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924022 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1924022 : Nat := 118140960795 + 1924022 * 2 ^ 59
def prefixEnd_1924022 : Nat := 4983230072969 + 3 ^ 40 * 1924022 * 2
def baseEnd_1924022 : Nat := 987948075824976488776591

theorem tailTrace_1924022 : CollatzResearch.WordTrace tailWord_1924022 prefixEnd_1924022 987948075824976488776591 := by
  unfold tailWord_1924022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385927964725272852611395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46783231623736243761188213 4385927964725272852611395)
  ·
    refine ⟨6578891947087909278917093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4385927964725272852611395 6578891947087909278917093)
    ·
      refine ⟨1233542240078982989796955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6578891947087909278917093 1233542240078982989796955)
      ·
        refine ⟨1850313360118474484695433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233542240078982989796955 1850313360118474484695433)
        ·
          refine ⟨1387735020088855863521575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850313360118474484695433 1387735020088855863521575)
          ·
            refine ⟨2081602530133283795282363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387735020088855863521575 2081602530133283795282363)
            ·
              refine ⟨3122403795199925692923545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081602530133283795282363 3122403795199925692923545)
              ·
                refine ⟨2341802846399944269692659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3122403795199925692923545 2341802846399944269692659)
                ·
                  refine ⟨3512704269599916404538989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341802846399944269692659 3512704269599916404538989)
                  ·
                    refine ⟨1317264101099968651702121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512704269599916404538989 1317264101099968651702121)
                    ·
                      refine ⟨987948075824976488776591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317264101099968651702121 987948075824976488776591)
                      ·
                        rfl

theorem cell23_1924022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1924022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924022 prefixEnd_1924022 := by exact prefixLift 1924022
  have htrace : WordTrace (prefixWord ++ tailWord_1924022) baseStart_1924022 baseEnd_1924022 := by
    simpa [prefixWord, tailWord_1924022, baseEnd_1924022] using wordTrace_append hprefix tailTrace_1924022
  have hstable : (prefixWord ++ tailWord_1924022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924022).length < 2 ^ (prefixWord ++ tailWord_1924022).sum := by decide
  have hdescent : baseEnd_1924022 < baseStart_1924022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924023 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1924023 : Nat := 118140960795 + 1924023 * 2 ^ 59
def prefixEnd_1924023 : Nat := 4983230072969 + 3 ^ 40 * 1924023 * 2
def baseEnd_1924023 : Nat := 987948589305630984864085

theorem tailTrace_1924023 : CollatzResearch.WordTrace tailWord_1924023 prefixEnd_1924023 987948589305630984864085 := by
  unfold tailWord_1924023
  simp only [CollatzResearch.WordTrace]
  refine ⟨70174883908600742812568723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46783255939067161875045815 70174883908600742812568723)
  ·
    refine ⟨105262325862901114218853085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70174883908600742812568723 105262325862901114218853085)
    ·
      refine ⟨39473372198587917832069907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105262325862901114218853085 39473372198587917832069907)
      ·
        refine ⟨59210058297881876748104861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39473372198587917832069907 59210058297881876748104861)
        ·
          refine ⟨22203771861705703780539323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59210058297881876748104861 22203771861705703780539323)
          ·
            refine ⟨33305657792558555670808985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22203771861705703780539323 33305657792558555670808985)
            ·
              refine ⟨24979243344418916753106739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33305657792558555670808985 24979243344418916753106739)
              ·
                refine ⟨37468865016628375129660109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24979243344418916753106739 37468865016628375129660109)
                ·
                  refine ⟨14050824381235640673622541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37468865016628375129660109 14050824381235640673622541)
                  ·
                    refine ⟨5269059142963365252608453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14050824381235640673622541 5269059142963365252608453)
                    ·
                      refine ⟨987948589305630984864085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5269059142963365252608453 987948589305630984864085)
                      ·
                        rfl

theorem cell23_1924023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1924023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924023 prefixEnd_1924023 := by exact prefixLift 1924023
  have htrace : WordTrace (prefixWord ++ tailWord_1924023) baseStart_1924023 baseEnd_1924023 := by
    simpa [prefixWord, tailWord_1924023, baseEnd_1924023] using wordTrace_append hprefix tailTrace_1924023
  have hstable : (prefixWord ++ tailWord_1924023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924023).length < 2 ^ (prefixWord ++ tailWord_1924023).sum := by decide
  have hdescent : baseEnd_1924023 < baseStart_1924023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924094 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1924094 : Nat := 118140960795 + 1924094 * 2 ^ 59
def prefixEnd_1924094 : Nat := 4983230072969 + 3 ^ 40 * 1924094 * 2
def baseEnd_1924094 : Nat := 987985046432100207076259

theorem tailTrace_1924094 : CollatzResearch.WordTrace tailWord_1924094 prefixEnd_1924094 987985046432100207076259 := by
  unfold tailWord_1924094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772184186417940242300417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46784982327562347958935557 8772184186417940242300417)
  ·
    refine ⟨6579138139813455181725313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8772184186417940242300417 6579138139813455181725313)
    ·
      refine ⟨4934353604860091386293985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6579138139813455181725313 4934353604860091386293985)
      ·
        refine ⟨3700765203645068539720489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4934353604860091386293985 3700765203645068539720489)
        ·
          refine ⟨2775573902733801404790367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700765203645068539720489 2775573902733801404790367)
          ·
            refine ⟨4163360854100702107185551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775573902733801404790367 4163360854100702107185551)
            ·
              refine ⟨6245041281151053160778327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163360854100702107185551 6245041281151053160778327)
              ·
                refine ⟨9367561921726579741167491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245041281151053160778327 9367561921726579741167491)
                ·
                  refine ⟨14051342882589869611751237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9367561921726579741167491 14051342882589869611751237)
                  ·
                    refine ⟨2634626790485600552203357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14051342882589869611751237 2634626790485600552203357)
                    ·
                      refine ⟨987985046432100207076259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634626790485600552203357 987985046432100207076259)
                      ·
                        rfl

theorem cell23_1924094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1924094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924094 prefixEnd_1924094 := by exact prefixLift 1924094
  have htrace : WordTrace (prefixWord ++ tailWord_1924094) baseStart_1924094 baseEnd_1924094 := by
    simpa [prefixWord, tailWord_1924094, baseEnd_1924094] using wordTrace_append hprefix tailTrace_1924094
  have hstable : (prefixWord ++ tailWord_1924094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924094).length < 2 ^ (prefixWord ++ tailWord_1924094).sum := by decide
  have hdescent : baseEnd_1924094 < baseStart_1924094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924157 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_1924157 : Nat := 118140960795 + 1924157 * 2 ^ 59
def prefixEnd_1924157 : Nat := 4983230072969 + 3 ^ 40 * 1924157 * 2
def baseEnd_1924157 : Nat := 329339131904444486862823

theorem tailTrace_1924157 : CollatzResearch.WordTrace tailWord_1924157 prefixEnd_1924157 329339131904444486862823 := by
  unfold tailWord_1924157
  simp only [CollatzResearch.WordTrace]
  refine ⟨70179771290115283697946725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46786514193410189131964483 70179771290115283697946725)
  ·
    refine ⟨13158707116896615693365011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70179771290115283697946725 13158707116896615693365011)
    ·
      refine ⟨19738060675344923540047517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13158707116896615693365011 19738060675344923540047517)
      ·
        refine ⟨7401772753254346327517819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19738060675344923540047517 7401772753254346327517819)
        ·
          refine ⟨11102659129881519491276729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7401772753254346327517819 11102659129881519491276729)
          ·
            refine ⟨8326994347411139618457547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11102659129881519491276729 8326994347411139618457547)
            ·
              refine ⟨12490491521116709427686321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326994347411139618457547 12490491521116709427686321)
              ·
                refine ⟨9367868640837532070764741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12490491521116709427686321 9367868640837532070764741)
                ·
                  refine ⟨1756475370157037263268389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9367868640837532070764741 1756475370157037263268389)
                  ·
                    refine ⟨329339131904444486862823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756475370157037263268389 329339131904444486862823)
                    ·
                      rfl

theorem cell23_1924157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_1924157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924157 prefixEnd_1924157 := by exact prefixLift 1924157
  have htrace : WordTrace (prefixWord ++ tailWord_1924157) baseStart_1924157 baseEnd_1924157 := by
    simpa [prefixWord, tailWord_1924157, baseEnd_1924157] using wordTrace_append hprefix tailTrace_1924157
  have hstable : (prefixWord ++ tailWord_1924157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924157).length < 2 ^ (prefixWord ++ tailWord_1924157).sum := by decide
  have hdescent : baseEnd_1924157 < baseStart_1924157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924158 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1924158 : Nat := 118140960795 + 1924158 * 2 ^ 59
def prefixEnd_1924158 : Nat := 4983230072969 + 3 ^ 40 * 1924158 * 2
def baseEnd_1924158 : Nat := 988017909193987956675965

theorem tailTrace_1924158 : CollatzResearch.WordTrace tailWord_1924158 prefixEnd_1924158 988017909193987956675965 := by
  unfold tailWord_1924158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772475970388957608591641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46786538508741107245822085 8772475970388957608591641)
  ·
    refine ⟨6579356977791718206443731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8772475970388957608591641 6579356977791718206443731)
    ·
      refine ⟨9869035466687577309665597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6579356977791718206443731 9869035466687577309665597)
      ·
        refine ⟨3700888300007841491124599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9869035466687577309665597 3700888300007841491124599)
        ·
          refine ⟨5551332450011762236686899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700888300007841491124599 5551332450011762236686899)
          ·
            refine ⟨8326998675017643355030349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551332450011762236686899 8326998675017643355030349)
            ·
              refine ⟨3122624503131616258136381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8326998675017643355030349 3122624503131616258136381)
              ·
                refine ⟨1170984188674356096801143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3122624503131616258136381 1170984188674356096801143)
                ·
                  refine ⟨1756476283011534145201715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170984188674356096801143 1756476283011534145201715)
                  ·
                    refine ⟨2634714424517301217802573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1756476283011534145201715 2634714424517301217802573)
                    ·
                      refine ⟨988017909193987956675965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634714424517301217802573 988017909193987956675965)
                      ·
                        rfl

theorem cell23_1924158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1924158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924158 prefixEnd_1924158 := by exact prefixLift 1924158
  have htrace : WordTrace (prefixWord ++ tailWord_1924158) baseStart_1924158 baseEnd_1924158 := by
    simpa [prefixWord, tailWord_1924158, baseEnd_1924158] using wordTrace_append hprefix tailTrace_1924158
  have hstable : (prefixWord ++ tailWord_1924158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924158).length < 2 ^ (prefixWord ++ tailWord_1924158).sum := by decide
  have hdescent : baseEnd_1924158 < baseStart_1924158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924160 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1924160 : Nat := 118140960795 + 1924160 * 2 ^ 59
def prefixEnd_1924160 : Nat := 4983230072969 + 3 ^ 40 * 1924160 * 2
def baseEnd_1924160 : Nat := 988018936155296948850955

theorem tailTrace_1924160 : CollatzResearch.WordTrace tailWord_1924160 prefixEnd_1924160 988018936155296948850955 := by
  unfold tailWord_1924160
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089940354552207605152967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46786587139402943473537289 35089940354552207605152967)
  ·
    refine ⟨52634910531828311407729451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35089940354552207605152967 52634910531828311407729451)
    ·
      refine ⟨78952365797742467111594177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52634910531828311407729451 78952365797742467111594177)
      ·
        refine ⟨59214274348306850333695633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78952365797742467111594177 59214274348306850333695633)
        ·
          refine ⟨44410705761230137750271725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59214274348306850333695633 44410705761230137750271725)
          ·
            refine ⟨16654014660461301656351897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44410705761230137750271725 16654014660461301656351897)
            ·
              refine ⟨12490510995345976242263923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16654014660461301656351897 12490510995345976242263923)
              ·
                refine ⟨18735766493018964363395885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12490510995345976242263923 18735766493018964363395885)
                ·
                  refine ⟨7025912434882111636273457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18735766493018964363395885 7025912434882111636273457)
                  ·
                    refine ⟨5269434326161583727205093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025912434882111636273457 5269434326161583727205093)
                    ·
                      refine ⟨988018936155296948850955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5269434326161583727205093 988018936155296948850955)
                      ·
                        rfl

theorem cell23_1924160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1924160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924160 prefixEnd_1924160 := by exact prefixLift 1924160
  have htrace : WordTrace (prefixWord ++ tailWord_1924160) baseStart_1924160 baseEnd_1924160 := by
    simpa [prefixWord, tailWord_1924160, baseEnd_1924160] using wordTrace_append hprefix tailTrace_1924160
  have hstable : (prefixWord ++ tailWord_1924160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924160).length < 2 ^ (prefixWord ++ tailWord_1924160).sum := by decide
  have hdescent : baseEnd_1924160 < baseStart_1924160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924167 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1924167 : Nat := 118140960795 + 1924167 * 2 ^ 59
def prefixEnd_1924167 : Nat := 4983230072969 + 3 ^ 40 * 1924167 * 2
def baseEnd_1924167 : Nat := 988022530519878421463423

theorem tailTrace_1924167 : CollatzResearch.WordTrace tailWord_1924167 prefixEnd_1924167 988022530519878421463423 := by
  unfold tailWord_1924167
  simp only [CollatzResearch.WordTrace]
  refine ⟨70180136020079055405810755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46786757346719370270540503 70180136020079055405810755)
  ·
    refine ⟨105270204030118583108716133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70180136020079055405810755 105270204030118583108716133)
    ·
      refine ⟨19738163255647234332884275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105270204030118583108716133 19738163255647234332884275)
      ·
        refine ⟨29607244883470851499326413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19738163255647234332884275 29607244883470851499326413)
        ·
          refine ⟨11102716831301569312247405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29607244883470851499326413 11102716831301569312247405)
          ·
            refine ⟨4163518811738088492092777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11102716831301569312247405 4163518811738088492092777)
            ·
              refine ⟨3122639108803566369069583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163518811738088492092777 3122639108803566369069583)
              ·
                refine ⟨4683958663205349553604375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122639108803566369069583 4683958663205349553604375)
                ·
                  refine ⟨7025937994808024330406563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683958663205349553604375 7025937994808024330406563)
                  ·
                    refine ⟨10538906992212036495609845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7025937994808024330406563 10538906992212036495609845)
                    ·
                      refine ⟨988022530519878421463423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10538906992212036495609845 988022530519878421463423)
                      ·
                        rfl

theorem cell23_1924167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1924167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924167 prefixEnd_1924167 := by exact prefixLift 1924167
  have htrace : WordTrace (prefixWord ++ tailWord_1924167) baseStart_1924167 baseEnd_1924167 := by
    simpa [prefixWord, tailWord_1924167, baseEnd_1924167] using wordTrace_append hprefix tailTrace_1924167
  have hstable : (prefixWord ++ tailWord_1924167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924167).length < 2 ^ (prefixWord ++ tailWord_1924167).sum := by decide
  have hdescent : baseEnd_1924167 < baseStart_1924167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924197 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1924197 : Nat := 118140960795 + 1924197 * 2 ^ 59
def prefixEnd_1924197 : Nat := 4983230072969 + 3 ^ 40 * 1924197 * 2
def baseEnd_1924197 : Nat := 988037934939513304088285

theorem tailTrace_1924197 : CollatzResearch.WordTrace tailWord_1924197 prefixEnd_1924197 988037934939513304088285 := by
  unfold tailWord_1924197
  simp only [CollatzResearch.WordTrace]
  refine ⟨70181230209970370529402845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46787486806646913686268563 70181230209970370529402845)
  ·
    refine ⟨26317961328738888948526067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70181230209970370529402845 26317961328738888948526067)
    ·
      refine ⟨39476941993108333422789101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26317961328738888948526067 39476941993108333422789101)
      ·
        refine ⟨14803853247415625033545913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39476941993108333422789101 14803853247415625033545913)
        ·
          refine ⟨11102889935561718775159435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14803853247415625033545913 11102889935561718775159435)
          ·
            refine ⟨16654334903342578162739153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102889935561718775159435 16654334903342578162739153)
            ·
              refine ⟨12490751177506933622054365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16654334903342578162739153 12490751177506933622054365)
              ·
                refine ⟨4684031691565100108270387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12490751177506933622054365 4684031691565100108270387)
                ·
                  refine ⟨7026047537347650162405581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684031691565100108270387 7026047537347650162405581)
                  ·
                    refine ⟨2634767826505368810902093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7026047537347650162405581 2634767826505368810902093)
                    ·
                      refine ⟨988037934939513304088285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634767826505368810902093 988037934939513304088285)
                      ·
                        rfl

theorem cell23_1924197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1924197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924197 prefixEnd_1924197 := by exact prefixLift 1924197
  have htrace : WordTrace (prefixWord ++ tailWord_1924197) baseStart_1924197 baseEnd_1924197 := by
    simpa [prefixWord, tailWord_1924197, baseEnd_1924197] using wordTrace_append hprefix tailTrace_1924197
  have hstable : (prefixWord ++ tailWord_1924197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924197).length < 2 ^ (prefixWord ++ tailWord_1924197).sum := by decide
  have hdescent : baseEnd_1924197 < baseStart_1924197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924214 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1924214 : Nat := 118140960795 + 1924214 * 2 ^ 59
def prefixEnd_1924214 : Nat := 4983230072969 + 3 ^ 40 * 1924214 * 2
def baseEnd_1924214 : Nat := 988046664110639737575707

theorem tailTrace_1924214 : CollatzResearch.WordTrace tailWord_1924214 prefixEnd_1924214 988046664110639737575707 := by
  unfold tailWord_1924214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386365640681798902048231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46787900167272521621847797 4386365640681798902048231)
  ·
    refine ⟨6579548461022698353072347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386365640681798902048231 6579548461022698353072347)
    ·
      refine ⟨9869322691534047529608521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6579548461022698353072347 9869322691534047529608521)
      ·
        refine ⟨7401992018650535647206391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9869322691534047529608521 7401992018650535647206391)
        ·
          refine ⟨11102988027975803470809587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7401992018650535647206391 11102988027975803470809587)
          ·
            refine ⟨16654482041963705206214381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102988027975803470809587 16654482041963705206214381)
            ·
              refine ⟨6245430765736389452330393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16654482041963705206214381 6245430765736389452330393)
              ·
                refine ⟨4684073074302292089247795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6245430765736389452330393 4684073074302292089247795)
                ·
                  refine ⟨7026109611453438133871693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684073074302292089247795 7026109611453438133871693)
                  ·
                    refine ⟨2634791104295039300201885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7026109611453438133871693 2634791104295039300201885)
                    ·
                      refine ⟨988046664110639737575707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634791104295039300201885 988046664110639737575707)
                      ·
                        rfl

theorem cell23_1924214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1924214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924214 prefixEnd_1924214 := by exact prefixLift 1924214
  have htrace : WordTrace (prefixWord ++ tailWord_1924214) baseStart_1924214 baseEnd_1924214 := by
    simpa [prefixWord, tailWord_1924214, baseEnd_1924214] using wordTrace_append hprefix tailTrace_1924214
  have hstable : (prefixWord ++ tailWord_1924214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924214).length < 2 ^ (prefixWord ++ tailWord_1924214).sum := by decide
  have hdescent : baseEnd_1924214 < baseStart_1924214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924224 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 1, 3, 2]
def baseStart_1924224 : Nat := 118140960795 + 1924224 * 2 ^ 59
def prefixEnd_1924224 : Nat := 4983230072969 + 3 ^ 40 * 1924224 * 2
def baseEnd_1924224 : Nat := 988051798917184698450661

theorem tailTrace_1924224 : CollatzResearch.WordTrace tailWord_1924224 prefixEnd_1924224 988051798917184698450661 := by
  unfold tailWord_1924224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091107490436277070317863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46788143320581702760423817 35091107490436277070317863)
  ·
    refine ⟨52636661235654415605476795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35091107490436277070317863 52636661235654415605476795)
    ·
      refine ⟨78954991853481623408215193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52636661235654415605476795 78954991853481623408215193)
      ·
        refine ⟨59216243890111217556161395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78954991853481623408215193 59216243890111217556161395)
        ·
          refine ⟨88824365835166826334242093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59216243890111217556161395 88824365835166826334242093)
          ·
            refine ⟨33309137188187559875340785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88824365835166826334242093 33309137188187559875340785)
            ·
              refine ⟨24981852891140669906505589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33309137188187559875340785 24981852891140669906505589)
              ·
                refine ⟨2342048708544437803734899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24981852891140669906505589 2342048708544437803734899)
                ·
                  refine ⟨3513073062816656705602349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342048708544437803734899 3513073062816656705602349)
                  ·
                    refine ⟨1317402398556246264600881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513073062816656705602349 1317402398556246264600881)
                    ·
                      refine ⟨988051798917184698450661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317402398556246264600881 988051798917184698450661)
                      ·
                        rfl

theorem cell23_1924224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_1924224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924224 prefixEnd_1924224 := by exact prefixLift 1924224
  have htrace : WordTrace (prefixWord ++ tailWord_1924224) baseStart_1924224 baseEnd_1924224 := by
    simpa [prefixWord, tailWord_1924224, baseEnd_1924224] using wordTrace_append hprefix tailTrace_1924224
  have hstable : (prefixWord ++ tailWord_1924224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924224).length < 2 ^ (prefixWord ++ tailWord_1924224).sum := by decide
  have hdescent : baseEnd_1924224 < baseStart_1924224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924232 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1924232 : Nat := 118140960795 + 1924232 * 2 ^ 59
def prefixEnd_1924232 : Nat := 4983230072969 + 3 ^ 40 * 1924232 * 2
def baseEnd_1924232 : Nat := 988055906762420667150625

theorem tailTrace_1924232 : CollatzResearch.WordTrace tailWord_1924232 prefixEnd_1924232 988055906762420667150625 := by
  unfold tailWord_1924232
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091253382421785753463475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46788337843229047671284633 35091253382421785753463475)
  ·
    refine ⟨52636880073632678630195213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35091253382421785753463475 52636880073632678630195213)
    ·
      refine ⟨19738830027612254486323205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52636880073632678630195213 19738830027612254486323205)
      ·
        refine ⟨3701030630177297716185601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19738830027612254486323205 3701030630177297716185601)
        ·
          refine ⟨2775772972632973287139201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701030630177297716185601 2775772972632973287139201)
          ·
            refine ⟨2081829729474729965354401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775772972632973287139201 2081829729474729965354401)
            ·
              refine ⟨1561372297106047474015801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081829729474729965354401 1561372297106047474015801)
              ·
                refine ⟨1171029222829535605511851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561372297106047474015801 1171029222829535605511851)
                ·
                  refine ⟨1756543834244303408267777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171029222829535605511851 1756543834244303408267777)
                  ·
                    refine ⟨1317407875683227556200833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1756543834244303408267777 1317407875683227556200833)
                    ·
                      refine ⟨988055906762420667150625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317407875683227556200833 988055906762420667150625)
                      ·
                        rfl

theorem cell23_1924232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1924232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924232 prefixEnd_1924232 := by exact prefixLift 1924232
  have htrace : WordTrace (prefixWord ++ tailWord_1924232) baseStart_1924232 baseEnd_1924232 := by
    simpa [prefixWord, tailWord_1924232, baseEnd_1924232] using wordTrace_append hprefix tailTrace_1924232
  have hstable : (prefixWord ++ tailWord_1924232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924232).length < 2 ^ (prefixWord ++ tailWord_1924232).sum := by decide
  have hdescent : baseEnd_1924232 < baseStart_1924232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924240 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_1924240 : Nat := 118140960795 + 1924240 * 2 ^ 59
def prefixEnd_1924240 : Nat := 4983230072969 + 3 ^ 40 * 1924240 * 2
def baseEnd_1924240 : Nat := 988060014607656635850587

theorem tailTrace_1924240 : CollatzResearch.WordTrace tailWord_1924240 prefixEnd_1924240 988060014607656635850587 := by
  unfold tailWord_1924240
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091399274407294436609087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46788532365876392582145449 35091399274407294436609087)
  ·
    refine ⟨52637098911610941654913631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35091399274407294436609087 52637098911610941654913631)
    ·
      refine ⟨78955648367416412482370447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52637098911610941654913631 78955648367416412482370447)
      ·
        refine ⟨118433472551124618723555671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78955648367416412482370447 118433472551124618723555671)
        ·
          refine ⟨177650208826686928085333507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118433472551124618723555671 177650208826686928085333507)
          ·
            refine ⟨266475313240030392128000261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177650208826686928085333507 266475313240030392128000261)
            ·
              refine ⟨49964121232505698524000049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266475313240030392128000261 49964121232505698524000049)
              ·
                refine ⟨37473090924379273893000037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49964121232505698524000049 37473090924379273893000037)
                ·
                  refine ⟨7026204548321113854937507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37473090924379273893000037 7026204548321113854937507)
                  ·
                    refine ⟨10539306822481670782406261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026204548321113854937507 10539306822481670782406261)
                    ·
                      refine ⟨988060014607656635850587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10539306822481670782406261 988060014607656635850587)
                      ·
                        rfl

theorem cell23_1924240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_1924240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924240 prefixEnd_1924240 := by exact prefixLift 1924240
  have htrace : WordTrace (prefixWord ++ tailWord_1924240) baseStart_1924240 baseEnd_1924240 := by
    simpa [prefixWord, tailWord_1924240, baseEnd_1924240] using wordTrace_append hprefix tailTrace_1924240
  have hstable : (prefixWord ++ tailWord_1924240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924240).length < 2 ^ (prefixWord ++ tailWord_1924240).sum := by decide
  have hdescent : baseEnd_1924240 < baseStart_1924240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924247 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 2, 6]
def baseStart_1924247 : Nat := 118140960795 + 1924247 * 2 ^ 59
def prefixEnd_1924247 : Nat := 4983230072969 + 3 ^ 40 * 1924247 * 2
def baseEnd_1924247 : Nat := 329354536324079369487685

theorem tailTrace_1924247 : CollatzResearch.WordTrace tailWord_1924247 prefixEnd_1924247 329354536324079369487685 := by
  unfold tailWord_1924247
  simp only [CollatzResearch.WordTrace]
  refine ⟨70183053859789229068722995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46788702573192819379148663 70183053859789229068722995)
  ·
    refine ⟨105274580789683843603084493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70183053859789229068722995 105274580789683843603084493)
    ·
      refine ⟨39477967796131441351156685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105274580789683843603084493 39477967796131441351156685)
      ·
        refine ⟨14804237923549290506683757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39477967796131441351156685 14804237923549290506683757)
        ·
          refine ⟨5551589221330983940006409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14804237923549290506683757 5551589221330983940006409)
          ·
            refine ⟨4163691915998237955004807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551589221330983940006409 4163691915998237955004807)
            ·
              refine ⟨6245537873997356932507211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163691915998237955004807 6245537873997356932507211)
              ·
                refine ⟨9368306810996035398760817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245537873997356932507211 9368306810996035398760817)
                ·
                  refine ⟨7026230108247026549070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9368306810996035398760817 7026230108247026549070613)
                  ·
                    refine ⟨329354536324079369487685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7026230108247026549070613 329354536324079369487685)
                    ·
                      rfl

theorem cell23_1924247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_1924247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924247 prefixEnd_1924247 := by exact prefixLift 1924247
  have htrace : WordTrace (prefixWord ++ tailWord_1924247) baseStart_1924247 baseEnd_1924247 := by
    simpa [prefixWord, tailWord_1924247, baseEnd_1924247] using wordTrace_append hprefix tailTrace_1924247
  have hstable : (prefixWord ++ tailWord_1924247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924247).length < 2 ^ (prefixWord ++ tailWord_1924247).sum := by decide
  have hdescent : baseEnd_1924247 < baseStart_1924247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924257 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1924257 : Nat := 118140960795 + 1924257 * 2 ^ 59
def prefixEnd_1924257 : Nat := 4983230072969 + 3 ^ 40 * 1924257 * 2
def baseEnd_1924257 : Nat := 988068743778783069338009

theorem tailTrace_1924257 : CollatzResearch.WordTrace tailWord_1924257 prefixEnd_1924257 988068743778783069338009 := by
  unfold tailWord_1924257
  simp only [CollatzResearch.WordTrace]
  refine ⟨70183418589753000776587025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46788945726502000517724683 70183418589753000776587025)
  ·
    refine ⟨52637563942314750582440269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70183418589753000776587025 52637563942314750582440269)
    ·
      refine ⟨19739086478368031468415101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52637563942314750582440269 19739086478368031468415101)
      ·
        refine ⟨7402157429388011800655663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19739086478368031468415101 7402157429388011800655663)
        ·
          refine ⟨11103236144082017700983495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402157429388011800655663 11103236144082017700983495)
          ·
            refine ⟨16654854216123026551475243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11103236144082017700983495 16654854216123026551475243)
            ·
              refine ⟨24982281324184539827212865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16654854216123026551475243 24982281324184539827212865)
              ·
                refine ⟨18736710993138404870409649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24982281324184539827212865 18736710993138404870409649)
                ·
                  refine ⟨14052533244853803652807237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18736710993138404870409649 14052533244853803652807237)
                  ·
                    refine ⟨2634849983410088184901357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14052533244853803652807237 2634849983410088184901357)
                    ·
                      refine ⟨988068743778783069338009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634849983410088184901357 988068743778783069338009)
                      ·
                        rfl

theorem cell23_1924257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1924257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924257 prefixEnd_1924257 := by exact prefixLift 1924257
  have htrace : WordTrace (prefixWord ++ tailWord_1924257) baseStart_1924257 baseEnd_1924257 := by
    simpa [prefixWord, tailWord_1924257, baseEnd_1924257] using wordTrace_append hprefix tailTrace_1924257
  have hstable : (prefixWord ++ tailWord_1924257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924257).length < 2 ^ (prefixWord ++ tailWord_1924257).sum := by decide
  have hdescent : baseEnd_1924257 < baseStart_1924257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924287 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_1924287 : Nat := 118140960795 + 1924287 * 2 ^ 59
def prefixEnd_1924287 : Nat := 4983230072969 + 3 ^ 40 * 1924287 * 2
def baseEnd_1924287 : Nat := 988084148198417951962871

theorem tailTrace_1924287 : CollatzResearch.WordTrace tailWord_1924287 prefixEnd_1924287 988084148198417951962871 := by
  unfold tailWord_1924287
  simp only [CollatzResearch.WordTrace]
  refine ⟨70184512779644315900179115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46789675186429543933452743 70184512779644315900179115)
  ·
    refine ⟨105276769169466473850268673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70184512779644315900179115 105276769169466473850268673)
    ·
      refine ⟨78957576877099855387701505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105276769169466473850268673 78957576877099855387701505)
      ·
        refine ⟨59218182657824891540776129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78957576877099855387701505 59218182657824891540776129)
        ·
          refine ⟨44413636993368668655582097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59218182657824891540776129 44413636993368668655582097)
          ·
            refine ⟨33310227745026501491686573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44413636993368668655582097 33310227745026501491686573)
            ·
              refine ⟨12491335404384938059382465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33310227745026501491686573 12491335404384938059382465)
              ·
                refine ⟨9368501553288703544536849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12491335404384938059382465 9368501553288703544536849)
                ·
                  refine ⟨7026376164966527658402637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9368501553288703544536849 7026376164966527658402637)
                  ·
                    refine ⟨2634891061862447871900989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7026376164966527658402637 2634891061862447871900989)
                    ·
                      refine ⟨988084148198417951962871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2634891061862447871900989 988084148198417951962871)
                      ·
                        rfl

theorem cell23_1924287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_1924287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924287 prefixEnd_1924287 := by exact prefixLift 1924287
  have htrace : WordTrace (prefixWord ++ tailWord_1924287) baseStart_1924287 baseEnd_1924287 := by
    simpa [prefixWord, tailWord_1924287, baseEnd_1924287] using wordTrace_append hprefix tailTrace_1924287
  have hstable : (prefixWord ++ tailWord_1924287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924287).length < 2 ^ (prefixWord ++ tailWord_1924287).sum := by decide
  have hdescent : baseEnd_1924287 < baseStart_1924287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924381 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1924381 : Nat := 118140960795 + 1924381 * 2 ^ 59
def prefixEnd_1924381 : Nat := 4983230072969 + 3 ^ 40 * 1924381 * 2
def baseEnd_1924381 : Nat := 988132415379940584187439

theorem tailTrace_1924381 : CollatzResearch.WordTrace tailWord_1924381 prefixEnd_1924381 988132415379940584187439 := by
  unfold tailWord_1924381
  simp only [CollatzResearch.WordTrace]
  refine ⟨70187941241303769954100997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46791960827535846636067331 70187941241303769954100997)
  ·
    refine ⟨13160238982744456866393937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70187941241303769954100997 13160238982744456866393937)
    ·
      refine ⟨9870179237058342649795453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13160238982744456866393937 9870179237058342649795453)
      ·
        refine ⟨3701317213896878493673295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9870179237058342649795453 3701317213896878493673295)
        ·
          refine ⟨5551975820845317740509943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701317213896878493673295 5551975820845317740509943)
          ·
            refine ⟨8327963731267976610764915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551975820845317740509943 8327963731267976610764915)
            ·
              refine ⟨12491945596901964916147373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8327963731267976610764915 12491945596901964916147373)
              ·
                refine ⟨4684479598838236843555265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12491945596901964916147373 4684479598838236843555265)
                ·
                  refine ⟨3513359699128677632666449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4684479598838236843555265 3513359699128677632666449)
                  ·
                    refine ⟨2635019774346508224499837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3513359699128677632666449 2635019774346508224499837)
                    ·
                      refine ⟨988132415379940584187439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2635019774346508224499837 988132415379940584187439)
                      ·
                        rfl

theorem cell23_1924381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1924381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924381 prefixEnd_1924381 := by exact prefixLift 1924381
  have htrace : WordTrace (prefixWord ++ tailWord_1924381) baseStart_1924381 baseEnd_1924381 := by
    simpa [prefixWord, tailWord_1924381, baseEnd_1924381] using wordTrace_append hprefix tailTrace_1924381
  have hstable : (prefixWord ++ tailWord_1924381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924381).length < 2 ^ (prefixWord ++ tailWord_1924381).sum := by decide
  have hdescent : baseEnd_1924381 < baseStart_1924381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924404 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1924404 : Nat := 118140960795 + 1924404 * 2 ^ 59
def prefixEnd_1924404 : Nat := 4983230072969 + 3 ^ 40 * 1924404 * 2
def baseEnd_1924404 : Nat := 988144225434993994199833

theorem tailTrace_1924404 : CollatzResearch.WordTrace tailWord_1924404 prefixEnd_1924404 988144225434993994199833 := by
  unfold tailWord_1924404
  simp only [CollatzResearch.WordTrace]
  refine ⟨35094390060110222441094133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46792520080146963254792177 35094390060110222441094133)
  ·
    refine ⟨3290099068135333353852575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35094390060110222441094133 3290099068135333353852575)
    ·
      refine ⟨4935148602203000030778863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290099068135333353852575 4935148602203000030778863)
      ·
        refine ⟨7402722903304500046168295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935148602203000030778863 7402722903304500046168295)
        ·
          refine ⟨11104084354956750069252443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402722903304500046168295 11104084354956750069252443)
          ·
            refine ⟨16656126532435125103878665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104084354956750069252443 16656126532435125103878665)
            ·
              refine ⟨12492094899326343827908999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16656126532435125103878665 12492094899326343827908999)
              ·
                refine ⟨18738142348989515741863499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12492094899326343827908999 18738142348989515741863499)
                ·
                  refine ⟨28107213523484273612795249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18738142348989515741863499 28107213523484273612795249)
                  ·
                    refine ⟨21080410142613205209596437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28107213523484273612795249 21080410142613205209596437)
                    ·
                      refine ⟨988144225434993994199833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21080410142613205209596437 988144225434993994199833)
                      ·
                        rfl

theorem cell23_1924404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1924404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924404 prefixEnd_1924404 := by exact prefixLift 1924404
  have htrace : WordTrace (prefixWord ++ tailWord_1924404) baseStart_1924404 baseEnd_1924404 := by
    simpa [prefixWord, tailWord_1924404, baseEnd_1924404] using wordTrace_append hprefix tailTrace_1924404
  have hstable : (prefixWord ++ tailWord_1924404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924404).length < 2 ^ (prefixWord ++ tailWord_1924404).sum := by decide
  have hdescent : baseEnd_1924404 < baseStart_1924404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924405 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1924405 : Nat := 118140960795 + 1924405 * 2 ^ 59
def prefixEnd_1924405 : Nat := 4983230072969 + 3 ^ 40 * 1924405 * 2
def baseEnd_1924405 : Nat := 329381579638549496762443

theorem tailTrace_1924405 : CollatzResearch.WordTrace tailWord_1924405 prefixEnd_1924405 329381579638549496762443 := by
  unfold tailWord_1924405
  simp only [CollatzResearch.WordTrace]
  refine ⟨70188816593216822052974669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46792544395477881368649779 70188816593216822052974669)
  ·
    refine ⟨26320806222456308269865501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70188816593216822052974669 26320806222456308269865501)
    ·
      refine ⟨9870302333421115601199563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26320806222456308269865501 9870302333421115601199563)
      ·
        refine ⟨14805453500131673401799345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9870302333421115601199563 14805453500131673401799345)
        ·
          refine ⟨11104090125098755051349509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14805453500131673401799345 11104090125098755051349509)
          ·
            refine ⟨2082016898456016572128033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11104090125098755051349509 2082016898456016572128033)
            ·
              refine ⟨1561512673842012429096025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082016898456016572128033 1561512673842012429096025)
              ·
                refine ⟨1171134505381509321822019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561512673842012429096025 1171134505381509321822019)
                ·
                  refine ⟨1756701758072263982733029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171134505381509321822019 1756701758072263982733029)
                  ·
                    refine ⟨329381579638549496762443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756701758072263982733029 329381579638549496762443)
                    ·
                      rfl

theorem cell23_1924405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1924405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924405 prefixEnd_1924405 := by exact prefixLift 1924405
  have htrace : WordTrace (prefixWord ++ tailWord_1924405) baseStart_1924405 baseEnd_1924405 := by
    simpa [prefixWord, tailWord_1924405, baseEnd_1924405] using wordTrace_append hprefix tailTrace_1924405
  have hstable : (prefixWord ++ tailWord_1924405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924405).length < 2 ^ (prefixWord ++ tailWord_1924405).sum := by decide
  have hdescent : baseEnd_1924405 < baseStart_1924405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924414 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1924414 : Nat := 118140960795 + 1924414 * 2 ^ 59
def prefixEnd_1924414 : Nat := 4983230072969 + 3 ^ 40 * 1924414 * 2
def baseEnd_1924414 : Nat := 329383120080512985024929

theorem tailTrace_1924414 : CollatzResearch.WordTrace tailWord_1924414 prefixEnd_1924414 329383120080512985024929 := by
  unfold tailWord_1924414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773643106273027073756537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46792763233456144393368197 8773643106273027073756537)
  ·
    refine ⟨6580232329704770305317403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8773643106273027073756537 6580232329704770305317403)
    ·
      refine ⟨9870348494557155457976105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580232329704770305317403 9870348494557155457976105)
      ·
        refine ⟨7402761370917866593482079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9870348494557155457976105 7402761370917866593482079)
        ·
          refine ⟨11104142056376799890223119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402761370917866593482079 11104142056376799890223119)
          ·
            refine ⟨16656213084565199835334679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104142056376799890223119 16656213084565199835334679)
            ·
              refine ⟨24984319626847799753002019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16656213084565199835334679 24984319626847799753002019)
              ·
                refine ⟨37476479440271699629503029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24984319626847799753002019 37476479440271699629503029)
                ·
                  refine ⟨3513419947525471840265909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37476479440271699629503029 3513419947525471840265909)
                  ·
                    refine ⟨329383120080512985024929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3513419947525471840265909 329383120080512985024929)
                    ·
                      rfl

theorem cell23_1924414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1924414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924414 prefixEnd_1924414 := by exact prefixLift 1924414
  have htrace : WordTrace (prefixWord ++ tailWord_1924414) baseStart_1924414 baseEnd_1924414 := by
    simpa [prefixWord, tailWord_1924414, baseEnd_1924414] using wordTrace_append hprefix tailTrace_1924414
  have hstable : (prefixWord ++ tailWord_1924414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924414).length < 2 ^ (prefixWord ++ tailWord_1924414).sum := by decide
  have hdescent : baseEnd_1924414 < baseStart_1924414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924447 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1924447 : Nat := 118140960795 + 1924447 * 2 ^ 59
def prefixEnd_1924447 : Nat := 4983230072969 + 3 ^ 40 * 1924447 * 2
def baseEnd_1924447 : Nat := 988166305103137325962135

theorem tailTrace_1924447 : CollatzResearch.WordTrace tailWord_1924447 prefixEnd_1924447 988166305103137325962135 := by
  unfold tailWord_1924447
  simp only [CollatzResearch.WordTrace]
  refine ⟨70190348459064663226003595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46793565639376442150669063 70190348459064663226003595)
  ·
    refine ⟨105285522688596994839005393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70190348459064663226003595 105285522688596994839005393)
    ·
      refine ⟨78964142016447746129254045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105285522688596994839005393 78964142016447746129254045)
      ·
        refine ⟨29611553256167904798470267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78964142016447746129254045 29611553256167904798470267)
        ·
          refine ⟨44417329884251857197705401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29611553256167904798470267 44417329884251857197705401)
          ·
            refine ⟨33312997413188892898279051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44417329884251857197705401 33312997413188892898279051)
            ·
              refine ⟨49969496119783339347418577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33312997413188892898279051 49969496119783339347418577)
              ·
                refine ⟨37477122089837504510563933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49969496119783339347418577 37477122089837504510563933)
                ·
                  refine ⟨14053920783689064191461475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37477122089837504510563933 14053920783689064191461475)
                  ·
                    refine ⟨21080881175533596287192213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14053920783689064191461475 21080881175533596287192213)
                    ·
                      refine ⟨988166305103137325962135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21080881175533596287192213 988166305103137325962135)
                      ·
                        rfl

theorem cell23_1924447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1924447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924447 prefixEnd_1924447 := by exact prefixLift 1924447
  have htrace : WordTrace (prefixWord ++ tailWord_1924447) baseStart_1924447 baseEnd_1924447 := by
    simpa [prefixWord, tailWord_1924447, baseEnd_1924447] using wordTrace_append hprefix tailTrace_1924447
  have hstable : (prefixWord ++ tailWord_1924447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924447).length < 2 ^ (prefixWord ++ tailWord_1924447).sum := by decide
  have hdescent : baseEnd_1924447 < baseStart_1924447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924448 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 1, 5]
def baseStart_1924448 : Nat := 118140960795 + 1924448 * 2 ^ 59
def prefixEnd_1924448 : Nat := 4983230072969 + 3 ^ 40 * 1924448 * 2
def baseEnd_1924448 : Nat := 329388939527930607349877

theorem tailTrace_1924448 : CollatzResearch.WordTrace tailWord_1924448 prefixEnd_1924448 329388939527930607349877 := by
  unfold tailWord_1924448
  simp only [CollatzResearch.WordTrace]
  refine ⟨35095192466030520198394999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46793589954707360264526665 35095192466030520198394999)
  ·
    refine ⟨52642788699045780297592499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35095192466030520198394999 52642788699045780297592499)
    ·
      refine ⟨78964183048568670446388749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52642788699045780297592499 78964183048568670446388749)
      ·
        refine ⟨29611568643213251417395781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78964183048568670446388749 29611568643213251417395781)
        ·
          refine ⟨5552169120602484640761709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29611568643213251417395781 5552169120602484640761709)
          ·
            refine ⟨2082063420225931740285641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5552169120602484640761709 2082063420225931740285641)
            ·
              refine ⟨1561547565169448805214231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082063420225931740285641 1561547565169448805214231)
              ·
                refine ⟨2342321347754173207821347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561547565169448805214231 2342321347754173207821347)
                ·
                  refine ⟨3513482021631259811732021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342321347754173207821347 3513482021631259811732021)
                  ·
                    refine ⟨329388939527930607349877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3513482021631259811732021 329388939527930607349877)
                    ·
                      rfl

theorem cell23_1924448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 5].length) (baseStart_1924448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924448 prefixEnd_1924448 := by exact prefixLift 1924448
  have htrace : WordTrace (prefixWord ++ tailWord_1924448) baseStart_1924448 baseEnd_1924448 := by
    simpa [prefixWord, tailWord_1924448, baseEnd_1924448] using wordTrace_append hprefix tailTrace_1924448
  have hstable : (prefixWord ++ tailWord_1924448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924448).length < 2 ^ (prefixWord ++ tailWord_1924448).sum := by decide
  have hdescent : baseEnd_1924448 < baseStart_1924448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924451 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1924451 : Nat := 118140960795 + 1924451 * 2 ^ 59
def prefixEnd_1924451 : Nat := 4983230072969 + 3 ^ 40 * 1924451 * 2
def baseEnd_1924451 : Nat := 988168359025755310312117

theorem tailTrace_1924451 : CollatzResearch.WordTrace tailWord_1924451 prefixEnd_1924451 988168359025755310312117 := by
  unfold tailWord_1924451
  simp only [CollatzResearch.WordTrace]
  refine ⟨70190494351050171909149207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46793662900700114606099471 70190494351050171909149207)
  ·
    refine ⟨105285741526575257863723811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70190494351050171909149207 105285741526575257863723811)
    ·
      refine ⟨157928612289862886795585717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105285741526575257863723811 157928612289862886795585717)
      ·
        refine ⟨14805807402174645637086161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157928612289862886795585717 14805807402174645637086161)
        ·
          refine ⟨11104355551630984227814621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14805807402174645637086161 11104355551630984227814621)
          ·
            refine ⟨4164133331861619085430483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11104355551630984227814621 4164133331861619085430483)
            ·
              refine ⟨6246199997792428628145725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164133331861619085430483 6246199997792428628145725)
              ·
                refine ⟨2342324999172160735554647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6246199997792428628145725 2342324999172160735554647)
                ·
                  refine ⟨3513487498758241103331971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342324999172160735554647 3513487498758241103331971)
                  ·
                    refine ⟨5270231248137361654997957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3513487498758241103331971 5270231248137361654997957)
                    ·
                      refine ⟨988168359025755310312117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5270231248137361654997957 988168359025755310312117)
                      ·
                        rfl

theorem cell23_1924451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1924451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924451 prefixEnd_1924451 := by exact prefixLift 1924451
  have htrace : WordTrace (prefixWord ++ tailWord_1924451) baseStart_1924451 baseEnd_1924451 := by
    simpa [prefixWord, tailWord_1924451, baseEnd_1924451] using wordTrace_append hprefix tailTrace_1924451
  have hstable : (prefixWord ++ tailWord_1924451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924451).length < 2 ^ (prefixWord ++ tailWord_1924451).sum := by decide
  have hdescent : baseEnd_1924451 < baseStart_1924451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924461 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1924461 : Nat := 118140960795 + 1924461 * 2 ^ 59
def prefixEnd_1924461 : Nat := 4983230072969 + 3 ^ 40 * 1924461 * 2
def baseEnd_1924461 : Nat := 329391164610766757062357

theorem tailTrace_1924461 : CollatzResearch.WordTrace tailWord_1924461 prefixEnd_1924461 329391164610766757062357 := by
  unfold tailWord_1924461
  simp only [CollatzResearch.WordTrace]
  refine ⟨70190859081013943617013237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46793906054009295744675491 70190859081013943617013237)
  ·
    refine ⟨6580393038845057214094991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70190859081013943617013237 6580393038845057214094991)
    ·
      refine ⟨9870589558267585821142487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580393038845057214094991 9870589558267585821142487)
      ·
        refine ⟨14805884337401378731713731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9870589558267585821142487 14805884337401378731713731)
        ·
          refine ⟨22208826506102068097570597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14805884337401378731713731 22208826506102068097570597)
          ·
            refine ⟨4164154969894137768294487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22208826506102068097570597 4164154969894137768294487)
            ·
              refine ⟨6246232454841206652441731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164154969894137768294487 6246232454841206652441731)
              ·
                refine ⟨9369348682261809978662597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246232454841206652441731 9369348682261809978662597)
                ·
                  refine ⟨1756752877924089370999237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9369348682261809978662597 1756752877924089370999237)
                  ·
                    refine ⟨329391164610766757062357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756752877924089370999237 329391164610766757062357)
                    ·
                      rfl

theorem cell23_1924461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1924461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924461 prefixEnd_1924461 := by exact prefixLift 1924461
  have htrace : WordTrace (prefixWord ++ tailWord_1924461) baseStart_1924461 baseEnd_1924461 := by
    simpa [prefixWord, tailWord_1924461, baseEnd_1924461] using wordTrace_append hprefix tailTrace_1924461
  have hstable : (prefixWord ++ tailWord_1924461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924461).length < 2 ^ (prefixWord ++ tailWord_1924461).sum := by decide
  have hdescent : baseEnd_1924461 < baseStart_1924461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924481 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1924481 : Nat := 118140960795 + 1924481 * 2 ^ 59
def prefixEnd_1924481 : Nat := 4983230072969 + 3 ^ 40 * 1924481 * 2
def baseEnd_1924481 : Nat := 988183763445390192936979

theorem tailTrace_1924481 : CollatzResearch.WordTrace tailWord_1924481 prefixEnd_1924481 988183763445390192936979 := by
  unfold tailWord_1924481
  simp only [CollatzResearch.WordTrace]
  refine ⟨70191588540941487032741297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46794392360627658021827531 70191588540941487032741297)
  ·
    refine ⟨52643691405706115274555973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70191588540941487032741297 52643691405706115274555973)
    ·
      refine ⟨9870692138569896613979245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52643691405706115274555973 9870692138569896613979245)
      ·
        refine ⟨3701509551963711230242217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9870692138569896613979245 3701509551963711230242217)
        ·
          refine ⟨2776132163972783422681663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701509551963711230242217 2776132163972783422681663)
          ·
            refine ⟨4164198245959175134022495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776132163972783422681663 4164198245959175134022495)
            ·
              refine ⟨6246297368938762701033743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164198245959175134022495 6246297368938762701033743)
              ·
                refine ⟨9369446053408144051550615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246297368938762701033743 9369446053408144051550615)
                ·
                  refine ⟨14054169080112216077325923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9369446053408144051550615 14054169080112216077325923)
                  ·
                    refine ⟨21081253620168324115988885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14054169080112216077325923 21081253620168324115988885)
                    ·
                      refine ⟨988183763445390192936979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21081253620168324115988885 988183763445390192936979)
                      ·
                        rfl

theorem cell23_1924481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1924481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924481 prefixEnd_1924481 := by exact prefixLift 1924481
  have htrace : WordTrace (prefixWord ++ tailWord_1924481) baseStart_1924481 baseEnd_1924481 := by
    simpa [prefixWord, tailWord_1924481, baseEnd_1924481] using wordTrace_append hprefix tailTrace_1924481
  have hstable : (prefixWord ++ tailWord_1924481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924481).length < 2 ^ (prefixWord ++ tailWord_1924481).sum := by decide
  have hdescent : baseEnd_1924481 < baseStart_1924481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924488 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1924488 : Nat := 118140960795 + 1924488 * 2 ^ 59
def prefixEnd_1924488 : Nat := 4983230072969 + 3 ^ 40 * 1924488 * 2
def baseEnd_1924488 : Nat := 988187357809971665549447

theorem tailTrace_1924488 : CollatzResearch.WordTrace tailWord_1924488 prefixEnd_1924488 988187357809971665549447 := by
  unfold tailWord_1924488
  simp only [CollatzResearch.WordTrace]
  refine ⟨35095921925958063614123059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46794562567944084818830745 35095921925958063614123059)
  ·
    refine ⟨52643882888937095421184589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35095921925958063614123059 52643882888937095421184589)
    ·
      refine ⟨19741456083351410782944221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52643882888937095421184589 19741456083351410782944221)
      ·
        refine ⟨7403046031256779043604083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19741456083351410782944221 7403046031256779043604083)
        ·
          refine ⟨11104569046885168565406125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403046031256779043604083 11104569046885168565406125)
          ·
            refine ⟨4164213392581938212027297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11104569046885168565406125 4164213392581938212027297)
            ·
              refine ⟨3123160044436453659020473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164213392581938212027297 3123160044436453659020473)
              ·
                refine ⟨2342370033327340244265355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123160044436453659020473 2342370033327340244265355)
                ·
                  refine ⟨3513555049991010366398033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342370033327340244265355 3513555049991010366398033)
                  ·
                    refine ⟨2635166287493257774798525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3513555049991010366398033 2635166287493257774798525)
                    ·
                      refine ⟨988187357809971665549447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2635166287493257774798525 988187357809971665549447)
                      ·
                        rfl

theorem cell23_1924488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1924488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924488 prefixEnd_1924488 := by exact prefixLift 1924488
  have htrace : WordTrace (prefixWord ++ tailWord_1924488) baseStart_1924488 baseEnd_1924488 := by
    simpa [prefixWord, tailWord_1924488, baseEnd_1924488] using wordTrace_append hprefix tailTrace_1924488
  have hstable : (prefixWord ++ tailWord_1924488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924488).length < 2 ^ (prefixWord ++ tailWord_1924488).sum := by decide
  have hdescent : baseEnd_1924488 < baseStart_1924488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924501 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_1924501 : Nat := 118140960795 + 1924501 * 2 ^ 59
def prefixEnd_1924501 : Nat := 4983230072969 + 3 ^ 40 * 1924501 * 2
def baseEnd_1924501 : Nat := 988194033058480114686887

theorem tailTrace_1924501 : CollatzResearch.WordTrace tailWord_1924501 prefixEnd_1924501 988194033058480114686887 := by
  unfold tailWord_1924501
  simp only [CollatzResearch.WordTrace]
  refine ⟨70192318000869030448469357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46794878667246020298979571 70192318000869030448469357)
  ·
    refine ⟨26322119250325886418176009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70192318000869030448469357 26322119250325886418176009)
    ·
      refine ⟨19741589437744414813632007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26322119250325886418176009 19741589437744414813632007)
      ·
        refine ⟨29612384156616622220448011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19741589437744414813632007 29612384156616622220448011)
        ·
          refine ⟨44418576234924933330672017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29612384156616622220448011 44418576234924933330672017)
          ·
            refine ⟨33313932176193699998004013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44418576234924933330672017 33313932176193699998004013)
            ·
              refine ⟨12492724566072637499251505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33313932176193699998004013 12492724566072637499251505)
              ·
                refine ⟨9369543424554478124438629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12492724566072637499251505 9369543424554478124438629)
                ·
                  refine ⟨1756789392103964648332243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9369543424554478124438629 1756789392103964648332243)
                  ·
                    refine ⟨2635184088155946972498365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1756789392103964648332243 2635184088155946972498365)
                    ·
                      refine ⟨988194033058480114686887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2635184088155946972498365 988194033058480114686887)
                      ·
                        rfl

theorem cell23_1924501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_1924501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924501 prefixEnd_1924501 := by exact prefixLift 1924501
  have htrace : WordTrace (prefixWord ++ tailWord_1924501) baseStart_1924501 baseEnd_1924501 := by
    simpa [prefixWord, tailWord_1924501, baseEnd_1924501] using wordTrace_append hprefix tailTrace_1924501
  have hstable : (prefixWord ++ tailWord_1924501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924501).length < 2 ^ (prefixWord ++ tailWord_1924501).sum := by decide
  have hdescent : baseEnd_1924501 < baseStart_1924501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924508 : List Nat := [2, 2, 3, 4, 2, 1, 9]
def baseStart_1924508 : Nat := 118140960795 + 1924508 * 2 ^ 59
def prefixEnd_1924508 : Nat := 4983230072969 + 3 ^ 40 * 1924508 * 2
def baseEnd_1924508 : Nat := 12199970708926686262955

theorem tailTrace_1924508 : CollatzResearch.WordTrace tailWord_1924508 prefixEnd_1924508 12199970708926686262955 := by
  unfold tailWord_1924508
  simp only [CollatzResearch.WordTrace]
  refine ⟨35096286655921835321987089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46795048874562447095982785 35096286655921835321987089)
  ·
    refine ⟨26322214991941376491490317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35096286655921835321987089 26322214991941376491490317)
    ·
      refine ⟨9870830621978016184308869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26322214991941376491490317 9870830621978016184308869)
      ·
        refine ⟨1850780741620878034557913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9870830621978016184308869 1850780741620878034557913)
        ·
          refine ⟨1388085556215658525918435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850780741620878034557913 1388085556215658525918435)
          ·
            refine ⟨2082128334323487788877653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388085556215658525918435 2082128334323487788877653)
            ·
              refine ⟨12199970708926686262955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2082128334323487788877653 12199970708926686262955)
              ·
                rfl

theorem cell23_1924508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 9].length) (baseStart_1924508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924508 prefixEnd_1924508 := by exact prefixLift 1924508
  have htrace : WordTrace (prefixWord ++ tailWord_1924508) baseStart_1924508 baseEnd_1924508 := by
    simpa [prefixWord, tailWord_1924508, baseEnd_1924508] using wordTrace_append hprefix tailTrace_1924508
  have hstable : (prefixWord ++ tailWord_1924508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924508).length < 2 ^ (prefixWord ++ tailWord_1924508).sum := by decide
  have hdescent : baseEnd_1924508 < baseStart_1924508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924544 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1924544 : Nat := 118140960795 + 1924544 * 2 ^ 59
def prefixEnd_1924544 : Nat := 4983230072969 + 3 ^ 40 * 1924544 * 2
def baseEnd_1924544 : Nat := 988216112726623446449189

theorem tailTrace_1924544 : CollatzResearch.WordTrace tailWord_1924544 prefixEnd_1924544 988216112726623446449189 := by
  unfold tailWord_1924544
  simp only [CollatzResearch.WordTrace]
  refine ⟨35096943169856624396142343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46795924226475499194856457 35096943169856624396142343)
  ·
    refine ⟨52645414754784936594213515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35096943169856624396142343 52645414754784936594213515)
    ·
      refine ⟨78968122132177404891320273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52645414754784936594213515 78968122132177404891320273)
      ·
        refine ⟨59226091599133053668490205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78968122132177404891320273 59226091599133053668490205)
        ·
          refine ⟨22209784349674895125683827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59226091599133053668490205 22209784349674895125683827)
          ·
            refine ⟨33314676524512342688525741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22209784349674895125683827 33314676524512342688525741)
            ·
              refine ⟨12493003696692128508197153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33314676524512342688525741 12493003696692128508197153)
              ·
                refine ⟨9369752772519096381147865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12493003696692128508197153 9369752772519096381147865)
                ·
                  refine ⟨7027314579389322285860899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9369752772519096381147865 7027314579389322285860899)
                  ·
                    refine ⟨10540971869083983428791349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7027314579389322285860899 10540971869083983428791349)
                    ·
                      refine ⟨988216112726623446449189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10540971869083983428791349 988216112726623446449189)
                      ·
                        rfl

theorem cell23_1924544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1924544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924544 prefixEnd_1924544 := by exact prefixLift 1924544
  have htrace : WordTrace (prefixWord ++ tailWord_1924544) baseStart_1924544 baseEnd_1924544 := by
    simpa [prefixWord, tailWord_1924544, baseEnd_1924544] using wordTrace_append hprefix tailTrace_1924544
  have hstable : (prefixWord ++ tailWord_1924544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924544).length < 2 ^ (prefixWord ++ tailWord_1924544).sum := by decide
  have hdescent : baseEnd_1924544 < baseStart_1924544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924558 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_1924558 : Nat := 118140960795 + 1924558 * 2 ^ 59
def prefixEnd_1924558 : Nat := 4983230072969 + 3 ^ 40 * 1924558 * 2
def baseEnd_1924558 : Nat := 988223301455786391674125

theorem tailTrace_1924558 : CollatzResearch.WordTrace tailWord_1924558 prefixEnd_1924558 988223301455786391674125 := by
  unfold tailWord_1924558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774299620207816147911791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46796264641108352788862885 8774299620207816147911791)
  ·
    refine ⟨13161449430311724221867687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8774299620207816147911791 13161449430311724221867687)
    ·
      refine ⟨19742174145467586332801531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13161449430311724221867687 19742174145467586332801531)
      ·
        refine ⟨29613261218201379499202297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742174145467586332801531 29613261218201379499202297)
        ·
          refine ⟨22209945913651034624401723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29613261218201379499202297 22209945913651034624401723)
          ·
            refine ⟨33314918870476551936602585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22209945913651034624401723 33314918870476551936602585)
            ·
              refine ⟨24986189152857413952451939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33314918870476551936602585 24986189152857413952451939)
              ·
                refine ⟨37479283729286120928677909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24986189152857413952451939 37479283729286120928677909)
                ·
                  refine ⟨1756841424810286918531777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37479283729286120928677909 1756841424810286918531777)
                  ·
                    refine ⟨1317631068607715188898833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1756841424810286918531777 1317631068607715188898833)
                    ·
                      refine ⟨988223301455786391674125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317631068607715188898833 988223301455786391674125)
                      ·
                        rfl

theorem cell23_1924558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_1924558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924558 prefixEnd_1924558 := by exact prefixLift 1924558
  have htrace : WordTrace (prefixWord ++ tailWord_1924558) baseStart_1924558 baseEnd_1924558 := by
    simpa [prefixWord, tailWord_1924558, baseEnd_1924558] using wordTrace_append hprefix tailTrace_1924558
  have hstable : (prefixWord ++ tailWord_1924558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924558).length < 2 ^ (prefixWord ++ tailWord_1924558).sum := by decide
  have hdescent : baseEnd_1924558 < baseStart_1924558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924575 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 2, 2, 2]
def baseStart_1924575 : Nat := 118140960795 + 1924575 * 2 ^ 59
def prefixEnd_1924575 : Nat := 4983230072969 + 3 ^ 40 * 1924575 * 2
def baseEnd_1924575 : Nat := 988232030626912825161547

theorem tailTrace_1924575 : CollatzResearch.WordTrace tailWord_1924575 prefixEnd_1924575 988232030626912825161547 := by
  unfold tailWord_1924575
  simp only [CollatzResearch.WordTrace]
  refine ⟨70195017002600941086663179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46796678001733960724442119 70195017002600941086663179)
  ·
    refine ⟨105292525503901411629994769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70195017002600941086663179 105292525503901411629994769)
    ·
      refine ⟨78969394127926058722496077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105292525503901411629994769 78969394127926058722496077)
      ·
        refine ⟨29613522797972272020936029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78969394127926058722496077 29613522797972272020936029)
        ·
          refine ⟨11105071049239602007851011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29613522797972272020936029 11105071049239602007851011)
          ·
            refine ⟨16657606573859403011776517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11105071049239602007851011 16657606573859403011776517)
            ·
              refine ⟨3123301232598638064708097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16657606573859403011776517 3123301232598638064708097)
              ·
                refine ⟨2342475924448978548531073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123301232598638064708097 2342475924448978548531073)
                ·
                  refine ⟨1756856943336733911398305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2342475924448978548531073 1756856943336733911398305)
                  ·
                    refine ⟨1317642707502550433548729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1756856943336733911398305 1317642707502550433548729)
                    ·
                      refine ⟨988232030626912825161547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317642707502550433548729 988232030626912825161547)
                      ·
                        rfl

theorem cell23_1924575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_1924575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924575 prefixEnd_1924575 := by exact prefixLift 1924575
  have htrace : WordTrace (prefixWord ++ tailWord_1924575) baseStart_1924575 baseEnd_1924575 := by
    simpa [prefixWord, tailWord_1924575, baseEnd_1924575] using wordTrace_append hprefix tailTrace_1924575
  have hstable : (prefixWord ++ tailWord_1924575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924575).length < 2 ^ (prefixWord ++ tailWord_1924575).sum := by decide
  have hdescent : baseEnd_1924575 < baseStart_1924575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924601 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 4, 5, 2]
def baseStart_1924601 : Nat := 118140960795 + 1924601 * 2 ^ 59
def prefixEnd_1924601 : Nat := 4983230072969 + 3 ^ 40 * 1924601 * 2
def baseEnd_1924601 : Nat := 988245381123929723436427

theorem tailTrace_1924601 : CollatzResearch.WordTrace tailWord_1924601 prefixEnd_1924601 988245381123929723436427 := by
  unfold tailWord_1924601
  simp only [CollatzResearch.WordTrace]
  refine ⟨70195965300506747527109657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46797310200337831684739771 70195965300506747527109657)
  ·
    refine ⟨52646973975380060645332243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70195965300506747527109657 52646973975380060645332243)
    ·
      refine ⟨78970460963070090967998365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52646973975380060645332243 78970460963070090967998365)
      ·
        refine ⟨29613922861151284112999387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78970460963070090967998365 29613922861151284112999387)
        ·
          refine ⟨44420884291726926169499081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29613922861151284112999387 44420884291726926169499081)
          ·
            refine ⟨33315663218795194627124311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44420884291726926169499081 33315663218795194627124311)
            ·
              refine ⟨49973494828192791940686467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33315663218795194627124311 49973494828192791940686467)
              ·
                refine ⟨74960242242289187911029701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49973494828192791940686467 74960242242289187911029701)
                ·
                  refine ⟨14055045420429222733318069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74960242242289187911029701 14055045420429222733318069)
                  ·
                    refine ⟨1317660508165239631248569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14055045420429222733318069 1317660508165239631248569)
                    ·
                      refine ⟨988245381123929723436427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317660508165239631248569 988245381123929723436427)
                      ·
                        rfl

theorem cell23_1924601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_1924601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924601 prefixEnd_1924601 := by exact prefixLift 1924601
  have htrace : WordTrace (prefixWord ++ tailWord_1924601) baseStart_1924601 baseEnd_1924601 := by
    simpa [prefixWord, tailWord_1924601, baseEnd_1924601] using wordTrace_append hprefix tailTrace_1924601
  have hstable : (prefixWord ++ tailWord_1924601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924601).length < 2 ^ (prefixWord ++ tailWord_1924601).sum := by decide
  have hdescent : baseEnd_1924601 < baseStart_1924601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924604 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1924604 : Nat := 118140960795 + 1924604 * 2 ^ 59
def prefixEnd_1924604 : Nat := 4983230072969 + 3 ^ 40 * 1924604 * 2
def baseEnd_1924604 : Nat := 988246921565893211698913

theorem tailTrace_1924604 : CollatzResearch.WordTrace tailWord_1924604 prefixEnd_1924604 988246921565893211698913 := by
  unfold tailWord_1924604
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098037359747939519734433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46797383146330586026312577 35098037359747939519734433)
  ·
    refine ⟨26323528019810954639800825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35098037359747939519734433 26323528019810954639800825)
    ·
      refine ⟨19742646014858215979850619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26323528019810954639800825 19742646014858215979850619)
      ·
        refine ⟨29613969022287323969775929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742646014858215979850619 29613969022287323969775929)
        ·
          refine ⟨22210476766715492977331947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29613969022287323969775929 22210476766715492977331947)
          ·
            refine ⟨33315715150073239465997921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22210476766715492977331947 33315715150073239465997921)
            ·
              refine ⟨24986786362554929599498441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33315715150073239465997921 24986786362554929599498441)
              ·
                refine ⟨18740089771916197199623831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24986786362554929599498441 18740089771916197199623831)
                ·
                  refine ⟨28110134657874295799435747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18740089771916197199623831 28110134657874295799435747)
                  ·
                    refine ⟨42165201986811443699153621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28110134657874295799435747 42165201986811443699153621)
                    ·
                      refine ⟨988246921565893211698913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42165201986811443699153621 988246921565893211698913)
                      ·
                        rfl

theorem cell23_1924604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1924604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924604 prefixEnd_1924604 := by exact prefixLift 1924604
  have htrace : WordTrace (prefixWord ++ tailWord_1924604) baseStart_1924604 baseEnd_1924604 := by
    simpa [prefixWord, tailWord_1924604, baseEnd_1924604] using wordTrace_append hprefix tailTrace_1924604
  have hstable : (prefixWord ++ tailWord_1924604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924604).length < 2 ^ (prefixWord ++ tailWord_1924604).sum := by decide
  have hdescent : baseEnd_1924604 < baseStart_1924604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924692 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1924692 : Nat := 118140960795 + 1924692 * 2 ^ 59
def prefixEnd_1924692 : Nat := 4983230072969 + 3 ^ 40 * 1924692 * 2
def baseEnd_1924692 : Nat := 329430702621162955799503

theorem tailTrace_1924692 : CollatzResearch.WordTrace tailWord_1924692 prefixEnd_1924692 329430702621162955799503 := by
  unfold tailWord_1924692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35099642171588535034336165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46799522895451380045781553 35099642171588535034336165)
  ·
    refine ⟨6581182907172850318938031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35099642171588535034336165 6581182907172850318938031)
    ·
      refine ⟨9871774360759275478407047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6581182907172850318938031 9871774360759275478407047)
      ·
        refine ⟨14807661541138913217610571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871774360759275478407047 14807661541138913217610571)
        ·
          refine ⟨22211492311708369826415857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807661541138913217610571 22211492311708369826415857)
          ·
            refine ⟨16658619233781277369811893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22211492311708369826415857 16658619233781277369811893)
            ·
              refine ⟨1561745553166994753419865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16658619233781277369811893 1561745553166994753419865)
              ·
                refine ⟨1171309164875246065064899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561745553166994753419865 1171309164875246065064899)
                ·
                  refine ⟨1756963747312869097597349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171309164875246065064899 1756963747312869097597349)
                  ·
                    refine ⟨329430702621162955799503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756963747312869097597349 329430702621162955799503)
                    ·
                      rfl

theorem cell23_1924692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1924692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924692 prefixEnd_1924692 := by exact prefixLift 1924692
  have htrace : WordTrace (prefixWord ++ tailWord_1924692) baseStart_1924692 baseEnd_1924692 := by
    simpa [prefixWord, tailWord_1924692, baseEnd_1924692] using wordTrace_append hprefix tailTrace_1924692
  have hstable : (prefixWord ++ tailWord_1924692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924692).length < 2 ^ (prefixWord ++ tailWord_1924692).sum := by decide
  have hdescent : baseEnd_1924692 < baseStart_1924692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924731 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 1, 6]
def baseStart_1924731 : Nat := 118140960795 + 1924731 * 2 ^ 59
def prefixEnd_1924731 : Nat := 4983230072969 + 3 ^ 40 * 1924731 * 2
def baseEnd_1924731 : Nat := 329437377869671404936943

theorem tailTrace_1924731 : CollatzResearch.WordTrace tailWord_1924731 prefixEnd_1924731 329437377869671404936943 := by
  unfold tailWord_1924731
  simp only [CollatzResearch.WordTrace]
  refine ⟨70200706790035779729342047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46800471193357186486228031 70200706790035779729342047)
  ·
    refine ⟨105301060185053669594013071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70200706790035779729342047 105301060185053669594013071)
    ·
      refine ⟨157951590277580504391019607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105301060185053669594013071 157951590277580504391019607)
      ·
        refine ⟨236927385416370756586529411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157951590277580504391019607 236927385416370756586529411)
        ·
          refine ⟨355391078124556134879794117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236927385416370756586529411 355391078124556134879794117)
          ·
            refine ⟨66635827148354275289961397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355391078124556134879794117 66635827148354275289961397)
            ·
              refine ⟨6247108795158213308433881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66635827148354275289961397 6247108795158213308433881)
              ·
                refine ⟨4685331596368659981325411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6247108795158213308433881 4685331596368659981325411)
                ·
                  refine ⟨7027997394552989971988117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685331596368659981325411 7027997394552989971988117)
                  ·
                    refine ⟨329437377869671404936943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7027997394552989971988117 329437377869671404936943)
                    ·
                      rfl

theorem cell23_1924731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 6].length) (baseStart_1924731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924731 prefixEnd_1924731 := by exact prefixLift 1924731
  have htrace : WordTrace (prefixWord ++ tailWord_1924731) baseStart_1924731 baseEnd_1924731 := by
    simpa [prefixWord, tailWord_1924731, baseEnd_1924731] using wordTrace_append hprefix tailTrace_1924731
  have hstable : (prefixWord ++ tailWord_1924731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924731).length < 2 ^ (prefixWord ++ tailWord_1924731).sum := by decide
  have hdescent : baseEnd_1924731 < baseStart_1924731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924768 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1924768 : Nat := 118140960795 + 1924768 * 2 ^ 59
def prefixEnd_1924768 : Nat := 4983230072969 + 3 ^ 40 * 1924768 * 2
def baseEnd_1924768 : Nat := 988331132393230570048159

theorem tailTrace_1924768 : CollatzResearch.WordTrace tailWord_1924768 prefixEnd_1924768 988331132393230570048159 := by
  unfold tailWord_1924768
  simp only [CollatzResearch.WordTrace]
  refine ⟨35101028145450867524219479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46801370860601156698959305 35101028145450867524219479)
  ·
    refine ⟨52651542218176301286329219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35101028145450867524219479 52651542218176301286329219)
    ·
      refine ⟨78977313327264451929493829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52651542218176301286329219 78977313327264451929493829)
      ·
        refine ⟨14808246248862084736780093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78977313327264451929493829 14808246248862084736780093)
        ·
          refine ⟨5553092343323281776292535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14808246248862084736780093 5553092343323281776292535)
          ·
            refine ⟨8329638514984922664438803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553092343323281776292535 8329638514984922664438803)
            ·
              refine ⟨12494457772477383996658205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329638514984922664438803 12494457772477383996658205)
              ·
                refine ⟨4685421664679018998746827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12494457772477383996658205 4685421664679018998746827)
                ·
                  refine ⟨7028132497018528498120241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685421664679018998746827 7028132497018528498120241)
                  ·
                    refine ⟨5271099372763896373590181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7028132497018528498120241 5271099372763896373590181)
                    ·
                      refine ⟨988331132393230570048159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5271099372763896373590181 988331132393230570048159)
                      ·
                        rfl

theorem cell23_1924768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1924768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924768 prefixEnd_1924768 := by exact prefixLift 1924768
  have htrace : WordTrace (prefixWord ++ tailWord_1924768) baseStart_1924768 baseEnd_1924768 := by
    simpa [prefixWord, tailWord_1924768, baseEnd_1924768] using wordTrace_append hprefix tailTrace_1924768
  have hstable : (prefixWord ++ tailWord_1924768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924768).length < 2 ^ (prefixWord ++ tailWord_1924768).sum := by decide
  have hdescent : baseEnd_1924768 < baseStart_1924768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924772 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_1924772 : Nat := 118140960795 + 1924772 * 2 ^ 59
def prefixEnd_1924772 : Nat := 4983230072969 + 3 ^ 40 * 1924772 * 2
def baseEnd_1924772 : Nat := 988333186315848554398141

theorem tailTrace_1924772 : CollatzResearch.WordTrace tailWord_1924772 prefixEnd_1924772 988333186315848554398141 := by
  unfold tailWord_1924772
  simp only [CollatzResearch.WordTrace]
  refine ⟨35101101091443621865792285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46801468121924829154389713 35101101091443621865792285)
  ·
    refine ⟨13162912909291358199672107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35101101091443621865792285 13162912909291358199672107)
    ·
      refine ⟨19744369363937037299508161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13162912909291358199672107 19744369363937037299508161)
      ·
        refine ⟨14808277022952777974631121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19744369363937037299508161 14808277022952777974631121)
        ·
          refine ⟨11106207767214583480973341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14808277022952777974631121 11106207767214583480973341)
          ·
            refine ⟨4164827912705468805365003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11106207767214583480973341 4164827912705468805365003)
            ·
              refine ⟨6247241869058203208047505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164827912705468805365003 6247241869058203208047505)
              ·
                refine ⟨4685431401793652406035629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6247241869058203208047505 4685431401793652406035629)
                ·
                  refine ⟨1757036775672619652263361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4685431401793652406035629 1757036775672619652263361)
                  ·
                    refine ⟨1317777581754464739197521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1757036775672619652263361 1317777581754464739197521)
                    ·
                      refine ⟨988333186315848554398141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317777581754464739197521 988333186315848554398141)
                      ·
                        rfl

theorem cell23_1924772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_1924772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924772 prefixEnd_1924772 := by exact prefixLift 1924772
  have htrace : WordTrace (prefixWord ++ tailWord_1924772) baseStart_1924772 baseEnd_1924772 := by
    simpa [prefixWord, tailWord_1924772, baseEnd_1924772] using wordTrace_append hprefix tailTrace_1924772
  have hstable : (prefixWord ++ tailWord_1924772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924772).length < 2 ^ (prefixWord ++ tailWord_1924772).sum := by decide
  have hdescent : baseEnd_1924772 < baseStart_1924772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924789 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1924789 : Nat := 118140960795 + 1924789 * 2 ^ 59
def prefixEnd_1924789 : Nat := 4983230072969 + 3 ^ 40 * 1924789 * 2
def baseEnd_1924789 : Nat := 988341915486974987885563

theorem tailTrace_1924789 : CollatzResearch.WordTrace tailWord_1924789 prefixEnd_1924789 988341915486974987885563 := by
  unfold tailWord_1924789
  simp only [CollatzResearch.WordTrace]
  refine ⟨70202822223825655634953421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46801881482550437089968947 70202822223825655634953421)
  ·
    refine ⟨26326058333934620863107533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70202822223825655634953421 26326058333934620863107533)
    ·
      refine ⟨9872271875225482823665325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26326058333934620863107533 9872271875225482823665325)
      ·
        refine ⟨3702101953209556058874497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9872271875225482823665325 3702101953209556058874497)
        ·
          refine ⟨2776576464907167044155873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702101953209556058874497 2776576464907167044155873)
          ·
            refine ⟨2082432348680375283116905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776576464907167044155873 2082432348680375283116905)
            ·
              refine ⟨1561824261510281462337679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082432348680375283116905 1561824261510281462337679)
              ·
                refine ⟨2342736392265422193506519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561824261510281462337679 2342736392265422193506519)
                ·
                  refine ⟨3514104588398133290259779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342736392265422193506519 3514104588398133290259779)
                  ·
                    refine ⟨5271156882597199935389669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514104588398133290259779 5271156882597199935389669)
                    ·
                      refine ⟨988341915486974987885563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5271156882597199935389669 988341915486974987885563)
                      ·
                        rfl

theorem cell23_1924789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1924789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924789 prefixEnd_1924789 := by exact prefixLift 1924789
  have htrace : WordTrace (prefixWord ++ tailWord_1924789) baseStart_1924789 baseEnd_1924789 := by
    simpa [prefixWord, tailWord_1924789, baseEnd_1924789] using wordTrace_append hprefix tailTrace_1924789
  have hstable : (prefixWord ++ tailWord_1924789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924789).length < 2 ^ (prefixWord ++ tailWord_1924789).sum := by decide
  have hdescent : baseEnd_1924789 < baseStart_1924789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924806 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1924806 : Nat := 118140960795 + 1924806 * 2 ^ 59
def prefixEnd_1924806 : Nat := 4983230072969 + 3 ^ 40 * 1924806 * 2
def baseEnd_1924806 : Nat := 988350644658101421372985

theorem tailTrace_1924806 : CollatzResearch.WordTrace tailWord_1924806 prefixEnd_1924806 988350644658101421372985 := by
  unfold tailWord_1924806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193857570773877110572571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46802294843176045025548181 2193857570773877110572571)
  ·
    refine ⟨3290786356160815665858857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193857570773877110572571 3290786356160815665858857)
    ·
      refine ⟨2468089767120611749394143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3290786356160815665858857 2468089767120611749394143)
      ·
        refine ⟨3702134650680917624091215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468089767120611749394143 3702134650680917624091215)
        ·
          refine ⟨5553201976021376436136823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702134650680917624091215 5553201976021376436136823)
          ·
            refine ⟨8329802964032064654205235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553201976021376436136823 8329802964032064654205235)
            ·
              refine ⟨12494704446048096981307853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329802964032064654205235 12494704446048096981307853)
              ·
                refine ⟨4685514167268036367990445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12494704446048096981307853 4685514167268036367990445)
                ·
                  refine ⟨1757067812725513637996417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4685514167268036367990445 1757067812725513637996417)
                  ·
                    refine ⟨1317800859544135228497313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1757067812725513637996417 1317800859544135228497313)
                    ·
                      refine ⟨988350644658101421372985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317800859544135228497313 988350644658101421372985)
                      ·
                        rfl

theorem cell23_1924806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1924806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924806 prefixEnd_1924806 := by exact prefixLift 1924806
  have htrace : WordTrace (prefixWord ++ tailWord_1924806) baseStart_1924806 baseEnd_1924806 := by
    simpa [prefixWord, tailWord_1924806, baseEnd_1924806] using wordTrace_append hprefix tailTrace_1924806
  have hstable : (prefixWord ++ tailWord_1924806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924806).length < 2 ^ (prefixWord ++ tailWord_1924806).sum := by decide
  have hdescent : baseEnd_1924806 < baseStart_1924806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924811 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4]
def baseStart_1924811 : Nat := 118140960795 + 1924811 * 2 ^ 59
def prefixEnd_1924811 : Nat := 4983230072969 + 3 ^ 40 * 1924811 * 2
def baseEnd_1924811 : Nat := 988353212061373901810461

theorem tailTrace_1924811 : CollatzResearch.WordTrace tailWord_1924811 prefixEnd_1924811 988353212061373901810461 := by
  unfold tailWord_1924811
  simp only [CollatzResearch.WordTrace]
  refine ⟨70203624629745953392254287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46802416419830635594836191 70203624629745953392254287)
  ·
    refine ⟨105305436944618930088381431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70203624629745953392254287 105305436944618930088381431)
    ·
      refine ⟨157958155416928395132572147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105305436944618930088381431 157958155416928395132572147)
      ·
        refine ⟨236937233125392592698858221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157958155416928395132572147 236937233125392592698858221)
        ·
          refine ⟨88851462422022222262071833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236937233125392592698858221 88851462422022222262071833)
          ·
            refine ⟨66638596816516666696553875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88851462422022222262071833 66638596816516666696553875)
            ·
              refine ⟨99957895224775000044830813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66638596816516666696553875 99957895224775000044830813)
              ·
                refine ⟨37484210709290625016811555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99957895224775000044830813 37484210709290625016811555)
                ·
                  refine ⟨56226316063935937525217333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37484210709290625016811555 56226316063935937525217333)
                  ·
                    refine ⟨5271217130993994142989125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56226316063935937525217333 5271217130993994142989125)
                    ·
                      refine ⟨988353212061373901810461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5271217130993994142989125 988353212061373901810461)
                      ·
                        rfl

theorem cell23_1924811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_1924811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924811 prefixEnd_1924811 := by exact prefixLift 1924811
  have htrace : WordTrace (prefixWord ++ tailWord_1924811) baseStart_1924811 baseEnd_1924811 := by
    simpa [prefixWord, tailWord_1924811, baseEnd_1924811] using wordTrace_append hprefix tailTrace_1924811
  have hstable : (prefixWord ++ tailWord_1924811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924811).length < 2 ^ (prefixWord ++ tailWord_1924811).sum := by decide
  have hdescent : baseEnd_1924811 < baseStart_1924811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924829 : List Nat := [1, 4, 3, 3, 2, 1, 2, 7]
def baseStart_1924829 : Nat := 118140960795 + 1924829 * 2 ^ 59
def prefixEnd_1924829 : Nat := 4983230072969 + 3 ^ 40 * 1924829 * 2
def baseEnd_1924829 : Nat := 36606016841227956717977

theorem tailTrace_1924829 : CollatzResearch.WordTrace tailWord_1924829 prefixEnd_1924829 36606016841227956717977 := by
  unfold tailWord_1924829
  simp only [CollatzResearch.WordTrace]
  refine ⟨70204281143680742466409541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46802854095787161644273027 70204281143680742466409541)
  ·
    refine ⟨13163302714440139212451789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70204281143680742466409541 13163302714440139212451789)
    ·
      refine ⟨4936238517915052204669421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13163302714440139212451789 4936238517915052204669421)
      ·
        refine ⟨1851089444218144576751033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4936238517915052204669421 1851089444218144576751033)
        ·
          refine ⟨1388317083163608432563275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851089444218144576751033 1388317083163608432563275)
          ·
            refine ⟨2082475624745412648844913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388317083163608432563275 2082475624745412648844913)
            ·
              refine ⟨1561856718559059486633685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082475624745412648844913 1561856718559059486633685)
              ·
                refine ⟨36606016841227956717977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1561856718559059486633685 36606016841227956717977)
                ·
                  rfl

theorem cell23_1924829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 7].length) (baseStart_1924829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924829 prefixEnd_1924829 := by exact prefixLift 1924829
  have htrace : WordTrace (prefixWord ++ tailWord_1924829) baseStart_1924829 baseEnd_1924829 := by
    simpa [prefixWord, tailWord_1924829, baseEnd_1924829] using wordTrace_append hprefix tailTrace_1924829
  have hstable : (prefixWord ++ tailWord_1924829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924829).length < 2 ^ (prefixWord ++ tailWord_1924829).sum := by decide
  have hdescent : baseEnd_1924829 < baseStart_1924829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924851 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 9]
def baseStart_1924851 : Nat := 118140960795 + 1924851 * 2 ^ 59
def prefixEnd_1924851 : Nat := 4983230072969 + 3 ^ 40 * 1924851 * 2
def baseEnd_1924851 : Nat := 109819305698617082812253

theorem tailTrace_1924851 : CollatzResearch.WordTrace tailWord_1924851 prefixEnd_1924851 109819305698617082812253 := by
  unfold tailWord_1924851
  simp only [CollatzResearch.WordTrace]
  refine ⟨70205083549601040223710407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46803389033067360149140271 70205083549601040223710407)
  ·
    refine ⟨105307625324401560335565611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70205083549601040223710407 105307625324401560335565611)
    ·
      refine ⟨157961437986602340503348417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105307625324401560335565611 157961437986602340503348417)
      ·
        refine ⟨118471078489951755377511313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157961437986602340503348417 118471078489951755377511313)
        ·
          refine ⟨88853308867463816533133485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118471078489951755377511313 88853308867463816533133485)
          ·
            refine ⟨33319990825298931199925057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88853308867463816533133485 33319990825298931199925057)
            ·
              refine ⟨24989993118974198399943793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33319990825298931199925057 24989993118974198399943793)
              ·
                refine ⟨18742494839230648799957845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24989993118974198399943793 18742494839230648799957845)
                ·
                  refine ⟨109819305698617082812253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18742494839230648799957845 109819305698617082812253)
                  ·
                    rfl

theorem cell23_1924851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 9].length) (baseStart_1924851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924851 prefixEnd_1924851 := by exact prefixLift 1924851
  have htrace : WordTrace (prefixWord ++ tailWord_1924851) baseStart_1924851 baseEnd_1924851 := by
    simpa [prefixWord, tailWord_1924851, baseEnd_1924851] using wordTrace_append hprefix tailTrace_1924851
  have hstable : (prefixWord ++ tailWord_1924851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924851).length < 2 ^ (prefixWord ++ tailWord_1924851).sum := by decide
  have hdescent : baseEnd_1924851 < baseStart_1924851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924908 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1924908 : Nat := 118140960795 + 1924908 * 2 ^ 59
def prefixEnd_1924908 : Nat := 4983230072969 + 3 ^ 40 * 1924908 * 2
def baseEnd_1924908 : Nat := 988403019684860022297515

theorem tailTrace_1924908 : CollatzResearch.WordTrace tailWord_1924908 prefixEnd_1924908 988403019684860022297515 := by
  unfold tailWord_1924908
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103581255197269479267689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46804775006929692639023585 35103581255197269479267689)
  ·
    refine ⟨26327685941397952109450767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35103581255197269479267689 26327685941397952109450767)
    ·
      refine ⟨39491528912096928164176151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26327685941397952109450767 39491528912096928164176151)
      ·
        refine ⟨59237293368145392246264227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39491528912096928164176151 59237293368145392246264227)
        ·
          refine ⟨88855940052218088369396341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59237293368145392246264227 88855940052218088369396341)
          ·
            refine ⟨8330244379895445784630907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88855940052218088369396341 8330244379895445784630907)
            ·
              refine ⟨12495366569843168676946361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8330244379895445784630907 12495366569843168676946361)
              ·
                refine ⟨9371524927382376507709771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12495366569843168676946361 9371524927382376507709771)
                ·
                  refine ⟨14057287391073564761564657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371524927382376507709771 14057287391073564761564657)
                  ·
                    refine ⟨10542965543305173571173493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14057287391073564761564657 10542965543305173571173493)
                    ·
                      refine ⟨988403019684860022297515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10542965543305173571173493 988403019684860022297515)
                      ·
                        rfl

theorem cell23_1924908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1924908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924908 prefixEnd_1924908 := by exact prefixLift 1924908
  have htrace : WordTrace (prefixWord ++ tailWord_1924908) baseStart_1924908 baseEnd_1924908 := by
    simpa [prefixWord, tailWord_1924908, baseEnd_1924908] using wordTrace_append hprefix tailTrace_1924908
  have hstable : (prefixWord ++ tailWord_1924908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924908).length < 2 ^ (prefixWord ++ tailWord_1924908).sum := by decide
  have hdescent : baseEnd_1924908 < baseStart_1924908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924925 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1924925 : Nat := 118140960795 + 1924925 * 2 ^ 59
def prefixEnd_1924925 : Nat := 4983230072969 + 3 ^ 40 * 1924925 * 2
def baseEnd_1924925 : Nat := 988411748855986455784937

theorem tailTrace_1924925 : CollatzResearch.WordTrace tailWord_1924925 prefixEnd_1924925 988411748855986455784937 := by
  unfold tailWord_1924925
  simp only [CollatzResearch.WordTrace]
  refine ⟨70207782551332950861904229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46805188367555300574602819 70207782551332950861904229)
  ·
    refine ⟨13163959228374928286607043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70207782551332950861904229 13163959228374928286607043)
    ·
      refine ⟨19745938842562392429910565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13163959228374928286607043 19745938842562392429910565)
      ·
        refine ⟨3702363532980448580608231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19745938842562392429910565 3702363532980448580608231)
        ·
          refine ⟨5553545299470672870912347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702363532980448580608231 5553545299470672870912347)
          ·
            refine ⟨8330317949206009306368521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553545299470672870912347 8330317949206009306368521)
            ·
              refine ⟨6247738461904506979776391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8330317949206009306368521 6247738461904506979776391)
              ·
                refine ⟨9371607692856760469664587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247738461904506979776391 9371607692856760469664587)
                ·
                  refine ⟨14057411539285140704496881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371607692856760469664587 14057411539285140704496881)
                  ·
                    refine ⟨10543058654463855528372661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14057411539285140704496881 10543058654463855528372661)
                    ·
                      refine ⟨988411748855986455784937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10543058654463855528372661 988411748855986455784937)
                      ·
                        rfl

theorem cell23_1924925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1924925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924925 prefixEnd_1924925 := by exact prefixLift 1924925
  have htrace : WordTrace (prefixWord ++ tailWord_1924925) baseStart_1924925 baseEnd_1924925 := by
    simpa [prefixWord, tailWord_1924925, baseEnd_1924925] using wordTrace_append hprefix tailTrace_1924925
  have hstable : (prefixWord ++ tailWord_1924925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924925).length < 2 ^ (prefixWord ++ tailWord_1924925).sum := by decide
  have hdescent : baseEnd_1924925 < baseStart_1924925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924935 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_1924935 : Nat := 118140960795 + 1924935 * 2 ^ 59
def prefixEnd_1924935 : Nat := 4983230072969 + 3 ^ 40 * 1924935 * 2
def baseEnd_1924935 : Nat := 988416883662531416659891

theorem tailTrace_1924935 : CollatzResearch.WordTrace tailWord_1924935 prefixEnd_1924935 988416883662531416659891 := by
  unfold tailWord_1924935
  simp only [CollatzResearch.WordTrace]
  refine ⟨70208147281296722569768259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46805431520864481713178839 70208147281296722569768259)
  ·
    refine ⟨105312220921945083854652389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70208147281296722569768259 105312220921945083854652389)
    ·
      refine ⟨19746041422864703222747323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105312220921945083854652389 19746041422864703222747323)
      ·
        refine ⟨29619062134297054834120985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19746041422864703222747323 29619062134297054834120985)
        ·
          refine ⟨22214296600722791125590739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29619062134297054834120985 22214296600722791125590739)
          ·
            refine ⟨33321444901084186688386109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22214296600722791125590739 33321444901084186688386109)
            ·
              refine ⟨12495541837906570008144791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33321444901084186688386109 12495541837906570008144791)
              ·
                refine ⟨18743312756859855012217187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12495541837906570008144791 18743312756859855012217187)
                ·
                  refine ⟨28114969135289782518325781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18743312756859855012217187 28114969135289782518325781)
                  ·
                    refine ⟨1317889178216708555546521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28114969135289782518325781 1317889178216708555546521)
                    ·
                      refine ⟨988416883662531416659891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1317889178216708555546521 988416883662531416659891)
                      ·
                        rfl

theorem cell23_1924935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_1924935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924935 prefixEnd_1924935 := by exact prefixLift 1924935
  have htrace : WordTrace (prefixWord ++ tailWord_1924935) baseStart_1924935 baseEnd_1924935 := by
    simpa [prefixWord, tailWord_1924935, baseEnd_1924935] using wordTrace_append hprefix tailTrace_1924935
  have hstable : (prefixWord ++ tailWord_1924935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924935).length < 2 ^ (prefixWord ++ tailWord_1924935).sum := by decide
  have hdescent : baseEnd_1924935 < baseStart_1924935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924945 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 5, 4]
def baseStart_1924945 : Nat := 118140960795 + 1924945 * 2 ^ 59
def prefixEnd_1924945 : Nat := 4983230072969 + 3 ^ 40 * 1924945 * 2
def baseEnd_1924945 : Nat := 329474006156358792511615

theorem tailTrace_1924945 : CollatzResearch.WordTrace tailWord_1924945 prefixEnd_1924945 329474006156358792511615 := by
  unfold tailWord_1924945
  simp only [CollatzResearch.WordTrace]
  refine ⟨70208512011260494277632289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46805674674173662851754859 70208512011260494277632289)
  ·
    refine ⟨52656384008445370708224217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70208512011260494277632289 52656384008445370708224217)
    ·
      refine ⟨39492288006334028031168163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52656384008445370708224217 39492288006334028031168163)
      ·
        refine ⟨59238432009501042046752245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39492288006334028031168163 59238432009501042046752245)
        ·
          refine ⟨5553603000890722691883023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59238432009501042046752245 5553603000890722691883023)
          ·
            refine ⟨8330404501336084037824535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553603000890722691883023 8330404501336084037824535)
            ·
              refine ⟨12495606752004126056736803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8330404501336084037824535 12495606752004126056736803)
              ·
                refine ⟨18743410128006189085105205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12495606752004126056736803 18743410128006189085105205)
                ·
                  refine ⟨1757194699500580226728613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18743410128006189085105205 1757194699500580226728613)
                  ·
                    refine ⟨329474006156358792511615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1757194699500580226728613 329474006156358792511615)
                    ·
                      rfl

theorem cell23_1924945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_1924945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1924945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1924945 prefixEnd_1924945 := by exact prefixLift 1924945
  have htrace : WordTrace (prefixWord ++ tailWord_1924945) baseStart_1924945 baseEnd_1924945 := by
    simpa [prefixWord, tailWord_1924945, baseEnd_1924945] using wordTrace_append hprefix tailTrace_1924945
  have hstable : (prefixWord ++ tailWord_1924945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924945).length < 2 ^ (prefixWord ++ tailWord_1924945).sum := by decide
  have hdescent : baseEnd_1924945 < baseStart_1924945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925055 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_1925055 : Nat := 118140960795 + 1925055 * 2 ^ 59
def prefixEnd_1925055 : Nat := 4983230072969 + 3 ^ 40 * 1925055 * 2
def baseEnd_1925055 : Nat := 988478501341070947159339

theorem tailTrace_1925055 : CollatzResearch.WordTrace tailWord_1925055 prefixEnd_1925055 988478501341070947159339 := by
  unfold tailWord_1925055
  simp only [CollatzResearch.WordTrace]
  refine ⟨70212524040861983064136619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46808349360574655376091079 70212524040861983064136619)
  ·
    refine ⟨105318786061292974596204929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70212524040861983064136619 105318786061292974596204929)
    ·
      refine ⟨78989089545969730947153697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105318786061292974596204929 78989089545969730947153697)
      ·
        refine ⟨59241817159477298210365273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78989089545969730947153697 59241817159477298210365273)
        ·
          refine ⟨44431362869607973657773955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59241817159477298210365273 44431362869607973657773955)
          ·
            refine ⟨66647044304411960486660933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44431362869607973657773955 66647044304411960486660933)
            ·
              refine ⟨12496320807077242591248925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66647044304411960486660933 12496320807077242591248925)
              ·
                refine ⟨4686120302653965971718347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12496320807077242591248925 4686120302653965971718347)
                ·
                  refine ⟨7029180453980948957577521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686120302653965971718347 7029180453980948957577521)
                  ·
                    refine ⟨5271885340485711718183141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7029180453980948957577521 5271885340485711718183141)
                    ·
                      refine ⟨988478501341070947159339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5271885340485711718183141 988478501341070947159339)
                      ·
                        rfl

theorem cell23_1925055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_1925055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925055 prefixEnd_1925055 := by exact prefixLift 1925055
  have htrace : WordTrace (prefixWord ++ tailWord_1925055) baseStart_1925055 baseEnd_1925055 := by
    simpa [prefixWord, tailWord_1925055, baseEnd_1925055] using wordTrace_append hprefix tailTrace_1925055
  have hstable : (prefixWord ++ tailWord_1925055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925055).length < 2 ^ (prefixWord ++ tailWord_1925055).sum := by decide
  have hdescent : baseEnd_1925055 < baseStart_1925055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925079 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 1, 2, 3]
def baseStart_1925079 : Nat := 118140960795 + 1925079 * 2 ^ 59
def prefixEnd_1925079 : Nat := 4983230072969 + 3 ^ 40 * 1925079 * 2
def baseEnd_1925079 : Nat := 988490824876778853259229

theorem tailTrace_1925079 : CollatzResearch.WordTrace tailWord_1925079 prefixEnd_1925079 988490824876778853259229 := by
  unfold tailWord_1925079
  simp only [CollatzResearch.WordTrace]
  refine ⟨70213399392775035163010291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46808932928516690108673527 70213399392775035163010291)
  ·
    refine ⟨105320099089162552744515437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70213399392775035163010291 105320099089162552744515437)
    ·
      refine ⟨39495037158435957279193289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105320099089162552744515437 39495037158435957279193289)
      ·
        refine ⟨29621277868826967959394967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39495037158435957279193289 29621277868826967959394967)
        ·
          refine ⟨44431916803240451939092451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29621277868826967959394967 44431916803240451939092451)
          ·
            refine ⟨66647875204860677908638677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44431916803240451939092451 66647875204860677908638677)
            ·
              refine ⟨1562059575113922138483719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66647875204860677908638677 1562059575113922138483719)
              ·
                refine ⟨2343089362670883207725579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562059575113922138483719 2343089362670883207725579)
                ·
                  refine ⟨3514634044006324811588369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343089362670883207725579 3514634044006324811588369)
                  ·
                    refine ⟨2635975533004743608691277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3514634044006324811588369 2635975533004743608691277)
                    ·
                      refine ⟨988490824876778853259229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2635975533004743608691277 988490824876778853259229)
                      ·
                        rfl

theorem cell23_1925079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_1925079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925079 prefixEnd_1925079 := by exact prefixLift 1925079
  have htrace : WordTrace (prefixWord ++ tailWord_1925079) baseStart_1925079 baseEnd_1925079 := by
    simpa [prefixWord, tailWord_1925079, baseEnd_1925079] using wordTrace_append hprefix tailTrace_1925079
  have hstable : (prefixWord ++ tailWord_1925079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925079).length < 2 ^ (prefixWord ++ tailWord_1925079).sum := by decide
  have hdescent : baseEnd_1925079 < baseStart_1925079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925143 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1925143 : Nat := 118140960795 + 1925143 * 2 ^ 59
def prefixEnd_1925143 : Nat := 4983230072969 + 3 ^ 40 * 1925143 * 2
def baseEnd_1925143 : Nat := 988523687638666602858935

theorem tailTrace_1925143 : CollatzResearch.WordTrace tailWord_1925143 prefixEnd_1925143 988523687638666602858935 := by
  unfold tailWord_1925143
  simp only [CollatzResearch.WordTrace]
  refine ⟨70215733664543174093340083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46810489109695449395560055 70215733664543174093340083)
  ·
    refine ⟨105323600496814761140010125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70215733664543174093340083 105323600496814761140010125)
    ·
      refine ⟨39496350186305535427503797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105323600496814761140010125 39496350186305535427503797)
      ·
        refine ⟨3702782829966143946328481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39496350186305535427503797 3702782829966143946328481)
        ·
          refine ⟨2777087122474607959746361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702782829966143946328481 2777087122474607959746361)
          ·
            refine ⟨2082815341855955969809771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777087122474607959746361 2082815341855955969809771)
            ·
              refine ⟨3124223012783933954714657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082815341855955969809771 3124223012783933954714657)
              ·
                refine ⟨2343167259587950466035993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124223012783933954714657 2343167259587950466035993)
                ·
                  refine ⟨1757375444690962849526995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343167259587950466035993 1757375444690962849526995)
                  ·
                    refine ⟨2636063167036444274290493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1757375444690962849526995 2636063167036444274290493)
                    ·
                      refine ⟨988523687638666602858935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2636063167036444274290493 988523687638666602858935)
                      ·
                        rfl

theorem cell23_1925143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1925143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925143 prefixEnd_1925143 := by exact prefixLift 1925143
  have htrace : WordTrace (prefixWord ++ tailWord_1925143) baseStart_1925143 baseEnd_1925143 := by
    simpa [prefixWord, tailWord_1925143, baseEnd_1925143] using wordTrace_append hprefix tailTrace_1925143
  have hstable : (prefixWord ++ tailWord_1925143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925143).length < 2 ^ (prefixWord ++ tailWord_1925143).sum := by decide
  have hdescent : baseEnd_1925143 < baseStart_1925143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925160 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1925160 : Nat := 118140960795 + 1925160 * 2 ^ 59
def prefixEnd_1925160 : Nat := 4983230072969 + 3 ^ 40 * 1925160 * 2
def baseEnd_1925160 : Nat := 988532416809793036346357

theorem tailTrace_1925160 : CollatzResearch.WordTrace tailWord_1925160 prefixEnd_1925160 988532416809793036346357 := by
  unfold tailWord_1925160
  simp only [CollatzResearch.WordTrace]
  refine ⟨35108176852740792998354467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46810902470321057331139289 35108176852740792998354467)
  ·
    refine ⟨52662265279111189497531701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35108176852740792998354467 52662265279111189497531701)
    ·
      refine ⟨4937087369916674015393597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52662265279111189497531701 4937087369916674015393597)
      ·
        refine ⟨1851407763718752755772599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4937087369916674015393597 1851407763718752755772599)
        ·
          refine ⟨2777111645578129133658899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851407763718752755772599 2777111645578129133658899)
          ·
            refine ⟨4165667468367193700488349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777111645578129133658899 4165667468367193700488349)
            ·
              refine ⟨1562125300637697637683131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4165667468367193700488349 1562125300637697637683131)
              ·
                refine ⟨2343187950956546456524697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562125300637697637683131 2343187950956546456524697)
                ·
                  refine ⟨1757390963217409842393523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343187950956546456524697 1757390963217409842393523)
                  ·
                    refine ⟨2636086444826114763590285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1757390963217409842393523 2636086444826114763590285)
                    ·
                      refine ⟨988532416809793036346357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2636086444826114763590285 988532416809793036346357)
                      ·
                        rfl

theorem cell23_1925160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1925160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925160 prefixEnd_1925160 := by exact prefixLift 1925160
  have htrace : WordTrace (prefixWord ++ tailWord_1925160) baseStart_1925160 baseEnd_1925160 := by
    simpa [prefixWord, tailWord_1925160, baseEnd_1925160] using wordTrace_append hprefix tailTrace_1925160
  have hstable : (prefixWord ++ tailWord_1925160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925160).length < 2 ^ (prefixWord ++ tailWord_1925160).sum := by decide
  have hdescent : baseEnd_1925160 < baseStart_1925160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925166 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_1925166 : Nat := 118140960795 + 1925166 * 2 ^ 59
def prefixEnd_1925166 : Nat := 4983230072969 + 3 ^ 40 * 1925166 * 2
def baseEnd_1925166 : Nat := 988535497693720012871329

theorem tailTrace_1925166 : CollatzResearch.WordTrace tailWord_1925166 prefixEnd_1925166 988535497693720012871329 := by
  unfold tailWord_1925166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777071567932481127678419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46811048362306566014284901 8777071567932481127678419)
  ·
    refine ⟨13165607351898721691517629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8777071567932481127678419 13165607351898721691517629)
    ·
      refine ⟨4937102756962020634319111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13165607351898721691517629 4937102756962020634319111)
      ·
        refine ⟨7405654135443030951478667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937102756962020634319111 7405654135443030951478667)
        ·
          refine ⟨11108481203164546427218001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7405654135443030951478667 11108481203164546427218001)
          ·
            refine ⟨8331360902373409820413501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11108481203164546427218001 8331360902373409820413501)
            ·
              refine ⟨3124260338390028682655063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8331360902373409820413501 3124260338390028682655063)
              ·
                refine ⟨4686390507585043023982595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124260338390028682655063 4686390507585043023982595)
                ·
                  refine ⟨7029585761377564535973893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686390507585043023982595 7029585761377564535973893)
                  ·
                    refine ⟨1318047330258293350495105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7029585761377564535973893 1318047330258293350495105)
                    ·
                      refine ⟨988535497693720012871329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318047330258293350495105 988535497693720012871329)
                      ·
                        rfl

theorem cell23_1925166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_1925166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925166 prefixEnd_1925166 := by exact prefixLift 1925166
  have htrace : WordTrace (prefixWord ++ tailWord_1925166) baseStart_1925166 baseEnd_1925166 := by
    simpa [prefixWord, tailWord_1925166, baseEnd_1925166] using wordTrace_append hprefix tailTrace_1925166
  have hstable : (prefixWord ++ tailWord_1925166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925166).length < 2 ^ (prefixWord ++ tailWord_1925166).sum := by decide
  have hdescent : baseEnd_1925166 < baseStart_1925166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925195 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_1925195 : Nat := 118140960795 + 1925195 * 2 ^ 59
def prefixEnd_1925195 : Nat := 4983230072969 + 3 ^ 40 * 1925195 * 2
def baseEnd_1925195 : Nat := 988550388632700399408695

theorem tailTrace_1925195 : CollatzResearch.WordTrace tailWord_1925195 prefixEnd_1925195 988550388632700399408695 := by
  unfold tailWord_1925195
  simp only [CollatzResearch.WordTrace]
  refine ⟨70217630260354786974233039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46811753506903191316155359 70217630260354786974233039)
  ·
    refine ⟨105326445390532180461349559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70217630260354786974233039 105326445390532180461349559)
    ·
      refine ⟨157989668085798270692024339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105326445390532180461349559 157989668085798270692024339)
      ·
        refine ⟨236984502128697406038036509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157989668085798270692024339 236984502128697406038036509)
        ·
          refine ⟨88869188298261527264263691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236984502128697406038036509 88869188298261527264263691)
          ·
            refine ⟨133303782447392290896395537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88869188298261527264263691 133303782447392290896395537)
            ·
              refine ⟨99977836835544218172296653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133303782447392290896395537 99977836835544218172296653)
              ·
                refine ⟨37491688813329081814611245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99977836835544218172296653 37491688813329081814611245)
                ·
                  refine ⟨14059383304998405680479217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37491688813329081814611245 14059383304998405680479217)
                  ·
                    refine ⟨10544537478748804260359413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14059383304998405680479217 10544537478748804260359413)
                    ·
                      refine ⟨988550388632700399408695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10544537478748804260359413 988550388632700399408695)
                      ·
                        rfl

theorem cell23_1925195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_1925195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925195 prefixEnd_1925195 := by exact prefixLift 1925195
  have htrace : WordTrace (prefixWord ++ tailWord_1925195) baseStart_1925195 baseEnd_1925195 := by
    simpa [prefixWord, tailWord_1925195, baseEnd_1925195] using wordTrace_append hprefix tailTrace_1925195
  have hstable : (prefixWord ++ tailWord_1925195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925195).length < 2 ^ (prefixWord ++ tailWord_1925195).sum := by decide
  have hdescent : baseEnd_1925195 < baseStart_1925195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925206 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1925206 : Nat := 118140960795 + 1925206 * 2 ^ 59
def prefixEnd_1925206 : Nat := 4983230072969 + 3 ^ 40 * 1925206 * 2
def baseEnd_1925206 : Nat := 109839559657766650707905

theorem tailTrace_1925206 : CollatzResearch.WordTrace tailWord_1925206 prefixEnd_1925206 109839559657766650707905 := by
  unfold tailWord_1925206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388626966457183490805217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46812020975543290568588981 4388626966457183490805217)
  ·
    refine ⟨3291470224842887618103913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4388626966457183490805217 3291470224842887618103913)
    ·
      refine ⟨2468602668632165713577935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3291470224842887618103913 2468602668632165713577935)
      ·
        refine ⟨3702904002948248570366903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468602668632165713577935 3702904002948248570366903)
        ·
          refine ⟨5554356004422372855550355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702904002948248570366903 5554356004422372855550355)
          ·
            refine ⟨8331534006633559283325533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554356004422372855550355 8331534006633559283325533)
            ·
              refine ⟨3124325252487584731247075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8331534006633559283325533 3124325252487584731247075)
              ·
                refine ⟨4686487878731377096870613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124325252487584731247075 4686487878731377096870613)
                ·
                  refine ⟨109839559657766650707905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4686487878731377096870613 109839559657766650707905)
                  ·
                    rfl

theorem cell23_1925206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1925206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925206 prefixEnd_1925206 := by exact prefixLift 1925206
  have htrace : WordTrace (prefixWord ++ tailWord_1925206) baseStart_1925206 baseEnd_1925206 := by
    simpa [prefixWord, tailWord_1925206, baseEnd_1925206] using wordTrace_append hprefix tailTrace_1925206
  have hstable : (prefixWord ++ tailWord_1925206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925206).length < 2 ^ (prefixWord ++ tailWord_1925206).sum := by decide
  have hdescent : baseEnd_1925206 < baseStart_1925206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925212 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1925212 : Nat := 118140960795 + 1925212 * 2 ^ 59
def prefixEnd_1925212 : Nat := 4983230072969 + 3 ^ 40 * 1925212 * 2
def baseEnd_1925212 : Nat := 988559117803826832896117

theorem tailTrace_1925212 : CollatzResearch.WordTrace tailWord_1925212 prefixEnd_1925212 988559117803826832896117 := by
  unfold tailWord_1925212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35109125150646599438800945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46812166867528799251734593 35109125150646599438800945)
  ·
    refine ⟨26331843862984949579100709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35109125150646599438800945 26331843862984949579100709)
    ·
      refine ⟨4937220724309678046081383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26331843862984949579100709 4937220724309678046081383)
      ·
        refine ⟨7405831086464517069122075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937220724309678046081383 7405831086464517069122075)
        ·
          refine ⟨11108746629696775603683113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7405831086464517069122075 11108746629696775603683113)
          ·
            refine ⟨8331559972272581702762335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11108746629696775603683113 8331559972272581702762335)
            ·
              refine ⟨12497339958408872554143503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8331559972272581702762335 12497339958408872554143503)
              ·
                refine ⟨18746009937613308831215255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12497339958408872554143503 18746009937613308831215255)
                ·
                  refine ⟨28119014906419963246822883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18746009937613308831215255 28119014906419963246822883)
                  ·
                    refine ⟨42178522359629944870234325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28119014906419963246822883 42178522359629944870234325)
                    ·
                      refine ⟨988559117803826832896117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42178522359629944870234325 988559117803826832896117)
                      ·
                        rfl

theorem cell23_1925212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1925212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925212 prefixEnd_1925212 := by exact prefixLift 1925212
  have htrace : WordTrace (prefixWord ++ tailWord_1925212) baseStart_1925212 baseEnd_1925212 := by
    simpa [prefixWord, tailWord_1925212, baseEnd_1925212] using wordTrace_append hprefix tailTrace_1925212
  have hstable : (prefixWord ++ tailWord_1925212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925212).length < 2 ^ (prefixWord ++ tailWord_1925212).sum := by decide
  have hdescent : baseEnd_1925212 < baseStart_1925212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925215 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 8]
def baseStart_1925215 : Nat := 118140960795 + 1925215 * 2 ^ 59
def prefixEnd_1925215 : Nat := 4983230072969 + 3 ^ 40 * 1925215 * 2
def baseEnd_1925215 : Nat := 329520219415263440386201

theorem tailTrace_1925215 : CollatzResearch.WordTrace tailWord_1925215 prefixEnd_1925215 329520219415263440386201 := by
  unfold tailWord_1925215
  simp only [CollatzResearch.WordTrace]
  refine ⟨70218359720282330389961099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46812239813521553593307399 70218359720282330389961099)
  ·
    refine ⟨105327539580423495584941649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70218359720282330389961099 105327539580423495584941649)
    ·
      refine ⟨78995654685317621688706237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105327539580423495584941649 78995654685317621688706237)
      ·
        refine ⟨29623370506994108133264839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78995654685317621688706237 29623370506994108133264839)
        ·
          refine ⟨44435055760491162199897259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29623370506994108133264839 44435055760491162199897259)
          ·
            refine ⟨66652583640736743299845889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44435055760491162199897259 66652583640736743299845889)
            ·
              refine ⟨49989437730552557474884417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66652583640736743299845889 49989437730552557474884417)
              ·
                refine ⟨37492078297914418106163313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49989437730552557474884417 37492078297914418106163313)
                ·
                  refine ⟨28119058723435813579622485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37492078297914418106163313 28119058723435813579622485)
                  ·
                    refine ⟨329520219415263440386201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28119058723435813579622485 329520219415263440386201)
                    ·
                      rfl

theorem cell23_1925215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_1925215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925215 prefixEnd_1925215 := by exact prefixLift 1925215
  have htrace : WordTrace (prefixWord ++ tailWord_1925215) baseStart_1925215 baseEnd_1925215 := by
    simpa [prefixWord, tailWord_1925215, baseEnd_1925215] using wordTrace_append hprefix tailTrace_1925215
  have hstable : (prefixWord ++ tailWord_1925215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925215).length < 2 ^ (prefixWord ++ tailWord_1925215).sum := by decide
  have hdescent : baseEnd_1925215 < baseStart_1925215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925239 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1925239 : Nat := 118140960795 + 1925239 * 2 ^ 59
def prefixEnd_1925239 : Nat := 4983230072969 + 3 ^ 40 * 1925239 * 2
def baseEnd_1925239 : Nat := 988572981781498227258493

theorem tailTrace_1925239 : CollatzResearch.WordTrace tailWord_1925239 prefixEnd_1925239 988572981781498227258493 := by
  unfold tailWord_1925239
  simp only [CollatzResearch.WordTrace]
  refine ⟨70219235072195382488834771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46812823381463588325889847 70219235072195382488834771)
  ·
    refine ⟨105328852608293073733252157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70219235072195382488834771 105328852608293073733252157)
    ·
      refine ⟨39498319728109902649969559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105328852608293073733252157 39498319728109902649969559)
      ·
        refine ⟨59247479592164853974954339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39498319728109902649969559 59247479592164853974954339)
        ·
          refine ⟨88871219388247280962431509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59247479592164853974954339 88871219388247280962431509)
          ·
            refine ⟨4165838408824091295113977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88871219388247280962431509 4165838408824091295113977)
            ·
              refine ⟨3124378806618068471335483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4165838408824091295113977 3124378806618068471335483)
              ·
                refine ⟨4686568209927102707003225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124378806618068471335483 4686568209927102707003225)
                ·
                  refine ⟨3514926157445327030252419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686568209927102707003225 3514926157445327030252419)
                  ·
                    refine ⟨5272389236167990545378629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514926157445327030252419 5272389236167990545378629)
                    ·
                      refine ⟨988572981781498227258493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5272389236167990545378629 988572981781498227258493)
                      ·
                        rfl

theorem cell23_1925239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1925239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925239 prefixEnd_1925239 := by exact prefixLift 1925239
  have htrace : WordTrace (prefixWord ++ tailWord_1925239) baseStart_1925239 baseEnd_1925239 := by
    simpa [prefixWord, tailWord_1925239, baseEnd_1925239] using wordTrace_append hprefix tailTrace_1925239
  have hstable : (prefixWord ++ tailWord_1925239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925239).length < 2 ^ (prefixWord ++ tailWord_1925239).sum := by decide
  have hdescent : baseEnd_1925239 < baseStart_1925239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925252 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1925252 : Nat := 118140960795 + 1925252 * 2 ^ 59
def prefixEnd_1925252 : Nat := 4983230072969 + 3 ^ 40 * 1925252 * 2
def baseEnd_1925252 : Nat := 988579657030006676395933

theorem tailTrace_1925252 : CollatzResearch.WordTrace tailWord_1925252 prefixEnd_1925252 988579657030006676395933 := by
  unfold tailWord_1925252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35109854610574142854529005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46813139480765523806038673 35109854610574142854529005)
  ·
    refine ⟨13166195478965303570448377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35109854610574142854529005 13166195478965303570448377)
    ·
      refine ⟨9874646609223977677836283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13166195478965303570448377 9874646609223977677836283)
      ·
        refine ⟨14811969913835966516754425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9874646609223977677836283 14811969913835966516754425)
        ·
          refine ⟨11108977435376974887565819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14811969913835966516754425 11108977435376974887565819)
          ·
            refine ⟨16663466153065462331348729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11108977435376974887565819 16663466153065462331348729)
            ·
              refine ⟨12497599614799096748511547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16663466153065462331348729 12497599614799096748511547)
              ·
                refine ⟨18746399422198645122767321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12497599614799096748511547 18746399422198645122767321)
                ·
                  refine ⟨14059799566648983842075491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18746399422198645122767321 14059799566648983842075491)
                  ·
                    refine ⟨21089699349973475763113237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14059799566648983842075491 21089699349973475763113237)
                    ·
                      refine ⟨988579657030006676395933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21089699349973475763113237 988579657030006676395933)
                      ·
                        rfl

theorem cell23_1925252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1925252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925252 prefixEnd_1925252 := by exact prefixLift 1925252
  have htrace : WordTrace (prefixWord ++ tailWord_1925252) baseStart_1925252 baseEnd_1925252 := by
    simpa [prefixWord, tailWord_1925252, baseEnd_1925252] using wordTrace_append hprefix tailTrace_1925252
  have hstable : (prefixWord ++ tailWord_1925252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925252).length < 2 ^ (prefixWord ++ tailWord_1925252).sum := by decide
  have hdescent : baseEnd_1925252 < baseStart_1925252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925279 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 6]
def baseStart_1925279 : Nat := 118140960795 + 1925279 * 2 ^ 59
def prefixEnd_1925279 : Nat := 4983230072969 + 3 ^ 40 * 1925279 * 2
def baseEnd_1925279 : Nat := 109843724556408674528701

theorem tailTrace_1925279 : CollatzResearch.WordTrace tailWord_1925279 prefixEnd_1925279 109843724556408674528701 := by
  unfold tailWord_1925279
  simp only [CollatzResearch.WordTrace]
  refine ⟨70220693992050469320290891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46813795994700312880193927 70220693992050469320290891)
  ·
    refine ⟨105331040988075703980436337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70220693992050469320290891 105331040988075703980436337)
    ·
      refine ⟨78998280741056777985327253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105331040988075703980436337 78998280741056777985327253)
      ·
        refine ⟨3703044409737036468062215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78998280741056777985327253 3703044409737036468062215)
        ·
          refine ⟨5554566614605554702093323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703044409737036468062215 5554566614605554702093323)
          ·
            refine ⟨8331849921908332053139985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554566614605554702093323 8331849921908332053139985)
            ·
              refine ⟨6248887441431249039854989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8331849921908332053139985 6248887441431249039854989)
              ·
                refine ⟨2343332790536718389945621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6248887441431249039854989 2343332790536718389945621)
                ·
                  refine ⟨109843724556408674528701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2343332790536718389945621 109843724556408674528701)
                  ·
                    rfl

theorem cell23_1925279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 6].length) (baseStart_1925279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925279 prefixEnd_1925279 := by exact prefixLift 1925279
  have htrace : WordTrace (prefixWord ++ tailWord_1925279) baseStart_1925279 baseEnd_1925279 := by
    simpa [prefixWord, tailWord_1925279, baseEnd_1925279] using wordTrace_append hprefix tailTrace_1925279
  have hstable : (prefixWord ++ tailWord_1925279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925279).length < 2 ^ (prefixWord ++ tailWord_1925279).sum := by decide
  have hdescent : baseEnd_1925279 < baseStart_1925279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925290 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1925290 : Nat := 118140960795 + 1925290 * 2 ^ 59
def prefixEnd_1925290 : Nat := 4983230072969 + 3 ^ 40 * 1925290 * 2
def baseEnd_1925290 : Nat := 988599169294877527720759

theorem tailTrace_1925290 : CollatzResearch.WordTrace tailWord_1925290 prefixEnd_1925290 988599169294877527720759 := by
  unfold tailWord_1925290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555273798752654549735331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46814063463340412132627549 17555273798752654549735331)
  ·
    refine ⟨26332910698128981824602997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17555273798752654549735331 26332910698128981824602997)
    ·
      refine ⟨2468710377949592046056531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26332910698128981824602997 2468710377949592046056531)
      ·
        refine ⟨3703065566924388069084797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468710377949592046056531 3703065566924388069084797)
        ·
          refine ⟨1388649587596645525906799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3703065566924388069084797 1388649587596645525906799)
          ·
            refine ⟨2082974381394968288860199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388649587596645525906799 2082974381394968288860199)
            ·
              refine ⟨3124461572092452433290299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082974381394968288860199 3124461572092452433290299)
              ·
                refine ⟨4686692358138678649935449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124461572092452433290299 4686692358138678649935449)
                ·
                  refine ⟨3515019268604008987451587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686692358138678649935449 3515019268604008987451587)
                  ·
                    refine ⟨5272528902906013481177381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515019268604008987451587 5272528902906013481177381)
                    ·
                      refine ⟨988599169294877527720759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5272528902906013481177381 988599169294877527720759)
                      ·
                        rfl

theorem cell23_1925290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1925290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925290 prefixEnd_1925290 := by exact prefixLift 1925290
  have htrace : WordTrace (prefixWord ++ tailWord_1925290) baseStart_1925290 baseEnd_1925290 := by
    simpa [prefixWord, tailWord_1925290, baseEnd_1925290] using wordTrace_append hprefix tailTrace_1925290
  have hstable : (prefixWord ++ tailWord_1925290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925290).length < 2 ^ (prefixWord ++ tailWord_1925290).sum := by decide
  have hdescent : baseEnd_1925290 < baseStart_1925290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925293 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1925293 : Nat := 118140960795 + 1925293 * 2 ^ 59
def prefixEnd_1925293 : Nat := 4983230072969 + 3 ^ 40 * 1925293 * 2
def baseEnd_1925293 : Nat := 988600709736841015983245

theorem tailTrace_1925293 : CollatzResearch.WordTrace tailWord_1925293 prefixEnd_1925293 988600709736841015983245 := by
  unfold tailWord_1925293
  simp only [CollatzResearch.WordTrace]
  refine ⟨70221204613999749711300533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46814136409333166474200355 70221204613999749711300533)
  ·
    refine ⟨6583237932562476535434425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70221204613999749711300533 6583237932562476535434425)
    ·
      refine ⟨4937428449421857401575819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6583237932562476535434425 4937428449421857401575819)
      ·
        refine ⟨7406142674132786102363729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937428449421857401575819 7406142674132786102363729)
        ·
          refine ⟨5554607005599589576772797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7406142674132786102363729 5554607005599589576772797)
          ·
            refine ⟨2082977627099846091289799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5554607005599589576772797 2082977627099846091289799)
            ·
              refine ⟨3124466440649769136934699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082977627099846091289799 3124466440649769136934699)
              ·
                refine ⟨4686699660974653705402049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124466440649769136934699 4686699660974653705402049)
                ·
                  refine ⟨3515024745730990279051537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686699660974653705402049 3515024745730990279051537)
                  ·
                    refine ⟨2636268559298242709288653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515024745730990279051537 2636268559298242709288653)
                    ·
                      refine ⟨988600709736841015983245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2636268559298242709288653 988600709736841015983245)
                      ·
                        rfl

theorem cell23_1925293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1925293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925293 prefixEnd_1925293 := by exact prefixLift 1925293
  have htrace : WordTrace (prefixWord ++ tailWord_1925293) baseStart_1925293 baseEnd_1925293 := by
    simpa [prefixWord, tailWord_1925293, baseEnd_1925293] using wordTrace_append hprefix tailTrace_1925293
  have hstable : (prefixWord ++ tailWord_1925293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925293).length < 2 ^ (prefixWord ++ tailWord_1925293).sum := by decide
  have hdescent : baseEnd_1925293 < baseStart_1925293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925313 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 6]
def baseStart_1925313 : Nat := 118140960795 + 1925313 * 2 ^ 59
def prefixEnd_1925313 : Nat := 4983230072969 + 3 ^ 40 * 1925313 * 2
def baseEnd_1925313 : Nat := 109845664372214548637017

theorem tailTrace_1925313 : CollatzResearch.WordTrace tailWord_1925313 prefixEnd_1925313 109845664372214548637017 := by
  unfold tailWord_1925313
  simp only [CollatzResearch.WordTrace]
  refine ⟨70221934073927293127028593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46814622715951528751352395 70221934073927293127028593)
  ·
    refine ⟨52666450555445469845271445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70221934073927293127028593 52666450555445469845271445)
    ·
      refine ⟨2468739869786506398997099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52666450555445469845271445 2468739869786506398997099)
      ·
        refine ⟨3703109804679759598495649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468739869786506398997099 3703109804679759598495649)
        ·
          refine ⟨2777332353509819698871737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3703109804679759598495649 2777332353509819698871737)
          ·
            refine ⟨2082999265132364774153803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777332353509819698871737 2082999265132364774153803)
            ·
              refine ⟨3124498897698547161230705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082999265132364774153803 3124498897698547161230705)
              ·
                refine ⟨2343374173273910370923029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124498897698547161230705 2343374173273910370923029)
                ·
                  refine ⟨109845664372214548637017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2343374173273910370923029 109845664372214548637017)
                  ·
                    rfl

theorem cell23_1925313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 6].length) (baseStart_1925313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925313 prefixEnd_1925313 := by exact prefixLift 1925313
  have htrace : WordTrace (prefixWord ++ tailWord_1925313) baseStart_1925313 baseEnd_1925313 := by
    simpa [prefixWord, tailWord_1925313, baseEnd_1925313] using wordTrace_append hprefix tailTrace_1925313
  have hstable : (prefixWord ++ tailWord_1925313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925313).length < 2 ^ (prefixWord ++ tailWord_1925313).sum := by decide
  have hdescent : baseEnd_1925313 < baseStart_1925313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925357 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_1925357 : Nat := 118140960795 + 1925357 * 2 ^ 59
def prefixEnd_1925357 : Nat := 4983230072969 + 3 ^ 40 * 1925357 * 2
def baseEnd_1925357 : Nat := 988633572498728765582951

theorem tailTrace_1925357 : CollatzResearch.WordTrace tailWord_1925357 prefixEnd_1925357 988633572498728765582951 := by
  unfold tailWord_1925357
  simp only [CollatzResearch.WordTrace]
  refine ⟨70223538885767888641630325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46815692590511925761086883 70223538885767888641630325)
  ·
    refine ⟨6583456770540739560152843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70223538885767888641630325 6583456770540739560152843)
    ·
      refine ⟨9875185155811109340229265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6583456770540739560152843 9875185155811109340229265)
      ·
        refine ⟨7406388866858332005171949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9875185155811109340229265 7406388866858332005171949)
        ·
          refine ⟨2777395825071874501939481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7406388866858332005171949 2777395825071874501939481)
          ·
            refine ⟨2083046868803905876454611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777395825071874501939481 2083046868803905876454611)
            ·
              refine ⟨3124570303205858814681917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083046868803905876454611 3124570303205858814681917)
              ·
                refine ⟨1171713863702197055505719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124570303205858814681917 1171713863702197055505719)
                ·
                  refine ⟨1757570795553295583258579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171713863702197055505719 1757570795553295583258579)
                  ·
                    refine ⟨2636356193329943374887869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1757570795553295583258579 2636356193329943374887869)
                    ·
                      refine ⟨988633572498728765582951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2636356193329943374887869 988633572498728765582951)
                      ·
                        rfl

theorem cell23_1925357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_1925357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925357 prefixEnd_1925357 := by exact prefixLift 1925357
  have htrace : WordTrace (prefixWord ++ tailWord_1925357) baseStart_1925357 baseEnd_1925357 := by
    simpa [prefixWord, tailWord_1925357, baseEnd_1925357] using wordTrace_append hprefix tailTrace_1925357
  have hstable : (prefixWord ++ tailWord_1925357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925357).length < 2 ^ (prefixWord ++ tailWord_1925357).sum := by decide
  have hdescent : baseEnd_1925357 < baseStart_1925357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925429 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1925429 : Nat := 118140960795 + 1925429 * 2 ^ 59
def prefixEnd_1925429 : Nat := 4983230072969 + 3 ^ 40 * 1925429 * 2
def baseEnd_1925429 : Nat := 329556847701950827960873

theorem tailTrace_1925429 : CollatzResearch.WordTrace tailWord_1925429 prefixEnd_1925429 329556847701950827960873 := by
  unfold tailWord_1925429
  simp only [CollatzResearch.WordTrace]
  refine ⟨70226164941507044938251341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46817443294338029958834227 70226164941507044938251341)
  ·
    refine ⟨26334811853065141851844253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70226164941507044938251341 26334811853065141851844253)
    ·
      refine ⟨9875554444899428194441595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26334811853065141851844253 9875554444899428194441595)
      ·
        refine ⟨14813331667349142291662393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9875554444899428194441595 14813331667349142291662393)
        ·
          refine ⟨11109998750511856718746795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14813331667349142291662393 11109998750511856718746795)
          ·
            refine ⟨16664998125767785078120193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109998750511856718746795 16664998125767785078120193)
            ·
              refine ⟨12498748594325838808590145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16664998125767785078120193 12498748594325838808590145)
              ·
                refine ⟨9374061445744379106442609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12498748594325838808590145 9374061445744379106442609)
                ·
                  refine ⟨7030546084308284329831957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374061445744379106442609 7030546084308284329831957)
                  ·
                    refine ⟨329556847701950827960873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7030546084308284329831957 329556847701950827960873)
                    ·
                      rfl

theorem cell23_1925429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1925429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925429 prefixEnd_1925429 := by exact prefixLift 1925429
  have htrace : WordTrace (prefixWord ++ tailWord_1925429) baseStart_1925429 baseEnd_1925429 := by
    simpa [prefixWord, tailWord_1925429, baseEnd_1925429] using wordTrace_append hprefix tailTrace_1925429
  have hstable : (prefixWord ++ tailWord_1925429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925429).length < 2 ^ (prefixWord ++ tailWord_1925429).sum := by decide
  have hdescent : baseEnd_1925429 < baseStart_1925429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925436 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_1925436 : Nat := 118140960795 + 1925436 * 2 ^ 59
def prefixEnd_1925436 : Nat := 4983230072969 + 3 ^ 40 * 1925436 * 2
def baseEnd_1925436 : Nat := 988674137470433956495087

theorem tailTrace_1925436 : CollatzResearch.WordTrace tailWord_1925436 prefixEnd_1925436 988674137470433956495087 := by
  unfold tailWord_1925436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35113210126240842566878081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46817613501654456755837441 35113210126240842566878081)
  ·
    refine ⟨26334907594680631925158561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35113210126240842566878081 26334907594680631925158561)
    ·
      refine ⟨19751180696010473943868921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26334907594680631925158561 19751180696010473943868921)
      ·
        refine ⟨14813385522007855457901691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19751180696010473943868921 14813385522007855457901691)
        ·
          refine ⟨22220078283011783186852537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813385522007855457901691 22220078283011783186852537)
          ·
            refine ⟨16665058712258837390139403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22220078283011783186852537 16665058712258837390139403)
            ·
              refine ⟨24997588068388256085209105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665058712258837390139403 24997588068388256085209105)
              ·
                refine ⟨18748191051291192063906829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24997588068388256085209105 18748191051291192063906829)
                ·
                  refine ⟨7030571644234197023965061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18748191051291192063906829 7030571644234197023965061)
                  ·
                    refine ⟨1318232183293911941993449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7030571644234197023965061 1318232183293911941993449)
                    ·
                      refine ⟨988674137470433956495087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318232183293911941993449 988674137470433956495087)
                      ·
                        rfl

theorem cell23_1925436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_1925436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925436 prefixEnd_1925436 := by exact prefixLift 1925436
  have htrace : WordTrace (prefixWord ++ tailWord_1925436) baseStart_1925436 baseEnd_1925436 := by
    simpa [prefixWord, tailWord_1925436, baseEnd_1925436] using wordTrace_append hprefix tailTrace_1925436
  have hstable : (prefixWord ++ tailWord_1925436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925436).length < 2 ^ (prefixWord ++ tailWord_1925436).sum := by decide
  have hdescent : baseEnd_1925436 < baseStart_1925436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925439 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_1925439 : Nat := 118140960795 + 1925439 * 2 ^ 59
def prefixEnd_1925439 : Nat := 4983230072969 + 3 ^ 40 * 1925439 * 2
def baseEnd_1925439 : Nat := 988675677912397444757573

theorem tailTrace_1925439 : CollatzResearch.WordTrace tailWord_1925439 prefixEnd_1925439 988675677912397444757573 := by
  unfold tailWord_1925439
  simp only [CollatzResearch.WordTrace]
  refine ⟨70226529671470816646115371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46817686447647211097410247 70226529671470816646115371)
  ·
    refine ⟨105339794507206224969173057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70226529671470816646115371 105339794507206224969173057)
    ·
      refine ⟨79004845880404668726879793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105339794507206224969173057 79004845880404668726879793)
      ·
        refine ⟨59253634410303501545159845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79004845880404668726879793 59253634410303501545159845)
        ·
          refine ⟨11110056451931906539717471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59253634410303501545159845 11110056451931906539717471)
          ·
            refine ⟨16665084677897859809576207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110056451931906539717471 16665084677897859809576207)
            ·
              refine ⟨24997627016846789714364311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665084677897859809576207 24997627016846789714364311)
              ·
                refine ⟨37496440525270184571546467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24997627016846789714364311 37496440525270184571546467)
                ·
                  refine ⟨56244660787905276857319701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37496440525270184571546467 56244660787905276857319701)
                  ·
                    refine ⟨2636468474433059852686861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56244660787905276857319701 2636468474433059852686861)
                    ·
                      refine ⟨988675677912397444757573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2636468474433059852686861 988675677912397444757573)
                      ·
                        rfl

theorem cell23_1925439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_1925439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925439 prefixEnd_1925439 := by exact prefixLift 1925439
  have htrace : WordTrace (prefixWord ++ tailWord_1925439) baseStart_1925439 baseEnd_1925439 := by
    simpa [prefixWord, tailWord_1925439, baseEnd_1925439] using wordTrace_append hprefix tailTrace_1925439
  have hstable : (prefixWord ++ tailWord_1925439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925439).length < 2 ^ (prefixWord ++ tailWord_1925439).sum := by decide
  have hdescent : baseEnd_1925439 < baseStart_1925439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925489 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_1925489 : Nat := 118140960795 + 1925489 * 2 ^ 59
def prefixEnd_1925489 : Nat := 4983230072969 + 3 ^ 40 * 1925489 * 2
def baseEnd_1925489 : Nat := 329567117315040749710781

theorem tailTrace_1925489 : CollatzResearch.WordTrace tailWord_1925489 prefixEnd_1925489 329567117315040749710781 := by
  unfold tailWord_1925489
  simp only [CollatzResearch.WordTrace]
  refine ⟨70228353321289675185435521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46818902214193116790290347 70228353321289675185435521)
  ·
    refine ⟨52671264990967256389076641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70228353321289675185435521 52671264990967256389076641)
    ·
      refine ⟨39503448743225442291807481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52671264990967256389076641 39503448743225442291807481)
      ·
        refine ⟨29627586557419081718855611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39503448743225442291807481 29627586557419081718855611)
        ·
          refine ⟨44441379836128622578283417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29627586557419081718855611 44441379836128622578283417)
          ·
            refine ⟨33331034877096466933712563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44441379836128622578283417 33331034877096466933712563)
            ·
              refine ⟨49996552315644700400568845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33331034877096466933712563 49996552315644700400568845)
              ·
                refine ⟨18748707118366762650213317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49996552315644700400568845 18748707118366762650213317)
                ·
                  refine ⟨3515382584693767996914997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18748707118366762650213317 3515382584693767996914997)
                  ·
                    refine ⟨329567117315040749710781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3515382584693767996914997 329567117315040749710781)
                    ·
                      rfl

theorem cell23_1925489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_1925489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925489 prefixEnd_1925489 := by exact prefixLift 1925489
  have htrace : WordTrace (prefixWord ++ tailWord_1925489) baseStart_1925489 baseEnd_1925489 := by
    simpa [prefixWord, tailWord_1925489, baseEnd_1925489] using wordTrace_append hprefix tailTrace_1925489
  have hstable : (prefixWord ++ tailWord_1925489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925489).length < 2 ^ (prefixWord ++ tailWord_1925489).sum := by decide
  have hdescent : baseEnd_1925489 < baseStart_1925489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925493 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 5]
def baseStart_1925493 : Nat := 118140960795 + 1925493 * 2 ^ 59
def prefixEnd_1925493 : Nat := 4983230072969 + 3 ^ 40 * 1925493 * 2
def baseEnd_1925493 : Nat := 109855933985304470386925

theorem tailTrace_1925493 : CollatzResearch.WordTrace tailWord_1925493 prefixEnd_1925493 109855933985304470386925 := by
  unfold tailWord_1925493
  simp only [CollatzResearch.WordTrace]
  refine ⟨70228499213275183868581133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46818999475516789245720755 70228499213275183868581133)
  ·
    refine ⟨26335687204978193950717925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70228499213275183868581133 26335687204978193950717925)
    ·
      refine ⟨4937941350933411365759611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26335687204978193950717925 4937941350933411365759611)
      ·
        refine ⟨7406912026400117048639417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937941350933411365759611 7406912026400117048639417)
        ·
          refine ⟨5555184019800087786479563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7406912026400117048639417 5555184019800087786479563)
          ·
            refine ⟨8332776029700131679719345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555184019800087786479563 8332776029700131679719345)
            ·
              refine ⟨6249582022275098759789509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8332776029700131679719345 6249582022275098759789509)
              ·
                refine ⟨1171796629176581017460533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6249582022275098759789509 1171796629176581017460533)
                ·
                  refine ⟨109855933985304470386925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1171796629176581017460533 109855933985304470386925)
                  ·
                    rfl

theorem cell23_1925493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_1925493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925493 prefixEnd_1925493 := by exact prefixLift 1925493
  have htrace : WordTrace (prefixWord ++ tailWord_1925493) baseStart_1925493 baseEnd_1925493 := by
    simpa [prefixWord, tailWord_1925493, baseEnd_1925493] using wordTrace_append hprefix tailTrace_1925493
  have hstable : (prefixWord ++ tailWord_1925493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925493).length < 2 ^ (prefixWord ++ tailWord_1925493).sum := by decide
  have hdescent : baseEnd_1925493 < baseStart_1925493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925543 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1925543 : Nat := 118140960795 + 1925543 * 2 ^ 59
def prefixEnd_1925543 : Nat := 4983230072969 + 3 ^ 40 * 1925543 * 2
def baseEnd_1925543 : Nat := 988729079900465037857095

theorem tailTrace_1925543 : CollatzResearch.WordTrace tailWord_1925543 prefixEnd_1925543 988729079900465037857095 := by
  unfold tailWord_1925543
  simp only [CollatzResearch.WordTrace]
  refine ⟨70230322863094042407901283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46820215242062694938600855 70230322863094042407901283)
  ·
    refine ⟨105345484294641063611851925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70230322863094042407901283 105345484294641063611851925)
    ·
      refine ⟨4938069576311299856805559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105345484294641063611851925 4938069576311299856805559)
      ·
        refine ⟨7407104364466949785208339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938069576311299856805559 7407104364466949785208339)
        ·
          refine ⟨11110656546700424677812509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407104364466949785208339 11110656546700424677812509)
          ·
            refine ⟨4166496205012659254179691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11110656546700424677812509 4166496205012659254179691)
            ·
              refine ⟨6249744307518988881269537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166496205012659254179691 6249744307518988881269537)
              ·
                refine ⟨4687308230639241660952153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6249744307518988881269537 4687308230639241660952153)
                ·
                  refine ⟨3515481172979431245714115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687308230639241660952153 3515481172979431245714115)
                  ·
                    refine ⟨5273221759469146868571173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515481172979431245714115 5273221759469146868571173)
                    ·
                      refine ⟨988729079900465037857095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5273221759469146868571173 988729079900465037857095)
                      ·
                        rfl

theorem cell23_1925543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1925543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925543 prefixEnd_1925543 := by exact prefixLift 1925543
  have htrace : WordTrace (prefixWord ++ tailWord_1925543) baseStart_1925543 baseEnd_1925543 := by
    simpa [prefixWord, tailWord_1925543, baseEnd_1925543] using wordTrace_append hprefix tailTrace_1925543
  have hstable : (prefixWord ++ tailWord_1925543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925543).length < 2 ^ (prefixWord ++ tailWord_1925543).sum := by decide
  have hdescent : baseEnd_1925543 < baseStart_1925543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925553 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 3, 4]
def baseStart_1925553 : Nat := 118140960795 + 1925553 * 2 ^ 59
def prefixEnd_1925553 : Nat := 4983230072969 + 3 ^ 40 * 1925553 * 2
def baseEnd_1925553 : Nat := 329578071569003332910683

theorem tailTrace_1925553 : CollatzResearch.WordTrace tailWord_1925553 prefixEnd_1925553 329578071569003332910683 := by
  unfold tailWord_1925553
  simp only [CollatzResearch.WordTrace]
  refine ⟨70230687593057814115765313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46820458395371876077176875 70230687593057814115765313)
  ·
    refine ⟨52673015694793360586823985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70230687593057814115765313 52673015694793360586823985)
    ·
      refine ⟨39504761771095020440117989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52673015694793360586823985 39504761771095020440117989)
      ·
        refine ⟨7407142832080316332522123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39504761771095020440117989 7407142832080316332522123)
        ·
          refine ⟨11110714248120474498783185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407142832080316332522123 11110714248120474498783185)
          ·
            refine ⟨8333035686090355874087389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11110714248120474498783185 8333035686090355874087389)
            ·
              refine ⟨3124888382283883452782771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8333035686090355874087389 3124888382283883452782771)
              ·
                refine ⟨4687332573425825179174157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124888382283883452782771 4687332573425825179174157)
                ·
                  refine ⟨1757749715034684442190309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4687332573425825179174157 1757749715034684442190309)
                  ·
                    refine ⟨329578071569003332910683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1757749715034684442190309 329578071569003332910683)
                    ·
                      rfl

theorem cell23_1925553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_1925553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925553 prefixEnd_1925553 := by exact prefixLift 1925553
  have htrace : WordTrace (prefixWord ++ tailWord_1925553) baseStart_1925553 baseEnd_1925553 := by
    simpa [prefixWord, tailWord_1925553, baseEnd_1925553] using wordTrace_append hprefix tailTrace_1925553
  have hstable : (prefixWord ++ tailWord_1925553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925553).length < 2 ^ (prefixWord ++ tailWord_1925553).sum := by decide
  have hdescent : baseEnd_1925553 < baseStart_1925553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925580 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1925580 : Nat := 118140960795 + 1925580 * 2 ^ 59
def prefixEnd_1925580 : Nat := 4983230072969 + 3 ^ 40 * 1925580 * 2
def baseEnd_1925580 : Nat := 988748078684681393094425

theorem tailTrace_1925580 : CollatzResearch.WordTrace tailWord_1925580 prefixEnd_1925580 988748078684681393094425 := by
  unfold tailWord_1925580
  simp only [CollatzResearch.WordTrace]
  refine ⟨35115836181979998863499097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46821114909306665151332129 35115836181979998863499097)
  ·
    refine ⟨26336877136484999147624323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35115836181979998863499097 26336877136484999147624323)
    ·
      refine ⟨39505315704727498721436485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26336877136484999147624323 39505315704727498721436485)
      ·
        refine ⟨7407246694636406010269341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39505315704727498721436485 7407246694636406010269341)
        ·
          refine ⟨2777717510488652253851003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7407246694636406010269341 2777717510488652253851003)
          ·
            refine ⟨4166576265732978380776505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777717510488652253851003 4166576265732978380776505)
            ·
              refine ⟨3124932199299733785582379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166576265732978380776505 3124932199299733785582379)
              ·
                refine ⟨4687398298949600678373569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124932199299733785582379 4687398298949600678373569)
                ·
                  refine ⟨3515548724212200508780177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687398298949600678373569 3515548724212200508780177)
                  ·
                    refine ⟨2636661543159150381585133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515548724212200508780177 2636661543159150381585133)
                    ·
                      refine ⟨988748078684681393094425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2636661543159150381585133 988748078684681393094425)
                      ·
                        rfl

theorem cell23_1925580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1925580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925580 prefixEnd_1925580 := by exact prefixLift 1925580
  have htrace : WordTrace (prefixWord ++ tailWord_1925580) baseStart_1925580 baseEnd_1925580 := by
    simpa [prefixWord, tailWord_1925580, baseEnd_1925580] using wordTrace_append hprefix tailTrace_1925580
  have hstable : (prefixWord ++ tailWord_1925580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925580).length < 2 ^ (prefixWord ++ tailWord_1925580).sum := by decide
  have hdescent : baseEnd_1925580 < baseStart_1925580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925613 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1925613 : Nat := 118140960795 + 1925613 * 2 ^ 59
def prefixEnd_1925613 : Nat := 4983230072969 + 3 ^ 40 * 1925613 * 2
def baseEnd_1925613 : Nat := 329588341182093254660591

theorem tailTrace_1925613 : CollatzResearch.WordTrace tailWord_1925613 prefixEnd_1925613 329588341182093254660591 := by
  unfold tailWord_1925613
  simp only [CollatzResearch.WordTrace]
  refine ⟨70232875972840444362949493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46821917315226962908632995 70232875972840444362949493)
  ·
    refine ⟨6584332122453791659026515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70232875972840444362949493 6584332122453791659026515)
    ·
      refine ⟨9876498183680687488539773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584332122453791659026515 9876498183680687488539773)
      ·
        refine ⟨3703686818880257808202415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9876498183680687488539773 3703686818880257808202415)
        ·
          refine ⟨5555530228320386712303623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703686818880257808202415 5555530228320386712303623)
          ·
            refine ⟨8333295342480580068455435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555530228320386712303623 8333295342480580068455435)
            ·
              refine ⟨12499943013720870102683153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333295342480580068455435 12499943013720870102683153)
              ·
                refine ⟨9374957260290652577012365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12499943013720870102683153 9374957260290652577012365)
                ·
                  refine ⟨3515608972608994716379637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9374957260290652577012365 3515608972608994716379637)
                  ·
                    refine ⟨329588341182093254660591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3515608972608994716379637 329588341182093254660591)
                    ·
                      rfl

theorem cell23_1925613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1925613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925613 prefixEnd_1925613 := by exact prefixLift 1925613
  have htrace : WordTrace (prefixWord ++ tailWord_1925613) baseStart_1925613 baseEnd_1925613 := by
    simpa [prefixWord, tailWord_1925613, baseEnd_1925613] using wordTrace_append hprefix tailTrace_1925613
  have hstable : (prefixWord ++ tailWord_1925613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925613).length < 2 ^ (prefixWord ++ tailWord_1925613).sum := by decide
  have hdescent : baseEnd_1925613 < baseStart_1925613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925616 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_1925616 : Nat := 118140960795 + 1925616 * 2 ^ 59
def prefixEnd_1925616 : Nat := 4983230072969 + 3 ^ 40 * 1925616 * 2
def baseEnd_1925616 : Nat := 988766563988243252244259

theorem tailTrace_1925616 : CollatzResearch.WordTrace tailWord_1925616 prefixEnd_1925616 988766563988243252244259 := by
  unfold tailWord_1925616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35116492695914787937654351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46821990261219717250205801 35116492695914787937654351)
  ·
    refine ⟨52674739043872181906481527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35116492695914787937654351 52674739043872181906481527)
    ·
      refine ⟨79012108565808272859722291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52674739043872181906481527 79012108565808272859722291)
      ·
        refine ⟨118518162848712409289583437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79012108565808272859722291 118518162848712409289583437)
        ·
          refine ⟨44444311068267153483593789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118518162848712409289583437 44444311068267153483593789)
          ·
            refine ⟨16666616650600182556347671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44444311068267153483593789 16666616650600182556347671)
            ·
              refine ⟨24999924975900273834521507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16666616650600182556347671 24999924975900273834521507)
              ·
                refine ⟨37499887463850410751782261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24999924975900273834521507 37499887463850410751782261)
                ·
                  refine ⟨3515614449735976007979587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37499887463850410751782261 3515614449735976007979587)
                  ·
                    refine ⟨5273421674603964011969381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515614449735976007979587 5273421674603964011969381)
                    ·
                      refine ⟨988766563988243252244259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5273421674603964011969381 988766563988243252244259)
                      ·
                        rfl

theorem cell23_1925616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_1925616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925616 prefixEnd_1925616 := by exact prefixLift 1925616
  have htrace : WordTrace (prefixWord ++ tailWord_1925616) baseStart_1925616 baseEnd_1925616 := by
    simpa [prefixWord, tailWord_1925616, baseEnd_1925616] using wordTrace_append hprefix tailTrace_1925616
  have hstable : (prefixWord ++ tailWord_1925616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925616).length < 2 ^ (prefixWord ++ tailWord_1925616).sum := by decide
  have hdescent : baseEnd_1925616 < baseStart_1925616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925633 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1925633 : Nat := 118140960795 + 1925633 * 2 ^ 59
def prefixEnd_1925633 : Nat := 4983230072969 + 3 ^ 40 * 1925633 * 2
def baseEnd_1925633 : Nat := 988775293159369685731681

theorem tailTrace_1925633 : CollatzResearch.WordTrace tailWord_1925633 prefixEnd_1925633 988775293159369685731681 := by
  unfold tailWord_1925633
  simp only [CollatzResearch.WordTrace]
  refine ⟨70233605432767987778677553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46822403621845325185785035 70233605432767987778677553)
  ·
    refine ⟨52675204074575990834008165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70233605432767987778677553 52675204074575990834008165)
    ·
      refine ⟨9876600763982998281376531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52675204074575990834008165 9876600763982998281376531)
      ·
        refine ⟨14814901145974497422064797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876600763982998281376531 14814901145974497422064797)
        ·
          refine ⟨5555587929740436533274299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14814901145974497422064797 5555587929740436533274299)
          ·
            refine ⟨8333381894610654799911449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555587929740436533274299 8333381894610654799911449)
            ·
              refine ⟨6250036420957991099933587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8333381894610654799911449 6250036420957991099933587)
              ·
                refine ⟨9375054631436986649900381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250036420957991099933587 9375054631436986649900381)
                ·
                  refine ⟨3515645486788869993712643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9375054631436986649900381 3515645486788869993712643)
                  ·
                    refine ⟨5273468230183304990568965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515645486788869993712643 5273468230183304990568965)
                    ·
                      refine ⟨988775293159369685731681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5273468230183304990568965 988775293159369685731681)
                      ·
                        rfl

theorem cell23_1925633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1925633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925633 prefixEnd_1925633 := by exact prefixLift 1925633
  have htrace : WordTrace (prefixWord ++ tailWord_1925633) baseStart_1925633 baseEnd_1925633 := by
    simpa [prefixWord, tailWord_1925633, baseEnd_1925633] using wordTrace_append hprefix tailTrace_1925633
  have hstable : (prefixWord ++ tailWord_1925633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925633).length < 2 ^ (prefixWord ++ tailWord_1925633).sum := by decide
  have hdescent : baseEnd_1925633 < baseStart_1925633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925656 : List Nat := [2, 1, 2, 3, 3, 2, 10]
def baseStart_1925656 : Nat := 118140960795 + 1925656 * 2 ^ 59
def prefixEnd_1925656 : Nat := 4983230072969 + 3 ^ 40 * 1925656 * 2
def baseEnd_1925656 : Nat := 12207248187832383898075

theorem tailTrace_1925656 : CollatzResearch.WordTrace tailWord_1925656 prefixEnd_1925656 12207248187832383898075 := by
  unfold tailWord_1925656
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117222155842331353382411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46822962874456441804509881 35117222155842331353382411)
  ·
    refine ⟨52675833233763497030073617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35117222155842331353382411 52675833233763497030073617)
    ·
      refine ⟨39506874925322622772555213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52675833233763497030073617 39506874925322622772555213)
      ·
        refine ⟨14815078096995983539708205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39506874925322622772555213 14815078096995983539708205)
        ·
          refine ⟨5555654286373493827390577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14815078096995983539708205 5555654286373493827390577)
          ·
            refine ⟨4166740714780120370542933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5555654286373493827390577 4166740714780120370542933)
            ·
              refine ⟨12207248187832383898075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4166740714780120370542933 12207248187832383898075)
              ·
                rfl

theorem cell23_1925656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 10].length) (baseStart_1925656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925656 prefixEnd_1925656 := by exact prefixLift 1925656
  have htrace : WordTrace (prefixWord ++ tailWord_1925656) baseStart_1925656 baseEnd_1925656 := by
    simpa [prefixWord, tailWord_1925656, baseEnd_1925656] using wordTrace_append hprefix tailTrace_1925656
  have hstable : (prefixWord ++ tailWord_1925656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925656).length < 2 ^ (prefixWord ++ tailWord_1925656).sum := by decide
  have hdescent : baseEnd_1925656 < baseStart_1925656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925660 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1925660 : Nat := 118140960795 + 1925660 * 2 ^ 59
def prefixEnd_1925660 : Nat := 4983230072969 + 3 ^ 40 * 1925660 * 2
def baseEnd_1925660 : Nat := 329596385712347026698019

theorem tailTrace_1925660 : CollatzResearch.WordTrace tailWord_1925660 prefixEnd_1925660 329596385712347026698019 := by
  unfold tailWord_1925660
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117295101835085694955217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46823060135780114259940289 35117295101835085694955217)
  ·
    refine ⟨26337971326376314271216413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35117295101835085694955217 26337971326376314271216413)
    ·
      refine ⟨9876739247391117851706155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26337971326376314271216413 9876739247391117851706155)
      ·
        refine ⟨14815108871086676777559233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876739247391117851706155 14815108871086676777559233)
        ·
          refine ⟨11111331653315007583169425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14815108871086676777559233 11111331653315007583169425)
          ·
            refine ⟨8333498739986255687377069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11111331653315007583169425 8333498739986255687377069)
            ·
              refine ⟨3125062027494845882766401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8333498739986255687377069 3125062027494845882766401)
              ·
                refine ⟨2343796520621134412074801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125062027494845882766401 2343796520621134412074801)
                ·
                  refine ⟨1757847390465850809056101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343796520621134412074801 1757847390465850809056101)
                  ·
                    refine ⟨329596385712347026698019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1757847390465850809056101 329596385712347026698019)
                    ·
                      rfl

theorem cell23_1925660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1925660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925660 prefixEnd_1925660 := by exact prefixLift 1925660
  have htrace : WordTrace (prefixWord ++ tailWord_1925660) baseStart_1925660 baseEnd_1925660 := by
    simpa [prefixWord, tailWord_1925660, baseEnd_1925660] using wordTrace_append hprefix tailTrace_1925660
  have hstable : (prefixWord ++ tailWord_1925660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925660).length < 2 ^ (prefixWord ++ tailWord_1925660).sum := by decide
  have hdescent : baseEnd_1925660 < baseStart_1925660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925666 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1925666 : Nat := 118140960795 + 1925666 * 2 ^ 59
def prefixEnd_1925666 : Nat := 4983230072969 + 3 ^ 40 * 1925666 * 2
def baseEnd_1925666 : Nat := 988792238020968056619029

theorem tailTrace_1925666 : CollatzResearch.WordTrace tailWord_1925666 prefixEnd_1925666 988792238020968056619029 := by
  unfold tailWord_1925666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558702260412108603657213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46823206027765622943085901 17558702260412108603657213)
  ·
    refine ⟨6584513347654540726371455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17558702260412108603657213 6584513347654540726371455)
    ·
      refine ⟨9876770021481811089557183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584513347654540726371455 9876770021481811089557183)
      ·
        refine ⟨14815155032222716634335775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876770021481811089557183 14815155032222716634335775)
        ·
          refine ⟨22222732548334074951503663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14815155032222716634335775 22222732548334074951503663)
          ·
            refine ⟨33334098822501112427255495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22222732548334074951503663 33334098822501112427255495)
            ·
              refine ⟨50001148233751668640883243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33334098822501112427255495 50001148233751668640883243)
              ·
                refine ⟨75001722350627502961324865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50001148233751668640883243 75001722350627502961324865)
                ·
                  refine ⟨56251291762970627220993649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75001722350627502961324865 56251291762970627220993649)
                  ·
                    refine ⟨42188468822227970415745237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56251291762970627220993649 42188468822227970415745237)
                    ·
                      refine ⟨988792238020968056619029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42188468822227970415745237 988792238020968056619029)
                      ·
                        rfl

theorem cell23_1925666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1925666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925666 prefixEnd_1925666 := by exact prefixLift 1925666
  have htrace : WordTrace (prefixWord ++ tailWord_1925666) baseStart_1925666 baseEnd_1925666 := by
    simpa [prefixWord, tailWord_1925666, baseEnd_1925666] using wordTrace_append hprefix tailTrace_1925666
  have hstable : (prefixWord ++ tailWord_1925666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925666).length < 2 ^ (prefixWord ++ tailWord_1925666).sum := by decide
  have hdescent : baseEnd_1925666 < baseStart_1925666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925667 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 3, 2, 2]
def baseStart_1925667 : Nat := 118140960795 + 1925667 * 2 ^ 59
def prefixEnd_1925667 : Nat := 4983230072969 + 3 ^ 40 * 1925667 * 2
def baseEnd_1925667 : Nat := 988792751501622552706525

theorem tailTrace_1925667 : CollatzResearch.WordTrace tailWord_1925667 prefixEnd_1925667 988792751501622552706525 := by
  unfold tailWord_1925667
  simp only [CollatzResearch.WordTrace]
  refine ⟨70234845514644811585415255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46823230343096541056943503 70234845514644811585415255)
  ·
    refine ⟨105352268271967217378122883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70234845514644811585415255 105352268271967217378122883)
    ·
      refine ⟨158028402407950826067184325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105352268271967217378122883 158028402407950826067184325)
      ·
        refine ⟨29630325451490779887597061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158028402407950826067184325 29630325451490779887597061)
        ·
          refine ⟨5555686022154521228924449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29630325451490779887597061 5555686022154521228924449)
          ·
            refine ⟨4166764516615890921693337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5555686022154521228924449 4166764516615890921693337)
            ·
              refine ⟨3125073387461918191270003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166764516615890921693337 3125073387461918191270003)
              ·
                refine ⟨4687610081192877286905005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125073387461918191270003 4687610081192877286905005)
                ·
                  refine ⟨1757853780447328982589377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4687610081192877286905005 1757853780447328982589377)
                  ·
                    refine ⟨1318390335335496736942033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1757853780447328982589377 1318390335335496736942033)
                    ·
                      refine ⟨988792751501622552706525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318390335335496736942033 988792751501622552706525)
                      ·
                        rfl

theorem cell23_1925667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_1925667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925667 prefixEnd_1925667 := by exact prefixLift 1925667
  have htrace : WordTrace (prefixWord ++ tailWord_1925667) baseStart_1925667 baseEnd_1925667 := by
    simpa [prefixWord, tailWord_1925667, baseEnd_1925667] using wordTrace_append hprefix tailTrace_1925667
  have hstable : (prefixWord ++ tailWord_1925667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925667).length < 2 ^ (prefixWord ++ tailWord_1925667).sum := by decide
  have hdescent : baseEnd_1925667 < baseStart_1925667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925684 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1925684 : Nat := 118140960795 + 1925684 * 2 ^ 59
def prefixEnd_1925684 : Nat := 4983230072969 + 3 ^ 40 * 1925684 * 2
def baseEnd_1925684 : Nat := 988801480672748986193947

theorem tailTrace_1925684 : CollatzResearch.WordTrace tailWord_1925684 prefixEnd_1925684 988801480672748986193947 := by
  unfold tailWord_1925684
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117732777791611744392053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46823643703722148992522737 35117732777791611744392053)
  ·
    refine ⟨3292287447917963601036755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35117732777791611744392053 3292287447917963601036755)
    ·
      refine ⟨4938431171876945401555133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292287447917963601036755 4938431171876945401555133)
      ·
        refine ⟨1851911689453854525583175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4938431171876945401555133 1851911689453854525583175)
        ·
          refine ⟨2777867534180781788374763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851911689453854525583175 2777867534180781788374763)
          ·
            refine ⟨4166801301271172682562145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777867534180781788374763 4166801301271172682562145)
            ·
              refine ⟨3125100975953379511921609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166801301271172682562145 3125100975953379511921609)
              ·
                refine ⟨2343825731965034633941207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125100975953379511921609 2343825731965034633941207)
                ·
                  refine ⟨3515738597947551950911811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343825731965034633941207 3515738597947551950911811)
                  ·
                    refine ⟨5273607896921327926367717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515738597947551950911811 5273607896921327926367717)
                    ·
                      refine ⟨988801480672748986193947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5273607896921327926367717 988801480672748986193947)
                      ·
                        rfl

theorem cell23_1925684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1925684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925684 prefixEnd_1925684 := by exact prefixLift 1925684
  have htrace : WordTrace (prefixWord ++ tailWord_1925684) baseStart_1925684 baseEnd_1925684 := by
    simpa [prefixWord, tailWord_1925684, baseEnd_1925684] using wordTrace_append hprefix tailTrace_1925684
  have hstable : (prefixWord ++ tailWord_1925684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925684).length < 2 ^ (prefixWord ++ tailWord_1925684).sum := by decide
  have hdescent : baseEnd_1925684 < baseStart_1925684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925696 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1925696 : Nat := 118140960795 + 1925696 * 2 ^ 59
def prefixEnd_1925696 : Nat := 4983230072969 + 3 ^ 40 * 1925696 * 2
def baseEnd_1925696 : Nat := 988807642440602939243891

theorem tailTrace_1925696 : CollatzResearch.WordTrace tailWord_1925696 prefixEnd_1925696 988807642440602939243891 := by
  unfold tailWord_1925696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117951615769874769110471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46823935487693166358813961 35117951615769874769110471)
  ·
    refine ⟨52676927423654812153665707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35117951615769874769110471 52676927423654812153665707)
    ·
      refine ⟨79015391135482218230498561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52676927423654812153665707 79015391135482218230498561)
      ·
        refine ⟨59261543351611663672873921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79015391135482218230498561 59261543351611663672873921)
        ·
          refine ⟨44446157513708747754655441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59261543351611663672873921 44446157513708747754655441)
          ·
            refine ⟨33334618135281560815991581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44446157513708747754655441 33334618135281560815991581)
            ·
              refine ⟨12500481800730585305996843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33334618135281560815991581 12500481800730585305996843)
              ·
                refine ⟨18750722701095877958995265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12500481800730585305996843 18750722701095877958995265)
                ·
                  refine ⟨14063042025821908469246449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18750722701095877958995265 14063042025821908469246449)
                  ·
                    refine ⟨10547281519366431351934837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14063042025821908469246449 10547281519366431351934837)
                    ·
                      refine ⟨988807642440602939243891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10547281519366431351934837 988807642440602939243891)
                      ·
                        rfl

theorem cell23_1925696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1925696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925696 prefixEnd_1925696 := by exact prefixLift 1925696
  have htrace : WordTrace (prefixWord ++ tailWord_1925696) baseStart_1925696 baseEnd_1925696 := by
    simpa [prefixWord, tailWord_1925696, baseEnd_1925696] using wordTrace_append hprefix tailTrace_1925696
  have hstable : (prefixWord ++ tailWord_1925696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925696).length < 2 ^ (prefixWord ++ tailWord_1925696).sum := by decide
  have hdescent : baseEnd_1925696 < baseStart_1925696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925744 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 1, 3, 2]
def baseStart_1925744 : Nat := 118140960795 + 1925744 * 2 ^ 59
def prefixEnd_1925744 : Nat := 4983230072969 + 3 ^ 40 * 1925744 * 2
def baseEnd_1925744 : Nat := 988832289512018751443671

theorem tailTrace_1925744 : CollatzResearch.WordTrace tailWord_1925744 prefixEnd_1925744 988832289512018751443671 := by
  unfold tailWord_1925744
  simp only [CollatzResearch.WordTrace]
  refine ⟨35118826967682926867984143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46825102623577235823978857 35118826967682926867984143)
  ·
    refine ⟨52678240451524390301976215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35118826967682926867984143 52678240451524390301976215)
    ·
      refine ⟨79017360677286585452964323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52678240451524390301976215 79017360677286585452964323)
      ·
        refine ⟨118526041015929878179446485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79017360677286585452964323 118526041015929878179446485)
        ·
          refine ⟨2777954086310856519830777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118526041015929878179446485 2777954086310856519830777)
          ·
            refine ⟨2083465564733142389873083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777954086310856519830777 2083465564733142389873083)
            ·
              refine ⟨3125198347099713584809625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083465564733142389873083 3125198347099713584809625)
              ·
                refine ⟨2343898760324785188607219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125198347099713584809625 2343898760324785188607219)
                ·
                  refine ⟨3515848140487177782910829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343898760324785188607219 3515848140487177782910829)
                  ·
                    refine ⟨1318443052682691668591561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515848140487177782910829 1318443052682691668591561)
                    ·
                      refine ⟨988832289512018751443671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318443052682691668591561 988832289512018751443671)
                      ·
                        rfl

theorem cell23_1925744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 3, 2].length) (baseStart_1925744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925744 prefixEnd_1925744 := by exact prefixLift 1925744
  have htrace : WordTrace (prefixWord ++ tailWord_1925744) baseStart_1925744 baseEnd_1925744 := by
    simpa [prefixWord, tailWord_1925744, baseEnd_1925744] using wordTrace_append hprefix tailTrace_1925744
  have hstable : (prefixWord ++ tailWord_1925744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925744).length < 2 ^ (prefixWord ++ tailWord_1925744).sum := by decide
  have hdescent : baseEnd_1925744 < baseStart_1925744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925757 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_1925757 : Nat := 118140960795 + 1925757 * 2 ^ 59
def prefixEnd_1925757 : Nat := 4983230072969 + 3 ^ 40 * 1925757 * 2
def baseEnd_1925757 : Nat := 988838964760527200581111

theorem tailTrace_1925757 : CollatzResearch.WordTrace tailWord_1925757 prefixEnd_1925757 988838964760527200581111 := by
  unfold tailWord_1925757
  simp only [CollatzResearch.WordTrace]
  refine ⟨70238128084318756956191525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46825418722879171304127683 70238128084318756956191525)
  ·
    refine ⟨13169649015809766929285911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70238128084318756956191525 13169649015809766929285911)
    ·
      refine ⟨19754473523714650393928867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13169649015809766929285911 19754473523714650393928867)
      ·
        refine ⟨29631710285571975590893301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754473523714650393928867 29631710285571975590893301)
        ·
          refine ⟨2777972839272372711646247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29631710285571975590893301 2777972839272372711646247)
          ·
            refine ⟨4166959258908559067469371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777972839272372711646247 4166959258908559067469371)
            ·
              refine ⟨6250438888362838601204057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166959258908559067469371 6250438888362838601204057)
              ·
                refine ⟨4687829166272128950903043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250438888362838601204057 4687829166272128950903043)
                ·
                  refine ⟨7031743749408193426354565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687829166272128950903043 7031743749408193426354565)
                  ·
                    refine ⟨1318451953014036267441481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031743749408193426354565 1318451953014036267441481)
                    ·
                      refine ⟨988838964760527200581111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318451953014036267441481 988838964760527200581111)
                      ·
                        rfl

theorem cell23_1925757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_1925757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925757 prefixEnd_1925757 := by exact prefixLift 1925757
  have htrace : WordTrace (prefixWord ++ tailWord_1925757) baseStart_1925757 baseEnd_1925757 := by
    simpa [prefixWord, tailWord_1925757, baseEnd_1925757] using wordTrace_append hprefix tailTrace_1925757
  have hstable : (prefixWord ++ tailWord_1925757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925757).length < 2 ^ (prefixWord ++ tailWord_1925757).sum := by decide
  have hdescent : baseEnd_1925757 < baseStart_1925757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925774 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1925774 : Nat := 118140960795 + 1925774 * 2 ^ 59
def prefixEnd_1925774 : Nat := 4983230072969 + 3 ^ 40 * 1925774 * 2
def baseEnd_1925774 : Nat := 988847693931653634068533

theorem tailTrace_1925774 : CollatzResearch.WordTrace tailWord_1925774 prefixEnd_1925774 988847693931653634068533 := by
  unfold tailWord_1925774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8779843515657146107445047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46825832083504779239706917 8779843515657146107445047)
  ·
    refine ⟨13169765273485719161167571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8779843515657146107445047 13169765273485719161167571)
    ·
      refine ⟨19754647910228578741751357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13169765273485719161167571 19754647910228578741751357)
      ·
        refine ⟨7407992966335717028156759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19754647910228578741751357 7407992966335717028156759)
        ·
          refine ⟨11111989449503575542235139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407992966335717028156759 11111989449503575542235139)
          ·
            refine ⟨16667984174255363313352709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111989449503575542235139 16667984174255363313352709)
            ·
              refine ⟨3125247032672880621253633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16667984174255363313352709 3125247032672880621253633)
              ·
                refine ⟨2343935274504660465940225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125247032672880621253633 2343935274504660465940225)
                ·
                  refine ⟨1757951455878495349455169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343935274504660465940225 1757951455878495349455169)
                  ·
                    refine ⟨1318463591908871512091377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1757951455878495349455169 1318463591908871512091377)
                    ·
                      refine ⟨988847693931653634068533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318463591908871512091377 988847693931653634068533)
                      ·
                        rfl

theorem cell23_1925774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1925774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925774 prefixEnd_1925774 := by exact prefixLift 1925774
  have htrace : WordTrace (prefixWord ++ tailWord_1925774) baseStart_1925774 baseEnd_1925774 := by
    simpa [prefixWord, tailWord_1925774, baseEnd_1925774] using wordTrace_append hprefix tailTrace_1925774
  have hstable : (prefixWord ++ tailWord_1925774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925774).length < 2 ^ (prefixWord ++ tailWord_1925774).sum := by decide
  have hdescent : baseEnd_1925774 < baseStart_1925774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925776 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_1925776 : Nat := 118140960795 + 1925776 * 2 ^ 59
def prefixEnd_1925776 : Nat := 4983230072969 + 3 ^ 40 * 1925776 * 2
def baseEnd_1925776 : Nat := 329616240297654208747841

theorem tailTrace_1925776 : CollatzResearch.WordTrace tailWord_1925776 prefixEnd_1925776 329616240297654208747841 := by
  unfold tailWord_1925776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35119410535624961600566591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46825880714166615467422121 35119410535624961600566591)
  ·
    refine ⟨52679115803437442400849887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35119410535624961600566591 52679115803437442400849887)
    ·
      refine ⟨79018673705156163601274831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52679115803437442400849887 79018673705156163601274831)
      ·
        refine ⟨118528010557734245401912247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79018673705156163601274831 118528010557734245401912247)
        ·
          refine ⟨177792015836601368102868371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118528010557734245401912247 177792015836601368102868371)
          ·
            refine ⟨266688023754902052154302557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177792015836601368102868371 266688023754902052154302557)
            ·
              refine ⟨100008008908088269557863459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266688023754902052154302557 100008008908088269557863459)
              ·
                refine ⟨150012013362132404336795189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100008008908088269557863459 150012013362132404336795189)
                ·
                  refine ⟨14063626252699912906574549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150012013362132404336795189 14063626252699912906574549)
                  ·
                    refine ⟨329616240297654208747841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14063626252699912906574549 329616240297654208747841)
                    ·
                      rfl

theorem cell23_1925776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_1925776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925776 prefixEnd_1925776 := by exact prefixLift 1925776
  have htrace : WordTrace (prefixWord ++ tailWord_1925776) baseStart_1925776 baseEnd_1925776 := by
    simpa [prefixWord, tailWord_1925776, baseEnd_1925776] using wordTrace_append hprefix tailTrace_1925776
  have hstable : (prefixWord ++ tailWord_1925776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925776).length < 2 ^ (prefixWord ++ tailWord_1925776).sum := by decide
  have hdescent : baseEnd_1925776 < baseStart_1925776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925825 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1925825 : Nat := 118140960795 + 1925825 * 2 ^ 59
def prefixEnd_1925825 : Nat := 4983230072969 + 3 ^ 40 * 1925825 * 2
def baseEnd_1925825 : Nat := 988873881445032934530799

theorem tailTrace_1925825 : CollatzResearch.WordTrace tailWord_1925825 prefixEnd_1925825 988873881445032934530799 := by
  unfold tailWord_1925825
  simp only [CollatzResearch.WordTrace]
  refine ⟨70240608248072404569666929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46827072165381603046444619 70240608248072404569666929)
  ·
    refine ⟨52680456186054303427250197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70240608248072404569666929 52680456186054303427250197)
    ·
      refine ⟨2469396383721295473152353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52680456186054303427250197 2469396383721295473152353)
      ·
        refine ⟨1852047287790971604864265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469396383721295473152353 1852047287790971604864265)
        ·
          refine ⟨1389035465843228703648199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852047287790971604864265 1389035465843228703648199)
          ·
            refine ⟨2083553198764843055472299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389035465843228703648199 2083553198764843055472299)
            ·
              refine ⟨3125329798147264583208449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083553198764843055472299 3125329798147264583208449)
              ·
                refine ⟨2343997348610448437406337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125329798147264583208449 2343997348610448437406337)
                ·
                  refine ⟨1757998011457836328054753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2343997348610448437406337 1757998011457836328054753)
                  ·
                    refine ⟨1318498508593377246041065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1757998011457836328054753 1318498508593377246041065)
                    ·
                      refine ⟨988873881445032934530799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318498508593377246041065 988873881445032934530799)
                      ·
                        rfl

theorem cell23_1925825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1925825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925825 prefixEnd_1925825 := by exact prefixLift 1925825
  have htrace : WordTrace (prefixWord ++ tailWord_1925825) baseStart_1925825 baseEnd_1925825 := by
    simpa [prefixWord, tailWord_1925825, baseEnd_1925825] using wordTrace_append hprefix tailTrace_1925825
  have hstable : (prefixWord ++ tailWord_1925825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925825).length < 2 ^ (prefixWord ++ tailWord_1925825).sum := by decide
  have hdescent : baseEnd_1925825 < baseStart_1925825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925874 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_1925874 : Nat := 118140960795 + 1925874 * 2 ^ 59
def prefixEnd_1925874 : Nat := 4983230072969 + 3 ^ 40 * 1925874 * 2
def baseEnd_1925874 : Nat := 329633013999034414272691

theorem tailTrace_1925874 : CollatzResearch.WordTrace tailWord_1925874 prefixEnd_1925874 329633013999034414272691 := by
  unfold tailWord_1925874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560598856223721484550169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46828263616596590625467117 17560598856223721484550169)
  ·
    refine ⟨13170449142167791113412627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17560598856223721484550169 13170449142167791113412627)
    ·
      refine ⟨19755673713251686670118941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13170449142167791113412627 19755673713251686670118941)
      ·
        refine ⟨7408377642469382501294603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19755673713251686670118941 7408377642469382501294603)
        ·
          refine ⟨11112566463704073751941905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408377642469382501294603 11112566463704073751941905)
          ·
            refine ⟨8334424847778055313956429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11112566463704073751941905 8334424847778055313956429)
            ·
              refine ⟨3125409317916770742733661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8334424847778055313956429 3125409317916770742733661)
              ·
                refine ⟨1172028494218789028525123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125409317916770742733661 1172028494218789028525123)
                ·
                  refine ⟨1758042741328183542787685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172028494218789028525123 1758042741328183542787685)
                  ·
                    refine ⟨329633013999034414272691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758042741328183542787685 329633013999034414272691)
                    ·
                      rfl

theorem cell23_1925874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_1925874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925874 prefixEnd_1925874 := by exact prefixLift 1925874
  have htrace : WordTrace (prefixWord ++ tailWord_1925874) baseStart_1925874 baseEnd_1925874 := by
    simpa [prefixWord, tailWord_1925874, baseEnd_1925874] using wordTrace_append hprefix tailTrace_1925874
  have hstable : (prefixWord ++ tailWord_1925874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925874).length < 2 ^ (prefixWord ++ tailWord_1925874).sum := by decide
  have hdescent : baseEnd_1925874 < baseStart_1925874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925897 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 3]
def baseStart_1925897 : Nat := 118140960795 + 1925897 * 2 ^ 59
def prefixEnd_1925897 : Nat := 4983230072969 + 3 ^ 40 * 1925897 * 2
def baseEnd_1925897 : Nat := 988910852052156652830467

theorem tailTrace_1925897 : CollatzResearch.WordTrace tailWord_1925897 prefixEnd_1925897 988910852052156652830467 := by
  unfold tailWord_1925897
  simp only [CollatzResearch.WordTrace]
  refine ⟨70243234303811560866287945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46828822869207707244191963 70243234303811560866287945)
  ·
    refine ⟨52682425727858670649715959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70243234303811560866287945 52682425727858670649715959)
    ·
      refine ⟨79023638591788005974573939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52682425727858670649715959 79023638591788005974573939)
      ·
        refine ⟨118535457887682008961860909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79023638591788005974573939 118535457887682008961860909)
        ·
          refine ⟨44450796707880753360697841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118535457887682008961860909 44450796707880753360697841)
          ·
            refine ⟨33338097530910565020523381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44450796707880753360697841 33338097530910565020523381)
            ·
              refine ⟨3125446643522865470674067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33338097530910565020523381 3125446643522865470674067)
              ·
                refine ⟨4688169965284298206011101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125446643522865470674067 4688169965284298206011101)
                ·
                  refine ⟨1758063736981611827254163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4688169965284298206011101 1758063736981611827254163)
                  ·
                    refine ⟨2637095605472417740881245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758063736981611827254163 2637095605472417740881245)
                    ·
                      refine ⟨988910852052156652830467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637095605472417740881245 988910852052156652830467)
                      ·
                        rfl

theorem cell23_1925897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_1925897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925897 prefixEnd_1925897 := by exact prefixLift 1925897
  have htrace : WordTrace (prefixWord ++ tailWord_1925897) baseStart_1925897 baseEnd_1925897 := by
    simpa [prefixWord, tailWord_1925897, baseEnd_1925897] using wordTrace_append hprefix tailTrace_1925897
  have hstable : (prefixWord ++ tailWord_1925897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925897).length < 2 ^ (prefixWord ++ tailWord_1925897).sum := by decide
  have hdescent : baseEnd_1925897 < baseStart_1925897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925987 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1925987 : Nat := 118140960795 + 1925987 * 2 ^ 59
def prefixEnd_1925987 : Nat := 4983230072969 + 3 ^ 40 * 1925987 * 2
def baseEnd_1925987 : Nat := 988957065311061300705053

theorem tailTrace_1925987 : CollatzResearch.WordTrace tailWord_1925987 prefixEnd_1925987 988957065311061300705053 := by
  unfold tailWord_1925987
  simp only [CollatzResearch.WordTrace]
  refine ⟨70246516873485506237064215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46831011248990337491376143 70246516873485506237064215)
  ·
    refine ⟨105369775310228259355596323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70246516873485506237064215 105369775310228259355596323)
    ·
      refine ⟨158054662965342389033394485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105369775310228259355596323 158054662965342389033394485)
      ·
        refine ⟨14817624653000848971880733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158054662965342389033394485 14817624653000848971880733)
        ·
          refine ⟨5556609244875318364455275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14817624653000848971880733 5556609244875318364455275)
          ·
            refine ⟨8334913867312977546682913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556609244875318364455275 8334913867312977546682913)
            ·
              refine ⟨6251185400484733160012185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8334913867312977546682913 6251185400484733160012185)
              ·
                refine ⟨4688389050363549870009139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251185400484733160012185 4688389050363549870009139)
                ·
                  refine ⟨7032583575545324805013709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688389050363549870009139 7032583575545324805013709)
                  ·
                    refine ⟨2637218840829496801880141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7032583575545324805013709 2637218840829496801880141)
                    ·
                      refine ⟨988957065311061300705053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637218840829496801880141 988957065311061300705053)
                      ·
                        rfl

theorem cell23_1925987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1925987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925987 prefixEnd_1925987 := by exact prefixLift 1925987
  have htrace : WordTrace (prefixWord ++ tailWord_1925987) baseStart_1925987 baseEnd_1925987 := by
    simpa [prefixWord, tailWord_1925987, baseEnd_1925987] using wordTrace_append hprefix tailTrace_1925987
  have hstable : (prefixWord ++ tailWord_1925987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925987).length < 2 ^ (prefixWord ++ tailWord_1925987).sum := by decide
  have hdescent : baseEnd_1925987 < baseStart_1925987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925988 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_1925988 : Nat := 118140960795 + 1925988 * 2 ^ 59
def prefixEnd_1925988 : Nat := 4983230072969 + 3 ^ 40 * 1925988 * 2
def baseEnd_1925988 : Nat := 988957578791715796792549

theorem tailTrace_1925988 : CollatzResearch.WordTrace tailWord_1925988 prefixEnd_1925988 988957578791715796792549 := by
  unfold tailWord_1925988
  simp only [CollatzResearch.WordTrace]
  refine ⟨35123276673240941703925309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46831035564321255605233745 35123276673240941703925309)
  ·
    refine ⟨13171228752465353138971991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35123276673240941703925309 13171228752465353138971991)
    ·
      refine ⟨19756843128698029708457987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13171228752465353138971991 19756843128698029708457987)
      ·
        refine ⟨29635264693047044562686981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19756843128698029708457987 29635264693047044562686981)
        ·
          refine ⟨5556612129946320855503809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29635264693047044562686981 5556612129946320855503809)
          ·
            refine ⟨4167459097459740641627857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5556612129946320855503809 4167459097459740641627857)
            ·
              refine ⟨3125594323094805481220893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167459097459740641627857 3125594323094805481220893)
              ·
                refine ⟨1172097871160552055457835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125594323094805481220893 1172097871160552055457835)
                ·
                  refine ⟨1758146806740828083186753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172097871160552055457835 1758146806740828083186753)
                  ·
                    refine ⟨1318610105055621062390065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1758146806740828083186753 1318610105055621062390065)
                    ·
                      refine ⟨988957578791715796792549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318610105055621062390065 988957578791715796792549)
                      ·
                        rfl

theorem cell23_1925988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_1925988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925988 prefixEnd_1925988 := by exact prefixLift 1925988
  have htrace : WordTrace (prefixWord ++ tailWord_1925988) baseStart_1925988 baseEnd_1925988 := by
    simpa [prefixWord, tailWord_1925988, baseEnd_1925988] using wordTrace_append hprefix tailTrace_1925988
  have hstable : (prefixWord ++ tailWord_1925988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925988).length < 2 ^ (prefixWord ++ tailWord_1925988).sum := by decide
  have hdescent : baseEnd_1925988 < baseStart_1925988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925991 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_1925991 : Nat := 118140960795 + 1925991 * 2 ^ 59
def prefixEnd_1925991 : Nat := 4983230072969 + 3 ^ 40 * 1925991 * 2
def baseEnd_1925991 : Nat := 988959119233679285055035

theorem tailTrace_1925991 : CollatzResearch.WordTrace tailWord_1925991 prefixEnd_1925991 988959119233679285055035 := by
  unfold tailWord_1925991
  simp only [CollatzResearch.WordTrace]
  refine ⟨70246662765471014920209827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46831108510314009946806551 70246662765471014920209827)
  ·
    refine ⟨105369994148206522380314741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70246662765471014920209827 105369994148206522380314741)
    ·
      refine ⟨9878436951394361473154507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105369994148206522380314741 9878436951394361473154507)
      ·
        refine ⟨14817655427091542209731761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9878436951394361473154507 14817655427091542209731761)
        ·
          refine ⟨11113241570318656657298821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14817655427091542209731761 11113241570318656657298821)
          ·
            refine ⟨2083732794434748123243529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11113241570318656657298821 2083732794434748123243529)
            ·
              refine ⟨1562799595826061092432647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083732794434748123243529 1562799595826061092432647)
              ·
                refine ⟨2344199393739091638648971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562799595826061092432647 2344199393739091638648971)
                ·
                  refine ⟨3516299090608637457973457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344199393739091638648971 3516299090608637457973457)
                  ·
                    refine ⟨2637224317956478093480093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3516299090608637457973457 2637224317956478093480093)
                    ·
                      refine ⟨988959119233679285055035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637224317956478093480093 988959119233679285055035)
                      ·
                        rfl

theorem cell23_1925991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_1925991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925991 prefixEnd_1925991 := by exact prefixLift 1925991
  have htrace : WordTrace (prefixWord ++ tailWord_1925991) baseStart_1925991 baseEnd_1925991 := by
    simpa [prefixWord, tailWord_1925991, baseEnd_1925991] using wordTrace_append hprefix tailTrace_1925991
  have hstable : (prefixWord ++ tailWord_1925991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925991).length < 2 ^ (prefixWord ++ tailWord_1925991).sum := by decide
  have hdescent : baseEnd_1925991 < baseStart_1925991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925998 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1925998 : Nat := 118140960795 + 1925998 * 2 ^ 59
def prefixEnd_1925998 : Nat := 4983230072969 + 3 ^ 40 * 1925998 * 2
def baseEnd_1925998 : Nat := 329654237866086919222501

theorem tailTrace_1925998 : CollatzResearch.WordTrace tailWord_1925998 prefixEnd_1925998 329654237866086919222501 := by
  unfold tailWord_1925998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780864759555706889464331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46831278717630436743809765 8780864759555706889464331)
  ·
    refine ⟨13171297139333560334196497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8780864759555706889464331 13171297139333560334196497)
    ·
      refine ⟨9878472854500170250647373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13171297139333560334196497 9878472854500170250647373)
      ·
        refine ⟨3704427320437563843992765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9878472854500170250647373 3704427320437563843992765)
        ·
          refine ⟨1389160245164086441497287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3704427320437563843992765 1389160245164086441497287)
          ·
            refine ⟨2083740367746129662245931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389160245164086441497287 2083740367746129662245931)
            ·
              refine ⟨3125610551619194493368897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083740367746129662245931 3125610551619194493368897)
              ·
                refine ⟨2344207913714395870026673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125610551619194493368897 2344207913714395870026673)
                ·
                  refine ⟨1758155935285796902520005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344207913714395870026673 1758155935285796902520005)
                  ·
                    refine ⟨329654237866086919222501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758155935285796902520005 329654237866086919222501)
                    ·
                      rfl

theorem cell23_1925998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1925998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1925998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1925998 prefixEnd_1925998 := by exact prefixLift 1925998
  have htrace : WordTrace (prefixWord ++ tailWord_1925998) baseStart_1925998 baseEnd_1925998 := by
    simpa [prefixWord, tailWord_1925998, baseEnd_1925998] using wordTrace_append hprefix tailTrace_1925998
  have hstable : (prefixWord ++ tailWord_1925998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925998).length < 2 ^ (prefixWord ++ tailWord_1925998).sum := by decide
  have hdescent : baseEnd_1925998 < baseStart_1925998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926018 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1926018 : Nat := 118140960795 + 1926018 * 2 ^ 59
def prefixEnd_1926018 : Nat := 4983230072969 + 3 ^ 40 * 1926018 * 2
def baseEnd_1926018 : Nat := 988972983211350679417411

theorem tailTrace_1926018 : CollatzResearch.WordTrace tailWord_1926018 prefixEnd_1926018 988972983211350679417411 := by
  unfold tailWord_1926018
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561911884093299632860677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46831765024248799020961805 17561911884093299632860677)
  ·
    refine ⟨3292858478267493681161377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17561911884093299632860677 3292858478267493681161377)
    ·
      refine ⟨2469643858700620260871033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3292858478267493681161377 2469643858700620260871033)
      ·
        refine ⟨1852232894025465195653275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469643858700620260871033 1852232894025465195653275)
        ·
          refine ⟨2778349341038197793479913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852232894025465195653275 2778349341038197793479913)
          ·
            refine ⟨2083762005778648345109935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778349341038197793479913 2083762005778648345109935)
            ·
              refine ⟨3125643008667972517664903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083762005778648345109935 3125643008667972517664903)
              ·
                refine ⟨4688464513001958776497355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125643008667972517664903 4688464513001958776497355)
                ·
                  refine ⟨7032696769502938164746033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688464513001958776497355 7032696769502938164746033)
                  ·
                    refine ⟨5274522577127203623559525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7032696769502938164746033 5274522577127203623559525)
                    ·
                      refine ⟨988972983211350679417411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5274522577127203623559525 988972983211350679417411)
                      ·
                        rfl

theorem cell23_1926018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1926018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926018 prefixEnd_1926018 := by exact prefixLift 1926018
  have htrace : WordTrace (prefixWord ++ tailWord_1926018) baseStart_1926018 baseEnd_1926018 := by
    simpa [prefixWord, tailWord_1926018, baseEnd_1926018] using wordTrace_append hprefix tailTrace_1926018
  have hstable : (prefixWord ++ tailWord_1926018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926018).length < 2 ^ (prefixWord ++ tailWord_1926018).sum := by decide
  have hdescent : baseEnd_1926018 < baseStart_1926018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926021 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 2, 1, 3]
def baseStart_1926021 : Nat := 118140960795 + 1926021 * 2 ^ 59
def prefixEnd_1926021 : Nat := 4983230072969 + 3 ^ 40 * 1926021 * 2
def baseEnd_1926021 : Nat := 988974523653314167679897

theorem tailTrace_1926021 : CollatzResearch.WordTrace tailWord_1926021 prefixEnd_1926021 988974523653314167679897 := by
  unfold tailWord_1926021
  simp only [CollatzResearch.WordTrace]
  refine ⟨70247756955362330043801917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46831837970241553362534611 70247756955362330043801917)
  ·
    refine ⟨26342908858260873766425719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70247756955362330043801917 26342908858260873766425719)
    ·
      refine ⟨39514363287391310649638579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26342908858260873766425719 39514363287391310649638579)
      ·
        refine ⟨59271544931086965974457869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39514363287391310649638579 59271544931086965974457869)
        ·
          refine ⟨22226829349157612240421701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59271544931086965974457869 22226829349157612240421701)
          ·
            refine ⟨4167530502967052295079069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22226829349157612240421701 4167530502967052295079069)
            ·
              refine ⟨1562823938612644610654651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4167530502967052295079069 1562823938612644610654651)
              ·
                refine ⟨2344235907918966915981977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562823938612644610654651 2344235907918966915981977)
                ·
                  refine ⟨1758176930939225186986483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344235907918966915981977 1758176930939225186986483)
                  ·
                    refine ⟨2637265396408837780479725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758176930939225186986483 2637265396408837780479725)
                    ·
                      refine ⟨988974523653314167679897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637265396408837780479725 988974523653314167679897)
                      ·
                        rfl

theorem cell23_1926021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_1926021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926021 prefixEnd_1926021 := by exact prefixLift 1926021
  have htrace : WordTrace (prefixWord ++ tailWord_1926021) baseStart_1926021 baseEnd_1926021 := by
    simpa [prefixWord, tailWord_1926021, baseEnd_1926021] using wordTrace_append hprefix tailTrace_1926021
  have hstable : (prefixWord ++ tailWord_1926021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926021).length < 2 ^ (prefixWord ++ tailWord_1926021).sum := by decide
  have hdescent : baseEnd_1926021 < baseStart_1926021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926038 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1926038 : Nat := 118140960795 + 1926038 * 2 ^ 59
def prefixEnd_1926038 : Nat := 4983230072969 + 3 ^ 40 * 1926038 * 2
def baseEnd_1926038 : Nat := 988983252824440601167319

theorem tailTrace_1926038 : CollatzResearch.WordTrace tailWord_1926038 prefixEnd_1926038 988983252824440601167319 := by
  unfold tailWord_1926038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390523562268796371698173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46832251330867161298113845 4390523562268796371698173)
  ·
    refine ⟨1646446335850798639386815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4390523562268796371698173 1646446335850798639386815)
    ·
      refine ⟨2469669503776197959080223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646446335850798639386815 2469669503776197959080223)
      ·
        refine ⟨3704504255664296938620335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469669503776197959080223 3704504255664296938620335)
        ·
          refine ⟨5556756383496445407930503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704504255664296938620335 5556756383496445407930503)
          ·
            refine ⟨8335134575244668111895755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556756383496445407930503 8335134575244668111895755)
            ·
              refine ⟨12502701862867002167843633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335134575244668111895755 12502701862867002167843633)
              ·
                refine ⟨9377026397150251625882725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12502701862867002167843633 9377026397150251625882725)
                ·
                  refine ⟨1758192449465672179853011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9377026397150251625882725 1758192449465672179853011)
                  ·
                    refine ⟨2637288674198508269779517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758192449465672179853011 2637288674198508269779517)
                    ·
                      refine ⟨988983252824440601167319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637288674198508269779517 988983252824440601167319)
                      ·
                        rfl

theorem cell23_1926038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1926038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926038 prefixEnd_1926038 := by exact prefixLift 1926038
  have htrace : WordTrace (prefixWord ++ tailWord_1926038) baseStart_1926038 baseEnd_1926038 := by
    simpa [prefixWord, tailWord_1926038, baseEnd_1926038] using wordTrace_append hprefix tailTrace_1926038
  have hstable : (prefixWord ++ tailWord_1926038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926038).length < 2 ^ (prefixWord ++ tailWord_1926038).sum := by decide
  have hdescent : baseEnd_1926038 < baseStart_1926038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926047 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1926047 : Nat := 118140960795 + 1926047 * 2 ^ 59
def prefixEnd_1926047 : Nat := 4983230072969 + 3 ^ 40 * 1926047 * 2
def baseEnd_1926047 : Nat := 988987874150331065954777

theorem tailTrace_1926047 : CollatzResearch.WordTrace tailWord_1926047 prefixEnd_1926047 988987874150331065954777 := by
  unfold tailWord_1926047
  simp only [CollatzResearch.WordTrace]
  refine ⟨70248705253268136484248395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46832470168845424322832263 70248705253268136484248395)
  ·
    refine ⟨105373057879902204726372593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70248705253268136484248395 105373057879902204726372593)
    ·
      refine ⟨79029793409926653544779445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105373057879902204726372593 79029793409926653544779445)
      ·
        refine ⟨7409043132180623769823073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79029793409926653544779445 7409043132180623769823073)
        ·
          refine ⟨5556782349135467827367305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409043132180623769823073 5556782349135467827367305)
          ·
            refine ⟨4167586761851600870525479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5556782349135467827367305 4167586761851600870525479)
            ·
              refine ⟨6251380142777401305788219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167586761851600870525479 6251380142777401305788219)
              ·
                refine ⟨9377070214166101958682329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6251380142777401305788219 9377070214166101958682329)
                ·
                  refine ⟨7032802660624576469011747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377070214166101958682329 7032802660624576469011747)
                  ·
                    refine ⟨10549203990936864703517621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032802660624576469011747 10549203990936864703517621)
                    ·
                      refine ⟨988987874150331065954777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10549203990936864703517621 988987874150331065954777)
                      ·
                        rfl

theorem cell23_1926047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1926047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926047 prefixEnd_1926047 := by exact prefixLift 1926047
  have htrace : WordTrace (prefixWord ++ tailWord_1926047) baseStart_1926047 baseEnd_1926047 := by
    simpa [prefixWord, tailWord_1926047, baseEnd_1926047] using wordTrace_append hprefix tailTrace_1926047
  have hstable : (prefixWord ++ tailWord_1926047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926047).length < 2 ^ (prefixWord ++ tailWord_1926047).sum := by decide
  have hdescent : baseEnd_1926047 < baseStart_1926047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926090 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1926090 : Nat := 118140960795 + 1926090 * 2 ^ 59
def prefixEnd_1926090 : Nat := 4983230072969 + 3 ^ 40 * 1926090 * 2
def baseEnd_1926090 : Nat := 989009953818474397717079

theorem tailTrace_1926090 : CollatzResearch.WordTrace tailWord_1926090 prefixEnd_1926090 989009953818474397717079 := by
  unfold tailWord_1926090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562568398028088707015931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46833515728074903218709149 17562568398028088707015931)
  ·
    refine ⟨26343852597042133060523897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17562568398028088707015931 26343852597042133060523897)
    ·
      refine ⟨19757889447781599795392923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26343852597042133060523897 19757889447781599795392923)
      ·
        refine ⟨29636834171672399693089385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19757889447781599795392923 29636834171672399693089385)
        ·
          refine ⟨22227625628754299769817039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29636834171672399693089385 22227625628754299769817039)
          ·
            refine ⟨33341438443131449654725559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22227625628754299769817039 33341438443131449654725559)
            ·
              refine ⟨50012157664697174482088339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33341438443131449654725559 50012157664697174482088339)
              ·
                refine ⟨75018236497045761723132509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50012157664697174482088339 75018236497045761723132509)
                ·
                  refine ⟨28131838686392160646174691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75018236497045761723132509 28131838686392160646174691)
                  ·
                    refine ⟨42197758029588240969262037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28131838686392160646174691 42197758029588240969262037)
                    ·
                      refine ⟨989009953818474397717079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42197758029588240969262037 989009953818474397717079)
                      ·
                        rfl

theorem cell23_1926090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1926090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926090 prefixEnd_1926090 := by exact prefixLift 1926090
  have htrace : WordTrace (prefixWord ++ tailWord_1926090) baseStart_1926090 baseEnd_1926090 := by
    simpa [prefixWord, tailWord_1926090, baseEnd_1926090] using wordTrace_append hprefix tailTrace_1926090
  have hstable : (prefixWord ++ tailWord_1926090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926090).length < 2 ^ (prefixWord ++ tailWord_1926090).sum := by decide
  have hdescent : baseEnd_1926090 < baseStart_1926090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926097 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 2, 5]
def baseStart_1926097 : Nat := 118140960795 + 1926097 * 2 ^ 59
def prefixEnd_1926097 : Nat := 4983230072969 + 3 ^ 40 * 1926097 * 2
def baseEnd_1926097 : Nat := 329671182727685290109849

theorem tailTrace_1926097 : CollatzResearch.WordTrace tailWord_1926097 prefixEnd_1926097 329671182727685290109849 := by
  unfold tailWord_1926097
  simp only [CollatzResearch.WordTrace]
  refine ⟨70250528903086995023568545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46833685935391330015712363 70250528903086995023568545)
  ·
    refine ⟨52687896677315246267676409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70250528903086995023568545 52687896677315246267676409)
    ·
      refine ⟨39515922507986434700757307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52687896677315246267676409 39515922507986434700757307)
      ·
        refine ⟨59273883761979652051135961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39515922507986434700757307 59273883761979652051135961)
        ·
          refine ⟨44455412821484739038351971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59273883761979652051135961 44455412821484739038351971)
          ·
            refine ⟨66683119232227108557527957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44455412821484739038351971 66683119232227108557527957)
            ·
              refine ⟨3125771214010645713634123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66683119232227108557527957 3125771214010645713634123)
              ·
                refine ⟨4688656821015968570451185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125771214010645713634123 4688656821015968570451185)
                ·
                  refine ⟨3516492615761976427838389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4688656821015968570451185 3516492615761976427838389)
                  ·
                    refine ⟨329671182727685290109849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3516492615761976427838389 329671182727685290109849)
                    ·
                      rfl

theorem cell23_1926097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_1926097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926097 prefixEnd_1926097 := by exact prefixLift 1926097
  have htrace : WordTrace (prefixWord ++ tailWord_1926097) baseStart_1926097 baseEnd_1926097 := by
    simpa [prefixWord, tailWord_1926097, baseEnd_1926097] using wordTrace_append hprefix tailTrace_1926097
  have hstable : (prefixWord ++ tailWord_1926097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926097).length < 2 ^ (prefixWord ++ tailWord_1926097).sum := by decide
  have hdescent : baseEnd_1926097 < baseStart_1926097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926137 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1926137 : Nat := 118140960795 + 1926137 * 2 ^ 59
def prefixEnd_1926137 : Nat := 4983230072969 + 3 ^ 40 * 1926137 * 2
def baseEnd_1926137 : Nat := 989034087409235713829363

theorem tailTrace_1926137 : CollatzResearch.WordTrace tailWord_1926137 prefixEnd_1926137 989034087409235713829363 := by
  unfold tailWord_1926137
  simp only [CollatzResearch.WordTrace]
  refine ⟨70251987822942081855024665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46834658548628054570016443 70251987822942081855024665)
  ·
    refine ⟨52688990867206561391268499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70251987822942081855024665 52688990867206561391268499)
    ·
      refine ⟨79033486300809842086902749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52688990867206561391268499 79033486300809842086902749)
      ·
        refine ⟨29637557362803690782588531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79033486300809842086902749 29637557362803690782588531)
        ·
          refine ⟨44456336044205536173882797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29637557362803690782588531 44456336044205536173882797)
          ·
            refine ⟨16671126016577076065206049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44456336044205536173882797 16671126016577076065206049)
            ·
              refine ⟨12503344512432807048904537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16671126016577076065206049 12503344512432807048904537)
              ·
                refine ⟨9377508384324605286678403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12503344512432807048904537 9377508384324605286678403)
                ·
                  refine ⟨14066262576486907930017605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9377508384324605286678403 14066262576486907930017605)
                  ·
                    refine ⟨2637424233091295236878301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14066262576486907930017605 2637424233091295236878301)
                    ·
                      refine ⟨989034087409235713829363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637424233091295236878301 989034087409235713829363)
                      ·
                        rfl

theorem cell23_1926137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1926137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926137 prefixEnd_1926137 := by exact prefixLift 1926137
  have htrace : WordTrace (prefixWord ++ tailWord_1926137) baseStart_1926137 baseEnd_1926137 := by
    simpa [prefixWord, tailWord_1926137, baseEnd_1926137] using wordTrace_append hprefix tailTrace_1926137
  have hstable : (prefixWord ++ tailWord_1926137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926137).length < 2 ^ (prefixWord ++ tailWord_1926137).sum := by decide
  have hdescent : baseEnd_1926137 < baseStart_1926137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926154 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1926154 : Nat := 118140960795 + 1926154 * 2 ^ 59
def prefixEnd_1926154 : Nat := 4983230072969 + 3 ^ 40 * 1926154 * 2
def baseEnd_1926154 : Nat := 989042816580362147316785

theorem tailTrace_1926154 : CollatzResearch.WordTrace tailWord_1926154 prefixEnd_1926154 989042816580362147316785 := by
  unfold tailWord_1926154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563151965970123439598379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46835071909253662505595677 17563151965970123439598379)
  ·
    refine ⟨26344727948955185159397569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17563151965970123439598379 26344727948955185159397569)
    ·
      refine ⟨19758545961716388869548177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26344727948955185159397569 19758545961716388869548177)
      ·
        refine ⟨14818909471287291652161133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19758545961716388869548177 14818909471287291652161133)
        ·
          refine ⟨5557091051732734369560425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14818909471287291652161133 5557091051732734369560425)
          ·
            refine ⟨4167818288799550777170319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557091051732734369560425 4167818288799550777170319)
            ·
              refine ⟨6251727433199326165755479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167818288799550777170319 6251727433199326165755479)
              ·
                refine ⟨9377591149798989248633219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6251727433199326165755479 9377591149798989248633219)
                ·
                  refine ⟨14066386724698483872949829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9377591149798989248633219 14066386724698483872949829)
                  ·
                    refine ⟨2637447510880965726178093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14066386724698483872949829 2637447510880965726178093)
                    ·
                      refine ⟨989042816580362147316785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637447510880965726178093 989042816580362147316785)
                      ·
                        rfl

theorem cell23_1926154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1926154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926154 prefixEnd_1926154 := by exact prefixLift 1926154
  have htrace : WordTrace (prefixWord ++ tailWord_1926154) baseStart_1926154 baseEnd_1926154 := by
    simpa [prefixWord, tailWord_1926154, baseEnd_1926154] using wordTrace_append hprefix tailTrace_1926154
  have hstable : (prefixWord ++ tailWord_1926154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926154).length < 2 ^ (prefixWord ++ tailWord_1926154).sum := by decide
  have hdescent : baseEnd_1926154 < baseStart_1926154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926160 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_1926160 : Nat := 118140960795 + 1926160 * 2 ^ 59
def prefixEnd_1926160 : Nat := 4983230072969 + 3 ^ 40 * 1926160 * 2
def baseEnd_1926160 : Nat := 989045897464289123841757

theorem tailTrace_1926160 : CollatzResearch.WordTrace tailWord_1926160 prefixEnd_1926160 989045897464289123841757 := by
  unfold tailWord_1926160
  simp only [CollatzResearch.WordTrace]
  refine ⟨35126413350929378391555967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46835217801239171188741289 35126413350929378391555967)
  ·
    refine ⟨52689620026394067587333951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35126413350929378391555967 52689620026394067587333951)
    ·
      refine ⟨79034430039591101381000927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52689620026394067587333951 79034430039591101381000927)
      ·
        refine ⟨118551645059386652071501391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79034430039591101381000927 118551645059386652071501391)
        ·
          refine ⟨177827467589079978107252087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118551645059386652071501391 177827467589079978107252087)
          ·
            refine ⟨266741201383619967160878131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177827467589079978107252087 266741201383619967160878131)
            ·
              refine ⟨400111802075429950741317197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266741201383619967160878131 400111802075429950741317197)
              ·
                refine ⟨150041925778286231527993949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400111802075429950741317197 150041925778286231527993949)
                ·
                  refine ⟨56265722166857336822997731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150041925778286231527993949 56265722166857336822997731)
                  ·
                    refine ⟨84398583250286005234496597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56265722166857336822997731 84398583250286005234496597)
                    ·
                      refine ⟨989045897464289123841757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 84398583250286005234496597 989045897464289123841757)
                      ·
                        rfl

theorem cell23_1926160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_1926160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926160 prefixEnd_1926160 := by exact prefixLift 1926160
  have htrace : WordTrace (prefixWord ++ tailWord_1926160) baseStart_1926160 baseEnd_1926160 := by
    simpa [prefixWord, tailWord_1926160, baseEnd_1926160] using wordTrace_append hprefix tailTrace_1926160
  have hstable : (prefixWord ++ tailWord_1926160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926160).length < 2 ^ (prefixWord ++ tailWord_1926160).sum := by decide
  have hdescent : baseEnd_1926160 < baseStart_1926160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926177 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1926177 : Nat := 118140960795 + 1926177 * 2 ^ 59
def prefixEnd_1926177 : Nat := 4983230072969 + 3 ^ 40 * 1926177 * 2
def baseEnd_1926177 : Nat := 989054626635415557329179

theorem tailTrace_1926177 : CollatzResearch.WordTrace tailWord_1926177 prefixEnd_1926177 989054626635415557329179 := by
  unfold tailWord_1926177
  simp only [CollatzResearch.WordTrace]
  refine ⟨70253446742797168686480785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46835631161864779124320523 70253446742797168686480785)
  ·
    refine ⟨52690085057097876514860589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70253446742797168686480785 52690085057097876514860589)
    ·
      refine ⟨19758781896411703693072721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52690085057097876514860589 19758781896411703693072721)
      ·
        refine ⟨14819086422308777769804541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19758781896411703693072721 14819086422308777769804541)
        ·
          refine ⟨5557157408365791663676703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14819086422308777769804541 5557157408365791663676703)
          ·
            refine ⟨8335736112548687495515055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557157408365791663676703 8335736112548687495515055)
            ·
              refine ⟨12503604168823031243272583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335736112548687495515055 12503604168823031243272583)
              ·
                refine ⟨18755406253234546864908875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12503604168823031243272583 18755406253234546864908875)
                ·
                  refine ⟨28133109379851820297363313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18755406253234546864908875 28133109379851820297363313)
                  ·
                    refine ⟨21099832034888865223022485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28133109379851820297363313 21099832034888865223022485)
                    ·
                      refine ⟨989054626635415557329179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21099832034888865223022485 989054626635415557329179)
                      ·
                        rfl

theorem cell23_1926177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1926177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926177 prefixEnd_1926177 := by exact prefixLift 1926177
  have htrace : WordTrace (prefixWord ++ tailWord_1926177) baseStart_1926177 baseEnd_1926177 := by
    simpa [prefixWord, tailWord_1926177, baseEnd_1926177] using wordTrace_append hprefix tailTrace_1926177
  have hstable : (prefixWord ++ tailWord_1926177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926177).length < 2 ^ (prefixWord ++ tailWord_1926177).sum := by decide
  have hdescent : baseEnd_1926177 < baseStart_1926177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926194 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_1926194 : Nat := 118140960795 + 1926194 * 2 ^ 59
def prefixEnd_1926194 : Nat := 4983230072969 + 3 ^ 40 * 1926194 * 2
def baseEnd_1926194 : Nat := 989063355806541990816601

theorem tailTrace_1926194 : CollatzResearch.WordTrace tailWord_1926194 prefixEnd_1926194 989063355806541990816601 := by
  unfold tailWord_1926194
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563516695933895147462409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46836044522490387059899757 17563516695933895147462409)
  ·
    refine ⟨13172637521950421360596807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17563516695933895147462409 13172637521950421360596807)
    ·
      refine ⟨19758956282925632040895211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13172637521950421360596807 19758956282925632040895211)
      ·
        refine ⟨29638434424388448061342817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19758956282925632040895211 29638434424388448061342817)
        ·
          refine ⟨22228825818291336046007113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29638434424388448061342817 22228825818291336046007113)
          ·
            refine ⟨16671619363718502034505335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22228825818291336046007113 16671619363718502034505335)
            ·
              refine ⟨25007429045577753051758003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16671619363718502034505335 25007429045577753051758003)
              ·
                refine ⟨37511143568366629577637005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25007429045577753051758003 37511143568366629577637005)
                ·
                  refine ⟨14066678838137486091613877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37511143568366629577637005 14066678838137486091613877)
                  ·
                    refine ⟨1318751141075389321088801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14066678838137486091613877 1318751141075389321088801)
                    ·
                      refine ⟨989063355806541990816601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318751141075389321088801 989063355806541990816601)
                      ·
                        rfl

theorem cell23_1926194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_1926194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926194 prefixEnd_1926194 := by exact prefixLift 1926194
  have htrace : WordTrace (prefixWord ++ tailWord_1926194) baseStart_1926194 baseEnd_1926194 := by
    simpa [prefixWord, tailWord_1926194, baseEnd_1926194] using wordTrace_append hprefix tailTrace_1926194
  have hstable : (prefixWord ++ tailWord_1926194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926194).length < 2 ^ (prefixWord ++ tailWord_1926194).sum := by decide
  have hdescent : baseEnd_1926194 < baseStart_1926194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926201 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1926201 : Nat := 118140960795 + 1926201 * 2 ^ 59
def prefixEnd_1926201 : Nat := 4983230072969 + 3 ^ 40 * 1926201 * 2
def baseEnd_1926201 : Nat := 989066950171123463429069

theorem tailTrace_1926201 : CollatzResearch.WordTrace tailWord_1926201 prefixEnd_1926201 989066950171123463429069 := by
  unfold tailWord_1926201
  simp only [CollatzResearch.WordTrace]
  refine ⟨70254322094710220785354457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46836214729806813856902971 70254322094710220785354457)
  ·
    refine ⟨52690741571032665589015843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70254322094710220785354457 52690741571032665589015843)
    ·
      refine ⟨79036112356548998383523765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52690741571032665589015843 79036112356548998383523765)
      ·
        refine ⟨7409635533426468598455353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79036112356548998383523765 7409635533426468598455353)
        ·
          refine ⟨5557226650069851448841515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409635533426468598455353 5557226650069851448841515)
          ·
            refine ⟨8335839975104777173262273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557226650069851448841515 8335839975104777173262273)
            ·
              refine ⟨6251879981328582879946705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335839975104777173262273 6251879981328582879946705)
              ·
                refine ⟨4688909985996437159960029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251879981328582879946705 4688909985996437159960029)
                ·
                  refine ⟨1758341244748663934985011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4688909985996437159960029 1758341244748663934985011)
                  ·
                    refine ⟨2637511867122995902477517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758341244748663934985011 2637511867122995902477517)
                    ·
                      refine ⟨989066950171123463429069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637511867122995902477517 989066950171123463429069)
                      ·
                        rfl

theorem cell23_1926201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1926201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926201 prefixEnd_1926201 := by exact prefixLift 1926201
  have htrace : WordTrace (prefixWord ++ tailWord_1926201) baseStart_1926201 baseEnd_1926201 := by
    simpa [prefixWord, tailWord_1926201, baseEnd_1926201] using wordTrace_append hprefix tailTrace_1926201
  have hstable : (prefixWord ++ tailWord_1926201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926201).length < 2 ^ (prefixWord ++ tailWord_1926201).sum := by decide
  have hdescent : baseEnd_1926201 < baseStart_1926201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926204 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_1926204 : Nat := 118140960795 + 1926204 * 2 ^ 59
def prefixEnd_1926204 : Nat := 4983230072969 + 3 ^ 40 * 1926204 * 2
def baseEnd_1926204 : Nat := 329689496871028983897185

theorem tailTrace_1926204 : CollatzResearch.WordTrace tailWord_1926204 prefixEnd_1926204 329689496871028983897185 := by
  unfold tailWord_1926204
  simp only [CollatzResearch.WordTrace]
  refine ⟨35127215756849676148856833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46836287675799568198475777 35127215756849676148856833)
  ·
    refine ⟨26345411817637257111642625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35127215756849676148856833 26345411817637257111642625)
    ·
      refine ⟨19759058863227942833731969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26345411817637257111642625 19759058863227942833731969)
      ·
        refine ⟨14819294147420957125298977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19759058863227942833731969 14819294147420957125298977)
        ·
          refine ⟨11114470610565717843974233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14819294147420957125298977 11114470610565717843974233)
          ·
            refine ⟨8335852957924288382980675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114470610565717843974233 8335852957924288382980675)
            ·
              refine ⟨12503779436886432574471013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335852957924288382980675 12503779436886432574471013)
              ·
                refine ⟨2344458644416206107713315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12503779436886432574471013 2344458644416206107713315)
                ·
                  refine ⟨3516687966624309161569973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344458644416206107713315 3516687966624309161569973)
                  ·
                    refine ⟨329689496871028983897185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3516687966624309161569973 329689496871028983897185)
                    ·
                      rfl

theorem cell23_1926204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_1926204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926204 prefixEnd_1926204 := by exact prefixLift 1926204
  have htrace : WordTrace (prefixWord ++ tailWord_1926204) baseStart_1926204 baseEnd_1926204 := by
    simpa [prefixWord, tailWord_1926204, baseEnd_1926204] using wordTrace_append hprefix tailTrace_1926204
  have hstable : (prefixWord ++ tailWord_1926204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926204).length < 2 ^ (prefixWord ++ tailWord_1926204).sum := by decide
  have hdescent : baseEnd_1926204 < baseStart_1926204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926218 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_1926218 : Nat := 118140960795 + 1926218 * 2 ^ 59
def prefixEnd_1926218 : Nat := 4983230072969 + 3 ^ 40 * 1926218 * 2
def baseEnd_1926218 : Nat := 989075679342249896916491

theorem tailTrace_1926218 : CollatzResearch.WordTrace tailWord_1926218 prefixEnd_1926218 989075679342249896916491 := by
  unfold tailWord_1926218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563735533912158172180827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46836628090432421792482205 17563735533912158172180827)
  ·
    refine ⟨26345603300868237258271241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17563735533912158172180827 26345603300868237258271241)
    ·
      refine ⟨19759202475651177943703431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26345603300868237258271241 19759202475651177943703431)
      ·
        refine ⟨29638803713476766915555147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19759202475651177943703431 29638803713476766915555147)
        ·
          refine ⟨44458205570215150373332721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29638803713476766915555147 44458205570215150373332721)
          ·
            refine ⟨33343654177661362779999541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44458205570215150373332721 33343654177661362779999541)
            ·
              refine ⟨3125967579155752760624957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33343654177661362779999541 3125967579155752760624957)
              ·
                refine ⟨1172237842183407285234359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125967579155752760624957 1172237842183407285234359)
                ·
                  refine ⟨1758356763275110927851539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172237842183407285234359 1758356763275110927851539)
                  ·
                    refine ⟨2637535144912666391777309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758356763275110927851539 2637535144912666391777309)
                    ·
                      refine ⟨989075679342249896916491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637535144912666391777309 989075679342249896916491)
                      ·
                        rfl

theorem cell23_1926218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_1926218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926218 prefixEnd_1926218 := by exact prefixLift 1926218
  have htrace : WordTrace (prefixWord ++ tailWord_1926218) baseStart_1926218 baseEnd_1926218 := by
    simpa [prefixWord, tailWord_1926218, baseEnd_1926218] using wordTrace_append hprefix tailTrace_1926218
  have hstable : (prefixWord ++ tailWord_1926218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926218).length < 2 ^ (prefixWord ++ tailWord_1926218).sum := by decide
  have hdescent : baseEnd_1926218 < baseStart_1926218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926221 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1926221 : Nat := 118140960795 + 1926221 * 2 ^ 59
def prefixEnd_1926221 : Nat := 4983230072969 + 3 ^ 40 * 1926221 * 2
def baseEnd_1926221 : Nat := 329692406594737795059659

theorem tailTrace_1926221 : CollatzResearch.WordTrace tailWord_1926221 prefixEnd_1926221 329692406594737795059659 := by
  unfold tailWord_1926221
  simp only [CollatzResearch.WordTrace]
  refine ⟨70255051554637764201082517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46836701036425176134055011 70255051554637764201082517)
  ·
    refine ⟨3293205541623645196925743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70255051554637764201082517 3293205541623645196925743)
    ·
      refine ⟨4939808312435467795388615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293205541623645196925743 4939808312435467795388615)
      ·
        refine ⟨7409712468653201693082923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939808312435467795388615 7409712468653201693082923)
        ·
          refine ⟨11114568702979802539624385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409712468653201693082923 11114568702979802539624385)
          ·
            refine ⟨8335926527234851904718289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114568702979802539624385 8335926527234851904718289)
            ·
              refine ⟨6251944895426138928538717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335926527234851904718289 6251944895426138928538717)
              ·
                refine ⟨2344479335784802098202019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6251944895426138928538717 2344479335784802098202019)
                ·
                  refine ⟨3516719003677203147303029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344479335784802098202019 3516719003677203147303029)
                  ·
                    refine ⟨329692406594737795059659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3516719003677203147303029 329692406594737795059659)
                    ·
                      rfl

theorem cell23_1926221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1926221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926221 prefixEnd_1926221 := by exact prefixLift 1926221
  have htrace : WordTrace (prefixWord ++ tailWord_1926221) baseStart_1926221 baseEnd_1926221 := by
    simpa [prefixWord, tailWord_1926221, baseEnd_1926221] using wordTrace_append hprefix tailTrace_1926221
  have hstable : (prefixWord ++ tailWord_1926221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926221).length < 2 ^ (prefixWord ++ tailWord_1926221).sum := by decide
  have hdescent : baseEnd_1926221 < baseStart_1926221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926227 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5]
def baseStart_1926227 : Nat := 118140960795 + 1926227 * 2 ^ 59
def prefixEnd_1926227 : Nat := 4983230072969 + 3 ^ 40 * 1926227 * 2
def baseEnd_1926227 : Nat := 989080300668140361703949

theorem tailTrace_1926227 : CollatzResearch.WordTrace tailWord_1926227 prefixEnd_1926227 989080300668140361703949 := by
  unfold tailWord_1926227
  simp only [CollatzResearch.WordTrace]
  refine ⟨70255270392616027225800935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46836846928410684817200623 70255270392616027225800935)
  ·
    refine ⟨105382905588924040838701403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70255270392616027225800935 105382905588924040838701403)
    ·
      refine ⟨158074358383386061258052105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105382905588924040838701403 158074358383386061258052105)
      ·
        refine ⟨118555768787539545943539079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158074358383386061258052105 118555768787539545943539079)
        ·
          refine ⟨177833653181309318915308619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118555768787539545943539079 177833653181309318915308619)
          ·
            refine ⟨266750479771963978372962929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177833653181309318915308619 266750479771963978372962929)
            ·
              refine ⟨200062859828972983779722197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266750479771963978372962929 200062859828972983779722197)
              ·
                refine ⟨4688973277241554307337239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 200062859828972983779722197 4688973277241554307337239)
                ·
                  refine ⟨7033459915862331461005859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688973277241554307337239 7033459915862331461005859)
                  ·
                    refine ⟨10550189873793497191508789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7033459915862331461005859 10550189873793497191508789)
                    ·
                      refine ⟨989080300668140361703949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10550189873793497191508789 989080300668140361703949)
                      ·
                        rfl

theorem cell23_1926227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_1926227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926227 prefixEnd_1926227 := by exact prefixLift 1926227
  have htrace : WordTrace (prefixWord ++ tailWord_1926227) baseStart_1926227 baseEnd_1926227 := by
    simpa [prefixWord, tailWord_1926227, baseEnd_1926227] using wordTrace_append hprefix tailTrace_1926227
  have hstable : (prefixWord ++ tailWord_1926227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926227).length < 2 ^ (prefixWord ++ tailWord_1926227).sum := by decide
  have hdescent : baseEnd_1926227 < baseStart_1926227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926244 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_1926244 : Nat := 118140960795 + 1926244 * 2 ^ 59
def prefixEnd_1926244 : Nat := 4983230072969 + 3 ^ 40 * 1926244 * 2
def baseEnd_1926244 : Nat := 989089029839266795191371

theorem tailTrace_1926244 : CollatzResearch.WordTrace tailWord_1926244 prefixEnd_1926244 989089029839266795191371 := by
  unfold tailWord_1926244
  simp only [CollatzResearch.WordTrace]
  refine ⟨35127945216777219564584893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46837260289036292752779857 35127945216777219564584893)
  ·
    refine ⟨13172979456291457336719335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35127945216777219564584893 13172979456291457336719335)
    ·
      refine ⟨19759469184437186005079003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13172979456291457336719335 19759469184437186005079003)
      ·
        refine ⟨29639203776655779007618505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19759469184437186005079003 29639203776655779007618505)
        ·
          refine ⟨22229402832491834255713879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29639203776655779007618505 22229402832491834255713879)
          ·
            refine ⟨33344104248737751383570819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22229402832491834255713879 33344104248737751383570819)
            ·
              refine ⟨50016156373106627075356229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33344104248737751383570819 50016156373106627075356229)
              ·
                refine ⟨9378029319957492576629293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50016156373106627075356229 9378029319957492576629293)
                ·
                  refine ⟨3516760994984059716235985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9378029319957492576629293 3516760994984059716235985)
                  ·
                    refine ⟨2637570746238044787176989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3516760994984059716235985 2637570746238044787176989)
                    ·
                      refine ⟨989089029839266795191371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637570746238044787176989 989089029839266795191371)
                      ·
                        rfl

theorem cell23_1926244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_1926244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926244 prefixEnd_1926244 := by exact prefixLift 1926244
  have htrace : WordTrace (prefixWord ++ tailWord_1926244) baseStart_1926244 baseEnd_1926244 := by
    simpa [prefixWord, tailWord_1926244, baseEnd_1926244] using wordTrace_append hprefix tailTrace_1926244
  have hstable : (prefixWord ++ tailWord_1926244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926244).length < 2 ^ (prefixWord ++ tailWord_1926244).sum := by decide
  have hdescent : baseEnd_1926244 < baseStart_1926244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926247 : List Nat := [1, 1, 5, 1, 1, 3, 1, 10]
def baseStart_1926247 : Nat := 118140960795 + 1926247 * 2 ^ 59
def prefixEnd_1926247 : Nat := 4983230072969 + 3 ^ 40 * 1926247 * 2
def baseEnd_1926247 : Nat := 36632984084490010498291

theorem tailTrace_1926247 : CollatzResearch.WordTrace tailWord_1926247 prefixEnd_1926247 36632984084490010498291 := by
  unfold tailWord_1926247
  simp only [CollatzResearch.WordTrace]
  refine ⟨70255999852543570641528995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46837333235029047094352663 70255999852543570641528995)
  ·
    refine ⟨105383999778815355962293493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70255999852543570641528995 105383999778815355962293493)
    ·
      refine ⟨9879749979263939621465015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105383999778815355962293493 9879749979263939621465015)
      ·
        refine ⟨14819624968895909432197523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879749979263939621465015 14819624968895909432197523)
        ·
          refine ⟨22229437453343864148296285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14819624968895909432197523 22229437453343864148296285)
          ·
            refine ⟨8336039045003949055611107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22229437453343864148296285 8336039045003949055611107)
            ·
              refine ⟨12504058567505923583416661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336039045003949055611107 12504058567505923583416661)
              ·
                refine ⟨36632984084490010498291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12504058567505923583416661 36632984084490010498291)
                ·
                  rfl

theorem cell23_1926247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 10].length) (baseStart_1926247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926247 prefixEnd_1926247 := by exact prefixLift 1926247
  have htrace : WordTrace (prefixWord ++ tailWord_1926247) baseStart_1926247 baseEnd_1926247 := by
    simpa [prefixWord, tailWord_1926247, baseEnd_1926247] using wordTrace_append hprefix tailTrace_1926247
  have hstable : (prefixWord ++ tailWord_1926247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926247).length < 2 ^ (prefixWord ++ tailWord_1926247).sum := by decide
  have hdescent : baseEnd_1926247 < baseStart_1926247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926254 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1926254 : Nat := 118140960795 + 1926254 * 2 ^ 59
def prefixEnd_1926254 : Nat := 4983230072969 + 3 ^ 40 * 1926254 * 2
def baseEnd_1926254 : Nat := 989094164645811756066325

theorem tailTrace_1926254 : CollatzResearch.WordTrace tailWord_1926254 prefixEnd_1926254 989094164645811756066325 := by
  unfold tailWord_1926254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782031895439776354629227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46837503442345473891355877 8782031895439776354629227)
  ·
    refine ⟨13173047843159664531943841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8782031895439776354629227 13173047843159664531943841)
    ·
      refine ⟨9879785882369748398957881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13173047843159664531943841 9879785882369748398957881)
      ·
        refine ⟨7409839411777311299218411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9879785882369748398957881 7409839411777311299218411)
        ·
          refine ⟨11114759117665966948827617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409839411777311299218411 11114759117665966948827617)
          ·
            refine ⟨8336069338249475211620713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114759117665966948827617 8336069338249475211620713)
            ·
              refine ⟨6252052003687106408715535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8336069338249475211620713 6252052003687106408715535)
              ·
                refine ⟨9378078005530659613073303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252052003687106408715535 9378078005530659613073303)
                ·
                  refine ⟨14067117008295989419609955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378078005530659613073303 14067117008295989419609955)
                  ·
                    refine ⟨21100675512443984129414933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14067117008295989419609955 21100675512443984129414933)
                    ·
                      refine ⟨989094164645811756066325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21100675512443984129414933 989094164645811756066325)
                      ·
                        rfl

theorem cell23_1926254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1926254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926254 prefixEnd_1926254 := by exact prefixLift 1926254
  have htrace : WordTrace (prefixWord ++ tailWord_1926254) baseStart_1926254 baseEnd_1926254 := by
    simpa [prefixWord, tailWord_1926254, baseEnd_1926254] using wordTrace_append hprefix tailTrace_1926254
  have hstable : (prefixWord ++ tailWord_1926254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926254).length < 2 ^ (prefixWord ++ tailWord_1926254).sum := by decide
  have hdescent : baseEnd_1926254 < baseStart_1926254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926291 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 3]
def baseStart_1926291 : Nat := 118140960795 + 1926291 * 2 ^ 59
def prefixEnd_1926291 : Nat := 4983230072969 + 3 ^ 40 * 1926291 * 2
def baseEnd_1926291 : Nat := 989113163430028111303655

theorem tailTrace_1926291 : CollatzResearch.WordTrace tailWord_1926291 prefixEnd_1926291 989113163430028111303655 := by
  unfold tailWord_1926291
  simp only [CollatzResearch.WordTrace]
  refine ⟨70257604664384166156130727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46838403109589444104087151 70257604664384166156130727)
  ·
    refine ⟨105386406996576249234196091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70257604664384166156130727 105386406996576249234196091)
    ·
      refine ⟨158079610494864373851294137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105386406996576249234196091 158079610494864373851294137)
      ·
        refine ⟨118559707871148280388470603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158079610494864373851294137 118559707871148280388470603)
        ·
          refine ⟨177839561806722420582705905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118559707871148280388470603 177839561806722420582705905)
          ·
            refine ⟨133379671355041815437029429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177839561806722420582705905 133379671355041815437029429)
            ·
              refine ⟨12504344189535170197221509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133379671355041815437029429 12504344189535170197221509)
              ·
                refine ⟨2344564535537844411979033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12504344189535170197221509 2344564535537844411979033)
                ·
                  refine ⟨1758423401653383308984275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344564535537844411979033 1758423401653383308984275)
                  ·
                    refine ⟨2637635102480074963476413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758423401653383308984275 2637635102480074963476413)
                    ·
                      refine ⟨989113163430028111303655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637635102480074963476413 989113163430028111303655)
                      ·
                        rfl

theorem cell23_1926291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_1926291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926291 prefixEnd_1926291 := by exact prefixLift 1926291
  have htrace : WordTrace (prefixWord ++ tailWord_1926291) baseStart_1926291 baseEnd_1926291 := by
    simpa [prefixWord, tailWord_1926291, baseEnd_1926291] using wordTrace_append hprefix tailTrace_1926291
  have hstable : (prefixWord ++ tailWord_1926291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926291).length < 2 ^ (prefixWord ++ tailWord_1926291).sum := by decide
  have hdescent : baseEnd_1926291 < baseStart_1926291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926301 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_1926301 : Nat := 118140960795 + 1926301 * 2 ^ 59
def prefixEnd_1926301 : Nat := 4983230072969 + 3 ^ 40 * 1926301 * 2
def baseEnd_1926301 : Nat := 989118298236573072178609

theorem tailTrace_1926301 : CollatzResearch.WordTrace tailWord_1926301 prefixEnd_1926301 989118298236573072178609 := by
  unfold tailWord_1926301
  simp only [CollatzResearch.WordTrace]
  refine ⟨70257969394347937863994757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46838646262898625242663171 70257969394347937863994757)
  ·
    refine ⟨13173369261440238349499017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70257969394347937863994757 13173369261440238349499017)
    ·
      refine ⟨9880026946080178762124263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13173369261440238349499017 9880026946080178762124263)
      ·
        refine ⟨14820040419120268143186395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880026946080178762124263 14820040419120268143186395)
        ·
          refine ⟨22230060628680402214779593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820040419120268143186395 22230060628680402214779593)
          ·
            refine ⟨16672545471510301661084695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22230060628680402214779593 16672545471510301661084695)
            ·
              refine ⟨25008818207265452491627043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16672545471510301661084695 25008818207265452491627043)
              ·
                refine ⟨37513227310898178737440565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25008818207265452491627043 37513227310898178737440565)
                ·
                  refine ⟨3516865060396704256635053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37513227310898178737440565 3516865060396704256635053)
                  ·
                    refine ⟨1318824397648764096238145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3516865060396704256635053 1318824397648764096238145)
                    ·
                      refine ⟨989118298236573072178609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318824397648764096238145 989118298236573072178609)
                      ·
                        rfl

theorem cell23_1926301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_1926301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926301 prefixEnd_1926301 := by exact prefixLift 1926301
  have htrace : WordTrace (prefixWord ++ tailWord_1926301) baseStart_1926301 baseEnd_1926301 := by
    simpa [prefixWord, tailWord_1926301, baseEnd_1926301] using wordTrace_append hprefix tailTrace_1926301
  have hstable : (prefixWord ++ tailWord_1926301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926301).length < 2 ^ (prefixWord ++ tailWord_1926301).sum := by decide
  have hdescent : baseEnd_1926301 < baseStart_1926301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926308 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_1926308 : Nat := 118140960795 + 1926308 * 2 ^ 59
def prefixEnd_1926308 : Nat := 4983230072969 + 3 ^ 40 * 1926308 * 2
def baseEnd_1926308 : Nat := 989121892601154544791077

theorem tailTrace_1926308 : CollatzResearch.WordTrace tailWord_1926308 prefixEnd_1926308 989121892601154544791077 := by
  unfold tailWord_1926308
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129112352661289029749789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46838816470215052039666385 35129112352661289029749789)
  ·
    refine ⟨13173417132247983386156171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35129112352661289029749789 13173417132247983386156171)
    ·
      refine ⟨19760125698371975079234257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13173417132247983386156171 19760125698371975079234257)
      ·
        refine ⟨14820094273778981309425693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19760125698371975079234257 14820094273778981309425693)
        ·
          refine ⟨5557535352667117991034635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14820094273778981309425693 5557535352667117991034635)
          ·
            refine ⟨8336303029000676986551953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557535352667117991034635 8336303029000676986551953)
            ·
              refine ⟨6252227271750507739913965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8336303029000676986551953 6252227271750507739913965)
              ·
                refine ⟨2344585226906440402467737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252227271750507739913965 2344585226906440402467737)
                ·
                  refine ⟨1758438920179830301850803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344585226906440402467737 1758438920179830301850803)
                  ·
                    refine ⟨2637658380269745452776205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758438920179830301850803 2637658380269745452776205)
                    ·
                      refine ⟨989121892601154544791077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637658380269745452776205 989121892601154544791077)
                      ·
                        rfl

theorem cell23_1926308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_1926308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926308 prefixEnd_1926308 := by exact prefixLift 1926308
  have htrace : WordTrace (prefixWord ++ tailWord_1926308) baseStart_1926308 baseEnd_1926308 := by
    simpa [prefixWord, tailWord_1926308, baseEnd_1926308] using wordTrace_append hprefix tailTrace_1926308
  have hstable : (prefixWord ++ tailWord_1926308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926308).length < 2 ^ (prefixWord ++ tailWord_1926308).sum := by decide
  have hdescent : baseEnd_1926308 < baseStart_1926308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926326 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1926326 : Nat := 118140960795 + 1926326 * 2 ^ 59
def prefixEnd_1926326 : Nat := 4983230072969 + 3 ^ 40 * 1926326 * 2
def baseEnd_1926326 : Nat := 989131135252935474365995

theorem tailTrace_1926326 : CollatzResearch.WordTrace tailWord_1926326 prefixEnd_1926326 989131135252935474365995 := by
  unfold tailWord_1926326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391180076203585445853427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46839254146171578089103221 4391180076203585445853427)
  ·
    refine ⟨6586770114305378168780141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4391180076203585445853427 6586770114305378168780141)
    ·
      refine ⟨2470038792864516813292553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6586770114305378168780141 2470038792864516813292553)
      ·
        refine ⟨1852529094648387609969415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2470038792864516813292553 1852529094648387609969415)
        ·
          refine ⟨2778793641972581414954123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852529094648387609969415 2778793641972581414954123)
          ·
            refine ⟨4168190462958872122431185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778793641972581414954123 4168190462958872122431185)
            ·
              refine ⟨3126142847219154091823389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168190462958872122431185 3126142847219154091823389)
              ·
                refine ⟨1172303567707182784433771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126142847219154091823389 1172303567707182784433771)
                ·
                  refine ⟨1758455351560774176650657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172303567707182784433771 1758455351560774176650657)
                  ·
                    refine ⟨1318841513670580632487993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1758455351560774176650657 1318841513670580632487993)
                    ·
                      refine ⟨989131135252935474365995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318841513670580632487993 989131135252935474365995)
                      ·
                        rfl

theorem cell23_1926326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1926326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926326 prefixEnd_1926326 := by exact prefixLift 1926326
  have htrace : WordTrace (prefixWord ++ tailWord_1926326) baseStart_1926326 baseEnd_1926326 := by
    simpa [prefixWord, tailWord_1926326, baseEnd_1926326] using wordTrace_append hprefix tailTrace_1926326
  have hstable : (prefixWord ++ tailWord_1926326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926326).length < 2 ^ (prefixWord ++ tailWord_1926326).sum := by decide
  have hdescent : baseEnd_1926326 < baseStart_1926326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926344 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1926344 : Nat := 118140960795 + 1926344 * 2 ^ 59
def prefixEnd_1926344 : Nat := 4983230072969 + 3 ^ 40 * 1926344 * 2
def baseEnd_1926344 : Nat := 989140377904716403940911

theorem tailTrace_1926344 : CollatzResearch.WordTrace tailWord_1926344 prefixEnd_1926344 989140377904716403940911 := by
  unfold tailWord_1926344
  simp only [CollatzResearch.WordTrace]
  refine ⟨35129768866596078103905043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46839691822128104138540057 35129768866596078103905043)
  ·
    refine ⟨52694653299894117155857565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35129768866596078103905043 52694653299894117155857565)
    ·
      refine ⟨19760494987460293933446587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52694653299894117155857565 19760494987460293933446587)
      ·
        refine ⟨29640742481190440900169881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19760494987460293933446587 29640742481190440900169881)
        ·
          refine ⟨22230556860892830675127411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29640742481190440900169881 22230556860892830675127411)
          ·
            refine ⟨33345835291339246012691117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22230556860892830675127411 33345835291339246012691117)
            ·
              refine ⟨12504688234252217254759169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33345835291339246012691117 12504688234252217254759169)
              ·
                refine ⟨9378516175689162941069377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12504688234252217254759169 9378516175689162941069377)
                ·
                  refine ⟨7033887131766872205802033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9378516175689162941069377 7033887131766872205802033)
                  ·
                    refine ⟨5275415348825154154351525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7033887131766872205802033 5275415348825154154351525)
                    ·
                      refine ⟨989140377904716403940911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5275415348825154154351525 989140377904716403940911)
                      ·
                        rfl

theorem cell23_1926344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1926344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926344 prefixEnd_1926344 := by exact prefixLift 1926344
  have htrace : WordTrace (prefixWord ++ tailWord_1926344) baseStart_1926344 baseEnd_1926344 := by
    simpa [prefixWord, tailWord_1926344, baseEnd_1926344] using wordTrace_append hprefix tailTrace_1926344
  have hstable : (prefixWord ++ tailWord_1926344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926344).length < 2 ^ (prefixWord ++ tailWord_1926344).sum := by decide
  have hdescent : baseEnd_1926344 < baseStart_1926344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926347 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_1926347 : Nat := 118140960795 + 1926347 * 2 ^ 59
def prefixEnd_1926347 : Nat := 4983230072969 + 3 ^ 40 * 1926347 * 2
def baseEnd_1926347 : Nat := 989141918346679892203397

theorem tailTrace_1926347 : CollatzResearch.WordTrace tailWord_1926347 prefixEnd_1926347 989141918346679892203397 := by
  unfold tailWord_1926347
  simp only [CollatzResearch.WordTrace]
  refine ⟨70259647152181287720169295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46839764768120858480112863 70259647152181287720169295)
  ·
    refine ⟨105389470728271931580253943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70259647152181287720169295 105389470728271931580253943)
    ·
      refine ⟨158084206092407897370380915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105389470728271931580253943 158084206092407897370380915)
      ·
        refine ⟨237126309138611846055571373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158084206092407897370380915 237126309138611846055571373)
        ·
          refine ⟨88922365926979442270839265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237126309138611846055571373 88922365926979442270839265)
          ·
            refine ⟨66691774445234581703129449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88922365926979442270839265 66691774445234581703129449)
            ·
              refine ⟨50018830833925936277347087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66691774445234581703129449 50018830833925936277347087)
              ·
                refine ⟨75028246250888904416020631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50018830833925936277347087 75028246250888904416020631)
                ·
                  refine ⟨112542369376333356624030947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75028246250888904416020631 112542369376333356624030947)
                  ·
                    refine ⟨168813554064500034936046421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112542369376333356624030947 168813554064500034936046421)
                    ·
                      refine ⟨989141918346679892203397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 168813554064500034936046421 989141918346679892203397)
                      ·
                        rfl

theorem cell23_1926347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_1926347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926347 prefixEnd_1926347 := by exact prefixLift 1926347
  have htrace : WordTrace (prefixWord ++ tailWord_1926347) baseStart_1926347 baseEnd_1926347 := by
    simpa [prefixWord, tailWord_1926347, baseEnd_1926347] using wordTrace_append hprefix tailTrace_1926347
  have hstable : (prefixWord ++ tailWord_1926347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926347).length < 2 ^ (prefixWord ++ tailWord_1926347).sum := by decide
  have hdescent : baseEnd_1926347 < baseStart_1926347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926394 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1926394 : Nat := 118140960795 + 1926394 * 2 ^ 59
def prefixEnd_1926394 : Nat := 4983230072969 + 3 ^ 40 * 1926394 * 2
def baseEnd_1926394 : Nat := 989166051937441208315681

theorem tailTrace_1926394 : CollatzResearch.WordTrace tailWord_1926394 prefixEnd_1926394 989166051937441208315681 := by
  unfold tailWord_1926394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565340345752753686782559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46840907588674009831420157 17565340345752753686782559)
  ·
    refine ⟨26348010518629130530173839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17565340345752753686782559 26348010518629130530173839)
    ·
      refine ⟨39522015777943695795260759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26348010518629130530173839 39522015777943695795260759)
      ·
        refine ⟨59283023666915543692891139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39522015777943695795260759 59283023666915543692891139)
        ·
          refine ⟨88924535500373315539336709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59283023666915543692891139 88924535500373315539336709)
          ·
            refine ⟨16673350406319996663625633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88924535500373315539336709 16673350406319996663625633)
            ·
              refine ⟨12505012804739997497719225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16673350406319996663625633 12505012804739997497719225)
              ·
                refine ⟨9378759603554998123289419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12505012804739997497719225 9378759603554998123289419)
                ·
                  refine ⟨14068139405332497184934129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378759603554998123289419 14068139405332497184934129)
                  ·
                    refine ⟨10551104553999372888700597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14068139405332497184934129 10551104553999372888700597)
                    ·
                      refine ⟨989166051937441208315681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10551104553999372888700597 989166051937441208315681)
                      ·
                        rfl

theorem cell23_1926394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1926394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926394 prefixEnd_1926394 := by exact prefixLift 1926394
  have htrace : WordTrace (prefixWord ++ tailWord_1926394) baseStart_1926394 baseEnd_1926394 := by
    simpa [prefixWord, tailWord_1926394, baseEnd_1926394] using wordTrace_append hprefix tailTrace_1926394
  have hstable : (prefixWord ++ tailWord_1926394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926394).length < 2 ^ (prefixWord ++ tailWord_1926394).sum := by decide
  have hdescent : baseEnd_1926394 < baseStart_1926394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926401 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1926401 : Nat := 118140960795 + 1926401 * 2 ^ 59
def prefixEnd_1926401 : Nat := 4983230072969 + 3 ^ 40 * 1926401 * 2
def baseEnd_1926401 : Nat := 329723215434007560309383

theorem tailTrace_1926401 : CollatzResearch.WordTrace tailWord_1926401 prefixEnd_1926401 329723215434007560309383 := by
  unfold tailWord_1926401
  simp only [CollatzResearch.WordTrace]
  refine ⟨70261616693985654942635057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46841077795990436628423371 70261616693985654942635057)
  ·
    refine ⟨52696212520489241206976293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70261616693985654942635057 52696212520489241206976293)
    ·
      refine ⟨9880539847591732726308055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52696212520489241206976293 9880539847591732726308055)
      ·
        refine ⟨14820809771387599089462083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880539847591732726308055 14820809771387599089462083)
        ·
          refine ⟨22231214657081398634193125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820809771387599089462083 22231214657081398634193125)
          ·
            refine ⟨4168352748202762243911211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22231214657081398634193125 4168352748202762243911211)
            ·
              refine ⟨6252529122304143365866817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168352748202762243911211 6252529122304143365866817)
              ·
                refine ⟨4689396841728107524400113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6252529122304143365866817 4689396841728107524400113)
                ·
                  refine ⟨3517047631296080643300085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4689396841728107524400113 3517047631296080643300085)
                  ·
                    refine ⟨329723215434007560309383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3517047631296080643300085 329723215434007560309383)
                    ·
                      rfl

theorem cell23_1926401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1926401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926401 prefixEnd_1926401 := by exact prefixLift 1926401
  have htrace : WordTrace (prefixWord ++ tailWord_1926401) baseStart_1926401 baseEnd_1926401 := by
    simpa [prefixWord, tailWord_1926401, baseEnd_1926401] using wordTrace_append hprefix tailTrace_1926401
  have hstable : (prefixWord ++ tailWord_1926401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926401).length < 2 ^ (prefixWord ++ tailWord_1926401).sum := by decide
  have hdescent : baseEnd_1926401 < baseStart_1926401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926421 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_1926421 : Nat := 118140960795 + 1926421 * 2 ^ 59
def prefixEnd_1926421 : Nat := 4983230072969 + 3 ^ 40 * 1926421 * 2
def baseEnd_1926421 : Nat := 989179915915112602678057

theorem tailTrace_1926421 : CollatzResearch.WordTrace tailWord_1926421 prefixEnd_1926421 989179915915112602678057 := by
  unfold tailWord_1926421
  simp only [CollatzResearch.WordTrace]
  refine ⟨70262346153913198358363117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46841564102608798905575411 70262346153913198358363117)
  ·
    refine ⟨26348379807717449384386169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70262346153913198358363117 26348379807717449384386169)
    ·
      refine ⟨19761284855788087038289627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26348379807717449384386169 19761284855788087038289627)
      ·
        refine ⟨29641927283682130557434441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19761284855788087038289627 29641927283682130557434441)
        ·
          refine ⟨22231445462761597918075831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29641927283682130557434441 22231445462761597918075831)
          ·
            refine ⟨33347168194142396877113747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22231445462761597918075831 33347168194142396877113747)
            ·
              refine ⟨50020752291213595315670621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33347168194142396877113747 50020752291213595315670621)
              ·
                refine ⟨18757782109205098243376483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50020752291213595315670621 18757782109205098243376483)
                ·
                  refine ⟨28136673163807647365064725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18757782109205098243376483 28136673163807647365064725)
                  ·
                    refine ⟨1318906554553483470237409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28136673163807647365064725 1318906554553483470237409)
                    ·
                      refine ⟨989179915915112602678057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1318906554553483470237409 989179915915112602678057)
                      ·
                        rfl

theorem cell23_1926421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_1926421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926421 prefixEnd_1926421 := by exact prefixLift 1926421
  have htrace : WordTrace (prefixWord ++ tailWord_1926421) baseStart_1926421 baseEnd_1926421 := by
    simpa [prefixWord, tailWord_1926421, baseEnd_1926421] using wordTrace_append hprefix tailTrace_1926421
  have hstable : (prefixWord ++ tailWord_1926421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926421).length < 2 ^ (prefixWord ++ tailWord_1926421).sum := by decide
  have hdescent : baseEnd_1926421 < baseStart_1926421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926448 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 1, 4]
def baseStart_1926448 : Nat := 118140960795 + 1926448 * 2 ^ 59
def prefixEnd_1926448 : Nat := 4983230072969 + 3 ^ 40 * 1926448 * 2
def baseEnd_1926448 : Nat := 329731259964261332346811

theorem tailTrace_1926448 : CollatzResearch.WordTrace tailWord_1926448 prefixEnd_1926448 329731259964261332346811 := by
  unfold tailWord_1926448
  simp only [CollatzResearch.WordTrace]
  refine ⟨35131665462407690984797999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46842220616543587979730665 35131665462407690984797999)
  ·
    refine ⟨52697498193611536477196999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35131665462407690984797999 52697498193611536477196999)
    ·
      refine ⟨79046247290417304715795499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52697498193611536477196999 79046247290417304715795499)
      ·
        refine ⟨118569370935625957073693249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79046247290417304715795499 118569370935625957073693249)
        ·
          refine ⟨88927028201719467805269937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118569370935625957073693249 88927028201719467805269937)
          ·
            refine ⟨66695271151289600853952453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88927028201719467805269937 66695271151289600853952453)
            ·
              refine ⟨12505363340866800160116085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66695271151289600853952453 12505363340866800160116085)
              ·
                refine ⟨1172377813206262515010883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12505363340866800160116085 1172377813206262515010883)
                ·
                  refine ⟨1758566719809393772516325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172377813206262515010883 1758566719809393772516325)
                  ·
                    refine ⟨329731259964261332346811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758566719809393772516325 329731259964261332346811)
                    ·
                      rfl

theorem cell23_1926448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 1, 4].length) (baseStart_1926448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926448 prefixEnd_1926448 := by exact prefixLift 1926448
  have htrace : WordTrace (prefixWord ++ tailWord_1926448) baseStart_1926448 baseEnd_1926448 := by
    simpa [prefixWord, tailWord_1926448, baseEnd_1926448] using wordTrace_append hprefix tailTrace_1926448
  have hstable : (prefixWord ++ tailWord_1926448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926448).length < 2 ^ (prefixWord ++ tailWord_1926448).sum := by decide
  have hdescent : baseEnd_1926448 < baseStart_1926448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926464 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1926464 : Nat := 118140960795 + 1926464 * 2 ^ 59
def prefixEnd_1926464 : Nat := 4983230072969 + 3 ^ 40 * 1926464 * 2
def baseEnd_1926464 : Nat := 989201995583255934440359

theorem tailTrace_1926464 : CollatzResearch.WordTrace tailWord_1926464 prefixEnd_1926464 989201995583255934440359 := by
  unfold tailWord_1926464
  simp only [CollatzResearch.WordTrace]
  refine ⟨35131957246378708351089223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46842609661838277801452297 35131957246378708351089223)
  ·
    refine ⟨52697935869568062526633835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35131957246378708351089223 52697935869568062526633835)
    ·
      refine ⟨79046903804352093789950753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52697935869568062526633835 79046903804352093789950753)
      ·
        refine ⟨59285177853264070342463065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79046903804352093789950753 59285177853264070342463065)
        ·
          refine ⟨44463883389948052756847299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59285177853264070342463065 44463883389948052756847299)
          ·
            refine ⟨66695825084922079135270949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44463883389948052756847299 66695825084922079135270949)
            ·
              refine ⟨12505467203422889837863303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66695825084922079135270949 12505467203422889837863303)
              ·
                refine ⟨18758200805134334756794955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12505467203422889837863303 18758200805134334756794955)
                ·
                  refine ⟨28137301207701502135192433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18758200805134334756794955 28137301207701502135192433)
                  ·
                    refine ⟨21102975905776126601394325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28137301207701502135192433 21102975905776126601394325)
                    ·
                      refine ⟨989201995583255934440359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21102975905776126601394325 989201995583255934440359)
                      ·
                        rfl

theorem cell23_1926464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1926464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926464 prefixEnd_1926464 := by exact prefixLift 1926464
  have htrace : WordTrace (prefixWord ++ tailWord_1926464) baseStart_1926464 baseEnd_1926464 := by
    simpa [prefixWord, tailWord_1926464, baseEnd_1926464] using wordTrace_append hprefix tailTrace_1926464
  have hstable : (prefixWord ++ tailWord_1926464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926464).length < 2 ^ (prefixWord ++ tailWord_1926464).sum := by decide
  have hdescent : baseEnd_1926464 < baseStart_1926464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926486 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1926486 : Nat := 118140960795 + 1926486 * 2 ^ 59
def prefixEnd_1926486 : Nat := 4983230072969 + 3 ^ 40 * 1926486 * 2
def baseEnd_1926486 : Nat := 329737764052551616121753

theorem tailTrace_1926486 : CollatzResearch.WordTrace tailWord_1926486 prefixEnd_1926486 329737764052551616121753 := by
  unfold tailWord_1926486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391544806167357153717457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46843144599118476306319541 4391544806167357153717457)
  ·
    refine ⟨3293658604625517865288093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391544806167357153717457 3293658604625517865288093)
    ·
      refine ⟨1235121976734569199483035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3293658604625517865288093 1235121976734569199483035)
      ·
        refine ⟨1852682965101853799224553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235121976734569199483035 1852682965101853799224553)
        ·
          refine ⟨1389512223826390349418415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852682965101853799224553 1389512223826390349418415)
          ·
            refine ⟨2084268335739585524127623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389512223826390349418415 2084268335739585524127623)
            ·
              refine ⟨3126402503609378286191435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084268335739585524127623 3126402503609378286191435)
              ·
                refine ⟨4689603755414067429287153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126402503609378286191435 4689603755414067429287153)
                ·
                  refine ⟨3517202816560550571965365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4689603755414067429287153 3517202816560550571965365)
                  ·
                    refine ⟨329737764052551616121753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3517202816560550571965365 329737764052551616121753)
                    ·
                      rfl

theorem cell23_1926486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1926486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926486 prefixEnd_1926486 := by exact prefixLift 1926486
  have htrace : WordTrace (prefixWord ++ tailWord_1926486) baseStart_1926486 baseEnd_1926486 := by
    simpa [prefixWord, tailWord_1926486, baseEnd_1926486] using wordTrace_append hprefix tailTrace_1926486
  have hstable : (prefixWord ++ tailWord_1926486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926486).length < 2 ^ (prefixWord ++ tailWord_1926486).sum := by decide
  have hdescent : baseEnd_1926486 < baseStart_1926486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926488 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_1926488 : Nat := 118140960795 + 1926488 * 2 ^ 59
def prefixEnd_1926488 : Nat := 4983230072969 + 3 ^ 40 * 1926488 * 2
def baseEnd_1926488 : Nat := 989214319118963840540249

theorem tailTrace_1926488 : CollatzResearch.WordTrace tailWord_1926488 prefixEnd_1926488 989214319118963840540249 := by
  unfold tailWord_1926488
  simp only [CollatzResearch.WordTrace]
  refine ⟨35132394922335234400526059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46843193229780312534034745 35132394922335234400526059)
  ·
    refine ⟨52698592383502851600789089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35132394922335234400526059 52698592383502851600789089)
    ·
      refine ⟨39523944287627138700591817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52698592383502851600789089 39523944287627138700591817)
      ·
        refine ⟨29642958215720354025443863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39523944287627138700591817 29642958215720354025443863)
        ·
          refine ⟨44464437323580531038165795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29642958215720354025443863 44464437323580531038165795)
          ·
            refine ⟨66696655985370796557248693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44464437323580531038165795 66696655985370796557248693)
            ·
              refine ⟨6252811498628512177242065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66696655985370796557248693 6252811498628512177242065)
              ·
                refine ⟨4689608623971384132931549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6252811498628512177242065 4689608623971384132931549)
                ·
                  refine ⟨1758603233989269049849331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4689608623971384132931549 1758603233989269049849331)
                  ·
                    refine ⟨2637904850983903574773997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758603233989269049849331 2637904850983903574773997)
                    ·
                      refine ⟨989214319118963840540249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637904850983903574773997 989214319118963840540249)
                      ·
                        rfl

theorem cell23_1926488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_1926488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926488 prefixEnd_1926488 := by exact prefixLift 1926488
  have htrace : WordTrace (prefixWord ++ tailWord_1926488) baseStart_1926488 baseEnd_1926488 := by
    simpa [prefixWord, tailWord_1926488, baseEnd_1926488] using wordTrace_append hprefix tailTrace_1926488
  have hstable : (prefixWord ++ tailWord_1926488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926488).length < 2 ^ (prefixWord ++ tailWord_1926488).sum := by decide
  have hdescent : baseEnd_1926488 < baseStart_1926488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926508 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_1926508 : Nat := 118140960795 + 1926508 * 2 ^ 59
def prefixEnd_1926508 : Nat := 4983230072969 + 3 ^ 40 * 1926508 * 2
def baseEnd_1926508 : Nat := 329741529577351254096719

theorem tailTrace_1926508 : CollatzResearch.WordTrace tailWord_1926508 prefixEnd_1926508 329741529577351254096719 := by
  unfold tailWord_1926508
  simp only [CollatzResearch.WordTrace]
  refine ⟨35132759652299006108390089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46843679536398674811186785 35132759652299006108390089)
  ·
    refine ⟨26349569739224254581292567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35132759652299006108390089 26349569739224254581292567)
    ·
      refine ⟨39524354608836381871938851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26349569739224254581292567 39524354608836381871938851)
      ·
        refine ⟨59286531913254572807908277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39524354608836381871938851 59286531913254572807908277)
        ·
          refine ⟨5558112366867616200741401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59286531913254572807908277 5558112366867616200741401)
          ·
            refine ⟨4168584275150712150556051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558112366867616200741401 4168584275150712150556051)
            ·
              refine ⟨6252876412726068225834077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168584275150712150556051 6252876412726068225834077)
              ·
                refine ⟨2344828654772275584687779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252876412726068225834077 2344828654772275584687779)
                ·
                  refine ⟨3517242982158413377031669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344828654772275584687779 3517242982158413377031669)
                  ·
                    refine ⟨329741529577351254096719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3517242982158413377031669 329741529577351254096719)
                    ·
                      rfl

theorem cell23_1926508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_1926508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926508 prefixEnd_1926508 := by exact prefixLift 1926508
  have htrace : WordTrace (prefixWord ++ tailWord_1926508) baseStart_1926508 baseEnd_1926508 := by
    simpa [prefixWord, tailWord_1926508, baseEnd_1926508] using wordTrace_append hprefix tailTrace_1926508
  have hstable : (prefixWord ++ tailWord_1926508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926508).length < 2 ^ (prefixWord ++ tailWord_1926508).sum := by decide
  have hdescent : baseEnd_1926508 < baseStart_1926508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926531 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5]
def baseStart_1926531 : Nat := 118140960795 + 1926531 * 2 ^ 59
def prefixEnd_1926531 : Nat := 4983230072969 + 3 ^ 40 * 1926531 * 2
def baseEnd_1926531 : Nat := 989236398787107172302551

theorem tailTrace_1926531 : CollatzResearch.WordTrace tailWord_1926531 prefixEnd_1926531 989236398787107172302551 := by
  unfold tailWord_1926531
  simp only [CollatzResearch.WordTrace]
  refine ⟨70266358183514687144867447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46844238789009791429911631 70266358183514687144867447)
  ·
    refine ⟨105399537275272030717301171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70266358183514687144867447 105399537275272030717301171)
    ·
      refine ⟨158099305912908046075951757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105399537275272030717301171 158099305912908046075951757)
      ·
        refine ⟨59287239717340517278481909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158099305912908046075951757 59287239717340517278481909)
        ·
          refine ⟨5558178723500673494857679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59287239717340517278481909 5558178723500673494857679)
          ·
            refine ⟨8337268085251010242286519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558178723500673494857679 8337268085251010242286519)
            ·
              refine ⟨12505902127876515363429779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337268085251010242286519 12505902127876515363429779)
              ·
                refine ⟨18758853191814773045144669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12505902127876515363429779 18758853191814773045144669)
                ·
                  refine ⟨7034569946930539891929251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18758853191814773045144669 7034569946930539891929251)
                  ·
                    refine ⟨10551854920395809837893877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034569946930539891929251 10551854920395809837893877)
                    ·
                      refine ⟨989236398787107172302551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10551854920395809837893877 989236398787107172302551)
                      ·
                        rfl

theorem cell23_1926531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_1926531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926531 prefixEnd_1926531 := by exact prefixLift 1926531
  have htrace : WordTrace (prefixWord ++ tailWord_1926531) baseStart_1926531 baseEnd_1926531 := by
    simpa [prefixWord, tailWord_1926531, baseEnd_1926531] using wordTrace_append hprefix tailTrace_1926531
  have hstable : (prefixWord ++ tailWord_1926531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926531).length < 2 ^ (prefixWord ++ tailWord_1926531).sum := by decide
  have hdescent : baseEnd_1926531 < baseStart_1926531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926556 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1926556 : Nat := 118140960795 + 1926556 * 2 ^ 59
def prefixEnd_1926556 : Nat := 4983230072969 + 3 ^ 40 * 1926556 * 2
def baseEnd_1926556 : Nat := 989249235803469574489937

theorem tailTrace_1926556 : CollatzResearch.WordTrace tailWord_1926556 prefixEnd_1926556 989249235803469574489937 := by
  unfold tailWord_1926556
  simp only [CollatzResearch.WordTrace]
  refine ⟨35133635004212058207263761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46844846672282744276351681 35133635004212058207263761)
  ·
    refine ⟨26350226253159043655447821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35133635004212058207263761 26350226253159043655447821)
    ·
      refine ⟨9881334844934641370792933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26350226253159043655447821 9881334844934641370792933)
      ·
        refine ⟨1852750283425245257023675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9881334844934641370792933 1852750283425245257023675)
        ·
          refine ⟨2779125425137867885535513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852750283425245257023675 2779125425137867885535513)
          ·
            refine ⟨2084344068853400914151635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2779125425137867885535513 2084344068853400914151635)
            ·
              refine ⟨3126516103280101371227453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084344068853400914151635 3126516103280101371227453)
              ·
                refine ⟨1172443538730038014210295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126516103280101371227453 1172443538730038014210295)
                ·
                  refine ⟨1758665308095057021315443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172443538730038014210295 1758665308095057021315443)
                  ·
                    refine ⟨2637997962142585531973165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758665308095057021315443 2637997962142585531973165)
                    ·
                      refine ⟨989249235803469574489937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2637997962142585531973165 989249235803469574489937)
                      ·
                        rfl

theorem cell23_1926556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1926556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926556 prefixEnd_1926556 := by exact prefixLift 1926556
  have htrace : WordTrace (prefixWord ++ tailWord_1926556) baseStart_1926556 baseEnd_1926556 := by
    simpa [prefixWord, tailWord_1926556, baseEnd_1926556] using wordTrace_append hprefix tailTrace_1926556
  have hstable : (prefixWord ++ tailWord_1926556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926556).length < 2 ^ (prefixWord ++ tailWord_1926556).sum := by decide
  have hdescent : baseEnd_1926556 < baseStart_1926556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926638 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1926638 : Nat := 118140960795 + 1926638 * 2 ^ 59
def prefixEnd_1926638 : Nat := 4983230072969 + 3 ^ 40 * 1926638 * 2
def baseEnd_1926638 : Nat := 989291341217138253664559

theorem tailTrace_1926638 : CollatzResearch.WordTrace tailWord_1926638 prefixEnd_1926638 989291341217138253664559 := by
  unfold tailWord_1926638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783782599265880552376571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46846840529418029612675045 8783782599265880552376571)
  ·
    refine ⟨13175673898898820828564857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783782599265880552376571 13175673898898820828564857)
    ·
      refine ⟨9881755424174115621423643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13175673898898820828564857 9881755424174115621423643)
      ·
        refine ⟨14822633136261173432135465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9881755424174115621423643 14822633136261173432135465)
        ·
          refine ⟨11116974852195880074101599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14822633136261173432135465 11116974852195880074101599)
          ·
            refine ⟨16675462278293820111152399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11116974852195880074101599 16675462278293820111152399)
            ·
              refine ⟨25013193417440730166728599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16675462278293820111152399 25013193417440730166728599)
              ·
                refine ⟨37519790126161095250092899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25013193417440730166728599 37519790126161095250092899)
                ·
                  refine ⟨56279685189241642875139349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37519790126161095250092899 56279685189241642875139349)
                  ·
                    refine ⟨2638110243245702009772157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56279685189241642875139349 2638110243245702009772157)
                    ·
                      refine ⟨989291341217138253664559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2638110243245702009772157 989291341217138253664559)
                      ·
                        rfl

theorem cell23_1926638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1926638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926638 prefixEnd_1926638 := by exact prefixLift 1926638
  have htrace : WordTrace (prefixWord ++ tailWord_1926638) baseStart_1926638 baseEnd_1926638 := by
    simpa [prefixWord, tailWord_1926638, baseEnd_1926638] using wordTrace_append hprefix tailTrace_1926638
  have hstable : (prefixWord ++ tailWord_1926638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926638).length < 2 ^ (prefixWord ++ tailWord_1926638).sum := by decide
  have hdescent : baseEnd_1926638 < baseStart_1926638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926645 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1926645 : Nat := 118140960795 + 1926645 * 2 ^ 59
def prefixEnd_1926645 : Nat := 4983230072969 + 3 ^ 40 * 1926645 * 2
def baseEnd_1926645 : Nat := 329764978527239908759009

theorem tailTrace_1926645 : CollatzResearch.WordTrace tailWord_1926645 prefixEnd_1926645 329764978527239908759009 := by
  unfold tailWord_1926645
  simp only [CollatzResearch.WordTrace]
  refine ⟨70270516105101684614517389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46847010736734456409678259 70270516105101684614517389)
  ·
    refine ⟨26351443539413131730444021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70270516105101684614517389 26351443539413131730444021)
    ·
      refine ⟨2470447831819981099729127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26351443539413131730444021 2470447831819981099729127)
      ·
        refine ⟨3705671747729971649593691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470447831819981099729127 3705671747729971649593691)
        ·
          refine ⟨5558507621594957474390537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705671747729971649593691 5558507621594957474390537)
          ·
            refine ⟨4168880716196218105792903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558507621594957474390537 4168880716196218105792903)
            ·
              refine ⟨6253321074294327158689355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168880716196218105792903 6253321074294327158689355)
              ·
                refine ⟨9379981611441490738034033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253321074294327158689355 9379981611441490738034033)
                ·
                  refine ⟨7034986208581118053525525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9379981611441490738034033 7034986208581118053525525)
                  ·
                    refine ⟨329764978527239908759009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7034986208581118053525525 329764978527239908759009)
                    ·
                      rfl

theorem cell23_1926645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1926645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926645 prefixEnd_1926645 := by exact prefixLift 1926645
  have htrace : WordTrace (prefixWord ++ tailWord_1926645) baseStart_1926645 baseEnd_1926645 := by
    simpa [prefixWord, tailWord_1926645, baseEnd_1926645] using wordTrace_append hprefix tailTrace_1926645
  have hstable : (prefixWord ++ tailWord_1926645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926645).length < 2 ^ (prefixWord ++ tailWord_1926645).sum := by decide
  have hdescent : baseEnd_1926645 < baseStart_1926645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926648 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1926648 : Nat := 118140960795 + 1926648 * 2 ^ 59
def prefixEnd_1926648 : Nat := 4983230072969 + 3 ^ 40 * 1926648 * 2
def baseEnd_1926648 : Nat := 989296476023683214539513

theorem tailTrace_1926648 : CollatzResearch.WordTrace tailWord_1926648 prefixEnd_1926648 989296476023683214539513 := by
  unfold tailWord_1926648
  simp only [CollatzResearch.WordTrace]
  refine ⟨35135312762045408063438299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46847083682727210751251065 35135312762045408063438299)
  ·
    refine ⟨52702969143068112095157449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35135312762045408063438299 52702969143068112095157449)
    ·
      refine ⟨39527226857301084071368087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52702969143068112095157449 39527226857301084071368087)
      ·
        refine ⟨59290840285951626107052131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39527226857301084071368087 59290840285951626107052131)
        ·
          refine ⟨88936260428927439160578197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59290840285951626107052131 88936260428927439160578197)
          ·
            refine ⟨4168887207605973710652103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88936260428927439160578197 4168887207605973710652103)
            ·
              refine ⟨6253330811408960565978155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168887207605973710652103 6253330811408960565978155)
              ·
                refine ⟨9379996217113440848967233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253330811408960565978155 9379996217113440848967233)
                ·
                  refine ⟨7034997162835080636725425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9379996217113440848967233 7034997162835080636725425)
                  ·
                    refine ⟨5276247872126310477544069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7034997162835080636725425 5276247872126310477544069)
                    ·
                      refine ⟨989296476023683214539513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5276247872126310477544069 989296476023683214539513)
                      ·
                        rfl

theorem cell23_1926648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1926648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926648 prefixEnd_1926648 := by exact prefixLift 1926648
  have htrace : WordTrace (prefixWord ++ tailWord_1926648) baseStart_1926648 baseEnd_1926648 := by
    simpa [prefixWord, tailWord_1926648, baseEnd_1926648] using wordTrace_append hprefix tailTrace_1926648
  have hstable : (prefixWord ++ tailWord_1926648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926648).length < 2 ^ (prefixWord ++ tailWord_1926648).sum := by decide
  have hdescent : baseEnd_1926648 < baseStart_1926648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926652 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_1926652 : Nat := 118140960795 + 1926652 * 2 ^ 59
def prefixEnd_1926652 : Nat := 4983230072969 + 3 ^ 40 * 1926652 * 2
def baseEnd_1926652 : Nat := 989298529946301198889495

theorem tailTrace_1926652 : CollatzResearch.WordTrace tailWord_1926652 prefixEnd_1926652 989298529946301198889495 := by
  unfold tailWord_1926652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35135385708038162405011105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46847180944050883206681473 35135385708038162405011105)
  ·
    refine ⟨26351539281028621803758329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35135385708038162405011105 26351539281028621803758329)
    ·
      refine ⟨19763654460771466352818747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26351539281028621803758329 19763654460771466352818747)
      ·
        refine ⟨29645481691157199529228121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19763654460771466352818747 29645481691157199529228121)
        ·
          refine ⟨22234111268367899646921091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29645481691157199529228121 22234111268367899646921091)
          ·
            refine ⟨33351166902551849470381637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22234111268367899646921091 33351166902551849470381637)
            ·
              refine ⟨6253343794228471775696557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33351166902551849470381637 6253343794228471775696557)
              ·
                refine ⟨2345003922835676915886209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6253343794228471775696557 2345003922835676915886209)
                ·
                  refine ⟨1758752942126757686914657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345003922835676915886209 1758752942126757686914657)
                  ·
                    refine ⟨1319064706595068265185993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1758752942126757686914657 1319064706595068265185993)
                    ·
                      refine ⟨989298529946301198889495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319064706595068265185993 989298529946301198889495)
                      ·
                        rfl

theorem cell23_1926652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_1926652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926652 prefixEnd_1926652 := by exact prefixLift 1926652
  have htrace : WordTrace (prefixWord ++ tailWord_1926652) baseStart_1926652 baseEnd_1926652 := by
    simpa [prefixWord, tailWord_1926652, baseEnd_1926652] using wordTrace_append hprefix tailTrace_1926652
  have hstable : (prefixWord ++ tailWord_1926652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926652).length < 2 ^ (prefixWord ++ tailWord_1926652).sum := by decide
  have hdescent : baseEnd_1926652 < baseStart_1926652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926675 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 5]
def baseStart_1926675 : Nat := 118140960795 + 1926675 * 2 ^ 59
def prefixEnd_1926675 : Nat := 4983230072969 + 3 ^ 40 * 1926675 * 2
def baseEnd_1926675 : Nat := 109923371111261623211321

theorem tailTrace_1926675 : CollatzResearch.WordTrace tailWord_1926675 prefixEnd_1926675 109923371111261623211321 := by
  unfold tailWord_1926675
  simp only [CollatzResearch.WordTrace]
  refine ⟨70271610294992999738109479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46847740196661999825406319 70271610294992999738109479)
  ·
    refine ⟨105407415442489499607164219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70271610294992999738109479 105407415442489499607164219)
    ·
      refine ⟨158111123163734249410746329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105407415442489499607164219 158111123163734249410746329)
      ·
        refine ⟨118583342372800687058059747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158111123163734249410746329 118583342372800687058059747)
        ·
          refine ⟨177875013559201030587089621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118583342372800687058059747 177875013559201030587089621)
          ·
            refine ⟨4168945630293774154384913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 177875013559201030587089621 4168945630293774154384913)
            ·
              refine ⟨3126709222720330615788685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168945630293774154384913 3126709222720330615788685)
              ·
                refine ⟨1172515958520123980920757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126709222720330615788685 1172515958520123980920757)
                ·
                  refine ⟨109923371111261623211321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172515958520123980920757 109923371111261623211321)
                  ·
                    rfl

theorem cell23_1926675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 5].length) (baseStart_1926675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926675 prefixEnd_1926675 := by exact prefixLift 1926675
  have htrace : WordTrace (prefixWord ++ tailWord_1926675) baseStart_1926675 baseEnd_1926675 := by
    simpa [prefixWord, tailWord_1926675, baseEnd_1926675] using wordTrace_append hprefix tailTrace_1926675
  have hstable : (prefixWord ++ tailWord_1926675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926675).length < 2 ^ (prefixWord ++ tailWord_1926675).sum := by decide
  have hdescent : baseEnd_1926675 < baseStart_1926675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926698 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1926698 : Nat := 118140960795 + 1926698 * 2 ^ 59
def prefixEnd_1926698 : Nat := 4983230072969 + 3 ^ 40 * 1926698 * 2
def baseEnd_1926698 : Nat := 989322150056408018914283

theorem tailTrace_1926698 : CollatzResearch.WordTrace tailWord_1926698 prefixEnd_1926698 989322150056408018914283 := by
  unfold tailWord_1926698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568112293477418666549187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46848299449273116444131165 17568112293477418666549187)
  ·
    refine ⟨26352168440216127999823781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17568112293477418666549187 26352168440216127999823781)
    ·
      refine ⟨4941031582540523999966959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26352168440216127999823781 4941031582540523999966959)
      ·
        refine ⟨7411547373810785999950439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941031582540523999966959 7411547373810785999950439)
        ·
          refine ⟨11117321060716178999925659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411547373810785999950439 11117321060716178999925659)
          ·
            refine ⟨16675981591074268499888489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117321060716178999925659 16675981591074268499888489)
            ·
              refine ⟨12506986193305701374916367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16675981591074268499888489 12506986193305701374916367)
              ·
                refine ⟨18760479289958552062374551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506986193305701374916367 18760479289958552062374551)
                ·
                  refine ⟨28140718934937828093561827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18760479289958552062374551 28140718934937828093561827)
                  ·
                    refine ⟨42211078402406742140342741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28140718934937828093561827 42211078402406742140342741)
                    ·
                      refine ⟨989322150056408018914283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42211078402406742140342741 989322150056408018914283)
                      ·
                        rfl

theorem cell23_1926698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1926698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926698 prefixEnd_1926698 := by exact prefixLift 1926698
  have htrace : WordTrace (prefixWord ++ tailWord_1926698) baseStart_1926698 baseEnd_1926698 := by
    simpa [prefixWord, tailWord_1926698, baseEnd_1926698] using wordTrace_append hprefix tailTrace_1926698
  have hstable : (prefixWord ++ tailWord_1926698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926698).length < 2 ^ (prefixWord ++ tailWord_1926698).sum := by decide
  have hdescent : baseEnd_1926698 < baseStart_1926698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926726 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1926726 : Nat := 118140960795 + 1926726 * 2 ^ 59
def prefixEnd_1926726 : Nat := 4983230072969 + 3 ^ 40 * 1926726 * 2
def baseEnd_1926726 : Nat := 109926280834970434373795

theorem tailTrace_1926726 : CollatzResearch.WordTrace tailWord_1926726 prefixEnd_1926726 109926280834970434373795 := by
  unfold tailWord_1926726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196045950556507357756751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46848980278538823632144021 2196045950556507357756751)
  ·
    refine ⟨3294068925834761036635127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196045950556507357756751 3294068925834761036635127)
    ·
      refine ⟨4941103388752141554952691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294068925834761036635127 4941103388752141554952691)
      ·
        refine ⟨7411655083128212332429037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941103388752141554952691 7411655083128212332429037)
        ·
          refine ⟨2779370656173079624660889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7411655083128212332429037 2779370656173079624660889)
          ·
            refine ⟨2084527992129809718495667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2779370656173079624660889 2084527992129809718495667)
            ·
              refine ⟨3126791988194714577743501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084527992129809718495667 3126791988194714577743501)
              ·
                refine ⟨1172546995573017966653813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126791988194714577743501 1172546995573017966653813)
                ·
                  refine ⟨109926280834970434373795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172546995573017966653813 109926280834970434373795)
                  ·
                    rfl

theorem cell23_1926726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1926726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926726 prefixEnd_1926726 := by exact prefixLift 1926726
  have htrace : WordTrace (prefixWord ++ tailWord_1926726) baseStart_1926726 baseEnd_1926726 := by
    simpa [prefixWord, tailWord_1926726, baseEnd_1926726] using wordTrace_append hprefix tailTrace_1926726
  have hstable : (prefixWord ++ tailWord_1926726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926726).length < 2 ^ (prefixWord ++ tailWord_1926726).sum := by decide
  have hdescent : baseEnd_1926726 < baseStart_1926726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926775 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_1926775 : Nat := 118140960795 + 1926775 * 2 ^ 59
def prefixEnd_1926775 : Nat := 4983230072969 + 3 ^ 40 * 1926775 * 2
def baseEnd_1926775 : Nat := 989361688066804217651429

theorem tailTrace_1926775 : CollatzResearch.WordTrace tailWord_1926775 prefixEnd_1926775 989361688066804217651429 := by
  unfold tailWord_1926775
  simp only [CollatzResearch.WordTrace]
  refine ⟨70275257594630716816749779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46850171729753811211166519 70275257594630716816749779)
  ·
    refine ⟨105412886391946075225124669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70275257594630716816749779 105412886391946075225124669)
    ·
      refine ⟨39529832396979778209421751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105412886391946075225124669 39529832396979778209421751)
      ·
        refine ⟨59294748595469667314132627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39529832396979778209421751 59294748595469667314132627)
        ·
          refine ⟨88942122893204500971198941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59294748595469667314132627 88942122893204500971198941)
          ·
            refine ⟨33353296084951687864199603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88942122893204500971198941 33353296084951687864199603)
            ·
              refine ⟨50029944127427531796299405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33353296084951687864199603 50029944127427531796299405)
              ·
                refine ⟨18761229047785324423612277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50029944127427531796299405 18761229047785324423612277)
                ·
                  refine ⟨1758865223229874164713651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18761229047785324423612277 1758865223229874164713651)
                  ·
                    refine ⟨2638297834844811247070477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1758865223229874164713651 2638297834844811247070477)
                    ·
                      refine ⟨989361688066804217651429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2638297834844811247070477 989361688066804217651429)
                      ·
                        rfl

theorem cell23_1926775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_1926775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926775 prefixEnd_1926775 := by exact prefixLift 1926775
  have htrace : WordTrace (prefixWord ++ tailWord_1926775) baseStart_1926775 baseEnd_1926775 := by
    simpa [prefixWord, tailWord_1926775, baseEnd_1926775] using wordTrace_append hprefix tailTrace_1926775
  have hstable : (prefixWord ++ tailWord_1926775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926775).length < 2 ^ (prefixWord ++ tailWord_1926775).sum := by decide
  have hdescent : baseEnd_1926775 < baseStart_1926775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926832 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 5, 2, 2]
def baseStart_1926832 : Nat := 118140960795 + 1926832 * 2 ^ 59
def prefixEnd_1926832 : Nat := 4983230072969 + 3 ^ 40 * 1926832 * 2
def baseEnd_1926832 : Nat := 989390956464110494638667

theorem tailTrace_1926832 : CollatzResearch.WordTrace tailWord_1926832 prefixEnd_1926832 989390956464110494638667 := by
  unfold tailWord_1926832
  simp only [CollatzResearch.WordTrace]
  refine ⟨35138668277712107775787375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46851557703616143701049833 35138668277712107775787375)
  ·
    refine ⟨52708002416568161663681063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35138668277712107775787375 52708002416568161663681063)
    ·
      refine ⟨79062003624852242495521595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52708002416568161663681063 79062003624852242495521595)
      ·
        refine ⟨118593005437278363743282393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79062003624852242495521595 118593005437278363743282393)
        ·
          refine ⟨88944754077958772807461795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118593005437278363743282393 88944754077958772807461795)
          ·
            refine ⟨133417131116938159211192693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88944754077958772807461795 133417131116938159211192693)
            ·
              refine ⟨12507856042212952426049315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133417131116938159211192693 12507856042212952426049315)
              ·
                refine ⟨18761784063319428639073973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507856042212952426049315 18761784063319428639073973)
                ·
                  refine ⟨1758917255936196434913185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18761784063319428639073973 1758917255936196434913185)
                  ·
                    refine ⟨1319187941952147326184889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1758917255936196434913185 1319187941952147326184889)
                    ·
                      refine ⟨989390956464110494638667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319187941952147326184889 989390956464110494638667)
                      ·
                        rfl

theorem cell23_1926832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 2, 2].length) (baseStart_1926832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926832 prefixEnd_1926832 := by exact prefixLift 1926832
  have htrace : WordTrace (prefixWord ++ tailWord_1926832) baseStart_1926832 baseEnd_1926832 := by
    simpa [prefixWord, tailWord_1926832, baseEnd_1926832] using wordTrace_append hprefix tailTrace_1926832
  have hstable : (prefixWord ++ tailWord_1926832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926832).length < 2 ^ (prefixWord ++ tailWord_1926832).sum := by decide
  have hdescent : baseEnd_1926832 < baseStart_1926832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926835 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 3]
def baseStart_1926835 : Nat := 118140960795 + 1926835 * 2 ^ 59
def prefixEnd_1926835 : Nat := 4983230072969 + 3 ^ 40 * 1926835 * 2
def baseEnd_1926835 : Nat := 989392496906073982901153

theorem tailTrace_1926835 : CollatzResearch.WordTrace tailWord_1926835 prefixEnd_1926835 989392496906073982901153 := by
  unfold tailWord_1926835
  simp only [CollatzResearch.WordTrace]
  refine ⟨70277445974413347063933959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46851630649608898042622639 70277445974413347063933959)
  ·
    refine ⟨105416168961620020595900939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70277445974413347063933959 105416168961620020595900939)
    ·
      refine ⟨158124253442430030893851409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105416168961620020595900939 158124253442430030893851409)
      ·
        refine ⟨118593190081822523170388557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158124253442430030893851409 118593190081822523170388557)
        ·
          refine ⟨44472446280683446188895709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118593190081822523170388557 44472446280683446188895709)
          ·
            refine ⟨16677167355256292320835891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44472446280683446188895709 16677167355256292320835891)
            ·
              refine ⟨25015751032884438481253837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16677167355256292320835891 25015751032884438481253837)
              ·
                refine ⟨9380906637331664430470189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25015751032884438481253837 9380906637331664430470189)
                ·
                  refine ⟨3517839988999374161426321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9380906637331664430470189 3517839988999374161426321)
                  ·
                    refine ⟨2638379991749530621069741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3517839988999374161426321 2638379991749530621069741)
                    ·
                      refine ⟨989392496906073982901153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2638379991749530621069741 989392496906073982901153)
                      ·
                        rfl

theorem cell23_1926835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_1926835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926835 prefixEnd_1926835 := by exact prefixLift 1926835
  have htrace : WordTrace (prefixWord ++ tailWord_1926835) baseStart_1926835 baseEnd_1926835 := by
    simpa [prefixWord, tailWord_1926835, baseEnd_1926835] using wordTrace_append hprefix tailTrace_1926835
  have hstable : (prefixWord ++ tailWord_1926835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926835).length < 2 ^ (prefixWord ++ tailWord_1926835).sum := by decide
  have hdescent : baseEnd_1926835 < baseStart_1926835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926845 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1926845 : Nat := 118140960795 + 1926845 * 2 ^ 59
def prefixEnd_1926845 : Nat := 4983230072969 + 3 ^ 40 * 1926845 * 2
def baseEnd_1926845 : Nat := 989397631712618943776107

theorem tailTrace_1926845 : CollatzResearch.WordTrace tailWord_1926845 prefixEnd_1926845 989397631712618943776107 := by
  unfold tailWord_1926845
  simp only [CollatzResearch.WordTrace]
  refine ⟨70277810704377118771797989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46851873802918079181198659 70277810704377118771797989)
  ·
    refine ⟨13177089507070709769712123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70277810704377118771797989 13177089507070709769712123)
    ·
      refine ⟨19765634260606064654568185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13177089507070709769712123 19765634260606064654568185)
      ·
        refine ⟨14824225695454548490926139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19765634260606064654568185 14824225695454548490926139)
        ·
          refine ⟨22236338543181822736389209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14824225695454548490926139 22236338543181822736389209)
          ·
            refine ⟨16677253907386367052291907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22236338543181822736389209 16677253907386367052291907)
            ·
              refine ⟨25015880861079550578437861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16677253907386367052291907 25015880861079550578437861)
              ·
                refine ⟨4690477661452415733457099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25015880861079550578437861 4690477661452415733457099)
                ·
                  refine ⟨7035716492178623600185649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690477661452415733457099 7035716492178623600185649)
                  ·
                    refine ⟨5276787369133967700139237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7035716492178623600185649 5276787369133967700139237)
                    ·
                      refine ⟨989397631712618943776107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5276787369133967700139237 989397631712618943776107)
                      ·
                        rfl

theorem cell23_1926845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1926845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926845 prefixEnd_1926845 := by exact prefixLift 1926845
  have htrace : WordTrace (prefixWord ++ tailWord_1926845) baseStart_1926845 baseEnd_1926845 := by
    simpa [prefixWord, tailWord_1926845, baseEnd_1926845] using wordTrace_append hprefix tailTrace_1926845
  have hstable : (prefixWord ++ tailWord_1926845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926845).length < 2 ^ (prefixWord ++ tailWord_1926845).sum := by decide
  have hdescent : baseEnd_1926845 < baseStart_1926845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926866 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_1926866 : Nat := 118140960795 + 1926866 * 2 ^ 59
def prefixEnd_1926866 : Nat := 4983230072969 + 3 ^ 40 * 1926866 * 2
def baseEnd_1926866 : Nat := 989408414806363361613511

theorem tailTrace_1926866 : CollatzResearch.WordTrace tailWord_1926866 prefixEnd_1926866 989408414806363361613511 := by
  unfold tailWord_1926866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569644159325259839578113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46852384424867359572208301 17569644159325259839578113)
  ·
    refine ⟨13177233119493944879683585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17569644159325259839578113 13177233119493944879683585)
    ·
      refine ⟨9882924839620458659762689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13177233119493944879683585 9882924839620458659762689)
      ·
        refine ⟨7412193629715343994822017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9882924839620458659762689 7412193629715343994822017)
        ·
          refine ⟨5559145222286507996116513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7412193629715343994822017 5559145222286507996116513)
          ·
            refine ⟨4169358916714880997087385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559145222286507996116513 4169358916714880997087385)
            ·
              refine ⟨3127019187536160747815539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169358916714880997087385 3127019187536160747815539)
              ·
                refine ⟨4690528781304241121723309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127019187536160747815539 4690528781304241121723309)
                ·
                  refine ⟨1758948292989090420646241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4690528781304241121723309 1758948292989090420646241)
                  ·
                    refine ⟨1319211219741817815484681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1758948292989090420646241 1319211219741817815484681)
                    ·
                      refine ⟨989408414806363361613511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319211219741817815484681 989408414806363361613511)
                      ·
                        rfl

theorem cell23_1926866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_1926866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926866 prefixEnd_1926866 := by exact prefixLift 1926866
  have htrace : WordTrace (prefixWord ++ tailWord_1926866) baseStart_1926866 baseEnd_1926866 := by
    simpa [prefixWord, tailWord_1926866, baseEnd_1926866] using wordTrace_append hprefix tailTrace_1926866
  have hstable : (prefixWord ++ tailWord_1926866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926866).length < 2 ^ (prefixWord ++ tailWord_1926866).sum := by decide
  have hdescent : baseEnd_1926866 < baseStart_1926866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926876 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1926876 : Nat := 118140960795 + 1926876 * 2 ^ 59
def prefixEnd_1926876 : Nat := 4983230072969 + 3 ^ 40 * 1926876 * 2
def baseEnd_1926876 : Nat := 329804516537636107496155

theorem tailTrace_1926876 : CollatzResearch.WordTrace tailWord_1926876 prefixEnd_1926876 329804516537636107496155 := by
  unfold tailWord_1926876
  simp only [CollatzResearch.WordTrace]
  refine ⟨35139470683632405533088241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46852627578176540710784321 35139470683632405533088241)
  ·
    refine ⟨26354603012724304149816181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35139470683632405533088241 26354603012724304149816181)
    ·
      refine ⟨2470744032442903514045267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26354603012724304149816181 2470744032442903514045267)
      ·
        refine ⟨3706116048664355271067901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470744032442903514045267 3706116048664355271067901)
        ·
          refine ⟨1389793518249133226650463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3706116048664355271067901 1389793518249133226650463)
          ·
            refine ⟨2084690277373699839975695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389793518249133226650463 2084690277373699839975695)
            ·
              refine ⟨3127035416060549759963543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084690277373699839975695 3127035416060549759963543)
              ·
                refine ⟨4690553124090824639945315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127035416060549759963543 4690553124090824639945315)
                ·
                  refine ⟨7035829686136236959917973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690553124090824639945315 7035829686136236959917973)
                  ·
                    refine ⟨329804516537636107496155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7035829686136236959917973 329804516537636107496155)
                    ·
                      rfl

theorem cell23_1926876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1926876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926876 prefixEnd_1926876 := by exact prefixLift 1926876
  have htrace : WordTrace (prefixWord ++ tailWord_1926876) baseStart_1926876 baseEnd_1926876 := by
    simpa [prefixWord, tailWord_1926876, baseEnd_1926876] using wordTrace_append hprefix tailTrace_1926876
  have hstable : (prefixWord ++ tailWord_1926876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926876).length < 2 ^ (prefixWord ++ tailWord_1926876).sum := by decide
  have hdescent : baseEnd_1926876 < baseStart_1926876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926892 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 3, 3, 2]
def baseStart_1926892 : Nat := 118140960795 + 1926892 * 2 ^ 59
def prefixEnd_1926892 : Nat := 4983230072969 + 3 ^ 40 * 1926892 * 2
def baseEnd_1926892 : Nat := 989421765303380259888391

theorem tailTrace_1926892 : CollatzResearch.WordTrace tailWord_1926892 prefixEnd_1926892 989421765303380259888391 := by
  unfold tailWord_1926892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35139762467603422899379465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46853016623471230532505953 35139762467603422899379465)
  ·
    refine ⟨26354821850702567174534599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35139762467603422899379465 26354821850702567174534599)
    ·
      refine ⟨39532232776053850761801899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26354821850702567174534599 39532232776053850761801899)
      ·
        refine ⟨59298349164080776142702849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39532232776053850761801899 59298349164080776142702849)
        ·
          refine ⟨44473761873060582107027137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59298349164080776142702849 44473761873060582107027137)
          ·
            refine ⟨33355321404795436580270353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44473761873060582107027137 33355321404795436580270353)
            ·
              refine ⟨25016491053596577435202765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33355321404795436580270353 25016491053596577435202765)
              ·
                refine ⟨9381184145098716538201037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25016491053596577435202765 9381184145098716538201037)
                ·
                  refine ⟨3517944054412018701825389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9381184145098716538201037 3517944054412018701825389)
                  ·
                    refine ⟨1319229020404507013184521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3517944054412018701825389 1319229020404507013184521)
                    ·
                      refine ⟨989421765303380259888391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319229020404507013184521 989421765303380259888391)
                      ·
                        rfl

theorem cell23_1926892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_1926892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926892 prefixEnd_1926892 := by exact prefixLift 1926892
  have htrace : WordTrace (prefixWord ++ tailWord_1926892) baseStart_1926892 baseEnd_1926892 := by
    simpa [prefixWord, tailWord_1926892, baseEnd_1926892] using wordTrace_append hprefix tailTrace_1926892
  have hstable : (prefixWord ++ tailWord_1926892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926892).length < 2 ^ (prefixWord ++ tailWord_1926892).sum := by decide
  have hdescent : baseEnd_1926892 < baseStart_1926892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926939 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 2, 2, 2]
def baseStart_1926939 : Nat := 118140960795 + 1926939 * 2 ^ 59
def prefixEnd_1926939 : Nat := 4983230072969 + 3 ^ 40 * 1926939 * 2
def baseEnd_1926939 : Nat := 989445898894141576000675

theorem tailTrace_1926939 : CollatzResearch.WordTrace tailWord_1926939 prefixEnd_1926939 989445898894141576000675 := by
  unfold tailWord_1926939
  simp only [CollatzResearch.WordTrace]
  refine ⟨70281239166036572825719871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46854159444024381883813247 70281239166036572825719871)
  ·
    refine ⟨105421858749054859238579807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70281239166036572825719871 105421858749054859238579807)
    ·
      refine ⟨158132788123582288857869711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105421858749054859238579807 158132788123582288857869711)
      ·
        refine ⟨237199182185373433286804567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158132788123582288857869711 237199182185373433286804567)
        ·
          refine ⟨355798773278060149930206851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237199182185373433286804567 355798773278060149930206851)
          ·
            refine ⟨533698159917090224895310277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355798773278060149930206851 533698159917090224895310277)
            ·
              refine ⟨100068404984454417167870677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 533698159917090224895310277 100068404984454417167870677)
              ·
                refine ⟨2345353241823150402371969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100068404984454417167870677 2345353241823150402371969)
                ·
                  refine ⟨1759014931367362801778977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345353241823150402371969 1759014931367362801778977)
                  ·
                    refine ⟨1319261198525522101334233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1759014931367362801778977 1319261198525522101334233)
                    ·
                      refine ⟨989445898894141576000675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319261198525522101334233 989445898894141576000675)
                      ·
                        rfl

theorem cell23_1926939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 2, 2].length) (baseStart_1926939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926939 prefixEnd_1926939 := by exact prefixLift 1926939
  have htrace : WordTrace (prefixWord ++ tailWord_1926939) baseStart_1926939 baseEnd_1926939 := by
    simpa [prefixWord, tailWord_1926939, baseEnd_1926939] using wordTrace_append hprefix tailTrace_1926939
  have hstable : (prefixWord ++ tailWord_1926939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926939).length < 2 ^ (prefixWord ++ tailWord_1926939).sum := by decide
  have hdescent : baseEnd_1926939 < baseStart_1926939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926973 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1926973 : Nat := 118140960795 + 1926973 * 2 ^ 59
def prefixEnd_1926973 : Nat := 4983230072969 + 3 ^ 40 * 1926973 * 2
def baseEnd_1926973 : Nat := 989463357236394442975519

theorem tailTrace_1926973 : CollatzResearch.WordTrace tailWord_1926973 prefixEnd_1926973 989463357236394442975519 := by
  unfold tailWord_1926973
  simp only [CollatzResearch.WordTrace]
  refine ⟨70282479247913396632457573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46854986165275597754971715 70282479247913396632457573)
  ·
    refine ⟨13177964858983761868585795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70282479247913396632457573 13177964858983761868585795)
    ·
      refine ⟨19766947288475642802878693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13177964858983761868585795 19766947288475642802878693)
      ·
        refine ⟨3706302616589183025539755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19766947288475642802878693 3706302616589183025539755)
        ·
          refine ⟨5559453924883774538309633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706302616589183025539755 5559453924883774538309633)
          ·
            refine ⟨4169590443662830903732225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5559453924883774538309633 4169590443662830903732225)
            ·
              refine ⟨3127192832747123177799169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169590443662830903732225 3127192832747123177799169)
              ·
                refine ⟨2345394624560342383349377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127192832747123177799169 2345394624560342383349377)
                ·
                  refine ⟨1759045968420256787512033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345394624560342383349377 1759045968420256787512033)
                  ·
                    refine ⟨1319284476315192590634025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1759045968420256787512033 1319284476315192590634025)
                    ·
                      refine ⟨989463357236394442975519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319284476315192590634025 989463357236394442975519)
                      ·
                        rfl

theorem cell23_1926973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1926973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926973 prefixEnd_1926973 := by exact prefixLift 1926973
  have htrace : WordTrace (prefixWord ++ tailWord_1926973) baseStart_1926973 baseEnd_1926973 := by
    simpa [prefixWord, tailWord_1926973, baseEnd_1926973] using wordTrace_append hprefix tailTrace_1926973
  have hstable : (prefixWord ++ tailWord_1926973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926973).length < 2 ^ (prefixWord ++ tailWord_1926973).sum := by decide
  have hdescent : baseEnd_1926973 < baseStart_1926973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926979 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 5]
def baseStart_1926979 : Nat := 118140960795 + 1926979 * 2 ^ 59
def prefixEnd_1926979 : Nat := 4983230072969 + 3 ^ 40 * 1926979 * 2
def baseEnd_1926979 : Nat := 109940715346702379944499

theorem tailTrace_1926979 : CollatzResearch.WordTrace tailWord_1926979 prefixEnd_1926979 109940715346702379944499 := by
  unfold tailWord_1926979
  simp only [CollatzResearch.WordTrace]
  refine ⟨70282698085891659657175991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46855132057261106438117327 70282698085891659657175991)
  ·
    refine ⟨105424047128837489485763987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70282698085891659657175991 105424047128837489485763987)
    ·
      refine ⟨158136070693256234228645981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105424047128837489485763987 158136070693256234228645981)
      ·
        refine ⟨59301026509971087835742243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158136070693256234228645981 59301026509971087835742243)
        ·
          refine ⟨88951539764956631753613365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59301026509971087835742243 88951539764956631753613365)
          ·
            refine ⟨8339206852964684226901253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88951539764956631753613365 8339206852964684226901253)
            ·
              refine ⟨1563601284930878292543985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8339206852964684226901253 1563601284930878292543985)
              ·
                refine ⟨1172700963698158719407989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563601284930878292543985 1172700963698158719407989)
                ·
                  refine ⟨109940715346702379944499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172700963698158719407989 109940715346702379944499)
                  ·
                    rfl

theorem cell23_1926979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 5].length) (baseStart_1926979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926979 prefixEnd_1926979 := by exact prefixLift 1926979
  have htrace : WordTrace (prefixWord ++ tailWord_1926979) baseStart_1926979 baseEnd_1926979 := by
    simpa [prefixWord, tailWord_1926979, baseEnd_1926979] using wordTrace_append hprefix tailTrace_1926979
  have hstable : (prefixWord ++ tailWord_1926979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926979).length < 2 ^ (prefixWord ++ tailWord_1926979).sum := by decide
  have hdescent : baseEnd_1926979 < baseStart_1926979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926985 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_1926985 : Nat := 118140960795 + 1926985 * 2 ^ 59
def prefixEnd_1926985 : Nat := 4983230072969 + 3 ^ 40 * 1926985 * 2
def baseEnd_1926985 : Nat := 989469519004248396025463

theorem tailTrace_1926985 : CollatzResearch.WordTrace tailWord_1926985 prefixEnd_1926985 989469519004248396025463 := by
  unfold tailWord_1926985
  simp only [CollatzResearch.WordTrace]
  refine ⟨70282916923869922681894409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46855277949246615121262939 70282916923869922681894409)
  ·
    refine ⟨52712187692902442011420807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70282916923869922681894409 52712187692902442011420807)
    ·
      refine ⟨79068281539353663017131211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52712187692902442011420807 79068281539353663017131211)
      ·
        refine ⟨118602422309030494525696817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79068281539353663017131211 118602422309030494525696817)
        ·
          refine ⟨88951816731772870894272613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118602422309030494525696817 88951816731772870894272613)
          ·
            refine ⟨16678465637207413292676115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88951816731772870894272613 16678465637207413292676115)
            ·
              refine ⟨25017698455811119939014173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678465637207413292676115 25017698455811119939014173)
              ·
                refine ⟨9381636920929169977130315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25017698455811119939014173 9381636920929169977130315)
                ·
                  refine ⟨14072455381393754965695473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381636920929169977130315 14072455381393754965695473)
                  ·
                    refine ⟨10554341536045316224271605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14072455381393754965695473 10554341536045316224271605)
                    ·
                      refine ⟨989469519004248396025463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10554341536045316224271605 989469519004248396025463)
                      ·
                        rfl

theorem cell23_1926985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_1926985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926985 prefixEnd_1926985 := by exact prefixLift 1926985
  have htrace : WordTrace (prefixWord ++ tailWord_1926985) baseStart_1926985 baseEnd_1926985 := by
    simpa [prefixWord, tailWord_1926985, baseEnd_1926985] using wordTrace_append hprefix tailTrace_1926985
  have hstable : (prefixWord ++ tailWord_1926985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926985).length < 2 ^ (prefixWord ++ tailWord_1926985).sum := by decide
  have hdescent : baseEnd_1926985 < baseStart_1926985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926989 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1926989 : Nat := 118140960795 + 1926989 * 2 ^ 59
def prefixEnd_1926989 : Nat := 4983230072969 + 3 ^ 40 * 1926989 * 2
def baseEnd_1926989 : Nat := 989471572926866380375445

theorem tailTrace_1926989 : CollatzResearch.WordTrace tailWord_1926989 prefixEnd_1926989 989471572926866380375445 := by
  unfold tailWord_1926989
  simp only [CollatzResearch.WordTrace]
  refine ⟨70283062815855431365040021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46855375210570287576693347 70283062815855431365040021)
  ·
    refine ⟨3294518569493223345236251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70283062815855431365040021 3294518569493223345236251)
    ·
      refine ⟨4941777854239835017854377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294518569493223345236251 4941777854239835017854377)
      ·
        refine ⟨3706333390679876263390783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4941777854239835017854377 3706333390679876263390783)
        ·
          refine ⟨5559500086019814395086175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706333390679876263390783 5559500086019814395086175)
          ·
            refine ⟨8339250129029721592629263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559500086019814395086175 8339250129029721592629263)
            ·
              refine ⟨12508875193544582388943895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339250129029721592629263 12508875193544582388943895)
              ·
                refine ⟨18763312790316873583415843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12508875193544582388943895 18763312790316873583415843)
                ·
                  refine ⟨28144969185475310375123765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18763312790316873583415843 28144969185475310375123765)
                  ·
                    refine ⟨2638590861138310347667853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28144969185475310375123765 2638590861138310347667853)
                    ·
                      refine ⟨989471572926866380375445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2638590861138310347667853 989471572926866380375445)
                      ·
                        rfl

theorem cell23_1926989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1926989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1926989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1926989 prefixEnd_1926989 := by exact prefixLift 1926989
  have htrace : WordTrace (prefixWord ++ tailWord_1926989) baseStart_1926989 baseEnd_1926989 := by
    simpa [prefixWord, tailWord_1926989, baseEnd_1926989] using wordTrace_append hprefix tailTrace_1926989
  have hstable : (prefixWord ++ tailWord_1926989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926989).length < 2 ^ (prefixWord ++ tailWord_1926989).sum := by decide
  have hdescent : baseEnd_1926989 < baseStart_1926989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927025 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1927025 : Nat := 118140960795 + 1927025 * 2 ^ 59
def prefixEnd_1927025 : Nat := 4983230072969 + 3 ^ 40 * 1927025 * 2
def baseEnd_1927025 : Nat := 989490058230428239525279

theorem tailTrace_1927025 : CollatzResearch.WordTrace tailWord_1927025 prefixEnd_1927025 989490058230428239525279 := by
  unfold tailWord_1927025
  simp only [CollatzResearch.WordTrace]
  refine ⟨70284375843725009513350529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46856250562483339675567019 70284375843725009513350529)
  ·
    refine ⟨52713281882793757135012897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70284375843725009513350529 52713281882793757135012897)
    ·
      refine ⟨39534961412095317851259673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52713281882793757135012897 39534961412095317851259673)
      ·
        refine ⟨29651221059071488388444755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39534961412095317851259673 29651221059071488388444755)
        ·
          refine ⟨44476831588607232582667133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29651221059071488388444755 44476831588607232582667133)
          ·
            refine ⟨16678811845727712218500175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44476831588607232582667133 16678811845727712218500175)
            ·
              refine ⟨25018217768591568327750263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678811845727712218500175 25018217768591568327750263)
              ·
                refine ⟨37527326652887352491625395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25018217768591568327750263 37527326652887352491625395)
                ·
                  refine ⟨56290989979331028737438093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37527326652887352491625395 56290989979331028737438093)
                  ·
                    refine ⟨21109121242249135776539285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56290989979331028737438093 21109121242249135776539285)
                    ·
                      refine ⟨989490058230428239525279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21109121242249135776539285 989490058230428239525279)
                      ·
                        rfl

theorem cell23_1927025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1927025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927025 prefixEnd_1927025 := by exact prefixLift 1927025
  have htrace : WordTrace (prefixWord ++ tailWord_1927025) baseStart_1927025 baseEnd_1927025 := by
    simpa [prefixWord, tailWord_1927025, baseEnd_1927025] using wordTrace_append hprefix tailTrace_1927025
  have hstable : (prefixWord ++ tailWord_1927025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927025).length < 2 ^ (prefixWord ++ tailWord_1927025).sum := by decide
  have hdescent : baseEnd_1927025 < baseStart_1927025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927029 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1927029 : Nat := 118140960795 + 1927029 * 2 ^ 59
def prefixEnd_1927029 : Nat := 4983230072969 + 3 ^ 40 * 1927029 * 2
def baseEnd_1927029 : Nat := 989492112153046223875261

theorem tailTrace_1927029 : CollatzResearch.WordTrace tailWord_1927029 prefixEnd_1927029 989492112153046223875261 := by
  unfold tailWord_1927029
  simp only [CollatzResearch.WordTrace]
  refine ⟨70284521735710518196496141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46856347823807012130997427 70284521735710518196496141)
  ·
    refine ⟨26356695650891444323686053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70284521735710518196496141 26356695650891444323686053)
    ·
      refine ⟨4941880434542145810691135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26356695650891444323686053 4941880434542145810691135)
      ·
        refine ⟨7412820651813218716036703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941880434542145810691135 7412820651813218716036703)
        ·
          refine ⟨11119230977719828074055055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412820651813218716036703 11119230977719828074055055)
          ·
            refine ⟨16678846466579742111082583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11119230977719828074055055 16678846466579742111082583)
            ·
              refine ⟨25018269699869613166623875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678846466579742111082583 25018269699869613166623875)
              ·
                refine ⟨37527404549804419749935813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25018269699869613166623875 37527404549804419749935813)
                ·
                  refine ⟨7036388353088328703112965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37527404549804419749935813 7036388353088328703112965)
                  ·
                    refine ⟨1319322816204061631833681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7036388353088328703112965 1319322816204061631833681)
                    ·
                      refine ⟨989492112153046223875261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1319322816204061631833681 989492112153046223875261)
                      ·
                        rfl

theorem cell23_1927029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1927029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927029 prefixEnd_1927029 := by exact prefixLift 1927029
  have htrace : WordTrace (prefixWord ++ tailWord_1927029) baseStart_1927029 baseEnd_1927029 := by
    simpa [prefixWord, tailWord_1927029, baseEnd_1927029] using wordTrace_append hprefix tailTrace_1927029
  have hstable : (prefixWord ++ tailWord_1927029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927029).length < 2 ^ (prefixWord ++ tailWord_1927029).sum := by decide
  have hdescent : baseEnd_1927029 < baseStart_1927029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927116 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_1927116 : Nat := 118140960795 + 1927116 * 2 ^ 59
def prefixEnd_1927116 : Nat := 4983230072969 + 3 ^ 40 * 1927116 * 2
def baseEnd_1927116 : Nat := 329845594989995794495787

theorem tailTrace_1927116 : CollatzResearch.WordTrace tailWord_1927116 prefixEnd_1927116 329845594989995794495787 := by
  unfold tailWord_1927116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35143847443197666027456601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46858463257596888036608801 35143847443197666027456601)
  ·
    refine ⟨26357885582398249520592451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35143847443197666027456601 26357885582398249520592451)
    ·
      refine ⟨39536828373597374280888677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26357885582398249520592451 39536828373597374280888677)
      ·
        refine ⟨7413155320049507677666627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39536828373597374280888677 7413155320049507677666627)
        ·
          refine ⟨11119732980074261516499941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413155320049507677666627 11119732980074261516499941)
          ·
            refine ⟨2084949933763924034343739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11119732980074261516499941 2084949933763924034343739)
            ·
              refine ⟨3127424900645886051515609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084949933763924034343739 3127424900645886051515609)
              ·
                refine ⟨2345568675484414538636707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127424900645886051515609 2345568675484414538636707)
                ·
                  refine ⟨3518353013226621807955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345568675484414538636707 3518353013226621807955061)
                  ·
                    refine ⟨329845594989995794495787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3518353013226621807955061 329845594989995794495787)
                    ·
                      rfl

theorem cell23_1927116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_1927116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927116 prefixEnd_1927116 := by exact prefixLift 1927116
  have htrace : WordTrace (prefixWord ++ tailWord_1927116) baseStart_1927116 baseEnd_1927116 := by
    simpa [prefixWord, tailWord_1927116, baseEnd_1927116] using wordTrace_append hprefix tailTrace_1927116
  have hstable : (prefixWord ++ tailWord_1927116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927116).length < 2 ^ (prefixWord ++ tailWord_1927116).sum := by decide
  have hdescent : baseEnd_1927116 < baseStart_1927116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927129 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 1, 6]
def baseStart_1927129 : Nat := 118140960795 + 1927129 * 2 ^ 59
def prefixEnd_1927129 : Nat := 4983230072969 + 3 ^ 40 * 1927129 * 2
def baseEnd_1927129 : Nat := 329847820072831944208267

theorem tailTrace_1927129 : CollatzResearch.WordTrace tailWord_1927129 prefixEnd_1927129 329847820072831944208267 := by
  unfold tailWord_1927129
  simp only [CollatzResearch.WordTrace]
  refine ⟨70288169035348235275136441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46858779356898823516757627 70288169035348235275136441)
  ·
    refine ⟨52716126776511176456352331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70288169035348235275136441 52716126776511176456352331)
    ·
      refine ⟨79074190164766764684528497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52716126776511176456352331 79074190164766764684528497)
      ·
        refine ⟨59305642623575073513396373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79074190164766764684528497 59305642623575073513396373)
        ·
          refine ⟨2779951997980081570940455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59305642623575073513396373 2779951997980081570940455)
          ·
            refine ⟨4169927996970122356410683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779951997980081570940455 4169927996970122356410683)
            ·
              refine ⟨6254891995455183534616025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169927996970122356410683 6254891995455183534616025)
              ·
                refine ⟨4691168996591387650962019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6254891995455183534616025 4691168996591387650962019)
                ·
                  refine ⟨7036753494887081476443029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691168996591387650962019 7036753494887081476443029)
                  ·
                    refine ⟨329847820072831944208267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7036753494887081476443029 329847820072831944208267)
                    ·
                      rfl

theorem cell23_1927129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_1927129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927129 prefixEnd_1927129 := by exact prefixLift 1927129
  have htrace : WordTrace (prefixWord ++ tailWord_1927129) baseStart_1927129 baseEnd_1927129 := by
    simpa [prefixWord, tailWord_1927129, baseEnd_1927129] using wordTrace_append hprefix tailTrace_1927129
  have hstable : (prefixWord ++ tailWord_1927129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927129).length < 2 ^ (prefixWord ++ tailWord_1927129).sum := by decide
  have hdescent : baseEnd_1927129 < baseStart_1927129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927133 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1927133 : Nat := 118140960795 + 1927133 * 2 ^ 59
def prefixEnd_1927133 : Nat := 4983230072969 + 3 ^ 40 * 1927133 * 2
def baseEnd_1927133 : Nat := 329848504713704605658261

theorem tailTrace_1927133 : CollatzResearch.WordTrace tailWord_1927133 prefixEnd_1927133 329848504713704605658261 := by
  unfold tailWord_1927133
  simp only [CollatzResearch.WordTrace]
  refine ⟨70288314927333743958282053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46858876618222495972188035 70288314927333743958282053)
  ·
    refine ⟨13179059048875076992177885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70288314927333743958282053 13179059048875076992177885)
    ·
      refine ⟨4942147143328153872066707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13179059048875076992177885 4942147143328153872066707)
      ·
        refine ⟨7413220714992230808100061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942147143328153872066707 7413220714992230808100061)
        ·
          refine ⟨2779957768122086553037523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7413220714992230808100061 2779957768122086553037523)
          ·
            refine ⟨4169936652183129829556285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779957768122086553037523 4169936652183129829556285)
            ·
              refine ⟨1563726244568673686083607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4169936652183129829556285 1563726244568673686083607)
              ·
                refine ⟨2345589366853010529125411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563726244568673686083607 2345589366853010529125411)
                ·
                  refine ⟨3518384050279515793688117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345589366853010529125411 3518384050279515793688117)
                  ·
                    refine ⟨329848504713704605658261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3518384050279515793688117 329848504713704605658261)
                    ·
                      rfl

theorem cell23_1927133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1927133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927133 prefixEnd_1927133 := by exact prefixLift 1927133
  have htrace : WordTrace (prefixWord ++ tailWord_1927133) baseStart_1927133 baseEnd_1927133 := by
    simpa [prefixWord, tailWord_1927133, baseEnd_1927133] using wordTrace_append hprefix tailTrace_1927133
  have hstable : (prefixWord ++ tailWord_1927133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927133).length < 2 ^ (prefixWord ++ tailWord_1927133).sum := by decide
  have hdescent : baseEnd_1927133 < baseStart_1927133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927139 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1927139 : Nat := 118140960795 + 1927139 * 2 ^ 59
def prefixEnd_1927139 : Nat := 4983230072969 + 3 ^ 40 * 1927139 * 2
def baseEnd_1927139 : Nat := 989548595025040793499755

theorem tailTrace_1927139 : CollatzResearch.WordTrace tailWord_1927139 prefixEnd_1927139 989548595025040793499755 := by
  unfold tailWord_1927139
  simp only [CollatzResearch.WordTrace]
  refine ⟨70288533765312006983000471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46859022510208004655333647 70288533765312006983000471)
  ·
    refine ⟨105432800647968010474500707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70288533765312006983000471 105432800647968010474500707)
    ·
      refine ⟨158149200971952015711751061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105432800647968010474500707 158149200971952015711751061)
      ·
        refine ⟨7413243795560250736488331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158149200971952015711751061 7413243795560250736488331)
        ·
          refine ⟨11119865693340376104732497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413243795560250736488331 11119865693340376104732497)
          ·
            refine ⟨8339899270005282078549373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11119865693340376104732497 8339899270005282078549373)
            ·
              refine ⟨3127462226251980779456015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8339899270005282078549373 3127462226251980779456015)
              ·
                refine ⟨4691193339377971169184023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127462226251980779456015 4691193339377971169184023)
                ·
                  refine ⟨7036790009066956753776035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691193339377971169184023 7036790009066956753776035)
                  ·
                    refine ⟨10555185013600435130664053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7036790009066956753776035 10555185013600435130664053)
                    ·
                      refine ⟨989548595025040793499755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10555185013600435130664053 989548595025040793499755)
                      ·
                        rfl

theorem cell23_1927139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1927139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927139 prefixEnd_1927139 := by exact prefixLift 1927139
  have htrace : WordTrace (prefixWord ++ tailWord_1927139) baseStart_1927139 baseEnd_1927139 := by
    simpa [prefixWord, tailWord_1927139, baseEnd_1927139] using wordTrace_append hprefix tailTrace_1927139
  have hstable : (prefixWord ++ tailWord_1927139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927139).length < 2 ^ (prefixWord ++ tailWord_1927139).sum := by decide
  have hdescent : baseEnd_1927139 < baseStart_1927139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927146 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1927146 : Nat := 118140960795 + 1927146 * 2 ^ 59
def prefixEnd_1927146 : Nat := 4983230072969 + 3 ^ 40 * 1927146 * 2
def baseEnd_1927146 : Nat := 329850729796540755370741

theorem tailTrace_1927146 : CollatzResearch.WordTrace tailWord_1927146 prefixEnd_1927146 329850729796540755370741 := by
  unfold tailWord_1927146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17572197269071661794626323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46859192717524431452336861 17572197269071661794626323)
  ·
    refine ⟨26358295903607492691939485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17572197269071661794626323 26358295903607492691939485)
    ·
      refine ⟨9884360963852809759477307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26358295903607492691939485 9884360963852809759477307)
      ·
        refine ⟨14826541445779214639215961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9884360963852809759477307 14826541445779214639215961)
        ·
          refine ⟨11119906084334410979411971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14826541445779214639215961 11119906084334410979411971)
          ·
            refine ⟨16679859126501616469117957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11119906084334410979411971 16679859126501616469117957)
            ·
              refine ⟨3127473586219053087959617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16679859126501616469117957 3127473586219053087959617)
              ·
                refine ⟨2345605189664289815969713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127473586219053087959617 2345605189664289815969713)
                ·
                  refine ⟨1759203892248217361977285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2345605189664289815969713 1759203892248217361977285)
                  ·
                    refine ⟨329850729796540755370741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1759203892248217361977285 329850729796540755370741)
                    ·
                      rfl

theorem cell23_1927146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1927146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927146 prefixEnd_1927146 := by exact prefixLift 1927146
  have htrace : WordTrace (prefixWord ++ tailWord_1927146) baseStart_1927146 baseEnd_1927146 := by
    simpa [prefixWord, tailWord_1927146, baseEnd_1927146] using wordTrace_append hprefix tailTrace_1927146
  have hstable : (prefixWord ++ tailWord_1927146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927146).length < 2 ^ (prefixWord ++ tailWord_1927146).sum := by decide
  have hdescent : baseEnd_1927146 < baseStart_1927146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927166 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1927166 : Nat := 118140960795 + 1927166 * 2 ^ 59
def prefixEnd_1927166 : Nat := 4983230072969 + 3 ^ 40 * 1927166 * 2
def baseEnd_1927166 : Nat := 989562459002712187862131

theorem tailTrace_1927166 : CollatzResearch.WordTrace tailWord_1927166 prefixEnd_1927166 989562459002712187862131 := by
  unfold tailWord_1927166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786189817026773824279169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46859679024142793729488901 8786189817026773824279169)
  ·
    refine ⟨6589642362770080368209377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8786189817026773824279169 6589642362770080368209377)
    ·
      refine ⟨4942231772077560276157033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6589642362770080368209377 4942231772077560276157033)
      ·
        refine ⟨3706673829058170207117775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4942231772077560276157033 3706673829058170207117775)
        ·
          refine ⟨5560010743587255310676663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706673829058170207117775 5560010743587255310676663)
          ·
            refine ⟨8340016115380882966014995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560010743587255310676663 8340016115380882966014995)
            ·
              refine ⟨12510024173071324449022493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340016115380882966014995 12510024173071324449022493)
              ·
                refine ⟨4691259064901746668383435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12510024173071324449022493 4691259064901746668383435)
                ·
                  refine ⟨7036888597352620002575153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691259064901746668383435 7036888597352620002575153)
                  ·
                    refine ⟨5277666448014465001931365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7036888597352620002575153 5277666448014465001931365)
                    ·
                      refine ⟨989562459002712187862131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5277666448014465001931365 989562459002712187862131)
                      ·
                        rfl

theorem cell23_1927166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1927166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927166 prefixEnd_1927166 := by exact prefixLift 1927166
  have htrace : WordTrace (prefixWord ++ tailWord_1927166) baseStart_1927166 baseEnd_1927166 := by
    simpa [prefixWord, tailWord_1927166, baseEnd_1927166] using wordTrace_append hprefix tailTrace_1927166
  have hstable : (prefixWord ++ tailWord_1927166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927166).length < 2 ^ (prefixWord ++ tailWord_1927166).sum := by decide
  have hdescent : baseEnd_1927166 < baseStart_1927166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927212 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1927212 : Nat := 118140960795 + 1927212 * 2 ^ 59
def prefixEnd_1927212 : Nat := 4983230072969 + 3 ^ 40 * 1927212 * 2
def baseEnd_1927212 : Nat := 989586079112819007886919

theorem tailTrace_1927212 : CollatzResearch.WordTrace tailWord_1927212 prefixEnd_1927212 989586079112819007886919 := by
  unfold tailWord_1927212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35145598147023770225203945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46860797529365026966938593 35145598147023770225203945)
  ·
    refine ⟨26359198610267827668902959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35145598147023770225203945 26359198610267827668902959)
    ·
      refine ⟨39538797915401741503354439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26359198610267827668902959 39538797915401741503354439)
      ·
        refine ⟨59308196873102612255031659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39538797915401741503354439 59308196873102612255031659)
        ·
          refine ⟨88962295309653918382547489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59308196873102612255031659 88962295309653918382547489)
          ·
            refine ⟨66721721482240438786910617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88962295309653918382547489 66721721482240438786910617)
            ·
              refine ⟨50041291111680329090182963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66721721482240438786910617 50041291111680329090182963)
              ·
                refine ⟨75061936667520493635274445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50041291111680329090182963 75061936667520493635274445)
                ·
                  refine ⟨28148226250320185113227917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75061936667520493635274445 28148226250320185113227917)
                  ·
                    refine ⟨10555584843870069417460469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28148226250320185113227917 10555584843870069417460469)
                    ·
                      refine ⟨989586079112819007886919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10555584843870069417460469 989586079112819007886919)
                      ·
                        rfl

theorem cell23_1927212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1927212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927212 prefixEnd_1927212 := by exact prefixLift 1927212
  have htrace : WordTrace (prefixWord ++ tailWord_1927212) baseStart_1927212 baseEnd_1927212 := by
    simpa [prefixWord, tailWord_1927212, baseEnd_1927212] using wordTrace_append hprefix tailTrace_1927212
  have hstable : (prefixWord ++ tailWord_1927212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927212).length < 2 ^ (prefixWord ++ tailWord_1927212).sum := by decide
  have hdescent : baseEnd_1927212 < baseStart_1927212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927220 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1927220 : Nat := 118140960795 + 1927220 * 2 ^ 59
def prefixEnd_1927220 : Nat := 4983230072969 + 3 ^ 40 * 1927220 * 2
def baseEnd_1927220 : Nat := 989590186958054976586883

theorem tailTrace_1927220 : CollatzResearch.WordTrace tailWord_1927220 prefixEnd_1927220 989590186958054976586883 := by
  unfold tailWord_1927220
  simp only [CollatzResearch.WordTrace]
  refine ⟨35145744039009278908349557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46860992052012371877799409 35145744039009278908349557)
  ·
    refine ⟨3294913503657119897657771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35145744039009278908349557 3294913503657119897657771)
    ·
      refine ⟨4942370255485679846486657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294913503657119897657771 4942370255485679846486657)
      ·
        refine ⟨3706777691614259884864993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4942370255485679846486657 3706777691614259884864993)
        ·
          refine ⟨2780083268710694913648745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3706777691614259884864993 2780083268710694913648745)
          ·
            refine ⟨2085062451533021185236559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780083268710694913648745 2085062451533021185236559)
            ·
              refine ⟨3127593677299531777854839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085062451533021185236559 3127593677299531777854839)
              ·
                refine ⟨4691390515949297666782259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127593677299531777854839 4691390515949297666782259)
                ·
                  refine ⟨7037085773923946500173389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691390515949297666782259 7037085773923946500173389)
                  ·
                    refine ⟨2638907165221479937565021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7037085773923946500173389 2638907165221479937565021)
                    ·
                      refine ⟨989590186958054976586883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2638907165221479937565021 989590186958054976586883)
                      ·
                        rfl

theorem cell23_1927220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1927220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927220 prefixEnd_1927220 := by exact prefixLift 1927220
  have htrace : WordTrace (prefixWord ++ tailWord_1927220) baseStart_1927220 baseEnd_1927220 := by
    simpa [prefixWord, tailWord_1927220, baseEnd_1927220] using wordTrace_append hprefix tailTrace_1927220
  have hstable : (prefixWord ++ tailWord_1927220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927220).length < 2 ^ (prefixWord ++ tailWord_1927220).sum := by decide
  have hdescent : baseEnd_1927220 < baseStart_1927220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927229 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1927229 : Nat := 118140960795 + 1927229 * 2 ^ 59
def prefixEnd_1927229 : Nat := 4983230072969 + 3 ^ 40 * 1927229 * 2
def baseEnd_1927229 : Nat := 989594808283945441374341

theorem tailTrace_1927229 : CollatzResearch.WordTrace tailWord_1927229 prefixEnd_1927229 989594808283945441374341 := by
  unfold tailWord_1927229
  simp only [CollatzResearch.WordTrace]
  refine ⟨70291816334985952353776741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46861210889990634902517827 70291816334985952353776741)
  ·
    refine ⟨13179715562809866066333139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70291816334985952353776741 13179715562809866066333139)
    ·
      refine ⟨19769573344214799099499709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13179715562809866066333139 19769573344214799099499709)
      ·
        refine ⟨7413590004080549662312391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19769573344214799099499709 7413590004080549662312391)
        ·
          refine ⟨11120385006120824493468587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413590004080549662312391 11120385006120824493468587)
          ·
            refine ⟨16680577509181236740202881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11120385006120824493468587 16680577509181236740202881)
            ·
              refine ⟨12510433131885927555152161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16680577509181236740202881 12510433131885927555152161)
              ·
                refine ⟨9382824848914445666364121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12510433131885927555152161 9382824848914445666364121)
                ·
                  refine ⟨7037118636685834249773091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9382824848914445666364121 7037118636685834249773091)
                  ·
                    refine ⟨10555677955028751374659637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7037118636685834249773091 10555677955028751374659637)
                    ·
                      refine ⟨989594808283945441374341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10555677955028751374659637 989594808283945441374341)
                      ·
                        rfl

theorem cell23_1927229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1927229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927229 prefixEnd_1927229 := by exact prefixLift 1927229
  have htrace : WordTrace (prefixWord ++ tailWord_1927229) baseStart_1927229 baseEnd_1927229 := by
    simpa [prefixWord, tailWord_1927229, baseEnd_1927229] using wordTrace_append hprefix tailTrace_1927229
  have hstable : (prefixWord ++ tailWord_1927229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927229).length < 2 ^ (prefixWord ++ tailWord_1927229).sum := by decide
  have hdescent : baseEnd_1927229 < baseStart_1927229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927360 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 1, 4]
def baseStart_1927360 : Nat := 118140960795 + 1927360 * 2 ^ 59
def prefixEnd_1927360 : Nat := 4983230072969 + 3 ^ 40 * 1927360 * 2
def baseEnd_1927360 : Nat := 329887358083228142945413

theorem tailTrace_1927360 : CollatzResearch.WordTrace tailWord_1927360 prefixEnd_1927360 329887358083228142945413 := by
  unfold tailWord_1927360
  simp only [CollatzResearch.WordTrace]
  refine ⟨35148297148755680863397767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46864396198340907817863689 35148297148755680863397767)
  ·
    refine ⟨52722445723133521295096651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35148297148755680863397767 52722445723133521295096651)
    ·
      refine ⟨79083668584700281942644977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52722445723133521295096651 79083668584700281942644977)
      ·
        refine ⟨59312751438525211456983733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79083668584700281942644977 59312751438525211456983733)
        ·
          refine ⟨5560570447361738574092225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59312751438525211456983733 5560570447361738574092225)
          ·
            refine ⟨4170427835521303930569169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5560570447361738574092225 4170427835521303930569169)
            ·
              refine ⟨3127820876640977947926877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4170427835521303930569169 3127820876640977947926877)
              ·
                refine ⟨1172932828740366730472579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3127820876640977947926877 1172932828740366730472579)
                ·
                  refine ⟨1759399243110550095708869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172932828740366730472579 1759399243110550095708869)
                  ·
                    refine ⟨329887358083228142945413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1759399243110550095708869 329887358083228142945413)
                    ·
                      rfl

theorem cell23_1927360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 1, 4].length) (baseStart_1927360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1927360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1927360 prefixEnd_1927360 := by exact prefixLift 1927360
  have htrace : WordTrace (prefixWord ++ tailWord_1927360) baseStart_1927360 baseEnd_1927360 := by
    simpa [prefixWord, tailWord_1927360, baseEnd_1927360] using wordTrace_append hprefix tailTrace_1927360
  have hstable : (prefixWord ++ tailWord_1927360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927360).length < 2 ^ (prefixWord ++ tailWord_1927360).sum := by decide
  have hdescent : baseEnd_1927360 < baseStart_1927360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
