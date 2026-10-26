import V185TrunkScan23Chunk1278

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7577502 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_7577502 : Nat := 118140960795 + 7577502 * 2 ^ 59
def prefixEnd_7577502 : Nat := 4983230072969 + 3 ^ 40 * 7577502 * 2
def baseEnd_7577502 : Nat := 432322298489501913586301

theorem tailTrace_7577502 : CollatzResearch.WordTrace tailWord_7577502 prefixEnd_7577502 432322298489501913586301 := by
  unfold tailWord_7577502
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546775374251482894426845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184249468662674575436943173 34546775374251482894426845)
  ·
    refine ⟨12955040765344306085410067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34546775374251482894426845 12955040765344306085410067)
    ·
      refine ⟨19432561148016459128115101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12955040765344306085410067 19432561148016459128115101)
      ·
        refine ⟨7287210430506172173043163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19432561148016459128115101 7287210430506172173043163)
        ·
          refine ⟨10930815645759258259564745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287210430506172173043163 10930815645759258259564745)
          ·
            refine ⟨8198111734319443694673559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10930815645759258259564745 8198111734319443694673559)
            ·
              refine ⟨12297167601479165542010339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198111734319443694673559 12297167601479165542010339)
              ·
                refine ⟨18445751402218748313015509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12297167601479165542010339 18445751402218748313015509)
                ·
                  refine ⟨432322298489501913586301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18445751402218748313015509 432322298489501913586301)
                  ·
                    rfl

theorem cell23_7577502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_7577502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577502 prefixEnd_7577502 := by exact prefixLift 7577502
  have htrace : WordTrace (prefixWord ++ tailWord_7577502) baseStart_7577502 baseEnd_7577502 := by
    simpa [prefixWord, tailWord_7577502, baseEnd_7577502] using wordTrace_append hprefix tailTrace_7577502
  have hstable : (prefixWord ++ tailWord_7577502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577502).length < 2 ^ (prefixWord ++ tailWord_7577502).sum := by decide
  have hdescent : baseEnd_7577502 < baseStart_7577502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577562 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_7577562 : Nat := 118140960795 + 7577562 * 2 ^ 59
def prefixEnd_7577562 : Nat := 4983230072969 + 3 ^ 40 * 7577562 * 2
def baseEnd_7577562 : Nat := 1296977165081595662508811

theorem tailTrace_7577562 : CollatzResearch.WordTrace tailWord_7577562 prefixEnd_7577562 1296977165081595662508811 := by
  unfold tailWord_7577562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69094097843448623350649735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184250927582529662268399293 69094097843448623350649735)
  ·
    refine ⟨103641146765172935025974603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69094097843448623350649735 103641146765172935025974603)
    ·
      refine ⟨155461720147759402538961905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103641146765172935025974603 155461720147759402538961905)
      ·
        refine ⟨116596290110819551904221429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155461720147759402538961905 116596290110819551904221429)
        ·
          refine ⟨10930902197889332991020759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116596290110819551904221429 10930902197889332991020759)
          ·
            refine ⟨16396353296833999486531139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10930902197889332991020759 16396353296833999486531139)
            ·
              refine ⟨24594529945250999229796709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16396353296833999486531139 24594529945250999229796709)
              ·
                refine ⟨4611474364734562355586883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24594529945250999229796709 4611474364734562355586883)
                ·
                  refine ⟨6917211547101843533380325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4611474364734562355586883 6917211547101843533380325)
                  ·
                    refine ⟨1296977165081595662508811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917211547101843533380325 1296977165081595662508811)
                    ·
                      rfl

theorem cell23_7577562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_7577562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577562 prefixEnd_7577562 := by exact prefixLift 7577562
  have htrace : WordTrace (prefixWord ++ tailWord_7577562) baseStart_7577562 baseEnd_7577562 := by
    simpa [prefixWord, tailWord_7577562, baseEnd_7577562] using wordTrace_append hprefix tailTrace_7577562
  have hstable : (prefixWord ++ tailWord_7577562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577562).length < 2 ^ (prefixWord ++ tailWord_7577562).sum := by decide
  have hdescent : baseEnd_7577562 < baseStart_7577562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577568 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 7, 1, 3]
def baseStart_7577568 : Nat := 118140960795 + 7577568 * 2 ^ 59
def prefixEnd_7577568 : Nat := 4983230072969 + 3 ^ 40 * 7577568 * 2
def baseEnd_7577568 : Nat := 3890934576128713964051405

theorem tailTrace_7577568 : CollatzResearch.WordTrace tailWord_7577568 prefixEnd_7577568 3890934576128713964051405 := by
  unfold tailWord_7577568
  simp only [CollatzResearch.WordTrace]
  refine ⟨138188305105886378213658679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184251073474515170951544905 138188305105886378213658679)
  ·
    refine ⟨207282457658829567320488019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138188305105886378213658679 207282457658829567320488019)
    ·
      refine ⟨310923686488244350980732029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207282457658829567320488019 310923686488244350980732029)
      ·
        refine ⟨116596382433091631617774511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310923686488244350980732029 116596382433091631617774511)
        ·
          refine ⟨174894573649637447426661767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116596382433091631617774511 174894573649637447426661767)
          ·
            refine ⟨262341860474456171139992651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174894573649637447426661767 262341860474456171139992651)
            ·
              refine ⟨393512790711684256709988977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262341860474456171139992651 393512790711684256709988977)
              ·
                refine ⟨295134593033763192532491733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393512790711684256709988977 295134593033763192532491733)
                ·
                  refine ⟨6917217024228824824980275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 295134593033763192532491733 6917217024228824824980275)
                  ·
                    refine ⟨10375825536343237237470413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6917217024228824824980275 10375825536343237237470413)
                    ·
                      refine ⟨3890934576128713964051405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10375825536343237237470413 3890934576128713964051405)
                      ·
                        rfl

theorem cell23_7577568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_7577568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577568 prefixEnd_7577568 := by exact prefixLift 7577568
  have htrace : WordTrace (prefixWord ++ tailWord_7577568) baseStart_7577568 baseEnd_7577568 := by
    simpa [prefixWord, tailWord_7577568, baseEnd_7577568] using wordTrace_append hprefix tailTrace_7577568
  have hstable : (prefixWord ++ tailWord_7577568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577568).length < 2 ^ (prefixWord ++ tailWord_7577568).sum := by decide
  have hdescent : baseEnd_7577568 < baseStart_7577568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577595 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 2, 3, 2]
def baseStart_7577595 : Nat := 118140960795 + 7577595 * 2 ^ 59
def prefixEnd_7577595 : Nat := 4983230072969 + 3 ^ 40 * 7577595 * 2
def baseEnd_7577595 : Nat := 3890948440106385358413781

theorem tailTrace_7577595 : CollatzResearch.WordTrace tailWord_7577595 prefixEnd_7577595 3890948440106385358413781 := by
  unfold tailWord_7577595
  simp only [CollatzResearch.WordTrace]
  refine ⟨276377594982674940038550239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184251729988449960025700159 276377594982674940038550239)
  ·
    refine ⟨414566392474012410057825359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276377594982674940038550239 414566392474012410057825359)
    ·
      refine ⟨621849588711018615086738039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414566392474012410057825359 621849588711018615086738039)
      ·
        refine ⟨932774383066527922630107059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621849588711018615086738039 932774383066527922630107059)
        ·
          refine ⟨1399161574599791883945160589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932774383066527922630107059 1399161574599791883945160589)
          ·
            refine ⟨524685590474921956479435221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1399161574599791883945160589 524685590474921956479435221)
            ·
              refine ⟨12297318526755983354986763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 524685590474921956479435221 12297318526755983354986763)
              ·
                refine ⟨18445977790133975032480145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12297318526755983354986763 18445977790133975032480145)
                ·
                  refine ⟨13834483342600481274360109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18445977790133975032480145 13834483342600481274360109)
                  ·
                    refine ⟨5187931253475180477885041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13834483342600481274360109 5187931253475180477885041)
                    ·
                      refine ⟨3890948440106385358413781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187931253475180477885041 3890948440106385358413781)
                      ·
                        rfl

theorem cell23_7577595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3, 2].length) (baseStart_7577595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577595 prefixEnd_7577595 := by exact prefixLift 7577595
  have htrace : WordTrace (prefixWord ++ tailWord_7577595) baseStart_7577595 baseEnd_7577595 := by
    simpa [prefixWord, tailWord_7577595, baseEnd_7577595] using wordTrace_append hprefix tailTrace_7577595
  have hstable : (prefixWord ++ tailWord_7577595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577595).length < 2 ^ (prefixWord ++ tailWord_7577595).sum := by decide
  have hdescent : baseEnd_7577595 < baseStart_7577595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577605 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_7577605 : Nat := 118140960795 + 7577605 * 2 ^ 59
def prefixEnd_7577605 : Nat := 4983230072969 + 3 ^ 40 * 7577605 * 2
def baseEnd_7577605 : Nat := 1296984524970976773096245

theorem tailTrace_7577605 : CollatzResearch.WordTrace tailWord_7577605 prefixEnd_7577605 1296984524970976773096245 := by
  unfold tailWord_7577605
  simp only [CollatzResearch.WordTrace]
  refine ⟨276377959712638711746414269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184251973141759141164276179 276377959712638711746414269)
  ·
    refine ⟨103641734892239516904905351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276377959712638711746414269 103641734892239516904905351)
    ·
      refine ⟨155462602338359275357358027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103641734892239516904905351 155462602338359275357358027)
      ·
        refine ⟨233193903507538913036037041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155462602338359275357358027 233193903507538913036037041)
        ·
          refine ⟨174895427630654184777027781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233193903507538913036037041 174895427630654184777027781)
          ·
            refine ⟨32792892680747659645692709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174895427630654184777027781 32792892680747659645692709)
            ·
              refine ⟨6148667377640186183567383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32792892680747659645692709 6148667377640186183567383)
              ·
                refine ⟨9223001066460279275351075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148667377640186183567383 9223001066460279275351075)
                ·
                  refine ⟨13834501599690418913026613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223001066460279275351075 13834501599690418913026613)
                  ·
                    refine ⟨1296984524970976773096245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13834501599690418913026613 1296984524970976773096245)
                    ·
                      rfl

theorem cell23_7577605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_7577605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577605 prefixEnd_7577605 := by exact prefixLift 7577605
  have htrace : WordTrace (prefixWord ++ tailWord_7577605) baseStart_7577605 baseEnd_7577605 := by
    simpa [prefixWord, tailWord_7577605, baseEnd_7577605] using wordTrace_append hprefix tailTrace_7577605
  have hstable : (prefixWord ++ tailWord_7577605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577605).length < 2 ^ (prefixWord ++ tailWord_7577605).sum := by decide
  have hdescent : baseEnd_7577605 < baseStart_7577605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577628 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7577628 : Nat := 118140960795 + 7577628 * 2 ^ 59
def prefixEnd_7577628 : Nat := 4983230072969 + 3 ^ 40 * 7577628 * 2
def baseEnd_7577628 : Nat := 3890965384967983729301129

theorem tailTrace_7577628 : CollatzResearch.WordTrace tailWord_7577628 prefixEnd_7577628 3890965384967983729301129 := by
  unfold tailWord_7577628
  simp only [CollatzResearch.WordTrace]
  refine ⟨138189399295777693337250769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184252532394370257783001025 138189399295777693337250769)
  ·
    refine ⟨103642049471833270002938077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138189399295777693337250769 103642049471833270002938077)
    ·
      refine ⟨38865768551937476251101779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103642049471833270002938077 38865768551937476251101779)
      ·
        refine ⟨58298652827906214376652669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38865768551937476251101779 58298652827906214376652669)
        ·
          refine ⟨21861994810464830391244751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58298652827906214376652669 21861994810464830391244751)
          ·
            refine ⟨32792992215697245586867127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21861994810464830391244751 32792992215697245586867127)
            ·
              refine ⟨49189488323545868380300691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32792992215697245586867127 49189488323545868380300691)
              ·
                refine ⟨73784232485318802570451037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49189488323545868380300691 73784232485318802570451037)
                ·
                  refine ⟨27669087181994550963919139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73784232485318802570451037 27669087181994550963919139)
                  ·
                    refine ⟨41503630772991826445878709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27669087181994550963919139 41503630772991826445878709)
                    ·
                      refine ⟨3890965384967983729301129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41503630772991826445878709 3890965384967983729301129)
                      ·
                        rfl

theorem cell23_7577628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7577628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577628 prefixEnd_7577628 := by exact prefixLift 7577628
  have htrace : WordTrace (prefixWord ++ tailWord_7577628) baseStart_7577628 baseEnd_7577628 := by
    simpa [prefixWord, tailWord_7577628, baseEnd_7577628] using wordTrace_append hprefix tailTrace_7577628
  have hstable : (prefixWord ++ tailWord_7577628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577628).length < 2 ^ (prefixWord ++ tailWord_7577628).sum := by decide
  have hdescent : baseEnd_7577628 < baseStart_7577628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577631 : List Nat := [1, 1, 2, 4, 1, 2, 2, 10]
def baseStart_7577631 : Nat := 118140960795 + 7577631 * 2 ^ 59
def prefixEnd_7577631 : Nat := 4983230072969 + 3 ^ 40 * 7577631 * 2
def baseEnd_7577631 : Nat := 144109886126294341391245

theorem tailTrace_7577631 : CollatzResearch.WordTrace tailWord_7577631 prefixEnd_7577631 144109886126294341391245 := by
  unfold tailWord_7577631
  simp only [CollatzResearch.WordTrace]
  refine ⟨276378908010544518186860747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184252605340363012124573831 276378908010544518186860747)
  ·
    refine ⟨414568362015816777280291121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276378908010544518186860747 414568362015816777280291121)
    ·
      refine ⟨310926271511862582960218341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414568362015816777280291121 310926271511862582960218341)
      ·
        refine ⟨58298675908474234305040939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310926271511862582960218341 58298675908474234305040939)
        ·
          refine ⟨87448013862711351457561409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58298675908474234305040939 87448013862711351457561409)
          ·
            refine ⟨65586010397033513593171057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87448013862711351457561409 65586010397033513593171057)
            ·
              refine ⟨49189507797775135194878293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65586010397033513593171057 49189507797775135194878293)
              ·
                refine ⟨144109886126294341391245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49189507797775135194878293 144109886126294341391245)
                ·
                  rfl

theorem cell23_7577631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 10].length) (baseStart_7577631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577631 prefixEnd_7577631 := by exact prefixLift 7577631
  have htrace : WordTrace (prefixWord ++ tailWord_7577631) baseStart_7577631 baseEnd_7577631 := by
    simpa [prefixWord, tailWord_7577631, baseEnd_7577631] using wordTrace_append hprefix tailTrace_7577631
  have hstable : (prefixWord ++ tailWord_7577631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577631).length < 2 ^ (prefixWord ++ tailWord_7577631).sum := by decide
  have hdescent : baseEnd_7577631 < baseStart_7577631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577642 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_7577642 : Nat := 118140960795 + 7577642 * 2 ^ 59
def prefixEnd_7577642 : Nat := 4983230072969 + 3 ^ 40 * 7577642 * 2
def baseEnd_7577642 : Nat := 3890972573697146674526065

theorem tailTrace_7577642 : CollatzResearch.WordTrace tailWord_7577642 prefixEnd_7577642 3890972573697146674526065 := by
  unfold tailWord_7577642
  simp only [CollatzResearch.WordTrace]
  refine ⟨69094827303376166766377795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184252872809003111377007453 69094827303376166766377795)
  ·
    refine ⟨103642240955064250149566693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69094827303376166766377795 103642240955064250149566693)
    ·
      refine ⟨19432920179074546903043755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103642240955064250149566693 19432920179074546903043755)
      ·
        refine ⟨29149380268611820354565633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19432920179074546903043755 29149380268611820354565633)
        ·
          refine ⟨21862035201458865265924225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29149380268611820354565633 21862035201458865265924225)
          ·
            refine ⟨16396526401094148949443169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21862035201458865265924225 16396526401094148949443169)
            ·
              refine ⟨12297394800820611712082377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16396526401094148949443169 12297394800820611712082377)
              ·
                refine ⟨9223046100615458784061783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12297394800820611712082377 9223046100615458784061783)
                ·
                  refine ⟨13834569150923188176092675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223046100615458784061783 13834569150923188176092675)
                  ·
                    refine ⟨20751853726384782264139013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13834569150923188176092675 20751853726384782264139013)
                    ·
                      refine ⟨3890972573697146674526065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20751853726384782264139013 3890972573697146674526065)
                      ·
                        rfl

theorem cell23_7577642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_7577642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577642 prefixEnd_7577642 := by exact prefixLift 7577642
  have htrace : WordTrace (prefixWord ++ tailWord_7577642) baseStart_7577642 baseEnd_7577642 := by
    simpa [prefixWord, tailWord_7577642, baseEnd_7577642] using wordTrace_append hprefix tailTrace_7577642
  have hstable : (prefixWord ++ tailWord_7577642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577642).length < 2 ^ (prefixWord ++ tailWord_7577642).sum := by decide
  have hdescent : baseEnd_7577642 < baseStart_7577642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577648 : List Nat := [2, 1, 1, 1, 2, 5, 4, 7]
def baseStart_7577648 : Nat := 118140960795 + 7577648 * 2 ^ 59
def prefixEnd_7577648 : Nat := 4983230072969 + 3 ^ 40 * 7577648 * 2
def baseEnd_7577648 : Nat := 144110209428928653742631

theorem tailTrace_7577648 : CollatzResearch.WordTrace tailWord_7577648 prefixEnd_7577648 144110209428928653742631 := by
  unfold tailWord_7577648
  simp only [CollatzResearch.WordTrace]
  refine ⟨138189764025741465045114799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184253018700988620060153065 138189764025741465045114799)
  ·
    refine ⟨207284646038612197567672199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138189764025741465045114799 207284646038612197567672199)
    ·
      refine ⟨310926969057918296351508299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207284646038612197567672199 310926969057918296351508299)
      ·
        refine ⟨466390453586877444527262449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310926969057918296351508299 466390453586877444527262449)
        ·
          refine ⟨349792840190158083395446837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466390453586877444527262449 349792840190158083395446837)
          ·
            refine ⟨32793078767827320318323141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349792840190158083395446837 32793078767827320318323141)
            ·
              refine ⟨6148702268967622559685589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32793078767827320318323141 6148702268967622559685589)
              ·
                refine ⟨144110209428928653742631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6148702268967622559685589 144110209428928653742631)
                ·
                  rfl

theorem cell23_7577648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 7].length) (baseStart_7577648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577648 prefixEnd_7577648 := by exact prefixLift 7577648
  have htrace : WordTrace (prefixWord ++ tailWord_7577648) baseStart_7577648 baseEnd_7577648 := by
    simpa [prefixWord, tailWord_7577648, baseEnd_7577648] using wordTrace_append hprefix tailTrace_7577648
  have hstable : (prefixWord ++ tailWord_7577648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577648).length < 2 ^ (prefixWord ++ tailWord_7577648).sum := by decide
  have hdescent : baseEnd_7577648 < baseStart_7577648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577658 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_7577658 : Nat := 118140960795 + 7577658 * 2 ^ 59
def prefixEnd_7577658 : Nat := 4983230072969 + 3 ^ 40 * 7577658 * 2
def baseEnd_7577658 : Nat := 3890980789387618611925991

theorem tailTrace_7577658 : CollatzResearch.WordTrace tailWord_7577658 prefixEnd_7577658 3890980789387618611925991 := by
  unfold tailWord_7577658
  simp only [CollatzResearch.WordTrace]
  refine ⟨69094973195361675449523407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184253261854297801198729085 69094973195361675449523407)
  ·
    refine ⟨103642459793042513174285111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69094973195361675449523407 103642459793042513174285111)
    ·
      refine ⟨155463689689563769761427667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103642459793042513174285111 155463689689563769761427667)
      ·
        refine ⟨233195534534345654642141501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155463689689563769761427667 233195534534345654642141501)
        ·
          refine ⟨87448325450379620490803063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233195534534345654642141501 87448325450379620490803063)
          ·
            refine ⟨131172488175569430736204595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87448325450379620490803063 131172488175569430736204595)
            ·
              refine ⟨196758732263354146104306893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131172488175569430736204595 196758732263354146104306893)
              ·
                refine ⟨73784524598757804789115085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196758732263354146104306893 73784524598757804789115085)
                ·
                  refine ⟨27669196724534176795918157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73784524598757804789115085 27669196724534176795918157)
                  ·
                    refine ⟨10375948771700316298469309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27669196724534176795918157 10375948771700316298469309)
                    ·
                      refine ⟨3890980789387618611925991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10375948771700316298469309 3890980789387618611925991)
                      ·
                        rfl

theorem cell23_7577658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_7577658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577658 prefixEnd_7577658 := by exact prefixLift 7577658
  have htrace : WordTrace (prefixWord ++ tailWord_7577658) baseStart_7577658 baseEnd_7577658 := by
    simpa [prefixWord, tailWord_7577658, baseEnd_7577658] using wordTrace_append hprefix tailTrace_7577658
  have hstable : (prefixWord ++ tailWord_7577658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577658).length < 2 ^ (prefixWord ++ tailWord_7577658).sum := by decide
  have hdescent : baseEnd_7577658 < baseStart_7577658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577662 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7577662 : Nat := 118140960795 + 7577662 * 2 ^ 59
def prefixEnd_7577662 : Nat := 4983230072969 + 3 ^ 40 * 7577662 * 2
def baseEnd_7577662 : Nat := 3890982843310236596275973

theorem tailTrace_7577662 : CollatzResearch.WordTrace tailWord_7577662 prefixEnd_7577662 3890982843310236596275973 := by
  unfold tailWord_7577662
  simp only [CollatzResearch.WordTrace]
  refine ⟨34547504834179026310154905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184253359115621473654159493 34547504834179026310154905)
  ·
    refine ⟨25910628625634269732616179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34547504834179026310154905 25910628625634269732616179)
    ·
      refine ⟨38865942938451404598924269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25910628625634269732616179 38865942938451404598924269)
      ·
        refine ⟨14574728601919276724596601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38865942938451404598924269 14574728601919276724596601)
        ·
          refine ⟨10931046451439457543447451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14574728601919276724596601 10931046451439457543447451)
          ·
            refine ⟨16396569677159186315171177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10931046451439457543447451 16396569677159186315171177)
            ·
              refine ⟨12297427257869389736378383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16396569677159186315171177 12297427257869389736378383)
              ·
                refine ⟨18446140886804084604567575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12297427257869389736378383 18446140886804084604567575)
                ·
                  refine ⟨27669211330206126906851363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18446140886804084604567575 27669211330206126906851363)
                  ·
                    refine ⟨41503816995309190360277045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27669211330206126906851363 41503816995309190360277045)
                    ·
                      refine ⟨3890982843310236596275973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41503816995309190360277045 3890982843310236596275973)
                      ·
                        rfl

theorem cell23_7577662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7577662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577662 prefixEnd_7577662 := by exact prefixLift 7577662
  have htrace : WordTrace (prefixWord ++ tailWord_7577662) baseStart_7577662 baseEnd_7577662 := by
    simpa [prefixWord, tailWord_7577662, baseEnd_7577662] using wordTrace_append hprefix tailTrace_7577662
  have hstable : (prefixWord ++ tailWord_7577662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577662).length < 2 ^ (prefixWord ++ tailWord_7577662).sum := by decide
  have hdescent : baseEnd_7577662 < baseStart_7577662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577686 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7577686 : Nat := 118140960795 + 7577686 * 2 ^ 59
def prefixEnd_7577686 : Nat := 4983230072969 + 3 ^ 40 * 7577686 * 2
def baseEnd_7577686 : Nat := 1296998388948648167458621

theorem tailTrace_7577686 : CollatzResearch.WordTrace tailWord_7577686 prefixEnd_7577686 1296998388948648167458621 := by
  unfold tailWord_7577686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273807126584078911257057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184253942683563508386741941 17273807126584078911257057)
  ·
    refine ⟨12955355344938059183442793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17273807126584078911257057 12955355344938059183442793)
    ·
      refine ⟨9716516508703544387582095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12955355344938059183442793 9716516508703544387582095)
      ·
        refine ⟨14574774763055316581373143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716516508703544387582095 14574774763055316581373143)
        ·
          refine ⟨21862162144582974872059715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14574774763055316581373143 21862162144582974872059715)
          ·
            refine ⟨32793243216874462308089573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21862162144582974872059715 32793243216874462308089573)
            ·
              refine ⟨6148733103163961682766795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32793243216874462308089573 6148733103163961682766795)
              ·
                refine ⟨9223099654745942524150193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148733103163961682766795 9223099654745942524150193)
                ·
                  refine ⟨6917324741059456893112645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9223099654745942524150193 6917324741059456893112645)
                  ·
                    refine ⟨1296998388948648167458621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917324741059456893112645 1296998388948648167458621)
                    ·
                      rfl

theorem cell23_7577686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7577686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577686 prefixEnd_7577686 := by exact prefixLift 7577686
  have htrace : WordTrace (prefixWord ++ tailWord_7577686) baseStart_7577686 baseEnd_7577686 := by
    simpa [prefixWord, tailWord_7577686, baseEnd_7577686] using wordTrace_append hprefix tailTrace_7577686
  have hstable : (prefixWord ++ tailWord_7577686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577686).length < 2 ^ (prefixWord ++ tailWord_7577686).sum := by decide
  have hdescent : baseEnd_7577686 < baseStart_7577686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577719 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 1, 3, 2]
def baseStart_7577719 : Nat := 118140960795 + 7577719 * 2 ^ 59
def prefixEnd_7577719 : Nat := 4983230072969 + 3 ^ 40 * 7577719 * 2
def baseEnd_7577719 : Nat := 3891012111707542873263211

theorem tailTrace_7577719 : CollatzResearch.WordTrace tailWord_7577719 prefixEnd_7577719 3891012111707542873263211 := by
  unfold tailWord_7577719
  simp only [CollatzResearch.WordTrace]
  refine ⟨276382117634225709216064211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184254745089483806144042807 276382117634225709216064211)
  ·
    refine ⟨414573176451338563824096317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276382117634225709216064211 414573176451338563824096317)
    ·
      refine ⟨155464941169251961434036119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414573176451338563824096317 155464941169251961434036119)
      ·
        refine ⟨233197411753877942151054179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155464941169251961434036119 233197411753877942151054179)
        ·
          refine ⟨349796117630816913226581269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233197411753877942151054179 349796117630816913226581269)
          ·
            refine ⟨16396693013944542807495997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 349796117630816913226581269 16396693013944542807495997)
            ·
              refine ⟨6148759880229203552810999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16396693013944542807495997 6148759880229203552810999)
              ·
                refine ⟨9223139820343805329216499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148759880229203552810999 9223139820343805329216499)
                ·
                  refine ⟨13834709730515707993824749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223139820343805329216499 13834709730515707993824749)
                  ·
                    refine ⟨5188016148943390497684281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13834709730515707993824749 5188016148943390497684281)
                    ·
                      refine ⟨3891012111707542873263211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188016148943390497684281 3891012111707542873263211)
                      ·
                        rfl

theorem cell23_7577719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_7577719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577719 prefixEnd_7577719 := by exact prefixLift 7577719
  have htrace : WordTrace (prefixWord ++ tailWord_7577719) baseStart_7577719 baseEnd_7577719 := by
    simpa [prefixWord, tailWord_7577719, baseEnd_7577719] using wordTrace_append hprefix tailTrace_7577719
  have hstable : (prefixWord ++ tailWord_7577719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577719).length < 2 ^ (prefixWord ++ tailWord_7577719).sum := by decide
  have hdescent : baseEnd_7577719 < baseStart_7577719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577728 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_7577728 : Nat := 118140960795 + 7577728 * 2 ^ 59
def prefixEnd_7577728 : Nat := 4983230072969 + 3 ^ 40 * 7577728 * 2
def baseEnd_7577728 : Nat := 3891016733033433338050669

theorem tailTrace_7577728 : CollatzResearch.WordTrace tailWord_7577728 prefixEnd_7577728 3891016733033433338050669 := by
  unfold tailWord_7577728
  simp only [CollatzResearch.WordTrace]
  refine ⟨138191222945596551876570919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184254963927462069168761225 138191222945596551876570919)
  ·
    refine ⟨207286834418394827814856379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138191222945596551876570919 207286834418394827814856379)
    ·
      refine ⟨310930251627592241722284569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207286834418394827814856379 310930251627592241722284569)
      ·
        refine ⟨233197688720694181291713427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310930251627592241722284569 233197688720694181291713427)
        ·
          refine ⟨349796533081041271937570141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233197688720694181291713427 349796533081041271937570141)
          ·
            refine ⟨131173699905390476976588803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349796533081041271937570141 131173699905390476976588803)
            ·
              refine ⟨196760549858085715464883205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131173699905390476976588803 196760549858085715464883205)
              ·
                refine ⟨36892603098391071649665601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196760549858085715464883205 36892603098391071649665601)
                ·
                  refine ⟨27669452323793303737249201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36892603098391071649665601 27669452323793303737249201)
                  ·
                    refine ⟨20752089242844977802936901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27669452323793303737249201 20752089242844977802936901)
                    ·
                      refine ⟨3891016733033433338050669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20752089242844977802936901 3891016733033433338050669)
                      ·
                        rfl

theorem cell23_7577728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_7577728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577728 prefixEnd_7577728 := by exact prefixLift 7577728
  have htrace : WordTrace (prefixWord ++ tailWord_7577728) baseStart_7577728 baseEnd_7577728 := by
    simpa [prefixWord, tailWord_7577728, baseEnd_7577728] using wordTrace_append hprefix tailTrace_7577728
  have hstable : (prefixWord ++ tailWord_7577728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577728).length < 2 ^ (prefixWord ++ tailWord_7577728).sum := by decide
  have hdescent : baseEnd_7577728 < baseStart_7577728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577770 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7577770 : Nat := 118140960795 + 7577770 * 2 ^ 59
def prefixEnd_7577770 : Nat := 4983230072969 + 3 ^ 40 * 7577770 * 2
def baseEnd_7577770 : Nat := 3891038299220922173725477

theorem tailTrace_7577770 : CollatzResearch.WordTrace tailWord_7577770 prefixEnd_7577770 3891038299220922173725477 := by
  unfold tailWord_7577770
  simp only [CollatzResearch.WordTrace]
  refine ⟨69095994439260236231542691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184255985171360629950780509 69095994439260236231542691)
  ·
    refine ⟨103643991658890354347314037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69095994439260236231542691 103643991658890354347314037)
    ·
      refine ⟨9716624218020970720060691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103643991658890354347314037 9716624218020970720060691)
      ·
        refine ⟨14574936327031456080091037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716624218020970720060691 14574936327031456080091037)
        ·
          refine ⟨5465601122636796030034139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14574936327031456080091037 5465601122636796030034139)
          ·
            refine ⟨8198401683955194045051209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465601122636796030034139 8198401683955194045051209)
            ·
              refine ⟨6148801262966395533788407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8198401683955194045051209 6148801262966395533788407)
              ·
                refine ⟨9223201894449593300682611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148801262966395533788407 9223201894449593300682611)
                ·
                  refine ⟨13834802841674389951023917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223201894449593300682611 13834802841674389951023917)
                  ·
                    refine ⟨5188051065627896231633969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13834802841674389951023917 5188051065627896231633969)
                    ·
                      refine ⟨3891038299220922173725477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188051065627896231633969 3891038299220922173725477)
                      ·
                        rfl

theorem cell23_7577770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7577770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577770 prefixEnd_7577770 := by exact prefixLift 7577770
  have htrace : WordTrace (prefixWord ++ tailWord_7577770) baseStart_7577770 baseEnd_7577770 := by
    simpa [prefixWord, tailWord_7577770, baseEnd_7577770] using wordTrace_append hprefix tailTrace_7577770
  have hstable : (prefixWord ++ tailWord_7577770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577770).length < 2 ^ (prefixWord ++ tailWord_7577770).sum := by decide
  have hdescent : baseEnd_7577770 < baseStart_7577770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577825 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_7577825 : Nat := 118140960795 + 7577825 * 2 ^ 59
def prefixEnd_7577825 : Nat := 4983230072969 + 3 ^ 40 * 7577825 * 2
def baseEnd_7577825 : Nat := 3891066540656919458537723

theorem tailTrace_7577825 : CollatzResearch.WordTrace tailWord_7577825 prefixEnd_7577825 3891066540656919458537723 := by
  unfold tailWord_7577825
  simp only [CollatzResearch.WordTrace]
  refine ⟨276385983771841689319422929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184257322514561126212948619 276385983771841689319422929)
  ·
    refine ⟨207289487828881266989567197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276385983771841689319422929 207289487828881266989567197)
    ·
      refine ⟨77733557935830475121087699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207289487828881266989567197 77733557935830475121087699)
      ·
        refine ⟨116600336903745712681631549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77733557935830475121087699 116600336903745712681631549)
        ·
          refine ⟨43725126338904642255611831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116600336903745712681631549 43725126338904642255611831)
          ·
            refine ⟨65587689508356963383417747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43725126338904642255611831 65587689508356963383417747)
            ·
              refine ⟨98381534262535445075126621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65587689508356963383417747 98381534262535445075126621)
              ·
                refine ⟨36893075348450791903172483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98381534262535445075126621 36893075348450791903172483)
                ·
                  refine ⟨55339613022676187854758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36893075348450791903172483 55339613022676187854758725)
                  ·
                    refine ⟨10376177441751785222767261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55339613022676187854758725 10376177441751785222767261)
                    ·
                      refine ⟨3891066540656919458537723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376177441751785222767261 3891066540656919458537723)
                      ·
                        rfl

theorem cell23_7577825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_7577825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577825 prefixEnd_7577825 := by exact prefixLift 7577825
  have htrace : WordTrace (prefixWord ++ tailWord_7577825) baseStart_7577825 baseEnd_7577825 := by
    simpa [prefixWord, tailWord_7577825, baseEnd_7577825] using wordTrace_append hprefix tailTrace_7577825
  have hstable : (prefixWord ++ tailWord_7577825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577825).length < 2 ^ (prefixWord ++ tailWord_7577825).sum := by decide
  have hdescent : baseEnd_7577825 < baseStart_7577825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577842 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_7577842 : Nat := 118140960795 + 7577842 * 2 ^ 59
def prefixEnd_7577842 : Nat := 4983230072969 + 3 ^ 40 * 7577842 * 2
def baseEnd_7577842 : Nat := 3891075269828045892025145

theorem tailTrace_7577842 : CollatzResearch.WordTrace tailWord_7577842 prefixEnd_7577842 3891075269828045892025145 := by
  unfold tailWord_7577842
  simp only [CollatzResearch.WordTrace]
  refine ⟨69096650953195025305697945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184257735875186734148527853 69096650953195025305697945)
  ·
    refine ⟨51822488214896268979273459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69096650953195025305697945 51822488214896268979273459)
    ·
      refine ⟨77733732322344403468910189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51822488214896268979273459 77733732322344403468910189)
      ·
        refine ⟨29150149620879151300841321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77733732322344403468910189 29150149620879151300841321)
        ·
          refine ⟨21862612215659363475630991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29150149620879151300841321 21862612215659363475630991)
          ·
            refine ⟨32793918323489045213446487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21862612215659363475630991 32793918323489045213446487)
            ·
              refine ⟨49190877485233567820169731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32793918323489045213446487 49190877485233567820169731)
              ·
                refine ⟨73786316227850351730254597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49190877485233567820169731 73786316227850351730254597)
                ·
                  refine ⟨13834934292721940949422737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73786316227850351730254597 13834934292721940949422737)
                  ·
                    refine ⟨10376200719541455712067053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13834934292721940949422737 10376200719541455712067053)
                    ·
                      refine ⟨3891075269828045892025145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376200719541455712067053 3891075269828045892025145)
                      ·
                        rfl

theorem cell23_7577842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_7577842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577842 prefixEnd_7577842 := by exact prefixLift 7577842
  have htrace : WordTrace (prefixWord ++ tailWord_7577842) baseStart_7577842 baseEnd_7577842 := by
    simpa [prefixWord, tailWord_7577842, baseEnd_7577842] using wordTrace_append hprefix tailTrace_7577842
  have hstable : (prefixWord ++ tailWord_7577842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577842).length < 2 ^ (prefixWord ++ tailWord_7577842).sum := by decide
  have hdescent : baseEnd_7577842 < baseStart_7577842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577848 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_7577848 : Nat := 118140960795 + 7577848 * 2 ^ 59
def prefixEnd_7577848 : Nat := 4983230072969 + 3 ^ 40 * 7577848 * 2
def baseEnd_7577848 : Nat := 3891078350711972868550117

theorem tailTrace_7577848 : CollatzResearch.WordTrace tailWord_7577848 prefixEnd_7577848 3891078350711972868550117 := by
  unfold tailWord_7577848
  simp only [CollatzResearch.WordTrace]
  refine ⟨138193411325379182123755099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184257881767172242831673465 138193411325379182123755099)
  ·
    refine ⟨207290116988068773185632649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138193411325379182123755099 207290116988068773185632649)
    ·
      refine ⟨155467587741051579889224487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207290116988068773185632649 155467587741051579889224487)
      ·
        refine ⟨233201381611577369833836731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155467587741051579889224487 233201381611577369833836731)
        ·
          refine ⟨349802072417366054750755097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233201381611577369833836731 349802072417366054750755097)
          ·
            refine ⟨262351554313024541063066323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349802072417366054750755097 262351554313024541063066323)
            ·
              refine ⟨393527331469536811594599485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262351554313024541063066323 393527331469536811594599485)
              ·
                refine ⟨147572749301076304347974807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393527331469536811594599485 147572749301076304347974807)
                ·
                  refine ⟨221359123951614456521962211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147572749301076304347974807 221359123951614456521962211)
                  ·
                    refine ⟨332038685927421684782943317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221359123951614456521962211 332038685927421684782943317)
                    ·
                      refine ⟨3891078350711972868550117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 332038685927421684782943317 3891078350711972868550117)
                      ·
                        rfl

theorem cell23_7577848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_7577848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577848 prefixEnd_7577848 := by exact prefixLift 7577848
  have htrace : WordTrace (prefixWord ++ tailWord_7577848) baseStart_7577848 baseEnd_7577848 := by
    simpa [prefixWord, tailWord_7577848, baseEnd_7577848] using wordTrace_append hprefix tailTrace_7577848
  have hstable : (prefixWord ++ tailWord_7577848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577848).length < 2 ^ (prefixWord ++ tailWord_7577848).sum := by decide
  have hdescent : baseEnd_7577848 < baseStart_7577848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577932 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7577932 : Nat := 118140960795 + 7577932 * 2 ^ 59
def prefixEnd_7577932 : Nat := 4983230072969 + 3 ^ 40 * 7577932 * 2
def baseEnd_7577932 : Nat := 3891121483086950539899731

theorem tailTrace_7577932 : CollatzResearch.WordTrace tailWord_7577932 prefixEnd_7577932 3891121483086950539899731 := by
  unfold tailWord_7577932
  simp only [CollatzResearch.WordTrace]
  refine ⟨138194943191227023296784025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184259924254969364395712033 138194943191227023296784025)
  ·
    refine ⟨103646207393420267472588019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138194943191227023296784025 103646207393420267472588019)
    ·
      refine ⟨155469311090130401208882029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103646207393420267472588019 155469311090130401208882029)
      ·
        refine ⟨58300991658798900453330761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155469311090130401208882029 58300991658798900453330761)
        ·
          refine ⟨43725743744099175339998071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58300991658798900453330761 43725743744099175339998071)
          ·
            refine ⟨65588615616148763009997107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43725743744099175339998071 65588615616148763009997107)
            ·
              refine ⟨98382923424223144514995661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65588615616148763009997107 98382923424223144514995661)
              ·
                refine ⟨36893596284083679193123373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98382923424223144514995661 36893596284083679193123373)
                ·
                  refine ⟨13835098606531379697421265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36893596284083679193123373 13835098606531379697421265)
                  ·
                    refine ⟨10376323954898534773065949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13835098606531379697421265 10376323954898534773065949)
                    ·
                      refine ⟨3891121483086950539899731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376323954898534773065949 3891121483086950539899731)
                      ·
                        rfl

theorem cell23_7577932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7577932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577932 prefixEnd_7577932 := by exact prefixLift 7577932
  have htrace : WordTrace (prefixWord ++ tailWord_7577932) baseStart_7577932 baseEnd_7577932 := by
    simpa [prefixWord, tailWord_7577932, baseEnd_7577932] using wordTrace_append hprefix tailTrace_7577932
  have hstable : (prefixWord ++ tailWord_7577932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577932).length < 2 ^ (prefixWord ++ tailWord_7577932).sum := by decide
  have hdescent : baseEnd_7577932 < baseStart_7577932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577979 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 3]
def baseStart_7577979 : Nat := 118140960795 + 7577979 * 2 ^ 59
def prefixEnd_7577979 : Nat := 4983230072969 + 3 ^ 40 * 7577979 * 2
def baseEnd_7577979 : Nat := 3891145616677711856012015

theorem tailTrace_7577979 : CollatzResearch.WordTrace tailWord_7577979 prefixEnd_7577979 3891145616677711856012015 := by
  unfold tailWord_7577979
  simp only [CollatzResearch.WordTrace]
  refine ⟨276391600613283773620528991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184261067075522515747019327 276391600613283773620528991)
  ·
    refine ⟨414587400919925660430793487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276391600613283773620528991 414587400919925660430793487)
    ·
      refine ⟨621881101379888490646190231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414587400919925660430793487 621881101379888490646190231)
      ·
        refine ⟨932821652069832735969285347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621881101379888490646190231 932821652069832735969285347)
        ·
          refine ⟨1399232478104749103953928021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932821652069832735969285347 1399232478104749103953928021)
          ·
            refine ⟨8198627801395014280980047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1399232478104749103953928021 8198627801395014280980047)
            ·
              refine ⟨12297941702092521421470071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198627801395014280980047 12297941702092521421470071)
              ·
                refine ⟨18446912553138782132205107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12297941702092521421470071 18446912553138782132205107)
                ·
                  refine ⟨27670368829708173198307661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18446912553138782132205107 27670368829708173198307661)
                  ·
                    refine ⟨10376388311140564949365373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27670368829708173198307661 10376388311140564949365373)
                    ·
                      refine ⟨3891145616677711856012015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376388311140564949365373 3891145616677711856012015)
                      ·
                        rfl

theorem cell23_7577979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 3].length) (baseStart_7577979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577979 prefixEnd_7577979 := by exact prefixLift 7577979
  have htrace : WordTrace (prefixWord ++ tailWord_7577979) baseStart_7577979 baseEnd_7577979 := by
    simpa [prefixWord, tailWord_7577979, baseEnd_7577979] using wordTrace_append hprefix tailTrace_7577979
  have hstable : (prefixWord ++ tailWord_7577979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577979).length < 2 ^ (prefixWord ++ tailWord_7577979).sum := by decide
  have hdescent : baseEnd_7577979 < baseStart_7577979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578070 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_7578070 : Nat := 118140960795 + 7578070 * 2 ^ 59
def prefixEnd_7578070 : Nat := 4983230072969 + 3 ^ 40 * 7578070 * 2
def baseEnd_7578070 : Nat := 3891192343417270999974097

theorem tailTrace_7578070 : CollatzResearch.WordTrace tailWord_7578070 prefixEnd_7578070 3891192343417270999974097 := by
  unfold tailWord_7578070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17274682478497131010130729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184263279770636064108061109 17274682478497131010130729)
  ·
    refine ⟨12956011858872848257598047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17274682478497131010130729 12956011858872848257598047)
    ·
      refine ⟨19434017788309272386397071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12956011858872848257598047 19434017788309272386397071)
      ·
        refine ⟨29151026682463908579595607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19434017788309272386397071 29151026682463908579595607)
        ·
          refine ⟨43726540023695862869393411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29151026682463908579595607 43726540023695862869393411)
          ·
            refine ⟨65589810035543794304090117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43726540023695862869393411 65589810035543794304090117)
            ·
              refine ⟨12298089381664461432016897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65589810035543794304090117 12298089381664461432016897)
              ·
                refine ⟨9223567036248346074012673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12298089381664461432016897 9223567036248346074012673)
                ·
                  refine ⟨6917675277186259555509505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9223567036248346074012673 6917675277186259555509505)
                  ·
                    refine ⟨5188256457889694666632129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6917675277186259555509505 5188256457889694666632129)
                    ·
                      refine ⟨3891192343417270999974097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188256457889694666632129 3891192343417270999974097)
                      ·
                        rfl

theorem cell23_7578070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_7578070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578070 prefixEnd_7578070 := by exact prefixLift 7578070
  have htrace : WordTrace (prefixWord ++ tailWord_7578070) baseStart_7578070 baseEnd_7578070 := by
    simpa [prefixWord, tailWord_7578070, baseEnd_7578070] using wordTrace_append hprefix tailTrace_7578070
  have hstable : (prefixWord ++ tailWord_7578070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578070).length < 2 ^ (prefixWord ++ tailWord_7578070).sum := by decide
  have hdescent : baseEnd_7578070 < baseStart_7578070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578079 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 2, 5, 2]
def baseStart_7578079 : Nat := 118140960795 + 7578079 * 2 ^ 59
def prefixEnd_7578079 : Nat := 4983230072969 + 3 ^ 40 * 7578079 * 2
def baseEnd_7578079 : Nat := 3891196964743161464761555

theorem tailTrace_7578079 : CollatzResearch.WordTrace tailWord_7578079 prefixEnd_7578079 3891196964743161464761555 := by
  unfold tailWord_7578079
  simp only [CollatzResearch.WordTrace]
  refine ⟨276395247912921490699169291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184263498608614327132779527 276395247912921490699169291)
  ·
    refine ⟨414592871869382236048753937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276395247912921490699169291 414592871869382236048753937)
    ·
      refine ⟨310944653902036677036565453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414592871869382236048753937 310944653902036677036565453)
      ·
        refine ⟨116604245213263753888712045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310944653902036677036565453 116604245213263753888712045)
        ·
          refine ⟨43726591954973907708267017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116604245213263753888712045 43726591954973907708267017)
          ·
            refine ⟨32794943966230430781200263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43726591954973907708267017 32794943966230430781200263)
            ·
              refine ⟨49192415949345646171800395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32794943966230430781200263 49192415949345646171800395)
              ·
                refine ⟨73788623924018469257700593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49192415949345646171800395 73788623924018469257700593)
                ·
                  refine ⟨55341467943013851943275445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73788623924018469257700593 55341467943013851943275445)
                  ·
                    refine ⟨5188262619657548619682073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55341467943013851943275445 5188262619657548619682073)
                    ·
                      refine ⟨3891196964743161464761555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188262619657548619682073 3891196964743161464761555)
                      ·
                        rfl

theorem cell23_7578079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_7578079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578079 prefixEnd_7578079 := by exact prefixLift 7578079
  have htrace : WordTrace (prefixWord ++ tailWord_7578079) baseStart_7578079 baseEnd_7578079 := by
    simpa [prefixWord, tailWord_7578079, baseEnd_7578079] using wordTrace_append hprefix tailTrace_7578079
  have hstable : (prefixWord ++ tailWord_7578079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578079).length < 2 ^ (prefixWord ++ tailWord_7578079).sum := by decide
  have hdescent : baseEnd_7578079 < baseStart_7578079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578092 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_7578092 : Nat := 118140960795 + 7578092 * 2 ^ 59
def prefixEnd_7578092 : Nat := 4983230072969 + 3 ^ 40 * 7578092 * 2
def baseEnd_7578092 : Nat := 3891203639991669913898995

theorem tailTrace_7578092 : CollatzResearch.WordTrace tailWord_7578092 prefixEnd_7578092 3891203639991669913898995 := by
  unfold tailWord_7578092
  simp only [CollatzResearch.WordTrace]
  refine ⟨138197861030937196959696265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184263814707916262612928353 138197861030937196959696265)
  ·
    refine ⟨103648395773202897719772199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138197861030937196959696265 103648395773202897719772199)
    ·
      refine ⟨155472593659804346579658299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103648395773202897719772199 155472593659804346579658299)
      ·
        refine ⟨233208890489706519869487449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155472593659804346579658299 233208890489706519869487449)
        ·
          refine ⟨174906667867279889902115587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233208890489706519869487449 174906667867279889902115587)
          ·
            refine ⟨262360001800919834853173381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174906667867279889902115587 262360001800919834853173381)
            ·
              refine ⟨49192500337672469034970009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262360001800919834853173381 49192500337672469034970009)
              ·
                refine ⟨36894375253254351776227507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49192500337672469034970009 36894375253254351776227507)
                ·
                  refine ⟨55341562879881527664341261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36894375253254351776227507 55341562879881527664341261)
                  ·
                    refine ⟨20753086079955572874127973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55341562879881527664341261 20753086079955572874127973)
                    ·
                      refine ⟨3891203639991669913898995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20753086079955572874127973 3891203639991669913898995)
                      ·
                        rfl

theorem cell23_7578092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_7578092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578092 prefixEnd_7578092 := by exact prefixLift 7578092
  have htrace : WordTrace (prefixWord ++ tailWord_7578092) baseStart_7578092 baseEnd_7578092 := by
    simpa [prefixWord, tailWord_7578092, baseEnd_7578092] using wordTrace_append hprefix tailTrace_7578092
  have hstable : (prefixWord ++ tailWord_7578092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578092).length < 2 ^ (prefixWord ++ tailWord_7578092).sum := by decide
  have hdescent : baseEnd_7578092 < baseStart_7578092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578109 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_7578109 : Nat := 118140960795 + 7578109 * 2 ^ 59
def prefixEnd_7578109 : Nat := 4983230072969 + 3 ^ 40 * 7578109 * 2
def baseEnd_7578109 : Nat := 3891212369162796347386417

theorem tailTrace_7578109 : CollatzResearch.WordTrace tailWord_7578109 prefixEnd_7578109 3891212369162796347386417 := by
  unfold tailWord_7578109
  simp only [CollatzResearch.WordTrace]
  refine ⟨276396342102812805822761381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184264228068541870548507587 276396342102812805822761381)
  ·
    refine ⟨51824314144277401091767759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276396342102812805822761381 51824314144277401091767759)
    ·
      refine ⟨77736471216416101637651639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51824314144277401091767759 77736471216416101637651639)
      ·
        refine ⟨116604706824624152456477459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77736471216416101637651639 116604706824624152456477459)
        ·
          refine ⟨174907060236936228684716189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116604706824624152456477459 174907060236936228684716189)
          ·
            refine ⟨65590147588851085756768571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174907060236936228684716189 65590147588851085756768571)
            ·
              refine ⟨98385221383276628635152857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65590147588851085756768571 98385221383276628635152857)
              ·
                refine ⟨73788916037457471476364643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98385221383276628635152857 73788916037457471476364643)
                ·
                  refine ⟨110683374056186207214546965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73788916037457471476364643 110683374056186207214546965)
                  ·
                    refine ⟨5188283158883728463181889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110683374056186207214546965 5188283158883728463181889)
                    ·
                      refine ⟨3891212369162796347386417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188283158883728463181889 3891212369162796347386417)
                      ·
                        rfl

theorem cell23_7578109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_7578109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578109 prefixEnd_7578109 := by exact prefixLift 7578109
  have htrace : WordTrace (prefixWord ++ tailWord_7578109) baseStart_7578109 baseEnd_7578109 := by
    simpa [prefixWord, tailWord_7578109, baseEnd_7578109] using wordTrace_append hprefix tailTrace_7578109
  have hstable : (prefixWord ++ tailWord_7578109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578109).length < 2 ^ (prefixWord ++ tailWord_7578109).sum := by decide
  have hdescent : baseEnd_7578109 < baseStart_7578109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578122 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_7578122 : Nat := 118140960795 + 7578122 * 2 ^ 59
def prefixEnd_7578122 : Nat := 4983230072969 + 3 ^ 40 * 7578122 * 2
def baseEnd_7578122 : Nat := 3891219044411304796523857

theorem tailTrace_7578122 : CollatzResearch.WordTrace tailWord_7578122 prefixEnd_7578122 3891219044411304796523857 := by
  unfold tailWord_7578122
  simp only [CollatzResearch.WordTrace]
  refine ⟨69099204062941427260746155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184264544167843806028656413 69099204062941427260746155)
  ·
    refine ⟨103648806094412140891119233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69099204062941427260746155 103648806094412140891119233)
    ·
      refine ⟨77736604570809105668339425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103648806094412140891119233 77736604570809105668339425)
      ·
        refine ⟨58302453428106829251254569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77736604570809105668339425 58302453428106829251254569)
        ·
          refine ⟨43726840071080121938440927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58302453428106829251254569 43726840071080121938440927)
          ·
            refine ⟨65590260106620182907661391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43726840071080121938440927 65590260106620182907661391)
            ·
              refine ⟨98385390159930274361492087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65590260106620182907661391 98385390159930274361492087)
              ·
                refine ⟨147578085239895411542238131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98385390159930274361492087 147578085239895411542238131)
                ·
                  refine ⟨221367127859843117313357197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147578085239895411542238131 221367127859843117313357197)
                  ·
                    refine ⟨83012672947441168992508949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221367127859843117313357197 83012672947441168992508949)
                    ·
                      refine ⟨3891219044411304796523857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83012672947441168992508949 3891219044411304796523857)
                      ·
                        rfl

theorem cell23_7578122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_7578122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578122 prefixEnd_7578122 := by exact prefixLift 7578122
  have htrace : WordTrace (prefixWord ++ tailWord_7578122) baseStart_7578122 baseEnd_7578122 := by
    simpa [prefixWord, tailWord_7578122, baseEnd_7578122] using wordTrace_append hprefix tailTrace_7578122
  have hstable : (prefixWord ++ tailWord_7578122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578122).length < 2 ^ (prefixWord ++ tailWord_7578122).sum := by decide
  have hdescent : baseEnd_7578122 < baseStart_7578122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578126 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7578126 : Nat := 118140960795 + 7578126 * 2 ^ 59
def prefixEnd_7578126 : Nat := 4983230072969 + 3 ^ 40 * 7578126 * 2
def baseEnd_7578126 : Nat := 3891221098333922780873839

theorem tailTrace_7578126 : CollatzResearch.WordTrace tailWord_7578126 prefixEnd_7578126 3891221098333922780873839 := by
  unfold tailWord_7578126
  simp only [CollatzResearch.WordTrace]
  refine ⟨34549620267968902215766279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184264641429167478484086821 34549620267968902215766279)
  ·
    refine ⟨51824430401953353323649419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34549620267968902215766279 51824430401953353323649419)
    ·
      refine ⟨77736645602930029985474129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51824430401953353323649419 77736645602930029985474129)
      ·
        refine ⟨58302484202197522489105597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77736645602930029985474129 58302484202197522489105597)
        ·
          refine ⟨21863431575824070933414599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58302484202197522489105597 21863431575824070933414599)
          ·
            refine ⟨32795147363736106400121899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21863431575824070933414599 32795147363736106400121899)
            ·
              refine ⟨49192721045604159600182849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32795147363736106400121899 49192721045604159600182849)
              ·
                refine ⟨36894540784203119700137137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49192721045604159600182849 36894540784203119700137137)
                ·
                  refine ⟨27670905588152339775102853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36894540784203119700137137 27670905588152339775102853)
                  ·
                    refine ⟨5188294797778563707831785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27670905588152339775102853 5188294797778563707831785)
                    ·
                      refine ⟨3891221098333922780873839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188294797778563707831785 3891221098333922780873839)
                      ·
                        rfl

theorem cell23_7578126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7578126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578126 prefixEnd_7578126 := by exact prefixLift 7578126
  have htrace : WordTrace (prefixWord ++ tailWord_7578126) baseStart_7578126 baseEnd_7578126 := by
    simpa [prefixWord, tailWord_7578126, baseEnd_7578126] using wordTrace_append hprefix tailTrace_7578126
  have hstable : (prefixWord ++ tailWord_7578126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578126).length < 2 ^ (prefixWord ++ tailWord_7578126).sum := by decide
  have hdescent : baseEnd_7578126 < baseStart_7578126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578136 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 3, 4]
def baseStart_7578136 : Nat := 118140960795 + 7578136 * 2 ^ 59
def prefixEnd_7578136 : Nat := 4983230072969 + 3 ^ 40 * 7578136 * 2
def baseEnd_7578136 : Nat := 1297075411046822580582931

theorem tailTrace_7578136 : CollatzResearch.WordTrace tailWord_7578136 prefixEnd_7578136 1297075411046822580582931 := by
  unfold tailWord_7578136
  simp only [CollatzResearch.WordTrace]
  refine ⟨138198663436857494716997131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184264884582476659622662841 138198663436857494716997131)
  ·
    refine ⟨207297995155286242075495697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138198663436857494716997131 207297995155286242075495697)
    ·
      refine ⟨155473496366464681556621773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207297995155286242075495697 155473496366464681556621773)
      ·
        refine ⟨58302561137424255583733165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155473496366464681556621773 58302561137424255583733165)
        ·
          refine ⟨21863460426534095843899937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58302561137424255583733165 21863460426534095843899937)
          ·
            refine ⟨16397595319900571882924953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21863460426534095843899937 16397595319900571882924953)
            ·
              refine ⟨12298196489925428912193715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16397595319900571882924953 12298196489925428912193715)
              ·
                refine ⟨18447294734888143368290573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12298196489925428912193715 18447294734888143368290573)
                ·
                  refine ⟨6917735525583053763108965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18447294734888143368290573 6917735525583053763108965)
                  ·
                    refine ⟨1297075411046822580582931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917735525583053763108965 1297075411046822580582931)
                    ·
                      rfl

theorem cell23_7578136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_7578136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578136 prefixEnd_7578136 := by exact prefixLift 7578136
  have htrace : WordTrace (prefixWord ++ tailWord_7578136) baseStart_7578136 baseEnd_7578136 := by
    simpa [prefixWord, tailWord_7578136, baseEnd_7578136] using wordTrace_append hprefix tailTrace_7578136
  have hstable : (prefixWord ++ tailWord_7578136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578136).length < 2 ^ (prefixWord ++ tailWord_7578136).sum := by decide
  have hdescent : baseEnd_7578136 < baseStart_7578136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578186 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_7578186 : Nat := 118140960795 + 7578186 * 2 ^ 59
def prefixEnd_7578186 : Nat := 4983230072969 + 3 ^ 40 * 7578186 * 2
def baseEnd_7578186 : Nat := 3891251907173192546123563

theorem tailTrace_7578186 : CollatzResearch.WordTrace tailWord_7578186 prefixEnd_7578186 3891251907173192546123563 := by
  unfold tailWord_7578186
  simp only [CollatzResearch.WordTrace]
  refine ⟨69099787630883461993328603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184266100349022565315542941 69099787630883461993328603)
  ·
    refine ⟨103649681446325192989992905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69099787630883461993328603 103649681446325192989992905)
    ·
      refine ⟨77737261084743894742494679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103649681446325192989992905 77737261084743894742494679)
      ·
        refine ⟨116605891627115842113742019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77737261084743894742494679 116605891627115842113742019)
        ·
          refine ⟨174908837440673763170613029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116605891627115842113742019 174908837440673763170613029)
          ·
            refine ⟨32795407020126330594489943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174908837440673763170613029 32795407020126330594489943)
            ·
              refine ⟨49193110530189495891734915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32795407020126330594489943 49193110530189495891734915)
              ·
                refine ⟨73789665795284243837602373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49193110530189495891734915 73789665795284243837602373)
                ·
                  refine ⟨13835562336615795719550445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73789665795284243837602373 13835562336615795719550445)
                  ·
                    refine ⟨5188335876230923394831417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13835562336615795719550445 5188335876230923394831417)
                    ·
                      refine ⟨3891251907173192546123563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188335876230923394831417 3891251907173192546123563)
                      ·
                        rfl

theorem cell23_7578186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_7578186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578186 prefixEnd_7578186 := by exact prefixLift 7578186
  have htrace : WordTrace (prefixWord ++ tailWord_7578186) baseStart_7578186 baseEnd_7578186 := by
    simpa [prefixWord, tailWord_7578186, baseEnd_7578186] using wordTrace_append hprefix tailTrace_7578186
  have hstable : (prefixWord ++ tailWord_7578186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578186).length < 2 ^ (prefixWord ++ tailWord_7578186).sum := by decide
  have hdescent : baseEnd_7578186 < baseStart_7578186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578192 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_7578192 : Nat := 118140960795 + 7578192 * 2 ^ 59
def prefixEnd_7578192 : Nat := 4983230072969 + 3 ^ 40 * 7578192 * 2
def baseEnd_7578192 : Nat := 1297084996019039840882845

theorem tailTrace_7578192 : CollatzResearch.WordTrace tailWord_7578192 prefixEnd_7578192 1297084996019039840882845 := by
  unfold tailWord_7578192
  simp only [CollatzResearch.WordTrace]
  refine ⟨138199684680756055499016415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184266246241008073998688553 138199684680756055499016415)
  ·
    refine ⟨207299527021134083248524623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138199684680756055499016415 207299527021134083248524623)
    ·
      refine ⟨310949290531701124872786935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207299527021134083248524623 310949290531701124872786935)
      ·
        refine ⟨466423935797551687309180403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310949290531701124872786935 466423935797551687309180403)
        ·
          refine ⟨699635903696327530963770605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466423935797551687309180403 699635903696327530963770605)
          ·
            refine ⟨262363463886122824111413977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 699635903696327530963770605 262363463886122824111413977)
            ·
              refine ⟨196772597914592118083560483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262363463886122824111413977 196772597914592118083560483)
              ·
                refine ⟨295158896871888177125340725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196772597914592118083560483 295158896871888177125340725)
                ·
                  refine ⟨27671146581739516605500693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295158896871888177125340725 27671146581739516605500693)
                  ·
                    refine ⟨1297084996019039840882845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27671146581739516605500693 1297084996019039840882845)
                    ·
                      rfl

theorem cell23_7578192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_7578192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578192 prefixEnd_7578192 := by exact prefixLift 7578192
  have htrace : WordTrace (prefixWord ++ tailWord_7578192) baseStart_7578192 baseEnd_7578192 := by
    simpa [prefixWord, tailWord_7578192, baseEnd_7578192] using wordTrace_append hprefix tailTrace_7578192
  have hstable : (prefixWord ++ tailWord_7578192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578192).length < 2 ^ (prefixWord ++ tailWord_7578192).sum := by decide
  have hdescent : baseEnd_7578192 < baseStart_7578192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578193 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_7578193 : Nat := 118140960795 + 7578193 * 2 ^ 59
def prefixEnd_7578193 : Nat := 4983230072969 + 3 ^ 40 * 7578193 * 2
def baseEnd_7578193 : Nat := 3891255501537774018736031

theorem tailTrace_7578193 : CollatzResearch.WordTrace tailWord_7578193 prefixEnd_7578193 3891255501537774018736031 := by
  unfold tailWord_7578193
  simp only [CollatzResearch.WordTrace]
  refine ⟨276399405834508488168819233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184266270556338992112546155 276399405834508488168819233)
  ·
    refine ⟨207299554375881366126614425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276399405834508488168819233 207299554375881366126614425)
    ·
      refine ⟨155474665781911024594960819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207299554375881366126614425 155474665781911024594960819)
      ·
        refine ⟨233211998672866536892441229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155474665781911024594960819 233211998672866536892441229)
        ·
          refine ⟨87454499502324951334665461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233211998672866536892441229 87454499502324951334665461)
          ·
            refine ⟨8198859328342964187624887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87454499502324951334665461 8198859328342964187624887)
            ·
              refine ⟨12298288992514446281437331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198859328342964187624887 12298288992514446281437331)
              ·
                refine ⟨18447433488771669422155997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12298288992514446281437331 18447433488771669422155997)
                ·
                  refine ⟨6917787558289376033308499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18447433488771669422155997 6917787558289376033308499)
                  ·
                    refine ⟨10376681337434064049962749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6917787558289376033308499 10376681337434064049962749)
                    ·
                      refine ⟨3891255501537774018736031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376681337434064049962749 3891255501537774018736031)
                      ·
                        rfl

theorem cell23_7578193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_7578193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578193 prefixEnd_7578193 := by exact prefixLift 7578193
  have htrace : WordTrace (prefixWord ++ tailWord_7578193) baseStart_7578193 baseEnd_7578193 := by
    simpa [prefixWord, tailWord_7578193, baseEnd_7578193] using wordTrace_append hprefix tailTrace_7578193
  have hstable : (prefixWord ++ tailWord_7578193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578193).length < 2 ^ (prefixWord ++ tailWord_7578193).sum := by decide
  have hdescent : baseEnd_7578193 < baseStart_7578193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578199 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_7578199 : Nat := 118140960795 + 7578199 * 2 ^ 59
def prefixEnd_7578199 : Nat := 4983230072969 + 3 ^ 40 * 7578199 * 2
def baseEnd_7578199 : Nat := 3891258582421700995261003

theorem tailTrace_7578199 : CollatzResearch.WordTrace tailWord_7578199 prefixEnd_7578199 3891258582421700995261003 := by
  unfold tailWord_7578199
  simp only [CollatzResearch.WordTrace]
  refine ⟨276399624672486751193537651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184266416448324500795691767 276399624672486751193537651)
  ·
    refine ⟨414599437008730126790306477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276399624672486751193537651 414599437008730126790306477)
    ·
      refine ⟨155474788878273797546364929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414599437008730126790306477 155474788878273797546364929)
      ·
        refine ⟨116606091658705348159773697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155474788878273797546364929 116606091658705348159773697)
        ·
          refine ⟨87454568744029011119830273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116606091658705348159773697 87454568744029011119830273)
          ·
            refine ⟨65590926558021758339872705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87454568744029011119830273 65590926558021758339872705)
            ·
              refine ⟨49193194918516318754904529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65590926558021758339872705 49193194918516318754904529)
              ·
                refine ⟨36894896188887239066178397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49193194918516318754904529 36894896188887239066178397)
                ·
                  refine ⟨13835586070832714649816899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36894896188887239066178397 13835586070832714649816899)
                  ·
                    refine ⟨20753379106249071974725349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13835586070832714649816899 20753379106249071974725349)
                    ·
                      refine ⟨3891258582421700995261003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20753379106249071974725349 3891258582421700995261003)
                      ·
                        rfl

theorem cell23_7578199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_7578199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578199 prefixEnd_7578199 := by exact prefixLift 7578199
  have htrace : WordTrace (prefixWord ++ tailWord_7578199) baseStart_7578199 baseEnd_7578199 := by
    simpa [prefixWord, tailWord_7578199, baseEnd_7578199] using wordTrace_append hprefix tailTrace_7578199
  have hstable : (prefixWord ++ tailWord_7578199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578199).length < 2 ^ (prefixWord ++ tailWord_7578199).sum := by decide
  have hdescent : baseEnd_7578199 < baseStart_7578199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578213 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_7578213 : Nat := 118140960795 + 7578213 * 2 ^ 59
def prefixEnd_7578213 : Nat := 4983230072969 + 3 ^ 40 * 7578213 * 2
def baseEnd_7578213 : Nat := 1297088590383621313495313

theorem tailTrace_7578213 : CollatzResearch.WordTrace tailWord_7578213 prefixEnd_7578213 1297088590383621313495313 := by
  unfold tailWord_7578213
  simp only [CollatzResearch.WordTrace]
  refine ⟨276400135294436031584547293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184266756862957354389698195 276400135294436031584547293)
  ·
    refine ⟨103650050735413511844205235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276400135294436031584547293 103650050735413511844205235)
    ·
      refine ⟨155475076103120267766307853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103650050735413511844205235 155475076103120267766307853)
      ·
        refine ⟨58303153538670100412365445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155475076103120267766307853 58303153538670100412365445)
        ·
          refine ⟨10931841288500643827318521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58303153538670100412365445 10931841288500643827318521)
          ·
            refine ⟨8198880966375482870488891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10931841288500643827318521 8198880966375482870488891)
            ·
              refine ⟨12298321449563224305733337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198880966375482870488891 12298321449563224305733337)
              ·
                refine ⟨9223741087172418229300003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12298321449563224305733337 9223741087172418229300003)
                ·
                  refine ⟨13835611630758627343950005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223741087172418229300003 13835611630758627343950005)
                  ·
                    refine ⟨1297088590383621313495313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13835611630758627343950005 1297088590383621313495313)
                    ·
                      rfl

theorem cell23_7578213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_7578213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578213 prefixEnd_7578213 := by exact prefixLift 7578213
  have htrace : WordTrace (prefixWord ++ tailWord_7578213) baseStart_7578213 baseEnd_7578213 := by
    simpa [prefixWord, tailWord_7578213, baseEnd_7578213] using wordTrace_append hprefix tailTrace_7578213
  have hstable : (prefixWord ++ tailWord_7578213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578213).length < 2 ^ (prefixWord ++ tailWord_7578213).sum := by decide
  have hdescent : baseEnd_7578213 < baseStart_7578213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578226 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_7578226 : Nat := 118140960795 + 7578226 * 2 ^ 59
def prefixEnd_7578226 : Nat := 4983230072969 + 3 ^ 40 * 7578226 * 2
def baseEnd_7578226 : Nat := 1297090815466457463207793

theorem tailTrace_7578226 : CollatzResearch.WordTrace tailWord_7578226 prefixEnd_7578226 1297090815466457463207793 := by
  unfold tailWord_7578226
  simp only [CollatzResearch.WordTrace]
  refine ⟨69100152360847233701192633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184267072962259289869847021 69100152360847233701192633)
  ·
    refine ⟨51825114270635425275894475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69100152360847233701192633 51825114270635425275894475)
    ·
      refine ⟨77737671405953137913841713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51825114270635425275894475 77737671405953137913841713)
      ·
        refine ⟨58303253554464853435381285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77737671405953137913841713 58303253554464853435381285)
        ·
          refine ⟨10931860041462160019133991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58303253554464853435381285 10931860041462160019133991)
          ·
            refine ⟨16397790062193240028700987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10931860041462160019133991 16397790062193240028700987)
            ·
              refine ⟨24596685093289860043051481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16397790062193240028700987 24596685093289860043051481)
              ·
                refine ⟨18447513819967395032288611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24596685093289860043051481 18447513819967395032288611)
                ·
                  refine ⟨27671270729951092548432917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18447513819967395032288611 27671270729951092548432917)
                  ·
                    refine ⟨1297090815466457463207793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27671270729951092548432917 1297090815466457463207793)
                    ·
                      rfl

theorem cell23_7578226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_7578226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578226 prefixEnd_7578226 := by exact prefixLift 7578226
  have htrace : WordTrace (prefixWord ++ tailWord_7578226) baseStart_7578226 baseEnd_7578226 := by
    simpa [prefixWord, tailWord_7578226, baseEnd_7578226] using wordTrace_append hprefix tailTrace_7578226
  have hstable : (prefixWord ++ tailWord_7578226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578226).length < 2 ^ (prefixWord ++ tailWord_7578226).sum := by decide
  have hdescent : baseEnd_7578226 < baseStart_7578226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578230 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_7578230 : Nat := 118140960795 + 7578230 * 2 ^ 59
def prefixEnd_7578230 : Nat := 4983230072969 + 3 ^ 40 * 7578230 * 2
def baseEnd_7578230 : Nat := 1297091500107330124657787

theorem tailTrace_7578230 : CollatzResearch.WordTrace tailWord_7578230 prefixEnd_7578230 1297091500107330124657787 := by
  unfold tailWord_7578230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275047208460902717994759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184267170223582962325277429 17275047208460902717994759)
  ·
    refine ⟨25912570812691354076992139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275047208460902717994759 25912570812691354076992139)
    ·
      refine ⟨38868856219037031115488209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25912570812691354076992139 38868856219037031115488209)
      ·
        refine ⟨29151642164277773336616157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38868856219037031115488209 29151642164277773336616157)
        ·
          refine ⟨10931865811604165001231059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29151642164277773336616157 10931865811604165001231059)
          ·
            refine ⟨16397798717406247501846589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10931865811604165001231059 16397798717406247501846589)
            ·
              refine ⟨6149174519027342813192471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16397798717406247501846589 6149174519027342813192471)
              ·
                refine ⟨9223761778541014219788707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149174519027342813192471 9223761778541014219788707)
                ·
                  refine ⟨13835642667811521329683061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223761778541014219788707 13835642667811521329683061)
                  ·
                    refine ⟨1297091500107330124657787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13835642667811521329683061 1297091500107330124657787)
                    ·
                      rfl

theorem cell23_7578230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_7578230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578230 prefixEnd_7578230 := by exact prefixLift 7578230
  have htrace : WordTrace (prefixWord ++ tailWord_7578230) baseStart_7578230 baseEnd_7578230 := by
    simpa [prefixWord, tailWord_7578230, baseEnd_7578230] using wordTrace_append hprefix tailTrace_7578230
  have hstable : (prefixWord ++ tailWord_7578230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578230).length < 2 ^ (prefixWord ++ tailWord_7578230).sum := by decide
  have hdescent : baseEnd_7578230 < baseStart_7578230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578233 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 1, 1, 4]
def baseStart_7578233 : Nat := 118140960795 + 7578233 * 2 ^ 59
def prefixEnd_7578233 : Nat := 4983230072969 + 3 ^ 40 * 7578233 * 2
def baseEnd_7578233 : Nat := 3891276040763953862235847

theorem tailTrace_7578233 : CollatzResearch.WordTrace tailWord_7578233 prefixEnd_7578233 3891276040763953862235847 := by
  unfold tailWord_7578233
  simp only [CollatzResearch.WordTrace]
  refine ⟨276400864754363575000275353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184267243169575716666850235 276400864754363575000275353)
  ·
    refine ⟨207300648565772681250206515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276400864754363575000275353 207300648565772681250206515)
    ·
      refine ⟨310950972848659021875309773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207300648565772681250206515 310950972848659021875309773)
      ·
        refine ⟨116606614818247133203241165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310950972848659021875309773 116606614818247133203241165)
        ·
          refine ⟨43727480556842674951215437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116606614818247133203241165 43727480556842674951215437)
          ·
            refine ⟨16397805208816003106705789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43727480556842674951215437 16397805208816003106705789)
            ·
              refine ⟨6149176953306001165014671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16397805208816003106705789 6149176953306001165014671)
              ·
                refine ⟨9223765429959001747522007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149176953306001165014671 9223765429959001747522007)
                ·
                  refine ⟨13835648144938502621283011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223765429959001747522007 13835648144938502621283011)
                  ·
                    refine ⟨20753472217407753931924517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13835648144938502621283011 20753472217407753931924517)
                    ·
                      refine ⟨3891276040763953862235847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20753472217407753931924517 3891276040763953862235847)
                      ·
                        rfl

theorem cell23_7578233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_7578233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578233 prefixEnd_7578233 := by exact prefixLift 7578233
  have htrace : WordTrace (prefixWord ++ tailWord_7578233) baseStart_7578233 baseEnd_7578233 := by
    simpa [prefixWord, tailWord_7578233, baseEnd_7578233] using wordTrace_append hprefix tailTrace_7578233
  have hstable : (prefixWord ++ tailWord_7578233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578233).length < 2 ^ (prefixWord ++ tailWord_7578233).sum := by decide
  have hdescent : baseEnd_7578233 < baseStart_7578233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578236 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_7578236 : Nat := 118140960795 + 7578236 * 2 ^ 59
def prefixEnd_7578236 : Nat := 4983230072969 + 3 ^ 40 * 7578236 * 2
def baseEnd_7578236 : Nat := 3891277581205917350498333

theorem tailTrace_7578236 : CollatzResearch.WordTrace tailWord_7578236 prefixEnd_7578236 3891277581205917350498333 := by
  unfold tailWord_7578236
  simp only [CollatzResearch.WordTrace]
  refine ⟨138200487086676353256317281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184267316115568471008423041 138200487086676353256317281)
  ·
    refine ⟨103650365315007264942237961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138200487086676353256317281 103650365315007264942237961)
    ·
      refine ⟨77737773986255448706678471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103650365315007264942237961 77737773986255448706678471)
      ·
        refine ⟨116606660979383173060017707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77737773986255448706678471 116606660979383173060017707)
        ·
          refine ⟨174909991469074759590026561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116606660979383173060017707 174909991469074759590026561)
          ·
            refine ⟨131182493601806069692519921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174909991469074759590026561 131182493601806069692519921)
            ·
              refine ⟨98386870201354552269389941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131182493601806069692519921 98386870201354552269389941)
              ·
                refine ⟨9223769081376989275255307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98386870201354552269389941 9223769081376989275255307)
                ·
                  refine ⟨13835653622065483912882961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223769081376989275255307 13835653622065483912882961)
                  ·
                    refine ⟨10376740216549112934662221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13835653622065483912882961 10376740216549112934662221)
                    ·
                      refine ⟨3891277581205917350498333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376740216549112934662221 3891277581205917350498333)
                      ·
                        rfl

theorem cell23_7578236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_7578236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578236 prefixEnd_7578236 := by exact prefixLift 7578236
  have htrace : WordTrace (prefixWord ++ tailWord_7578236) baseStart_7578236 baseEnd_7578236 := by
    simpa [prefixWord, tailWord_7578236, baseEnd_7578236] using wordTrace_append hprefix tailTrace_7578236
  have hstable : (prefixWord ++ tailWord_7578236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578236).length < 2 ^ (prefixWord ++ tailWord_7578236).sum := by decide
  have hdescent : baseEnd_7578236 < baseStart_7578236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578249 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_7578249 : Nat := 118140960795 + 7578249 * 2 ^ 59
def prefixEnd_7578249 : Nat := 4983230072969 + 3 ^ 40 * 7578249 * 2
def baseEnd_7578249 : Nat := 3891284256454425799635773

theorem tailTrace_7578249 : CollatzResearch.WordTrace tailWord_7578249 prefixEnd_7578249 3891284256454425799635773 := by
  unfold tailWord_7578249
  simp only [CollatzResearch.WordTrace]
  refine ⟨276401448322305609732857801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184267632214870406488571867 276401448322305609732857801)
  ·
    refine ⟨207301086241729207299643351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276401448322305609732857801 207301086241729207299643351)
    ·
      refine ⟨310951629362593810949465027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207301086241729207299643351 310951629362593810949465027)
      ·
        refine ⟨466427444043890716424197541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310951629362593810949465027 466427444043890716424197541)
        ·
          refine ⟨87455145758229509329537039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466427444043890716424197541 87455145758229509329537039)
          ·
            refine ⟨131182718637344263994305559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87455145758229509329537039 131182718637344263994305559)
            ·
              refine ⟨196774077956016395991458339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131182718637344263994305559 196774077956016395991458339)
              ·
                refine ⟨295161116934024593987187509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196774077956016395991458339 295161116934024593987187509)
                ·
                  refine ⟨27671354712564805686298829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295161116934024593987187509 27671354712564805686298829)
                  ·
                    refine ⟨10376758017211802132362061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27671354712564805686298829 10376758017211802132362061)
                    ·
                      refine ⟨3891284256454425799635773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376758017211802132362061 3891284256454425799635773)
                      ·
                        rfl

theorem cell23_7578249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_7578249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578249 prefixEnd_7578249 := by exact prefixLift 7578249
  have htrace : WordTrace (prefixWord ++ tailWord_7578249) baseStart_7578249 baseEnd_7578249 := by
    simpa [prefixWord, tailWord_7578249, baseEnd_7578249] using wordTrace_append hprefix tailTrace_7578249
  have hstable : (prefixWord ++ tailWord_7578249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578249).length < 2 ^ (prefixWord ++ tailWord_7578249).sum := by decide
  have hdescent : baseEnd_7578249 < baseStart_7578249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578294 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7578294 : Nat := 118140960795 + 7578294 * 2 ^ 59
def prefixEnd_7578294 : Nat := 4983230072969 + 3 ^ 40 * 7578294 * 2
def baseEnd_7578294 : Nat := 1297102454361292707857689

theorem tailTrace_7578294 : CollatzResearch.WordTrace tailWord_7578294 prefixEnd_7578294 1297102454361292707857689 := by
  unfold tailWord_7578294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275193100446411401140371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184268726404761721612163957 17275193100446411401140371)
  ·
    refine ⟨25912789650669617101710557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275193100446411401140371 25912789650669617101710557)
    ·
      refine ⟨9717296119001106413141459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25912789650669617101710557 9717296119001106413141459)
      ·
        refine ⟨14575944178501659619712189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9717296119001106413141459 14575944178501659619712189)
        ·
          refine ⟨5465979066938122357392071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14575944178501659619712189 5465979066938122357392071)
          ·
            refine ⟨8198968600407183536088107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465979066938122357392071 8198968600407183536088107)
            ·
              refine ⟨12298452900610775304132161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198968600407183536088107 12298452900610775304132161)
              ·
                refine ⟨9223839675458081478099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12298452900610775304132161 9223839675458081478099121)
                ·
                  refine ⟨6917879756593561108574341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9223839675458081478099121 6917879756593561108574341)
                  ·
                    refine ⟨1297102454361292707857689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917879756593561108574341 1297102454361292707857689)
                    ·
                      rfl

theorem cell23_7578294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7578294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578294 prefixEnd_7578294 := by exact prefixLift 7578294
  have htrace : WordTrace (prefixWord ++ tailWord_7578294) baseStart_7578294 baseEnd_7578294 := by
    simpa [prefixWord, tailWord_7578294, baseEnd_7578294] using wordTrace_append hprefix tailTrace_7578294
  have hstable : (prefixWord ++ tailWord_7578294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578294).length < 2 ^ (prefixWord ++ tailWord_7578294).sum := by decide
  have hdescent : baseEnd_7578294 < baseStart_7578294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578316 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_7578316 : Nat := 118140960795 + 7578316 * 2 ^ 59
def prefixEnd_7578316 : Nat := 4983230072969 + 3 ^ 40 * 7578316 * 2
def baseEnd_7578316 : Nat := 1297106219886092345832655

theorem tailTrace_7578316 : CollatzResearch.WordTrace tailWord_7578316 prefixEnd_7578316 1297106219886092345832655 := by
  unfold tailWord_7578316
  simp only [CollatzResearch.WordTrace]
  refine ⟨138201946006531440087773401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184269261342041920117031201 138201946006531440087773401)
  ·
    refine ⟨103651459504898580065830051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138201946006531440087773401 103651459504898580065830051)
    ·
      refine ⟨155477189257347870098745077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103651459504898580065830051 155477189257347870098745077)
      ·
        refine ⟨14575986492876362821757351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155477189257347870098745077 14575986492876362821757351)
        ·
          refine ⟨21863979739314544232636027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14575986492876362821757351 21863979739314544232636027)
          ·
            refine ⟨32795969608971816348954041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21863979739314544232636027 32795969608971816348954041)
            ·
              refine ⟨24596977206728862261715531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32795969608971816348954041 24596977206728862261715531)
              ·
                refine ⟨36895465810093293392573297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24596977206728862261715531 36895465810093293392573297)
                ·
                  refine ⟨27671599357569970044429973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36895465810093293392573297 27671599357569970044429973)
                  ·
                    refine ⟨1297106219886092345832655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27671599357569970044429973 1297106219886092345832655)
                    ·
                      rfl

theorem cell23_7578316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_7578316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578316 prefixEnd_7578316 := by exact prefixLift 7578316
  have htrace : WordTrace (prefixWord ++ tailWord_7578316) baseStart_7578316 baseEnd_7578316 := by
    simpa [prefixWord, tailWord_7578316, baseEnd_7578316] using wordTrace_append hprefix tailTrace_7578316
  have hstable : (prefixWord ++ tailWord_7578316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578316).length < 2 ^ (prefixWord ++ tailWord_7578316).sum := by decide
  have hdescent : baseEnd_7578316 < baseStart_7578316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578317 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7578317 : Nat := 118140960795 + 7578317 * 2 ^ 59
def prefixEnd_7578317 : Nat := 4983230072969 + 3 ^ 40 * 7578317 * 2
def baseEnd_7578317 : Nat := 3891319173138931533585461

theorem tailTrace_7578317 : CollatzResearch.WordTrace tailWord_7578317 prefixEnd_7578317 3891319173138931533585461 := by
  unfold tailWord_7578317
  simp only [CollatzResearch.WordTrace]
  refine ⟨276403928486059257346333205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184269285657372838230888803 276403928486059257346333205)
  ·
    refine ⟨12956434147784027688109369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 276403928486059257346333205 12956434147784027688109369)
    ·
      refine ⟨9717325610838020766082027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12956434147784027688109369 9717325610838020766082027)
      ·
        refine ⟨14575988416257031149123041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9717325610838020766082027 14575988416257031149123041)
        ·
          refine ⟨10931991312192773361842281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14575988416257031149123041 10931991312192773361842281)
          ·
            refine ⟨8198993484144580021381711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10931991312192773361842281 8198993484144580021381711)
            ·
              refine ⟨12298490226216870032072567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198993484144580021381711 12298490226216870032072567)
              ·
                refine ⟨18447735339325305048108851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12298490226216870032072567 18447735339325305048108851)
                ·
                  refine ⟨27671603008987957572163277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18447735339325305048108851 27671603008987957572163277)
                  ·
                    refine ⟨10376851128370484089561229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27671603008987957572163277 10376851128370484089561229)
                    ·
                      refine ⟨3891319173138931533585461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10376851128370484089561229 3891319173138931533585461)
                      ·
                        rfl

theorem cell23_7578317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7578317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578317 prefixEnd_7578317 := by exact prefixLift 7578317
  have htrace : WordTrace (prefixWord ++ tailWord_7578317) baseStart_7578317 baseEnd_7578317 := by
    simpa [prefixWord, tailWord_7578317, baseEnd_7578317] using wordTrace_append hprefix tailTrace_7578317
  have hstable : (prefixWord ++ tailWord_7578317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578317).length < 2 ^ (prefixWord ++ tailWord_7578317).sum := by decide
  have hdescent : baseEnd_7578317 < baseStart_7578317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578329 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 7]
def baseStart_7578329 : Nat := 118140960795 + 7578329 * 2 ^ 59
def prefixEnd_7578329 : Nat := 4983230072969 + 3 ^ 40 * 7578329 * 2
def baseEnd_7578329 : Nat := 432369481656309498515045

theorem tailTrace_7578329 : CollatzResearch.WordTrace tailWord_7578329 prefixEnd_7578329 432369481656309498515045 := by
  unfold tailWord_7578329
  simp only [CollatzResearch.WordTrace]
  refine ⟨276404366162015783395770041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184269577441343855597180027 276404366162015783395770041)
  ·
    refine ⟨207303274621511837546827531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276404366162015783395770041 207303274621511837546827531)
    ·
      refine ⟨310954911932267756320241297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207303274621511837546827531 310954911932267756320241297)
      ·
        refine ⟨233216183949200817240180973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310954911932267756320241297 233216183949200817240180973)
        ·
          refine ⟨87456068980950306465067865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233216183949200817240180973 87456068980950306465067865)
          ·
            refine ⟨65592051735712729848800899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87456068980950306465067865 65592051735712729848800899)
            ·
              refine ⟨98388077603569094773201349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65592051735712729848800899 98388077603569094773201349)
              ·
                refine ⟨18447764550669205269975253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98388077603569094773201349 18447764550669205269975253)
                ·
                  refine ⟨432369481656309498515045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18447764550669205269975253 432369481656309498515045)
                  ·
                    rfl

theorem cell23_7578329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_7578329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578329 prefixEnd_7578329 := by exact prefixLift 7578329
  have htrace : WordTrace (prefixWord ++ tailWord_7578329) baseStart_7578329 baseEnd_7578329 := by
    simpa [prefixWord, tailWord_7578329, baseEnd_7578329] using wordTrace_append hprefix tailTrace_7578329
  have hstable : (prefixWord ++ tailWord_7578329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578329).length < 2 ^ (prefixWord ++ tailWord_7578329).sum := by decide
  have hdescent : baseEnd_7578329 < baseStart_7578329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578409 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_7578409 : Nat := 118140960795 + 7578409 * 2 ^ 59
def prefixEnd_7578409 : Nat := 4983230072969 + 3 ^ 40 * 7578409 * 2
def baseEnd_7578409 : Nat := 3891366413359145173635037

theorem tailTrace_7578409 : CollatzResearch.WordTrace tailWord_7578409 prefixEnd_7578409 3891366413359145173635037 := by
  unfold tailWord_7578409
  simp only [CollatzResearch.WordTrace]
  refine ⟨276407284001725957058682281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184271522667817304705788187 276407284001725957058682281)
  ·
    refine ⟨207305463001294467794011711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276407284001725957058682281 207305463001294467794011711)
    ·
      refine ⟨310958194501941701691017567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207305463001294467794011711 310958194501941701691017567)
      ·
        refine ⟨466437291752912552536526351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310958194501941701691017567 466437291752912552536526351)
        ·
          refine ⟨699655937629368828804789527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466437291752912552536526351 699655937629368828804789527)
          ·
            refine ⟨1049483906444053243207184291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699655937629368828804789527 1049483906444053243207184291)
            ·
              refine ⟨1574225859666079864810776437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049483906444053243207184291 1574225859666079864810776437)
              ·
                refine ⟨147583674343694987326010291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574225859666079864810776437 147583674343694987326010291)
                ·
                  refine ⟨221375511515542480989015437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147583674343694987326010291 221375511515542480989015437)
                  ·
                    refine ⟨83015816818328430370880789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221375511515542480989015437 83015816818328430370880789)
                    ·
                      refine ⟨3891366413359145173635037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83015816818328430370880789 3891366413359145173635037)
                      ·
                        rfl

theorem cell23_7578409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_7578409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578409 prefixEnd_7578409 := by exact prefixLift 7578409
  have htrace : WordTrace (prefixWord ++ tailWord_7578409) baseStart_7578409 baseEnd_7578409 := by
    simpa [prefixWord, tailWord_7578409, baseEnd_7578409] using wordTrace_append hprefix tailTrace_7578409
  have hstable : (prefixWord ++ tailWord_7578409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578409).length < 2 ^ (prefixWord ++ tailWord_7578409).sum := by decide
  have hdescent : baseEnd_7578409 < baseStart_7578409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578463 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 3]
def baseStart_7578463 : Nat := 118140960795 + 7578463 * 2 ^ 59
def prefixEnd_7578463 : Nat := 4983230072969 + 3 ^ 40 * 7578463 * 2
def baseEnd_7578463 : Nat := 3891394141314487962359789

theorem tailTrace_7578463 : CollatzResearch.WordTrace tailWord_7578463 prefixEnd_7578463 3891394141314487962359789 := by
  unfold tailWord_7578463
  simp only [CollatzResearch.WordTrace]
  refine ⟨276409253543530324281148043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184272835695686882854098695 276409253543530324281148043)
  ·
    refine ⟨414613880315295486421722065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276409253543530324281148043 414613880315295486421722065)
    ·
      refine ⟨310960410236471614816291549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414613880315295486421722065 310960410236471614816291549)
      ·
        refine ⟨116610153838676855556109331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310960410236471614816291549 116610153838676855556109331)
        ·
          refine ⟨174915230758015283334163997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116610153838676855556109331 174915230758015283334163997)
          ·
            refine ⟨65593211534255731250311499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174915230758015283334163997 65593211534255731250311499)
            ·
              refine ⟨98389817301383596875467249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65593211534255731250311499 98389817301383596875467249)
              ·
                refine ⟨73792362976037697656600437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98389817301383596875467249 73792362976037697656600437)
                ·
                  refine ⟨6918034029003534155306291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73792362976037697656600437 6918034029003534155306291)
                  ·
                    refine ⟨10377051043505301232959437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6918034029003534155306291 10377051043505301232959437)
                    ·
                      refine ⟨3891394141314487962359789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10377051043505301232959437 3891394141314487962359789)
                      ·
                        rfl

theorem cell23_7578463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_7578463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578463 prefixEnd_7578463 := by exact prefixLift 7578463
  have htrace : WordTrace (prefixWord ++ tailWord_7578463) baseStart_7578463 baseEnd_7578463 := by
    simpa [prefixWord, tailWord_7578463, baseEnd_7578463] using wordTrace_append hprefix tailTrace_7578463
  have hstable : (prefixWord ++ tailWord_7578463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578463).length < 2 ^ (prefixWord ++ tailWord_7578463).sum := by decide
  have hdescent : baseEnd_7578463 < baseStart_7578463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578496 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_7578496 : Nat := 118140960795 + 7578496 * 2 ^ 59
def prefixEnd_7578496 : Nat := 4983230072969 + 3 ^ 40 * 7578496 * 2
def baseEnd_7578496 : Nat := 1297137028725362111082379

theorem tailTrace_7578496 : CollatzResearch.WordTrace tailWord_7578496 prefixEnd_7578496 1297137028725362111082379 := by
  unfold tailWord_7578496
  simp only [CollatzResearch.WordTrace]
  refine ⟨138205228576205385458549671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184273638101607180611399561 138205228576205385458549671)
  ·
    refine ⟨207307842864308078187824507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138205228576205385458549671 207307842864308078187824507)
    ·
      refine ⟨310961764296462117281736761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207307842864308078187824507 310961764296462117281736761)
      ·
        refine ⟨233221323222346587961302571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310961764296462117281736761 233221323222346587961302571)
        ·
          refine ⟨349831984833519881941953857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233221323222346587961302571 349831984833519881941953857)
          ·
            refine ⟨262373988625139911456465393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349831984833519881941953857 262373988625139911456465393)
            ·
              refine ⟨196780491468854933592349045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262373988625139911456465393 196780491468854933592349045)
              ·
                refine ⟨18448171075205150024282723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196780491468854933592349045 18448171075205150024282723)
                ·
                  refine ⟨27672256612807725036424085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18448171075205150024282723 27672256612807725036424085)
                  ·
                    refine ⟨1297137028725362111082379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27672256612807725036424085 1297137028725362111082379)
                    ·
                      rfl

theorem cell23_7578496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_7578496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578496 prefixEnd_7578496 := by exact prefixLift 7578496
  have htrace : WordTrace (prefixWord ++ tailWord_7578496) baseStart_7578496 baseEnd_7578496 := by
    simpa [prefixWord, tailWord_7578496, baseEnd_7578496] using wordTrace_append hprefix tailTrace_7578496
  have hstable : (prefixWord ++ tailWord_7578496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578496).length < 2 ^ (prefixWord ++ tailWord_7578496).sum := by decide
  have hdescent : baseEnd_7578496 < baseStart_7578496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578530 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7578530 : Nat := 118140960795 + 7578530 * 2 ^ 59
def prefixEnd_7578530 : Nat := 4983230072969 + 3 ^ 40 * 7578530 * 2
def baseEnd_7578530 : Nat := 1297142848172779733407327

theorem tailTrace_7578530 : CollatzResearch.WordTrace tailWord_7578530 prefixEnd_7578530 1297142848172779733407327 := by
  unfold tailWord_7578530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69102924308571898680959261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184274464822858396482558029 69102924308571898680959261)
  ·
    refine ⟨25913596615714462005359723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69102924308571898680959261 25913596615714462005359723)
    ·
      refine ⟨38870394923571693008039585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25913596615714462005359723 38870394923571693008039585)
      ·
        refine ⟨29152796192678769756029689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38870394923571693008039585 29152796192678769756029689)
        ·
          refine ⟨21864597144509077317022267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29152796192678769756029689 21864597144509077317022267)
          ·
            refine ⟨32796895716763615975533401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21864597144509077317022267 32796895716763615975533401)
            ·
              refine ⟨24597671787572711981650051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32796895716763615975533401 24597671787572711981650051)
              ·
                refine ⟨36896507681359067972475077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24597671787572711981650051 36896507681359067972475077)
                ·
                  refine ⟨6918095190254825244839077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36896507681359067972475077 6918095190254825244839077)
                  ·
                    refine ⟨1297142848172779733407327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918095190254825244839077 1297142848172779733407327)
                    ·
                      rfl

theorem cell23_7578530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7578530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578530 prefixEnd_7578530 := by exact prefixLift 7578530
  have htrace : WordTrace (prefixWord ++ tailWord_7578530) baseStart_7578530 baseEnd_7578530 := by
    simpa [prefixWord, tailWord_7578530, baseEnd_7578530] using wordTrace_append hprefix tailTrace_7578530
  have hstable : (prefixWord ++ tailWord_7578530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578530).length < 2 ^ (prefixWord ++ tailWord_7578530).sum := by decide
  have hdescent : baseEnd_7578530 < baseStart_7578530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578563 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 7, 2]
def baseStart_7578563 : Nat := 118140960795 + 7578563 * 2 ^ 59
def prefixEnd_7578563 : Nat := 4983230072969 + 3 ^ 40 * 7578563 * 2
def baseEnd_7578563 : Nat := 3891445489379937571109329

theorem tailTrace_7578563 : CollatzResearch.WordTrace tailWord_7578563 prefixEnd_7578563 3891445489379937571109329 := by
  unfold tailWord_7578563
  simp only [CollatzResearch.WordTrace]
  refine ⟨276412900843168041359788343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184275267228778694239858895 276412900843168041359788343)
  ·
    refine ⟨414619351264752062039682515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276412900843168041359788343 414619351264752062039682515)
    ·
      refine ⟨621929026897128093059523773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414619351264752062039682515 621929026897128093059523773)
      ·
        refine ⟨233223385086423034897321415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621929026897128093059523773 233223385086423034897321415)
        ·
          refine ⟨349835077629634552345982123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233223385086423034897321415 349835077629634552345982123)
          ·
            refine ⟨524752616444451828518973185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349835077629634552345982123 524752616444451828518973185)
            ·
              refine ⟨393564462333338871389229889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524752616444451828518973185 393564462333338871389229889)
              ·
                refine ⟨295173346750004153541922417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393564462333338871389229889 295173346750004153541922417)
                ·
                  refine ⟨221380010062503115156441813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295173346750004153541922417 221380010062503115156441813)
                  ·
                    refine ⟨5188593985839916761479105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 221380010062503115156441813 5188593985839916761479105)
                    ·
                      refine ⟨3891445489379937571109329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188593985839916761479105 3891445489379937571109329)
                      ·
                        rfl

theorem cell23_7578563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_7578563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578563 prefixEnd_7578563 := by exact prefixLift 7578563
  have htrace : WordTrace (prefixWord ++ tailWord_7578563) baseStart_7578563 baseEnd_7578563 := by
    simpa [prefixWord, tailWord_7578563, baseEnd_7578563] using wordTrace_append hprefix tailTrace_7578563
  have hstable : (prefixWord ++ tailWord_7578563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578563).length < 2 ^ (prefixWord ++ tailWord_7578563).sum := by decide
  have hdescent : baseEnd_7578563 < baseStart_7578563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578650 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_7578650 : Nat := 118140960795 + 7578650 * 2 ^ 59
def prefixEnd_7578650 : Nat := 4983230072969 + 3 ^ 40 * 7578650 * 2
def baseEnd_7578650 : Nat := 432387795799653192302381

theorem tailTrace_7578650 : CollatzResearch.WordTrace tailWord_7578650 prefixEnd_7578650 432387795799653192302381 := by
  unfold tailWord_7578650
  simp only [CollatzResearch.WordTrace]
  refine ⟨69104018498463213804551351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184277382662568570145470269 69104018498463213804551351)
  ·
    refine ⟨103656027747694820706827027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69104018498463213804551351 103656027747694820706827027)
    ·
      refine ⟨155484041621542231060240541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103656027747694820706827027 155484041621542231060240541)
      ·
        refine ⟨58306515608078336647590203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155484041621542231060240541 58306515608078336647590203)
        ·
          refine ⟨87459773412117504971385305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58306515608078336647590203 87459773412117504971385305)
          ·
            refine ⟨65594830059088128728538979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87459773412117504971385305 65594830059088128728538979)
            ·
              refine ⟨98392245088632193092808469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65594830059088128728538979 98392245088632193092808469)
              ·
                refine ⟨4612136488529634051225397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98392245088632193092808469 4612136488529634051225397)
                ·
                  refine ⟨432387795799653192302381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4612136488529634051225397 432387795799653192302381)
                  ·
                    rfl

theorem cell23_7578650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_7578650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578650 prefixEnd_7578650 := by exact prefixLift 7578650
  have htrace : WordTrace (prefixWord ++ tailWord_7578650) baseStart_7578650 baseEnd_7578650 := by
    simpa [prefixWord, tailWord_7578650, baseEnd_7578650] using wordTrace_append hprefix tailTrace_7578650
  have hstable : (prefixWord ++ tailWord_7578650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578650).length < 2 ^ (prefixWord ++ tailWord_7578650).sum := by decide
  have hdescent : baseEnd_7578650 < baseStart_7578650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578713 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_7578713 : Nat := 118140960795 + 7578713 * 2 ^ 59
def prefixEnd_7578713 : Nat := 4983230072969 + 3 ^ 40 * 7578713 * 2
def baseEnd_7578713 : Nat := 3891522511478111984233639

theorem tailTrace_7578713 : CollatzResearch.WordTrace tailWord_7578713 prefixEnd_7578713 3891522511478111984233639 := by
  unfold tailWord_7578713
  simp only [CollatzResearch.WordTrace]
  refine ⟨276418371792624616977748793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184278914528416411318499195 276418371792624616977748793)
  ·
    refine ⟨207313778844468462733311595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276418371792624616977748793 207313778844468462733311595)
    ·
      refine ⟨310970668266702694099967393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207313778844468462733311595 310970668266702694099967393)
      ·
        refine ⟨233228001200027020574975545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310970668266702694099967393 233228001200027020574975545)
        ·
          refine ⟨174921000900020265431231659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233228001200027020574975545 174921000900020265431231659)
          ·
            refine ⟨262381501350030398146847489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174921000900020265431231659 262381501350030398146847489)
            ·
              refine ⟨196786126012522798610135617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262381501350030398146847489 196786126012522798610135617)
              ·
                refine ⟨147589594509392098957601713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196786126012522798610135617 147589594509392098957601713)
                ·
                  refine ⟨110692195882044074218201285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147589594509392098957601713 110692195882044074218201285)
                  ·
                    refine ⟨20754786727883263915912741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110692195882044074218201285 20754786727883263915912741)
                    ·
                      refine ⟨3891522511478111984233639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20754786727883263915912741 3891522511478111984233639)
                      ·
                        rfl

theorem cell23_7578713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_7578713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578713 prefixEnd_7578713 := by exact prefixLift 7578713
  have htrace : WordTrace (prefixWord ++ tailWord_7578713) baseStart_7578713 baseEnd_7578713 := by
    simpa [prefixWord, tailWord_7578713, baseEnd_7578713] using wordTrace_append hprefix tailTrace_7578713
  have hstable : (prefixWord ++ tailWord_7578713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578713).length < 2 ^ (prefixWord ++ tailWord_7578713).sum := by decide
  have hdescent : baseEnd_7578713 < baseStart_7578713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578720 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_7578720 : Nat := 118140960795 + 7578720 * 2 ^ 59
def prefixEnd_7578720 : Nat := 4983230072969 + 3 ^ 40 * 7578720 * 2
def baseEnd_7578720 : Nat := 3891526105842693456846107

theorem tailTrace_7578720 : CollatzResearch.WordTrace tailWord_7578720 prefixEnd_7578720 3891526105842693456846107 := by
  unfold tailWord_7578720
  simp only [CollatzResearch.WordTrace]
  refine ⟨138209313551799628586626807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184279084735732838115502409 138209313551799628586626807)
  ·
    refine ⟨207313970327699442879940211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138209313551799628586626807 207313970327699442879940211)
    ·
      refine ⟨310970955491549164319910317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207313970327699442879940211 310970955491549164319910317)
      ·
        refine ⟨116614108309330936619966369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310970955491549164319910317 116614108309330936619966369)
        ·
          refine ⟨87460581231998202464974777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116614108309330936619966369 87460581231998202464974777)
          ·
            refine ⟨65595435923998651848731083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87460581231998202464974777 65595435923998651848731083)
            ·
              refine ⟨98393153885997977773096625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65595435923998651848731083 98393153885997977773096625)
              ·
                refine ⟨73794865414498483329822469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98393153885997977773096625 73794865414498483329822469)
                ·
                  refine ⟨13836537265218465624341713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73794865414498483329822469 13836537265218465624341713)
                  ·
                    refine ⟨10377402948913849218256285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13836537265218465624341713 10377402948913849218256285)
                    ·
                      refine ⟨3891526105842693456846107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10377402948913849218256285 3891526105842693456846107)
                      ·
                        rfl

theorem cell23_7578720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_7578720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578720 prefixEnd_7578720 := by exact prefixLift 7578720
  have htrace : WordTrace (prefixWord ++ tailWord_7578720) baseStart_7578720 baseEnd_7578720 := by
    simpa [prefixWord, tailWord_7578720, baseEnd_7578720] using wordTrace_append hprefix tailTrace_7578720
  have hstable : (prefixWord ++ tailWord_7578720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578720).length < 2 ^ (prefixWord ++ tailWord_7578720).sum := by decide
  have hdescent : baseEnd_7578720 < baseStart_7578720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578757 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 6]
def baseStart_7578757 : Nat := 118140960795 + 7578757 * 2 ^ 59
def prefixEnd_7578757 : Nat := 4983230072969 + 3 ^ 40 * 7578757 * 2
def baseEnd_7578757 : Nat := 432393900514101090231493

theorem tailTrace_7578757 : CollatzResearch.WordTrace tailWord_7578757 prefixEnd_7578757 432393900514101090231493 := by
  unfold tailWord_7578757
  simp only [CollatzResearch.WordTrace]
  refine ⟨276419976604465212492350525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184279984402976808328233683 276419976604465212492350525)
  ·
    refine ⟨103657491226674454684631447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276419976604465212492350525 103657491226674454684631447)
    ·
      refine ⟨155486236840011682026947171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103657491226674454684631447 155486236840011682026947171)
      ·
        refine ⟨233229355260017523040420757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155486236840011682026947171 233229355260017523040420757)
        ·
          refine ⟨10932626027813321392519723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233229355260017523040420757 10932626027813321392519723)
          ·
            refine ⟨16398939041719982088779585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10932626027813321392519723 16398939041719982088779585)
            ·
              refine ⟨12299204281289986566584689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16398939041719982088779585 12299204281289986566584689)
              ·
                refine ⟨9224403210967489924938517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12299204281289986566584689 9224403210967489924938517)
                ·
                  refine ⟨432393900514101090231493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9224403210967489924938517 432393900514101090231493)
                  ·
                    rfl

theorem cell23_7578757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_7578757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578757 prefixEnd_7578757 := by exact prefixLift 7578757
  have htrace : WordTrace (prefixWord ++ tailWord_7578757) baseStart_7578757 baseEnd_7578757 := by
    simpa [prefixWord, tailWord_7578757, baseEnd_7578757] using wordTrace_append hprefix tailTrace_7578757
  have hstable : (prefixWord ++ tailWord_7578757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578757).length < 2 ^ (prefixWord ++ tailWord_7578757).sum := by decide
  have hdescent : baseEnd_7578757 < baseStart_7578757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578761 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 1, 4]
def baseStart_7578761 : Nat := 118140960795 + 7578761 * 2 ^ 59
def prefixEnd_7578761 : Nat := 4983230072969 + 3 ^ 40 * 7578761 * 2
def baseEnd_7578761 : Nat := 1297182386183175932144473

theorem tailTrace_7578761 : CollatzResearch.WordTrace tailWord_7578761 prefixEnd_7578761 1297182386183175932144473 := by
  unfold tailWord_7578761
  simp only [CollatzResearch.WordTrace]
  refine ⟨276420122496450721175496137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184280081664300480783664091 276420122496450721175496137)
  ·
    refine ⟨207315091872338040881622103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276420122496450721175496137 207315091872338040881622103)
    ·
      refine ⟨310972637808507061322433155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207315091872338040881622103 310972637808507061322433155)
      ·
        refine ⟨466458956712760591983649733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310972637808507061322433155 466458956712760591983649733)
        ·
          refine ⟨87461054383642610996934325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466458956712760591983649733 87461054383642610996934325)
          ·
            refine ⟨8199473848466494780962593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87461054383642610996934325 8199473848466494780962593)
            ·
              refine ⟨6149605386349871085721945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8199473848466494780962593 6149605386349871085721945)
              ·
                refine ⟨4612204039762403314291459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149605386349871085721945 4612204039762403314291459)
                ·
                  refine ⟨6918306059643604971437189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612204039762403314291459 6918306059643604971437189)
                  ·
                    refine ⟨1297182386183175932144473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918306059643604971437189 1297182386183175932144473)
                    ·
                      rfl

theorem cell23_7578761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 4].length) (baseStart_7578761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578761 prefixEnd_7578761 := by exact prefixLift 7578761
  have htrace : WordTrace (prefixWord ++ tailWord_7578761) baseStart_7578761 baseEnd_7578761 := by
    simpa [prefixWord, tailWord_7578761, baseEnd_7578761] using wordTrace_append hprefix tailTrace_7578761
  have hstable : (prefixWord ++ tailWord_7578761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578761).length < 2 ^ (prefixWord ++ tailWord_7578761).sum := by decide
  have hdescent : baseEnd_7578761 < baseStart_7578761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578763 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_7578763 : Nat := 118140960795 + 7578763 * 2 ^ 59
def prefixEnd_7578763 : Nat := 4983230072969 + 3 ^ 40 * 7578763 * 2
def baseEnd_7578763 : Nat := 3891548185510836788608409

theorem tailTrace_7578763 : CollatzResearch.WordTrace tailWord_7578763 prefixEnd_7578763 3891548185510836788608409 := by
  unfold tailWord_7578763
  simp only [CollatzResearch.WordTrace]
  refine ⟨276420195442443475517068943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184280130294962317011379295 276420195442443475517068943)
  ·
    refine ⟨414630293163665213275603415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276420195442443475517068943 414630293163665213275603415)
    ·
      refine ⟨621945439745497819913405123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414630293163665213275603415 621945439745497819913405123)
      ·
        refine ⟨932918159618246729870107685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621945439745497819913405123 932918159618246729870107685)
        ·
          refine ⟨174922154928421261850645191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 932918159618246729870107685 174922154928421261850645191)
          ·
            refine ⟨262383232392631892775967787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174922154928421261850645191 262383232392631892775967787)
            ·
              refine ⟨393574848588947839163951681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262383232392631892775967787 393574848588947839163951681)
              ·
                refine ⟨295181136441710879372963761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393574848588947839163951681 295181136441710879372963761)
                ·
                  refine ⟨221385852331283159529722821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295181136441710879372963761 221385852331283159529722821)
                  ·
                    refine ⟨41509847312115592411823029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221385852331283159529722821 41509847312115592411823029)
                    ·
                      refine ⟨3891548185510836788608409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41509847312115592411823029 3891548185510836788608409)
                      ·
                        rfl

theorem cell23_7578763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_7578763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578763 prefixEnd_7578763 := by exact prefixLift 7578763
  have htrace : WordTrace (prefixWord ++ tailWord_7578763) baseStart_7578763 baseEnd_7578763 := by
    simpa [prefixWord, tailWord_7578763, baseEnd_7578763] using wordTrace_append hprefix tailTrace_7578763
  have hstable : (prefixWord ++ tailWord_7578763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578763).length < 2 ^ (prefixWord ++ tailWord_7578763).sum := by decide
  have hdescent : baseEnd_7578763 < baseStart_7578763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578800 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 6, 4]
def baseStart_7578800 : Nat := 118140960795 + 7578800 * 2 ^ 59
def prefixEnd_7578800 : Nat := 4983230072969 + 3 ^ 40 * 7578800 * 2
def baseEnd_7578800 : Nat := 1297189061431684381281913

theorem tailTrace_7578800 : CollatzResearch.WordTrace tailWord_7578800 prefixEnd_7578800 1297189061431684381281913 := by
  unfold tailWord_7578800
  simp only [CollatzResearch.WordTrace]
  refine ⟨138210772471654715418082927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184281029962206287224110569 138210772471654715418082927)
  ·
    refine ⟨207316158707482073127124391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138210772471654715418082927 207316158707482073127124391)
    ·
      refine ⟨310974238061223109690686587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207316158707482073127124391 310974238061223109690686587)
      ·
        refine ⟨466461357091834664536029881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310974238061223109690686587 466461357091834664536029881)
        ·
          refine ⟨349846017818875998402022411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466461357091834664536029881 349846017818875998402022411)
          ·
            refine ⟨524769026728313997603033617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349846017818875998402022411 524769026728313997603033617)
            ·
              refine ⟨393576770046235498202275213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524769026728313997603033617 393576770046235498202275213)
              ·
                refine ⟨147591288767338311825853205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393576770046235498202275213 147591288767338311825853205)
                ·
                  refine ⟨6918341660968983366836869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147591288767338311825853205 6918341660968983366836869)
                  ·
                    refine ⟨1297189061431684381281913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918341660968983366836869 1297189061431684381281913)
                    ·
                      rfl

theorem cell23_7578800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_7578800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578800 prefixEnd_7578800 := by exact prefixLift 7578800
  have htrace : WordTrace (prefixWord ++ tailWord_7578800) baseStart_7578800 baseEnd_7578800 := by
    simpa [prefixWord, tailWord_7578800, baseEnd_7578800] using wordTrace_append hprefix tailTrace_7578800
  have hstable : (prefixWord ++ tailWord_7578800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578800).length < 2 ^ (prefixWord ++ tailWord_7578800).sum := by decide
  have hdescent : baseEnd_7578800 < baseStart_7578800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578801 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7578801 : Nat := 118140960795 + 7578801 * 2 ^ 59
def prefixEnd_7578801 : Nat := 4983230072969 + 3 ^ 40 * 7578801 * 2
def baseEnd_7578801 : Nat := 3891567697775707639933235

theorem tailTrace_7578801 : CollatzResearch.WordTrace tailWord_7578801 prefixEnd_7578801 3891567697775707639933235 := by
  unfold tailWord_7578801
  simp only [CollatzResearch.WordTrace]
  refine ⟨276421581416305808006952257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184281054277537205337968171 276421581416305808006952257)
  ·
    refine ⟨207316186062229356005214193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276421581416305808006952257 207316186062229356005214193)
    ·
      refine ⟨155487139546672017003910645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207316186062229356005214193 155487139546672017003910645)
      ·
        refine ⟨14576919332500501594116623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155487139546672017003910645 14576919332500501594116623)
        ·
          refine ⟨21865378998750752391174935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14576919332500501594116623 21865378998750752391174935)
          ·
            refine ⟨32798068498126128586762403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21865378998750752391174935 32798068498126128586762403)
            ·
              refine ⟨49197102747189192880143605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32798068498126128586762403 49197102747189192880143605)
              ·
                refine ⟨4612228382548986832513463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49197102747189192880143605 4612228382548986832513463)
                ·
                  refine ⟨6918342573823480248770195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612228382548986832513463 6918342573823480248770195)
                  ·
                    refine ⟨10377513860735220373155293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6918342573823480248770195 10377513860735220373155293)
                    ·
                      refine ⟨3891567697775707639933235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10377513860735220373155293 3891567697775707639933235)
                      ·
                        rfl

theorem cell23_7578801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7578801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578801 prefixEnd_7578801 := by exact prefixLift 7578801
  have htrace : WordTrace (prefixWord ++ tailWord_7578801) baseStart_7578801 baseEnd_7578801 := by
    simpa [prefixWord, tailWord_7578801, baseEnd_7578801] using wordTrace_append hprefix tailTrace_7578801
  have hstable : (prefixWord ++ tailWord_7578801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578801).length < 2 ^ (prefixWord ++ tailWord_7578801).sum := by decide
  have hdescent : baseEnd_7578801 < baseStart_7578801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578807 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_7578807 : Nat := 118140960795 + 7578807 * 2 ^ 59
def prefixEnd_7578807 : Nat := 4983230072969 + 3 ^ 40 * 7578807 * 2
def baseEnd_7578807 : Nat := 3891570778659634616458207

theorem tailTrace_7578807 : CollatzResearch.WordTrace tailWord_7578807 prefixEnd_7578807 3891570778659634616458207 := by
  unfold tailWord_7578807
  simp only [CollatzResearch.WordTrace]
  refine ⟨276421800254284071031670675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184281200169522714021113783 276421800254284071031670675)
  ·
    refine ⟨414632700381426106547506013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276421800254284071031670675 414632700381426106547506013)
    ·
      refine ⟨155487262643034789955314755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414632700381426106547506013 155487262643034789955314755)
      ·
        refine ⟨233230893964552184932972133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155487262643034789955314755 233230893964552184932972133)
        ·
          refine ⟨43730792618353534674932275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233230893964552184932972133 43730792618353534674932275)
          ·
            refine ⟨65596188927530302012398413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43730792618353534674932275 65596188927530302012398413)
            ·
              refine ⟨24598570847823863254649405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65596188927530302012398413 24598570847823863254649405)
              ·
                refine ⟨9224464067933948720493527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24598570847823863254649405 9224464067933948720493527)
                ·
                  refine ⟨13836696101900923080740291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9224464067933948720493527 13836696101900923080740291)
                  ·
                    refine ⟨20755044152851384621110437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13836696101900923080740291 20755044152851384621110437)
                    ·
                      refine ⟨3891570778659634616458207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20755044152851384621110437 3891570778659634616458207)
                      ·
                        rfl

theorem cell23_7578807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_7578807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578807 prefixEnd_7578807 := by exact prefixLift 7578807
  have htrace : WordTrace (prefixWord ++ tailWord_7578807) baseStart_7578807 baseEnd_7578807 := by
    simpa [prefixWord, tailWord_7578807, baseEnd_7578807] using wordTrace_append hprefix tailTrace_7578807
  have hstable : (prefixWord ++ tailWord_7578807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578807).length < 2 ^ (prefixWord ++ tailWord_7578807).sum := by decide
  have hdescent : baseEnd_7578807 < baseStart_7578807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578810 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_7578810 : Nat := 118140960795 + 7578810 * 2 ^ 59
def prefixEnd_7578810 : Nat := 4983230072969 + 3 ^ 40 * 7578810 * 2
def baseEnd_7578810 : Nat := 3891572319101598104720693

theorem tailTrace_7578810 : CollatzResearch.WordTrace tailWord_7578810 prefixEnd_7578810 3891572319101598104720693 := by
  unfold tailWord_7578810
  simp only [CollatzResearch.WordTrace]
  refine ⟨69105477418318300636007471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184281273115515468362686589 69105477418318300636007471)
  ·
    refine ⟨103658216127477450954011207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69105477418318300636007471 103658216127477450954011207)
    ·
      refine ⟨155487324191216176431016811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103658216127477450954011207 155487324191216176431016811)
      ·
        refine ⟨233230986286824264646525217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155487324191216176431016811 233230986286824264646525217)
        ·
          refine ⟨174923239715118198484893913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233230986286824264646525217 174923239715118198484893913)
          ·
            refine ⟨131192429786338648863670435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174923239715118198484893913 131192429786338648863670435)
            ·
              refine ⟨196788644679507973295505653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131192429786338648863670435 196788644679507973295505653)
              ·
                refine ⟨18448935438703872496453655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196788644679507973295505653 18448935438703872496453655)
                ·
                  refine ⟨27673403158055808744680483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18448935438703872496453655 27673403158055808744680483)
                  ·
                    refine ⟨41510104737083713117020725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27673403158055808744680483 41510104737083713117020725)
                    ·
                      refine ⟨3891572319101598104720693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41510104737083713117020725 3891572319101598104720693)
                      ·
                        rfl

theorem cell23_7578810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_7578810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578810 prefixEnd_7578810 := by exact prefixLift 7578810
  have htrace : WordTrace (prefixWord ++ tailWord_7578810) baseStart_7578810 baseEnd_7578810 := by
    simpa [prefixWord, tailWord_7578810, baseEnd_7578810] using wordTrace_append hprefix tailTrace_7578810
  have hstable : (prefixWord ++ tailWord_7578810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578810).length < 2 ^ (prefixWord ++ tailWord_7578810).sum := by decide
  have hdescent : baseEnd_7578810 < baseStart_7578810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578824 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_7578824 : Nat := 118140960795 + 7578824 * 2 ^ 59
def prefixEnd_7578824 : Nat := 4983230072969 + 3 ^ 40 * 7578824 * 2
def baseEnd_7578824 : Nat := 3891579507830761049945629

theorem tailTrace_7578824 : CollatzResearch.WordTrace tailWord_7578824 prefixEnd_7578824 3891579507830761049945629 := by
  unfold tailWord_7578824
  simp only [CollatzResearch.WordTrace]
  refine ⟨138211210147611241467519763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184281613530148321956693017 138211210147611241467519763)
  ·
    refine ⟨207316815221416862201279645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138211210147611241467519763 207316815221416862201279645)
    ·
      refine ⟨77743805708031323325479867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207316815221416862201279645 77743805708031323325479867)
      ·
        refine ⟨116615708562046984988219801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77743805708031323325479867 116615708562046984988219801)
        ·
          refine ⟨87461781421535238741164851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116615708562046984988219801 87461781421535238741164851)
          ·
            refine ⟨131192672132302858111747277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87461781421535238741164851 131192672132302858111747277)
            ·
              refine ⟨49197252049613571791905229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131192672132302858111747277 49197252049613571791905229)
              ·
                refine ⟨18448969518605089421964461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49197252049613571791905229 18448969518605089421964461)
                ·
                  refine ⟨6918363569476908533236673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18448969518605089421964461 6918363569476908533236673)
                  ·
                    refine ⟨5188772677107681399927505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918363569476908533236673 5188772677107681399927505)
                    ·
                      refine ⟨3891579507830761049945629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188772677107681399927505 3891579507830761049945629)
                      ·
                        rfl

theorem cell23_7578824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_7578824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578824 prefixEnd_7578824 := by exact prefixLift 7578824
  have htrace : WordTrace (prefixWord ++ tailWord_7578824) baseStart_7578824 baseEnd_7578824 := by
    simpa [prefixWord, tailWord_7578824, baseEnd_7578824] using wordTrace_append hprefix tailTrace_7578824
  have hstable : (prefixWord ++ tailWord_7578824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578824).length < 2 ^ (prefixWord ++ tailWord_7578824).sum := by decide
  have hdescent : baseEnd_7578824 < baseStart_7578824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578837 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7578837 : Nat := 118140960795 + 7578837 * 2 ^ 59
def prefixEnd_7578837 : Nat := 4983230072969 + 3 ^ 40 * 7578837 * 2
def baseEnd_7578837 : Nat := 3891586183079269499083069

theorem tailTrace_7578837 : CollatzResearch.WordTrace tailWord_7578837 prefixEnd_7578837 3891586183079269499083069 := by
  unfold tailWord_7578837
  simp only [CollatzResearch.WordTrace]
  refine ⟨276422894444175386155262765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184281929629450257436841843 276422894444175386155262765)
  ·
    refine ⟨103658585416565769808223537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276422894444175386155262765 103658585416565769808223537)
    ·
      refine ⟨77743939062424327356167653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103658585416565769808223537 77743939062424327356167653)
      ·
        refine ⟨14576988574204561379281435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77743939062424327356167653 14576988574204561379281435)
        ·
          refine ⟨21865482861306842068922153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14576988574204561379281435 21865482861306842068922153)
          ·
            refine ⟨16399112145980131551691615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21865482861306842068922153 16399112145980131551691615)
            ·
              refine ⟨24598668218970197327537423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399112145980131551691615 24598668218970197327537423)
              ·
                refine ⟨36898002328455295991306135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24598668218970197327537423 36898002328455295991306135)
                ·
                  refine ⟨55347003492682943986959203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36898002328455295991306135 55347003492682943986959203)
                  ·
                    refine ⟨83020505239024415980438805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55347003492682943986959203 83020505239024415980438805)
                    ·
                      refine ⟨3891586183079269499083069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83020505239024415980438805 3891586183079269499083069)
                      ·
                        rfl

theorem cell23_7578837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7578837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578837 prefixEnd_7578837 := by exact prefixLift 7578837
  have htrace : WordTrace (prefixWord ++ tailWord_7578837) baseStart_7578837 baseEnd_7578837 := by
    simpa [prefixWord, tailWord_7578837, baseEnd_7578837] using wordTrace_append hprefix tailTrace_7578837
  have hstable : (prefixWord ++ tailWord_7578837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578837).length < 2 ^ (prefixWord ++ tailWord_7578837).sum := by decide
  have hdescent : baseEnd_7578837 < baseStart_7578837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578858 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_7578858 : Nat := 118140960795 + 7578858 * 2 ^ 59
def prefixEnd_7578858 : Nat := 4983230072969 + 3 ^ 40 * 7578858 * 2
def baseEnd_7578858 : Nat := 3891596966173013916920473

theorem tailTrace_7578858 : CollatzResearch.WordTrace tailWord_7578858 prefixEnd_7578858 3891596966173013916920473 := by
  unfold tailWord_7578858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69105915094274826685444307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184282440251399537827851485 69105915094274826685444307)
  ·
    refine ⟨103658872641412240028166461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69105915094274826685444307 103658872641412240028166461)
    ·
      refine ⟨38872077240529590010562423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103658872641412240028166461 38872077240529590010562423)
      ·
        refine ⟨58308115860794385015843635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38872077240529590010562423 58308115860794385015843635)
        ·
          refine ⟨87462173791191577523765453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58308115860794385015843635 87462173791191577523765453)
          ·
            refine ⟨32798315171696841571412045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87462173791191577523765453 32798315171696841571412045)
            ·
              refine ⟨12299368189386315589279517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32798315171696841571412045 12299368189386315589279517)
              ·
                refine ⟨4612263071019868345979819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12299368189386315589279517 4612263071019868345979819)
                ·
                  refine ⟨6918394606529802518969729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612263071019868345979819 6918394606529802518969729)
                  ·
                    refine ⟨5188795954897351889227297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918394606529802518969729 5188795954897351889227297)
                    ·
                      refine ⟨3891596966173013916920473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188795954897351889227297 3891596966173013916920473)
                      ·
                        rfl

theorem cell23_7578858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_7578858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578858 prefixEnd_7578858 := by exact prefixLift 7578858
  have htrace : WordTrace (prefixWord ++ tailWord_7578858) baseStart_7578858 baseEnd_7578858 := by
    simpa [prefixWord, tailWord_7578858, baseEnd_7578858] using wordTrace_append hprefix tailTrace_7578858
  have hstable : (prefixWord ++ tailWord_7578858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578858).length < 2 ^ (prefixWord ++ tailWord_7578858).sum := by decide
  have hdescent : baseEnd_7578858 < baseStart_7578858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578874 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_7578874 : Nat := 118140960795 + 7578874 * 2 ^ 59
def prefixEnd_7578874 : Nat := 4983230072969 + 3 ^ 40 * 7578874 * 2
def baseEnd_7578874 : Nat := 3891605181863485854320399

theorem tailTrace_7578874 : CollatzResearch.WordTrace tailWord_7578874 prefixEnd_7578874 3891605181863485854320399 := by
  unfold tailWord_7578874
  simp only [CollatzResearch.WordTrace]
  refine ⟨69106060986260335368589919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184282829296694227649573117 69106060986260335368589919)
  ·
    refine ⟨103659091479390503052884879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69106060986260335368589919 103659091479390503052884879)
    ·
      refine ⟨155488637219085754579327319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103659091479390503052884879 155488637219085754579327319)
      ·
        refine ⟨233232955828628631868990979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155488637219085754579327319 233232955828628631868990979)
        ·
          refine ⟨349849433742942947803486469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233232955828628631868990979 349849433742942947803486469)
          ·
            refine ⟨65596768826801802713153713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349849433742942947803486469 65596768826801802713153713)
            ·
              refine ⟨49197576620101352034865285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65596768826801802713153713 49197576620101352034865285)
              ·
                refine ⟨9224545616269003506537241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49197576620101352034865285 9224545616269003506537241)
                ·
                  refine ⟨6918409212201752629902931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224545616269003506537241 6918409212201752629902931)
                  ·
                    refine ⟨10377613818302628944854397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6918409212201752629902931 10377613818302628944854397)
                    ·
                      refine ⟨3891605181863485854320399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10377613818302628944854397 3891605181863485854320399)
                      ·
                        rfl

theorem cell23_7578874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_7578874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578874 prefixEnd_7578874 := by exact prefixLift 7578874
  have htrace : WordTrace (prefixWord ++ tailWord_7578874) baseStart_7578874 baseEnd_7578874 := by
    simpa [prefixWord, tailWord_7578874, baseEnd_7578874] using wordTrace_append hprefix tailTrace_7578874
  have hstable : (prefixWord ++ tailWord_7578874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578874).length < 2 ^ (prefixWord ++ tailWord_7578874).sum := by decide
  have hdescent : baseEnd_7578874 < baseStart_7578874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578880 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_7578880 : Nat := 118140960795 + 7578880 * 2 ^ 59
def prefixEnd_7578880 : Nat := 4983230072969 + 3 ^ 40 * 7578880 * 2
def baseEnd_7578880 : Nat := 3891608262747412830845371

theorem tailTrace_7578880 : CollatzResearch.WordTrace tailWord_7578880 prefixEnd_7578880 3891608262747412830845371 := by
  unfold tailWord_7578880
  simp only [CollatzResearch.WordTrace]
  refine ⟨138212231391509802249539047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184282975188679736332718729 138212231391509802249539047)
  ·
    refine ⟨207318347087264703374308571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138212231391509802249539047 207318347087264703374308571)
    ·
      refine ⟨310977520630897055061462857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207318347087264703374308571 310977520630897055061462857)
      ·
        refine ⟨233233140473172791296097143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310977520630897055061462857 233233140473172791296097143)
        ·
          refine ⟨349849710709759186944145715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233233140473172791296097143 349849710709759186944145715)
          ·
            refine ⟨524774566064638780416218573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349849710709759186944145715 524774566064638780416218573)
            ·
              refine ⟨196790462274239542656081965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524774566064638780416218573 196790462274239542656081965)
              ·
                refine ⟨73796423352839828496030737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196790462274239542656081965 73796423352839828496030737)
                ·
                  refine ⟨55347317514629871372023053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73796423352839828496030737 55347317514629871372023053)
                  ·
                    refine ⟨20755244067986201764508645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55347317514629871372023053 20755244067986201764508645)
                    ·
                      refine ⟨3891608262747412830845371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20755244067986201764508645 3891608262747412830845371)
                      ·
                        rfl

theorem cell23_7578880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_7578880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578880 prefixEnd_7578880 := by exact prefixLift 7578880
  have htrace : WordTrace (prefixWord ++ tailWord_7578880) baseStart_7578880 baseEnd_7578880 := by
    simpa [prefixWord, tailWord_7578880, baseEnd_7578880] using wordTrace_append hprefix tailTrace_7578880
  have hstable : (prefixWord ++ tailWord_7578880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578880).length < 2 ^ (prefixWord ++ tailWord_7578880).sum := by decide
  have hdescent : baseEnd_7578880 < baseStart_7578880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578890 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_7578890 : Nat := 118140960795 + 7578890 * 2 ^ 59
def prefixEnd_7578890 : Nat := 4983230072969 + 3 ^ 40 * 7578890 * 2
def baseEnd_7578890 : Nat := 1297204465851319263906775

theorem tailTrace_7578890 : CollatzResearch.WordTrace tailWord_7578890 prefixEnd_7578890 1297204465851319263906775 := by
  unfold tailWord_7578890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69106206878245844051735531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184283218341988917471294749 69106206878245844051735531)
  ·
    refine ⟨103659310317368766077603297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69106206878245844051735531 103659310317368766077603297)
    ·
      refine ⟨77744482738026574558202473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103659310317368766077603297 77744482738026574558202473)
      ·
        refine ⟨58308362053519930918651855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77744482738026574558202473 58308362053519930918651855)
        ·
          refine ⟨87462543080279896377977783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58308362053519930918651855 87462543080279896377977783)
          ·
            refine ⟨131193814620419844566966675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87462543080279896377977783 131193814620419844566966675)
            ·
              refine ⟨196790721930629766850450013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131193814620419844566966675 196790721930629766850450013)
              ·
                refine ⟨73796520723986162568918755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196790721930629766850450013 73796520723986162568918755)
                ·
                  refine ⟨110694781085979243853378133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73796520723986162568918755 110694781085979243853378133)
                  ·
                    refine ⟨1297204465851319263906775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110694781085979243853378133 1297204465851319263906775)
                    ·
                      rfl

theorem cell23_7578890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_7578890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578890 prefixEnd_7578890 := by exact prefixLift 7578890
  have htrace : WordTrace (prefixWord ++ tailWord_7578890) baseStart_7578890 baseEnd_7578890 := by
    simpa [prefixWord, tailWord_7578890, baseEnd_7578890] using wordTrace_append hprefix tailTrace_7578890
  have hstable : (prefixWord ++ tailWord_7578890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578890).length < 2 ^ (prefixWord ++ tailWord_7578890).sum := by decide
  have hdescent : baseEnd_7578890 < baseStart_7578890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578891 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 2, 1, 3]
def baseStart_7578891 : Nat := 118140960795 + 7578891 * 2 ^ 59
def prefixEnd_7578891 : Nat := 4983230072969 + 3 ^ 40 * 7578891 * 2
def baseEnd_7578891 : Nat := 3891613911034612287807821

theorem tailTrace_7578891 : CollatzResearch.WordTrace tailWord_7578891 prefixEnd_7578891 3891613911034612287807821 := by
  unfold tailWord_7578891
  simp only [CollatzResearch.WordTrace]
  refine ⟨276424863985979753377728527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184283242657319835585152351 276424863985979753377728527)
  ·
    refine ⟨414637295978969630066592791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276424863985979753377728527 414637295978969630066592791)
    ·
      refine ⟨621955943968454445099889187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414637295978969630066592791 621955943968454445099889187)
      ·
        refine ⟨932933915952681667649833781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621955943968454445099889187 932933915952681667649833781)
        ·
          refine ⟨87462554620563906342171917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 932933915952681667649833781 87462554620563906342171917)
          ·
            refine ⟨32798457982711464878314469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87462554620563906342171917 32798457982711464878314469)
            ·
              refine ⟨6149710871758399664683963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32798457982711464878314469 6149710871758399664683963)
              ·
                refine ⟨9224566307637599497025945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149710871758399664683963 9224566307637599497025945)
                ·
                  refine ⟨6918424730728199622769459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224566307637599497025945 6918424730728199622769459)
                  ·
                    refine ⟨10377637096092299434154189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6918424730728199622769459 10377637096092299434154189)
                    ·
                      refine ⟨3891613911034612287807821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10377637096092299434154189 3891613911034612287807821)
                      ·
                        rfl

theorem cell23_7578891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 1, 3].length) (baseStart_7578891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578891 prefixEnd_7578891 := by exact prefixLift 7578891
  have htrace : WordTrace (prefixWord ++ tailWord_7578891) baseStart_7578891 baseEnd_7578891 := by
    simpa [prefixWord, tailWord_7578891, baseEnd_7578891] using wordTrace_append hprefix tailTrace_7578891
  have hstable : (prefixWord ++ tailWord_7578891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578891).length < 2 ^ (prefixWord ++ tailWord_7578891).sum := by decide
  have hdescent : baseEnd_7578891 < baseStart_7578891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578917 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_7578917 : Nat := 118140960795 + 7578917 * 2 ^ 59
def prefixEnd_7578917 : Nat := 4983230072969 + 3 ^ 40 * 7578917 * 2
def baseEnd_7578917 : Nat := 3891627261531629186082701

theorem tailTrace_7578917 : CollatzResearch.WordTrace tailWord_7578917 prefixEnd_7578917 3891627261531629186082701 := by
  unfold tailWord_7578917
  simp only [CollatzResearch.WordTrace]
  refine ⟨276425812283885559818175005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184283874855923706545450003 276425812283885559818175005)
  ·
    refine ⟨103659679606457084931815627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276425812283885559818175005 103659679606457084931815627)
    ·
      refine ⟨155489519409685627397723441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103659679606457084931815627 155489519409685627397723441)
      ·
        refine ⟨116617139557264220548292581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155489519409685627397723441 116617139557264220548292581)
        ·
          refine ⟨21865713666987041352804859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116617139557264220548292581 21865713666987041352804859)
          ·
            refine ⟨32798570500480562029207289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21865713666987041352804859 32798570500480562029207289)
            ·
              refine ⟨24598927875360421521905467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32798570500480562029207289 24598927875360421521905467)
              ·
                refine ⟨36898391813040632282858201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24598927875360421521905467 36898391813040632282858201)
                ·
                  refine ⟨27673793859780474212143651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36898391813040632282858201 27673793859780474212143651)
                  ·
                    refine ⟨41510690789670711318215477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27673793859780474212143651 41510690789670711318215477)
                    ·
                      refine ⟨3891627261531629186082701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41510690789670711318215477 3891627261531629186082701)
                      ·
                        rfl

theorem cell23_7578917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_7578917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578917 prefixEnd_7578917 := by exact prefixLift 7578917
  have htrace : WordTrace (prefixWord ++ tailWord_7578917) baseStart_7578917 baseEnd_7578917 := by
    simpa [prefixWord, tailWord_7578917, baseEnd_7578917] using wordTrace_append hprefix tailTrace_7578917
  have hstable : (prefixWord ++ tailWord_7578917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578917).length < 2 ^ (prefixWord ++ tailWord_7578917).sum := by decide
  have hdescent : baseEnd_7578917 < baseStart_7578917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578931 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 2, 2, 2]
def baseStart_7578931 : Nat := 118140960795 + 7578931 * 2 ^ 59
def prefixEnd_7578931 : Nat := 4983230072969 + 3 ^ 40 * 7578931 * 2
def baseEnd_7578931 : Nat := 3891634450260792131307637

theorem tailTrace_7578931 : CollatzResearch.WordTrace tailWord_7578931 prefixEnd_7578931 3891634450260792131307637 := by
  unfold tailWord_7578931
  simp only [CollatzResearch.WordTrace]
  refine ⟨276426322905834840209184647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184284215270556560139456431 276426322905834840209184647)
  ·
    refine ⟨414639484358752260313776971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276426322905834840209184647 414639484358752260313776971)
    ·
      refine ⟨621959226538128390470665457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414639484358752260313776971 621959226538128390470665457)
      ·
        refine ⟨466469419903596292852999093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621959226538128390470665457 466469419903596292852999093)
        ·
          refine ⟨43731508115962152454968665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 466469419903596292852999093 43731508115962152454968665)
          ·
            refine ⟨32798631086971614341226499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43731508115962152454968665 32798631086971614341226499)
            ·
              refine ⟨49197946630457421511839749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32798631086971614341226499 49197946630457421511839749)
              ·
                refine ⟨9224614993210766533469953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49197946630457421511839749 9224614993210766533469953)
                ·
                  refine ⟨6918461244908074900102465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224614993210766533469953 6918461244908074900102465)
                  ·
                    refine ⟨5188845933681056175076849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918461244908074900102465 5188845933681056175076849)
                    ·
                      refine ⟨3891634450260792131307637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188845933681056175076849 3891634450260792131307637)
                      ·
                        rfl

theorem cell23_7578931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 2, 2].length) (baseStart_7578931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578931 prefixEnd_7578931 := by exact prefixLift 7578931
  have htrace : WordTrace (prefixWord ++ tailWord_7578931) baseStart_7578931 baseEnd_7578931 := by
    simpa [prefixWord, tailWord_7578931, baseEnd_7578931] using wordTrace_append hprefix tailTrace_7578931
  have hstable : (prefixWord ++ tailWord_7578931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578931).length < 2 ^ (prefixWord ++ tailWord_7578931).sum := by decide
  have hdescent : baseEnd_7578931 < baseStart_7578931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578948 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7578948 : Nat := 118140960795 + 7578948 * 2 ^ 59
def prefixEnd_7578948 : Nat := 4983230072969 + 3 ^ 40 * 7578948 * 2
def baseEnd_7578948 : Nat := 3891643179431918564795059

theorem tailTrace_7578948 : CollatzResearch.WordTrace tailWord_7578948 prefixEnd_7578948 3891643179431918564795059 := by
  unfold tailWord_7578948
  simp only [CollatzResearch.WordTrace]
  refine ⟨138213471473386626056276749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184284628631182168075035665 138213471473386626056276749)
  ·
    refine ⟨51830051802519984771103781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138213471473386626056276749 51830051802519984771103781)
    ·
      refine ⟨9718134712972497144581959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51830051802519984771103781 9718134712972497144581959)
      ·
        refine ⟨14577202069458745716872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9718134712972497144581959 14577202069458745716872939)
        ·
          refine ⟨21865803104188118575309409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14577202069458745716872939 21865803104188118575309409)
          ·
            refine ⟨16399352328141088931482057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21865803104188118575309409 16399352328141088931482057)
            ·
              refine ⟨12299514246105816698611543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16399352328141088931482057 12299514246105816698611543)
              ·
                refine ⟨18449271369158725047917315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12299514246105816698611543 18449271369158725047917315)
                ·
                  refine ⟨27673907053738087571875973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18449271369158725047917315 27673907053738087571875973)
                  ·
                    refine ⟨5188857572575891419726745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27673907053738087571875973 5188857572575891419726745)
                    ·
                      refine ⟨3891643179431918564795059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188857572575891419726745 3891643179431918564795059)
                      ·
                        rfl

theorem cell23_7578948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7578948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578948 prefixEnd_7578948 := by exact prefixLift 7578948
  have htrace : WordTrace (prefixWord ++ tailWord_7578948) baseStart_7578948 baseEnd_7578948 := by
    simpa [prefixWord, tailWord_7578948, baseEnd_7578948] using wordTrace_append hprefix tailTrace_7578948
  have hstable : (prefixWord ++ tailWord_7578948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578948).length < 2 ^ (prefixWord ++ tailWord_7578948).sum := by decide
  have hdescent : baseEnd_7578948 < baseStart_7578948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7578967 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 1, 7]
def baseStart_7578967 : Nat := 118140960795 + 7578967 * 2 ^ 59
def prefixEnd_7578967 : Nat := 4983230072969 + 3 ^ 40 * 7578967 * 2
def baseEnd_7578967 : Nat := 1297217645188117996819157

theorem tailTrace_7578967 : CollatzResearch.WordTrace tailWord_7578967 prefixEnd_7578967 1297217645188117996819157 := by
  unfold tailWord_7578967
  simp only [CollatzResearch.WordTrace]
  refine ⟨276427635933704418357495155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184285090622469612238330103 276427635933704418357495155)
  ·
    refine ⟨414641453900556627536242733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276427635933704418357495155 414641453900556627536242733)
    ·
      refine ⟨155490545212708735326091025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414641453900556627536242733 155490545212708735326091025)
      ·
        refine ⟨116617908909531551494568269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155490545212708735326091025 116617908909531551494568269)
        ·
          refine ⟨43731715841074331810463101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116617908909531551494568269 43731715841074331810463101)
          ·
            refine ⟨16399393440402874428923663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43731715841074331810463101 16399393440402874428923663)
            ·
              refine ⟨24599090160604311643385495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399393440402874428923663 24599090160604311643385495)
              ·
                refine ⟨36898635240906467465078243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24599090160604311643385495 36898635240906467465078243)
                ·
                  refine ⟨55347952861359701197617365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36898635240906467465078243 55347952861359701197617365)
                  ·
                    refine ⟨1297217645188117996819157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55347952861359701197617365 1297217645188117996819157)
                    ·
                      rfl

theorem cell23_7578967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_7578967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7578967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7578967 prefixEnd_7578967 := by exact prefixLift 7578967
  have htrace : WordTrace (prefixWord ++ tailWord_7578967) baseStart_7578967 baseEnd_7578967 := by
    simpa [prefixWord, tailWord_7578967, baseEnd_7578967] using wordTrace_append hprefix tailTrace_7578967
  have hstable : (prefixWord ++ tailWord_7578967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7578967).length < 2 ^ (prefixWord ++ tailWord_7578967).sum := by decide
  have hdescent : baseEnd_7578967 < baseStart_7578967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7578967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579004 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_7579004 : Nat := 118140960795 + 7579004 * 2 ^ 59
def prefixEnd_7579004 : Nat := 4983230072969 + 3 ^ 40 * 7579004 * 2
def baseEnd_7579004 : Nat := 3891671934348570345694801

theorem tailTrace_7579004 : CollatzResearch.WordTrace tailWord_7579004 prefixEnd_7579004 3891671934348570345694801 := by
  unfold tailWord_7579004
  simp only [CollatzResearch.WordTrace]
  refine ⟨138214492717285186838296033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184285990289713582451061377 138214492717285186838296033)
  ·
    refine ⟨103660869537963890128722025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138214492717285186838296033 103660869537963890128722025)
    ·
      refine ⟨77745652153472917596541519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103660869537963890128722025 77745652153472917596541519)
      ·
        refine ⟨116618478230209376394812279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77745652153472917596541519 116618478230209376394812279)
        ·
          refine ⟨174927717345314064592218419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116618478230209376394812279 174927717345314064592218419)
          ·
            refine ⟨262391576017971096888327629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174927717345314064592218419 262391576017971096888327629)
            ·
              refine ⟨98396841006739161333122861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262391576017971096888327629 98396841006739161333122861)
              ·
                refine ⟨36898815377527185499921073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98396841006739161333122861 36898815377527185499921073)
                ·
                  refine ⟨27674111533145389124940805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36898815377527185499921073 27674111533145389124940805)
                  ·
                    refine ⟨5188895912464760460926401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27674111533145389124940805 5188895912464760460926401)
                    ·
                      refine ⟨3891671934348570345694801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188895912464760460926401 3891671934348570345694801)
                      ·
                        rfl

theorem cell23_7579004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_7579004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579004 prefixEnd_7579004 := by exact prefixLift 7579004
  have htrace : WordTrace (prefixWord ++ tailWord_7579004) baseStart_7579004 baseEnd_7579004 := by
    simpa [prefixWord, tailWord_7579004, baseEnd_7579004] using wordTrace_append hprefix tailTrace_7579004
  have hstable : (prefixWord ++ tailWord_7579004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579004).length < 2 ^ (prefixWord ++ tailWord_7579004).sum := by decide
  have hdescent : baseEnd_7579004 < baseStart_7579004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579038 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7579038 : Nat := 118140960795 + 7579038 * 2 ^ 59
def prefixEnd_7579038 : Nat := 4983230072969 + 3 ^ 40 * 7579038 * 2
def baseEnd_7579038 : Nat := 3891689392690823212669645

theorem tailTrace_7579038 : CollatzResearch.WordTrace tailWord_7579038 prefixEnd_7579038 3891689392690823212669645 := by
  unfold tailWord_7579038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553778189555899685416221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184286817010964798322219845 34553778189555899685416221)
  ·
    refine ⟨12957666821083462382031083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34553778189555899685416221 12957666821083462382031083)
    ·
      refine ⟨19436500231625193573046625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12957666821083462382031083 19436500231625193573046625)
      ·
        refine ⟨14577375173718895179784969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19436500231625193573046625 14577375173718895179784969)
        ·
          refine ⟨10933031380289171384838727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14577375173718895179784969 10933031380289171384838727)
          ·
            refine ⟨16399547070433757077258091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10933031380289171384838727 16399547070433757077258091)
            ·
              refine ⟨24599320605650635615887137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399547070433757077258091 24599320605650635615887137)
              ·
                refine ⟨18449490454237976711915353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24599320605650635615887137 18449490454237976711915353)
                ·
                  refine ⟨13837117840678482533936515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18449490454237976711915353 13837117840678482533936515)
                  ·
                    refine ⟨20755676761017723800904773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13837117840678482533936515 20755676761017723800904773)
                    ·
                      refine ⟨3891689392690823212669645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20755676761017723800904773 3891689392690823212669645)
                      ·
                        rfl

theorem cell23_7579038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7579038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579038 prefixEnd_7579038 := by exact prefixLift 7579038
  have htrace : WordTrace (prefixWord ++ tailWord_7579038) baseStart_7579038 baseEnd_7579038 := by
    simpa [prefixWord, tailWord_7579038, baseEnd_7579038] using wordTrace_append hprefix tailTrace_7579038
  have hstable : (prefixWord ++ tailWord_7579038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579038).length < 2 ^ (prefixWord ++ tailWord_7579038).sum := by decide
  have hdescent : baseEnd_7579038 < baseStart_7579038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579061 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 6]
def baseStart_7579061 : Nat := 118140960795 + 7579061 * 2 ^ 59
def prefixEnd_7579061 : Nat := 4983230072969 + 3 ^ 40 * 7579061 * 2
def baseEnd_7579061 : Nat := 432411244749541846964671

theorem tailTrace_7579061 : CollatzResearch.WordTrace tailWord_7579061 prefixEnd_7579061 432411244749541846964671 := by
  unfold tailWord_7579061
  simp only [CollatzResearch.WordTrace]
  refine ⟨276431064395363872411417037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184287376263575914940944691 276431064395363872411417037)
  ·
    refine ⟨103661649148261452154281389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276431064395363872411417037 103661649148261452154281389)
    ·
      refine ⟨38873118430598044557855521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103661649148261452154281389 38873118430598044557855521)
      ·
        refine ⟨29154838822948533418391641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38873118430598044557855521 29154838822948533418391641)
        ·
          refine ⟨21866129117211400063793731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29154838822948533418391641 21866129117211400063793731)
          ·
            refine ⟨32799193675817100095690597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21866129117211400063793731 32799193675817100095690597)
            ·
              refine ⟨6149848814215706267941987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32799193675817100095690597 6149848814215706267941987)
              ·
                refine ⟨9224773221323559401912981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149848814215706267941987 9224773221323559401912981)
                ·
                  refine ⟨432411244749541846964671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9224773221323559401912981 432411244749541846964671)
                  ·
                    rfl

theorem cell23_7579061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_7579061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579061 prefixEnd_7579061 := by exact prefixLift 7579061
  have htrace : WordTrace (prefixWord ++ tailWord_7579061) baseStart_7579061 baseEnd_7579061 := by
    simpa [prefixWord, tailWord_7579061, baseEnd_7579061] using wordTrace_append hprefix tailTrace_7579061
  have hstable : (prefixWord ++ tailWord_7579061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579061).length < 2 ^ (prefixWord ++ tailWord_7579061).sum := by decide
  have hdescent : baseEnd_7579061 < baseStart_7579061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579064 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 3, 5, 2]
def baseStart_7579064 : Nat := 118140960795 + 7579064 * 2 ^ 59
def prefixEnd_7579064 : Nat := 4983230072969 + 3 ^ 40 * 7579064 * 2
def baseEnd_7579064 : Nat := 3891702743187840110944525

theorem tailTrace_7579064 : CollatzResearch.WordTrace tailWord_7579064 prefixEnd_7579064 3891702743187840110944525 := by
  unfold tailWord_7579064
  simp only [CollatzResearch.WordTrace]
  refine ⟨138215586907176501961888123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184287449209568669282517497 138215586907176501961888123)
  ·
    refine ⟨207323380360764752942832185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138215586907176501961888123 207323380360764752942832185)
    ·
      refine ⟨155492535270573564707124139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207323380360764752942832185 155492535270573564707124139)
      ·
        refine ⟨233238802905860347060686209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155492535270573564707124139 233238802905860347060686209)
        ·
          refine ⟨174929102179395260295514657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233238802905860347060686209 174929102179395260295514657)
          ·
            refine ⟨131196826634546445221635993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174929102179395260295514657 131196826634546445221635993)
            ·
              refine ⟨98397619975909833916226995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131196826634546445221635993 98397619975909833916226995)
              ·
                refine ⟨147596429963864750874340493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98397619975909833916226995 147596429963864750874340493)
                ·
                  refine ⟨55348661236449281577877685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147596429963864750874340493 55348661236449281577877685)
                  ·
                    refine ⟨5188936990917120147926033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55348661236449281577877685 5188936990917120147926033)
                    ·
                      refine ⟨3891702743187840110944525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188936990917120147926033 3891702743187840110944525)
                      ·
                        rfl

theorem cell23_7579064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_7579064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579064 prefixEnd_7579064 := by exact prefixLift 7579064
  have htrace : WordTrace (prefixWord ++ tailWord_7579064) baseStart_7579064 baseEnd_7579064 := by
    simpa [prefixWord, tailWord_7579064, baseEnd_7579064] using wordTrace_append hprefix tailTrace_7579064
  have hstable : (prefixWord ++ tailWord_7579064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579064).length < 2 ^ (prefixWord ++ tailWord_7579064).sum := by decide
  have hdescent : baseEnd_7579064 < baseStart_7579064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579087 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 3, 6]
def baseStart_7579087 : Nat := 118140960795 + 7579087 * 2 ^ 59
def prefixEnd_7579087 : Nat := 4983230072969 + 3 ^ 40 * 7579087 * 2
def baseEnd_7579087 : Nat := 1297238184414297840318973

theorem tailTrace_7579087 : CollatzResearch.WordTrace tailWord_7579087 prefixEnd_7579087 1297238184414297840318973 := by
  unfold tailWord_7579087
  simp only [CollatzResearch.WordTrace]
  refine ⟨276432012693269678851863515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184288008462179785901242343 276432012693269678851863515)
  ·
    refine ⟨414648019039904518277795273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276432012693269678851863515 414648019039904518277795273)
    ·
      refine ⟨310986014279928388708346455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414648019039904518277795273 310986014279928388708346455)
      ·
        refine ⟨466479021419892583062519683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310986014279928388708346455 466479021419892583062519683)
        ·
          refine ⟨699718532129838874593779525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466479021419892583062519683 699718532129838874593779525)
          ·
            refine ⟨131197224774344788986333661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 699718532129838874593779525 131197224774344788986333661)
            ·
              refine ⟨49198959290379295869875123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131197224774344788986333661 49198959290379295869875123)
              ·
                refine ⟨73798438935568943804812685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49198959290379295869875123 73798438935568943804812685)
                ·
                  refine ⟨27674414600838353926804757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73798438935568943804812685 27674414600838353926804757)
                  ·
                    refine ⟨1297238184414297840318973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27674414600838353926804757 1297238184414297840318973)
                    ·
                      rfl

theorem cell23_7579087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_7579087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579087 prefixEnd_7579087 := by exact prefixLift 7579087
  have htrace : WordTrace (prefixWord ++ tailWord_7579087) baseStart_7579087 baseEnd_7579087 := by
    simpa [prefixWord, tailWord_7579087, baseEnd_7579087] using wordTrace_append hprefix tailTrace_7579087
  have hstable : (prefixWord ++ tailWord_7579087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579087).length < 2 ^ (prefixWord ++ tailWord_7579087).sum := by decide
  have hdescent : baseEnd_7579087 < baseStart_7579087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579105 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_7579105 : Nat := 118140960795 + 7579105 * 2 ^ 59
def prefixEnd_7579105 : Nat := 4983230072969 + 3 ^ 40 * 7579105 * 2
def baseEnd_7579105 : Nat := 3891723795894674450531837

theorem tailTrace_7579105 : CollatzResearch.WordTrace tailWord_7579105 prefixEnd_7579105 3891723795894674450531837 := by
  unfold tailWord_7579105
  simp only [CollatzResearch.WordTrace]
  refine ⟨276432669207204467926018769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184288446138136311950679179 276432669207204467926018769)
  ·
    refine ⟨207324501905403350944514077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276432669207204467926018769 207324501905403350944514077)
    ·
      refine ⟨77746688214526256604192779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207324501905403350944514077 77746688214526256604192779)
      ·
        refine ⟨116620032321789384906289169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77746688214526256604192779 116620032321789384906289169)
        ·
          refine ⟨87465024241342038679716877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116620032321789384906289169 87465024241342038679716877)
          ·
            refine ⟨32799384090503264504893829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87465024241342038679716877 32799384090503264504893829)
            ·
              refine ⟨6149884516969362094667593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32799384090503264504893829 6149884516969362094667593)
              ·
                refine ⟨4612413387727021571000695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149884516969362094667593 4612413387727021571000695)
                ·
                  refine ⟨6918620081590532356501043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612413387727021571000695 6918620081590532356501043)
                  ·
                    refine ⟨10377930122385798534751565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6918620081590532356501043 10377930122385798534751565)
                    ·
                      refine ⟨3891723795894674450531837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10377930122385798534751565 3891723795894674450531837)
                      ·
                        rfl

theorem cell23_7579105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_7579105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579105 prefixEnd_7579105 := by exact prefixLift 7579105
  have htrace : WordTrace (prefixWord ++ tailWord_7579105) baseStart_7579105 baseEnd_7579105 := by
    simpa [prefixWord, tailWord_7579105, baseEnd_7579105] using wordTrace_append hprefix tailTrace_7579105
  have hstable : (prefixWord ++ tailWord_7579105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579105).length < 2 ^ (prefixWord ++ tailWord_7579105).sum := by decide
  have hdescent : baseEnd_7579105 < baseStart_7579105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579121 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 2, 4]
def baseStart_7579121 : Nat := 118140960795 + 7579121 * 2 ^ 59
def prefixEnd_7579121 : Nat := 4983230072969 + 3 ^ 40 * 7579121 * 2
def baseEnd_7579121 : Nat := 1297244003861715462643921

theorem tailTrace_7579121 : CollatzResearch.WordTrace tailWord_7579121 prefixEnd_7579121 1297244003861715462643921 := by
  unfold tailWord_7579121
  simp only [CollatzResearch.WordTrace]
  refine ⟨276433252775146502658601217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184288835183431001772400811 276433252775146502658601217)
  ·
    refine ⟨207324939581359876993950913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276433252775146502658601217 207324939581359876993950913)
    ·
      refine ⟨155493704686019907745463185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207324939581359876993950913 155493704686019907745463185)
      ·
        refine ⟨116620278514514930809097389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155493704686019907745463185 116620278514514930809097389)
        ·
          refine ⟨43732604442943099053411521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116620278514514930809097389 43732604442943099053411521)
          ·
            refine ⟨32799453332207324290058641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43732604442943099053411521 32799453332207324290058641)
            ·
              refine ⟨24599589999155493217543981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32799453332207324290058641 24599589999155493217543981)
              ·
                refine ⟨9224846249683309956578993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24599589999155493217543981 9224846249683309956578993)
                ·
                  refine ⟨6918634687262482467434245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224846249683309956578993 6918634687262482467434245)
                  ·
                    refine ⟨1297244003861715462643921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918634687262482467434245 1297244003861715462643921)
                    ·
                      rfl

theorem cell23_7579121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_7579121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579121 prefixEnd_7579121 := by exact prefixLift 7579121
  have htrace : WordTrace (prefixWord ++ tailWord_7579121) baseStart_7579121 baseEnd_7579121 := by
    simpa [prefixWord, tailWord_7579121, baseEnd_7579121] using wordTrace_append hprefix tailTrace_7579121
  have hstable : (prefixWord ++ tailWord_7579121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579121).length < 2 ^ (prefixWord ++ tailWord_7579121).sum := by decide
  have hdescent : baseEnd_7579121 < baseStart_7579121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579128 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 3, 2, 2]
def baseStart_7579128 : Nat := 118140960795 + 7579128 * 2 ^ 59
def prefixEnd_7579128 : Nat := 4983230072969 + 3 ^ 40 * 7579128 * 2
def baseEnd_7579128 : Nat := 3891735605949727860544231

theorem tailTrace_7579128 : CollatzResearch.WordTrace tailWord_7579128 prefixEnd_7579128 3891735605949727860544231 := by
  unfold tailWord_7579128
  simp only [CollatzResearch.WordTrace]
  refine ⟨138216754043060571427053019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184289005390747428569404025 138216754043060571427053019)
  ·
    refine ⟨207325131064590857140579529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138216754043060571427053019 207325131064590857140579529)
    ·
      refine ⟨155493848298443142855434647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207325131064590857140579529 155493848298443142855434647)
      ·
        refine ⟨233240772447664714283151971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155493848298443142855434647 233240772447664714283151971)
        ·
          refine ⟨349861158671497071424727957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233240772447664714283151971 349861158671497071424727957)
          ·
            refine ⟨16399741812726425223034123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 349861158671497071424727957 16399741812726425223034123)
            ·
              refine ⟨24599612719089637834551185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399741812726425223034123 24599612719089637834551185)
              ·
                refine ⟨18449709539317228375913389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24599612719089637834551185 18449709539317228375913389)
                ·
                  refine ⟨6918641077243960640967521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18449709539317228375913389 6918641077243960640967521)
                  ·
                    refine ⟨5188980807932970480725641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918641077243960640967521 5188980807932970480725641)
                    ·
                      refine ⟨3891735605949727860544231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188980807932970480725641 3891735605949727860544231)
                      ·
                        rfl

theorem cell23_7579128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_7579128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579128 prefixEnd_7579128 := by exact prefixLift 7579128
  have htrace : WordTrace (prefixWord ++ tailWord_7579128) baseStart_7579128 baseEnd_7579128 := by
    simpa [prefixWord, tailWord_7579128, baseEnd_7579128] using wordTrace_append hprefix tailTrace_7579128
  have hstable : (prefixWord ++ tailWord_7579128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579128).length < 2 ^ (prefixWord ++ tailWord_7579128).sum := by decide
  have hdescent : baseEnd_7579128 < baseStart_7579128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579142 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_7579142 : Nat := 118140960795 + 7579142 * 2 ^ 59
def prefixEnd_7579142 : Nat := 4983230072969 + 3 ^ 40 * 7579142 * 2
def baseEnd_7579142 : Nat := 1297247598226296935256389

theorem tailTrace_7579142 : CollatzResearch.WordTrace tailWord_7579142 prefixEnd_7579142 1297247598226296935256389 := by
  unfold tailWord_7579142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638563084627200726409865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184289345805380282163410453 8638563084627200726409865)
  ·
    refine ⟨6478922313470400544807399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8638563084627200726409865 6478922313470400544807399)
    ·
      refine ⟨9718383470205600817211099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6478922313470400544807399 9718383470205600817211099)
      ·
        refine ⟨14577575205308401225816649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9718383470205600817211099 14577575205308401225816649)
        ·
          refine ⟨10933181403981300919362487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14577575205308401225816649 10933181403981300919362487)
          ·
            refine ⟨16399772105971951379043731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10933181403981300919362487 16399772105971951379043731)
            ·
              refine ⟨24599658158957927068565597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399772105971951379043731 24599658158957927068565597)
              ·
                refine ⟨9224871809609222650712099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24599658158957927068565597 9224871809609222650712099)
                ·
                  refine ⟨13837307714413833976068149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9224871809609222650712099 13837307714413833976068149)
                  ·
                    refine ⟨1297247598226296935256389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13837307714413833976068149 1297247598226296935256389)
                    ·
                      rfl

theorem cell23_7579142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_7579142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579142 prefixEnd_7579142 := by exact prefixLift 7579142
  have htrace : WordTrace (prefixWord ++ tailWord_7579142) baseStart_7579142 baseEnd_7579142 := by
    simpa [prefixWord, tailWord_7579142, baseEnd_7579142] using wordTrace_append hprefix tailTrace_7579142
  have hstable : (prefixWord ++ tailWord_7579142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579142).length < 2 ^ (prefixWord ++ tailWord_7579142).sum := by decide
  have hdescent : baseEnd_7579142 < baseStart_7579142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579145 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 1, 2, 2]
def baseStart_7579145 : Nat := 118140960795 + 7579145 * 2 ^ 59
def prefixEnd_7579145 : Nat := 4983230072969 + 3 ^ 40 * 7579145 * 2
def baseEnd_7579145 : Nat := 3891744335120854294031653

theorem tailTrace_7579145 : CollatzResearch.WordTrace tailWord_7579145 prefixEnd_7579145 3891744335120854294031653 := by
  unfold tailWord_7579145
  simp only [CollatzResearch.WordTrace]
  refine ⟨276434128127059554757474889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184289418751373036504983259 276434128127059554757474889)
  ·
    refine ⟨207325596095294666068106167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276434128127059554757474889 207325596095294666068106167)
    ·
      refine ⟨310988394142941999102159251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207325596095294666068106167 310988394142941999102159251)
      ·
        refine ⟨466482591214412998653238877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310988394142941999102159251 466482591214412998653238877)
        ·
          refine ⟨174930971705404874494964579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466482591214412998653238877 174930971705404874494964579)
          ·
            refine ⟨262396457558107311742446869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174930971705404874494964579 262396457558107311742446869)
            ·
              refine ⟨12299833948036280237927197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262396457558107311742446869 12299833948036280237927197)
              ·
                refine ⟨4612437730513605089222699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12299833948036280237927197 4612437730513605089222699)
                ·
                  refine ⟨6918656595770407633834049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612437730513605089222699 6918656595770407633834049)
                  ·
                    refine ⟨5188992446827805725375537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918656595770407633834049 5188992446827805725375537)
                    ·
                      refine ⟨3891744335120854294031653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5188992446827805725375537 3891744335120854294031653)
                      ·
                        rfl

theorem cell23_7579145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 2, 2].length) (baseStart_7579145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579145 prefixEnd_7579145 := by exact prefixLift 7579145
  have htrace : WordTrace (prefixWord ++ tailWord_7579145) baseStart_7579145 baseEnd_7579145 := by
    simpa [prefixWord, tailWord_7579145, baseEnd_7579145] using wordTrace_append hprefix tailTrace_7579145
  have hstable : (prefixWord ++ tailWord_7579145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579145).length < 2 ^ (prefixWord ++ tailWord_7579145).sum := by decide
  have hdescent : baseEnd_7579145 < baseStart_7579145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579148 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_7579148 : Nat := 118140960795 + 7579148 * 2 ^ 59
def prefixEnd_7579148 : Nat := 4983230072969 + 3 ^ 40 * 7579148 * 2
def baseEnd_7579148 : Nat := 3891745875562817782294139

theorem tailTrace_7579148 : CollatzResearch.WordTrace tailWord_7579148 prefixEnd_7579148 3891745875562817782294139 := by
  unfold tailWord_7579148
  simp only [CollatzResearch.WordTrace]
  refine ⟨138217118773024343134917049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184289491697365790846556065 138217118773024343134917049)
  ·
    refine ⟨103662839079768257351187787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138217118773024343134917049 103662839079768257351187787)
    ·
      refine ⟨155494258619652386026781681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103662839079768257351187787 155494258619652386026781681)
      ·
        refine ⟨116620693964739289520086261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155494258619652386026781681 116620693964739289520086261)
        ·
          refine ⟨10933190059194308392508087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116620693964739289520086261 10933190059194308392508087)
          ·
            refine ⟨16399785088791462588762131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10933190059194308392508087 16399785088791462588762131)
            ·
              refine ⟨24599677633187193883143197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399785088791462588762131 24599677633187193883143197)
              ·
                refine ⟨9224879112445197706178699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24599677633187193883143197 9224879112445197706178699)
                ·
                  refine ⟨13837318668667796559268049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9224879112445197706178699 13837318668667796559268049)
                  ·
                    refine ⟨10377989001500847419451037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13837318668667796559268049 10377989001500847419451037)
                    ·
                      refine ⟨3891745875562817782294139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10377989001500847419451037 3891745875562817782294139)
                      ·
                        rfl

theorem cell23_7579148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_7579148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579148 prefixEnd_7579148 := by exact prefixLift 7579148
  have htrace : WordTrace (prefixWord ++ tailWord_7579148) baseStart_7579148 baseEnd_7579148 := by
    simpa [prefixWord, tailWord_7579148, baseEnd_7579148] using wordTrace_append hprefix tailTrace_7579148
  have hstable : (prefixWord ++ tailWord_7579148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579148).length < 2 ^ (prefixWord ++ tailWord_7579148).sum := by decide
  have hdescent : baseEnd_7579148 < baseStart_7579148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579235 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 2, 2, 2]
def baseStart_7579235 : Nat := 118140960795 + 7579235 * 2 ^ 59
def prefixEnd_7579235 : Nat := 4983230072969 + 3 ^ 40 * 7579235 * 2
def baseEnd_7579235 : Nat := 3891790548379758941906239

theorem tailTrace_7579235 : CollatzResearch.WordTrace tailWord_7579235 prefixEnd_7579235 3891790548379758941906239 := by
  unfold tailWord_7579235
  simp only [CollatzResearch.WordTrace]
  refine ⟨276437410696733500128251159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184291607131155666752167439 276437410696733500128251159)
  ·
    refine ⟨414656116045100250192376739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276437410696733500128251159 414656116045100250192376739)
    ·
      refine ⟨621984174067650375288565109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414656116045100250192376739 621984174067650375288565109)
      ·
        refine ⟨58311016318842222683302979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 621984174067650375288565109 58311016318842222683302979)
        ·
          refine ⟨87466524478263334024954469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58311016318842222683302979 87466524478263334024954469)
          ·
            refine ⟨16399973339674375129678963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87466524478263334024954469 16399973339674375129678963)
            ·
              refine ⟨24599960009511562694518445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16399973339674375129678963 24599960009511562694518445)
              ·
                refine ⟨9224985003566836010444417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24599960009511562694518445 9224985003566836010444417)
                ·
                  refine ⟨6918738752675127007833313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224985003566836010444417 6918738752675127007833313)
                  ·
                    refine ⟨5189054064506345255874985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918738752675127007833313 5189054064506345255874985)
                    ·
                      refine ⟨3891790548379758941906239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189054064506345255874985 3891790548379758941906239)
                      ·
                        rfl

theorem cell23_7579235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_7579235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579235 prefixEnd_7579235 := by exact prefixLift 7579235
  have htrace : WordTrace (prefixWord ++ tailWord_7579235) baseStart_7579235 baseEnd_7579235 := by
    simpa [prefixWord, tailWord_7579235, baseEnd_7579235] using wordTrace_append hprefix tailTrace_7579235
  have hstable : (prefixWord ++ tailWord_7579235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579235).length < 2 ^ (prefixWord ++ tailWord_7579235).sum := by decide
  have hdescent : baseEnd_7579235 < baseStart_7579235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579264 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_7579264 : Nat := 118140960795 + 7579264 * 2 ^ 59
def prefixEnd_7579264 : Nat := 4983230072969 + 3 ^ 40 * 7579264 * 2
def baseEnd_7579264 : Nat := 3891805439318739328443605

theorem tailTrace_7579264 : CollatzResearch.WordTrace tailWord_7579264 prefixEnd_7579264 3891805439318739328443605 := by
  unfold tailWord_7579264
  simp only [CollatzResearch.WordTrace]
  refine ⟨138219234206814219040528423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184292312275752292054037897 138219234206814219040528423)
  ·
    refine ⟨207328851310221328560792635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138219234206814219040528423 207328851310221328560792635)
    ·
      refine ⟨310993276965331992841188953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207328851310221328560792635 310993276965331992841188953)
      ·
        refine ⟨233244957723998994630891715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310993276965331992841188953 233244957723998994630891715)
        ·
          refine ⟨349867436585998491946337573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233244957723998994630891715 349867436585998491946337573)
          ·
            refine ⟨65600144359874717239938295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349867436585998491946337573 65600144359874717239938295)
            ·
              refine ⟨98400216539812075859907443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65600144359874717239938295 98400216539812075859907443)
              ·
                refine ⟨147600324809718113789861165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98400216539812075859907443 147600324809718113789861165)
                ·
                  refine ⟨55350121803644292671197937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147600324809718113789861165 55350121803644292671197937)
                  ·
                    refine ⟨41512591352733219503398453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55350121803644292671197937 41512591352733219503398453)
                    ·
                      refine ⟨3891805439318739328443605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41512591352733219503398453 3891805439318739328443605)
                      ·
                        rfl

theorem cell23_7579264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_7579264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579264 prefixEnd_7579264 := by exact prefixLift 7579264
  have htrace : WordTrace (prefixWord ++ tailWord_7579264) baseStart_7579264 baseEnd_7579264 := by
    simpa [prefixWord, tailWord_7579264, baseEnd_7579264] using wordTrace_append hprefix tailTrace_7579264
  have hstable : (prefixWord ++ tailWord_7579264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579264).length < 2 ^ (prefixWord ++ tailWord_7579264).sum := by decide
  have hdescent : baseEnd_7579264 < baseStart_7579264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579271 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 2, 5]
def baseStart_7579271 : Nat := 118140960795 + 7579271 * 2 ^ 59
def prefixEnd_7579271 : Nat := 4983230072969 + 3 ^ 40 * 7579271 * 2
def baseEnd_7579271 : Nat := 1297269677894440267018691

theorem tailTrace_7579271 : CollatzResearch.WordTrace tailWord_7579271 prefixEnd_7579271 1297269677894440267018691 := by
  unfold tailWord_7579271
  simp only [CollatzResearch.WordTrace]
  refine ⟨276438723724603078276561667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184292482483068718851041111 276438723724603078276561667)
  ·
    refine ⟨414658085586904617414842501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276438723724603078276561667 414658085586904617414842501)
    ·
      refine ⟨77748391047544615765282969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414658085586904617414842501 77748391047544615765282969)
      ·
        refine ⟨58311293285658461823962227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77748391047544615765282969 58311293285658461823962227)
        ·
          refine ⟨87466939928487692735943341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58311293285658461823962227 87466939928487692735943341)
          ·
            refine ⟨32800102473182884775978753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87466939928487692735943341 32800102473182884775978753)
            ·
              refine ⟨24600076854887163581984065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32800102473182884775978753 24600076854887163581984065)
              ·
                refine ⟨18450057641165372686488049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24600076854887163581984065 18450057641165372686488049)
                ·
                  refine ⟨13837543230874029514866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18450057641165372686488049 13837543230874029514866037)
                  ·
                    refine ⟨1297269677894440267018691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13837543230874029514866037 1297269677894440267018691)
                    ·
                      rfl

theorem cell23_7579271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_7579271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579271 prefixEnd_7579271 := by exact prefixLift 7579271
  have htrace : WordTrace (prefixWord ++ tailWord_7579271) baseStart_7579271 baseEnd_7579271 := by
    simpa [prefixWord, tailWord_7579271, baseEnd_7579271] using wordTrace_append hprefix tailTrace_7579271
  have hstable : (prefixWord ++ tailWord_7579271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579271).length < 2 ^ (prefixWord ++ tailWord_7579271).sum := by decide
  have hdescent : baseEnd_7579271 < baseStart_7579271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579278 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7579278 : Nat := 118140960795 + 7579278 * 2 ^ 59
def prefixEnd_7579278 : Nat := 4983230072969 + 3 ^ 40 * 7579278 * 2
def baseEnd_7579278 : Nat := 3891812628047902273668541

theorem tailTrace_7579278 : CollatzResearch.WordTrace tailWord_7579278 prefixEnd_7579278 3891812628047902273668541 := by
  unfold tailWord_7579278
  simp only [CollatzResearch.WordTrace]
  refine ⟨34554872379447214809008311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184292652690385145648044325 34554872379447214809008311)
  ·
    refine ⟨51832308569170822213512467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34554872379447214809008311 51832308569170822213512467)
    ·
      refine ⟨77748462853756233320268701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51832308569170822213512467 77748462853756233320268701)
      ·
        refine ⟨29155673570158587495100763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77748462853756233320268701 29155673570158587495100763)
        ·
          refine ⟨43733510355237881242651145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29155673570158587495100763 43733510355237881242651145)
          ·
            refine ⟨32800132766428410931988359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43733510355237881242651145 32800132766428410931988359)
            ·
              refine ⟨49200199149642616397982539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32800132766428410931988359 49200199149642616397982539)
              ·
                refine ⟨73800298724463924596973809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49200199149642616397982539 73800298724463924596973809)
                ·
                  refine ⟨55350224043347943447730357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73800298724463924596973809 55350224043347943447730357)
                  ·
                    refine ⟨5189083504063869698224721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55350224043347943447730357 5189083504063869698224721)
                    ·
                      refine ⟨3891812628047902273668541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189083504063869698224721 3891812628047902273668541)
                      ·
                        rfl

theorem cell23_7579278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7579278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579278 prefixEnd_7579278 := by exact prefixLift 7579278
  have htrace : WordTrace (prefixWord ++ tailWord_7579278) baseStart_7579278 baseEnd_7579278 := by
    simpa [prefixWord, tailWord_7579278, baseEnd_7579278] using wordTrace_append hprefix tailTrace_7579278
  have hstable : (prefixWord ++ tailWord_7579278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579278).length < 2 ^ (prefixWord ++ tailWord_7579278).sum := by decide
  have hdescent : baseEnd_7579278 < baseStart_7579278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579301 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_7579301 : Nat := 118140960795 + 7579301 * 2 ^ 59
def prefixEnd_7579301 : Nat := 4983230072969 + 3 ^ 40 * 7579301 * 2
def baseEnd_7579301 : Nat := 1297274812700985227893645

theorem tailTrace_7579301 : CollatzResearch.WordTrace tailWord_7579301 prefixEnd_7579301 1297274812700985227893645 := by
  unfold tailWord_7579301
  simp only [CollatzResearch.WordTrace]
  refine ⟨276439817914494393400153757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184293211942996262266769171 276439817914494393400153757)
  ·
    refine ⟨103664931717935397525057659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276439817914494393400153757 103664931717935397525057659)
    ·
      refine ⟨155497397576903096287586489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103664931717935397525057659 155497397576903096287586489)
      ·
        refine ⟨116623048182677322215689867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155497397576903096287586489 116623048182677322215689867)
        ·
          refine ⟨174934572274015983323534801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116623048182677322215689867 174934572274015983323534801)
          ·
            refine ⟨131200929205511987492651101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174934572274015983323534801 131200929205511987492651101)
            ·
              refine ⟨49200348452066995309744163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131200929205511987492651101 49200348452066995309744163)
              ·
                refine ⟨73800522678100492964616245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49200348452066995309744163 73800522678100492964616245)
                ·
                  refine ⟨6918799001071921215432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73800522678100492964616245 6918799001071921215432773)
                  ·
                    refine ⟨1297274812700985227893645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918799001071921215432773 1297274812700985227893645)
                    ·
                      rfl

theorem cell23_7579301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_7579301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579301 prefixEnd_7579301 := by exact prefixLift 7579301
  have htrace : WordTrace (prefixWord ++ tailWord_7579301) baseStart_7579301 baseEnd_7579301 := by
    simpa [prefixWord, tailWord_7579301, baseEnd_7579301] using wordTrace_append hprefix tailTrace_7579301
  have hstable : (prefixWord ++ tailWord_7579301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579301).length < 2 ^ (prefixWord ++ tailWord_7579301).sum := by decide
  have hdescent : baseEnd_7579301 < baseStart_7579301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579311 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_7579311 : Nat := 118140960795 + 7579311 * 2 ^ 59
def prefixEnd_7579311 : Nat := 4983230072969 + 3 ^ 40 * 7579311 * 2
def baseEnd_7579311 : Nat := 3891829572909500644555889

theorem tailTrace_7579311 : CollatzResearch.WordTrace tailWord_7579311 prefixEnd_7579311 3891829572909500644555889 := by
  unfold tailWord_7579311
  simp only [CollatzResearch.WordTrace]
  refine ⟨276440182644458165108017787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184293455096305443405345191 276440182644458165108017787)
  ·
    refine ⟨414660273966687247662026681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276440182644458165108017787 414660273966687247662026681)
    ·
      refine ⟨310995205475015435746520011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414660273966687247662026681 310995205475015435746520011)
      ·
        refine ⟨466492808212523153619780017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310995205475015435746520011 466492808212523153619780017)
        ·
          refine ⟨349869606159392365214835013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466492808212523153619780017 349869606159392365214835013)
          ·
            refine ⟨65600551154886068477781565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349869606159392365214835013 65600551154886068477781565)
            ·
              refine ⟨24600206683082275679168087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65600551154886068477781565 24600206683082275679168087)
              ·
                refine ⟨36900310024623413518752131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24600206683082275679168087 36900310024623413518752131)
                ·
                  refine ⟨55350465036935120278128197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36900310024623413518752131 55350465036935120278128197)
                  ·
                    refine ⟨10378212194425335052149037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55350465036935120278128197 10378212194425335052149037)
                    ·
                      refine ⟨3891829572909500644555889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10378212194425335052149037 3891829572909500644555889)
                      ·
                        rfl

theorem cell23_7579311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_7579311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579311 prefixEnd_7579311 := by exact prefixLift 7579311
  have htrace : WordTrace (prefixWord ++ tailWord_7579311) baseStart_7579311 baseEnd_7579311 := by
    simpa [prefixWord, tailWord_7579311, baseEnd_7579311] using wordTrace_append hprefix tailTrace_7579311
  have hstable : (prefixWord ++ tailWord_7579311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579311).length < 2 ^ (prefixWord ++ tailWord_7579311).sum := by decide
  have hdescent : baseEnd_7579311 < baseStart_7579311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579344 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_7579344 : Nat := 118140960795 + 7579344 * 2 ^ 59
def prefixEnd_7579344 : Nat := 4983230072969 + 3 ^ 40 * 7579344 * 2
def baseEnd_7579344 : Nat := 1297282172590366338481079

theorem tailTrace_7579344 : CollatzResearch.WordTrace tailWord_7579344 prefixEnd_7579344 1297282172590366338481079 := by
  unfold tailWord_7579344
  simp only [CollatzResearch.WordTrace]
  refine ⟨138220693126669305871984543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184294257502225741162646057 138220693126669305871984543)
  ·
    refine ⟨207331039690003958807976815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138220693126669305871984543 207331039690003958807976815)
    ·
      refine ⟨310996559535005938211965223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207331039690003958807976815 310996559535005938211965223)
      ·
        refine ⟨466494839302508907317947835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310996559535005938211965223 466494839302508907317947835)
        ·
          refine ⟨699742258953763360976921753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466494839302508907317947835 699742258953763360976921753)
          ·
            refine ⟨524806694215322520732691315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699742258953763360976921753 524806694215322520732691315)
            ·
              refine ⟨787210041322983781099036973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524806694215322520732691315 787210041322983781099036973)
              ·
                refine ⟨295203765496118917912138865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787210041322983781099036973 295203765496118917912138865)
                ·
                  refine ⟨221402824122089188434104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295203765496118917912138865 221402824122089188434104149)
                  ·
                    refine ⟨1297282172590366338481079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221402824122089188434104149 1297282172590366338481079)
                    ·
                      rfl

theorem cell23_7579344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_7579344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579344 prefixEnd_7579344 := by exact prefixLift 7579344
  have htrace : WordTrace (prefixWord ++ tailWord_7579344) baseStart_7579344 baseEnd_7579344 := by
    simpa [prefixWord, tailWord_7579344, baseEnd_7579344] using wordTrace_append hprefix tailTrace_7579344
  have hstable : (prefixWord ++ tailWord_7579344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579344).length < 2 ^ (prefixWord ++ tailWord_7579344).sum := by decide
  have hdescent : baseEnd_7579344 < baseStart_7579344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579378 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_7579378 : Nat := 118140960795 + 7579378 * 2 ^ 59
def prefixEnd_7579378 : Nat := 4983230072969 + 3 ^ 40 * 7579378 * 2
def baseEnd_7579378 : Nat := 1297287992037783960806027

theorem tailTrace_7579378 : CollatzResearch.WordTrace tailWord_7579378 prefixEnd_7579378 1297287992037783960806027 := by
  unfold tailWord_7579378
  simp only [CollatzResearch.WordTrace]
  refine ⟨69110656583803858887676697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184295084223476957033804525 69110656583803858887676697)
  ·
    refine ⟨51832992437852894165757523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69110656583803858887676697 51832992437852894165757523)
    ·
      refine ⟨77749488656779341248636285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51832992437852894165757523 77749488656779341248636285)
      ·
        refine ⟨29156058246292252968238607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77749488656779341248636285 29156058246292252968238607)
        ·
          refine ⟨43734087369438379452357911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29156058246292252968238607 43734087369438379452357911)
          ·
            refine ⟨65601131054157569178536867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43734087369438379452357911 65601131054157569178536867)
            ·
              refine ⟨98401696581236353767805301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65601131054157569178536867 98401696581236353767805301)
              ·
                refine ⟨9225159054490908165731747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98401696581236353767805301 9225159054490908165731747)
                ·
                  refine ⟨13837738581736362248597621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225159054490908165731747 13837738581736362248597621)
                  ·
                    refine ⟨1297287992037783960806027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13837738581736362248597621 1297287992037783960806027)
                    ·
                      rfl

theorem cell23_7579378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_7579378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579378 prefixEnd_7579378 := by exact prefixLift 7579378
  have htrace : WordTrace (prefixWord ++ tailWord_7579378) baseStart_7579378 baseEnd_7579378 := by
    simpa [prefixWord, tailWord_7579378, baseEnd_7579378] using wordTrace_append hprefix tailTrace_7579378
  have hstable : (prefixWord ++ tailWord_7579378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579378).length < 2 ^ (prefixWord ++ tailWord_7579378).sum := by decide
  have hdescent : baseEnd_7579378 < baseStart_7579378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579401 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_7579401 : Nat := 118140960795 + 7579401 * 2 ^ 59
def prefixEnd_7579401 : Nat := 4983230072969 + 3 ^ 40 * 7579401 * 2
def baseEnd_7579401 : Nat := 3891875786168405292430475

theorem tailTrace_7579401 : CollatzResearch.WordTrace tailWord_7579401 prefixEnd_7579401 3891875786168405292430475 := by
  unfold tailWord_7579401
  simp only [CollatzResearch.WordTrace]
  refine ⟨276443465214132110478794057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184295643476088073652529371 276443465214132110478794057)
  ·
    refine ⟨207332598910599082859095543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276443465214132110478794057 207332598910599082859095543)
    ·
      refine ⟨310998898365898624288643315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207332598910599082859095543 310998898365898624288643315)
      ·
        refine ⟨466498347548847936432964973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310998898365898624288643315 466498347548847936432964973)
        ·
          refine ⟨174936880330817976162361865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466498347548847936432964973 174936880330817976162361865)
          ·
            refine ⟨131202660248113482121771399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174936880330817976162361865 131202660248113482121771399)
            ·
              refine ⟨196803990372170223182657099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131202660248113482121771399 196803990372170223182657099)
              ·
                refine ⟨295205985558255334773985649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196803990372170223182657099 295205985558255334773985649)
                ·
                  refine ⟨221404489168691501080489237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295205985558255334773985649 221404489168691501080489237)
                  ·
                    refine ⟨10378335429782414113147933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221404489168691501080489237 10378335429782414113147933)
                    ·
                      refine ⟨3891875786168405292430475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10378335429782414113147933 3891875786168405292430475)
                      ·
                        rfl

theorem cell23_7579401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_7579401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579401 prefixEnd_7579401 := by exact prefixLift 7579401
  have htrace : WordTrace (prefixWord ++ tailWord_7579401) baseStart_7579401 baseEnd_7579401 := by
    simpa [prefixWord, tailWord_7579401, baseEnd_7579401] using wordTrace_append hprefix tailTrace_7579401
  have hstable : (prefixWord ++ tailWord_7579401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579401).length < 2 ^ (prefixWord ++ tailWord_7579401).sum := by decide
  have hdescent : baseEnd_7579401 < baseStart_7579401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579415 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_7579415 : Nat := 118140960795 + 7579415 * 2 ^ 59
def prefixEnd_7579415 : Nat := 4983230072969 + 3 ^ 40 * 7579415 * 2
def baseEnd_7579415 : Nat := 3891882974897568237655411

theorem tailTrace_7579415 : CollatzResearch.WordTrace tailWord_7579415 prefixEnd_7579415 3891882974897568237655411 := by
  unfold tailWord_7579415
  simp only [CollatzResearch.WordTrace]
  refine ⟨276443975836081390869803699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184295983890720927246535799 276443975836081390869803699)
  ·
    refine ⟨414665963754122086304705549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276443975836081390869803699 414665963754122086304705549)
    ·
      refine ⟨155499736407795782364264581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414665963754122086304705549 155499736407795782364264581)
      ·
        refine ⟨29156200576461709193299609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155499736407795782364264581 29156200576461709193299609)
        ·
          refine ⟨21867150432346281894974707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29156200576461709193299609 21867150432346281894974707)
          ·
            refine ⟨32800725648519422842462061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21867150432346281894974707 32800725648519422842462061)
            ·
              refine ⟨12300272118194783565923273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32800725648519422842462061 12300272118194783565923273)
              ·
                refine ⟨9225204088646087674442455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12300272118194783565923273 9225204088646087674442455)
                ·
                  refine ⟨13837806132969131511663683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225204088646087674442455 13837806132969131511663683)
                  ·
                    refine ⟨20756709199453697267495525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13837806132969131511663683 20756709199453697267495525)
                    ·
                      refine ⟨3891882974897568237655411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20756709199453697267495525 3891882974897568237655411)
                      ·
                        rfl

theorem cell23_7579415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_7579415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579415 prefixEnd_7579415 := by exact prefixLift 7579415
  have htrace : WordTrace (prefixWord ++ tailWord_7579415) baseStart_7579415 baseEnd_7579415 := by
    simpa [prefixWord, tailWord_7579415, baseEnd_7579415] using wordTrace_append hprefix tailTrace_7579415
  have hstable : (prefixWord ++ tailWord_7579415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579415).length < 2 ^ (prefixWord ++ tailWord_7579415).sum := by decide
  have hdescent : baseEnd_7579415 < baseStart_7579415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579428 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7579428 : Nat := 118140960795 + 7579428 * 2 ^ 59
def prefixEnd_7579428 : Nat := 4983230072969 + 3 ^ 40 * 7579428 * 2
def baseEnd_7579428 : Nat := 3891889650146076686792851

theorem tailTrace_7579428 : CollatzResearch.WordTrace tailWord_7579428 prefixEnd_7579428 3891889650146076686792851 := by
  unfold tailWord_7579428
  simp only [CollatzResearch.WordTrace]
  refine ⟨138222224992517147045013469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184296299990022862726684625 138222224992517147045013469)
  ·
    refine ⟨51833334372193930141880051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138222224992517147045013469 51833334372193930141880051)
    ·
      refine ⟨77750001558290895212820077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51833334372193930141880051 77750001558290895212820077)
      ·
        refine ⟨29156250584359085704807529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77750001558290895212820077 29156250584359085704807529)
        ·
          refine ⟨21867187938269314278605647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29156250584359085704807529 21867187938269314278605647)
          ·
            refine ⟨32800781907403971417908471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21867187938269314278605647 32800781907403971417908471)
            ·
              refine ⟨49201172861105957126862707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32800781907403971417908471 49201172861105957126862707)
              ·
                refine ⟨73801759291658935690294061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49201172861105957126862707 73801759291658935690294061)
                ·
                  refine ⟨27675659734372100883860273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73801759291658935690294061 27675659734372100883860273)
                  ·
                    refine ⟨20756744800779075662895205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27675659734372100883860273 20756744800779075662895205)
                    ·
                      refine ⟨3891889650146076686792851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20756744800779075662895205 3891889650146076686792851)
                      ·
                        rfl

theorem cell23_7579428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7579428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579428 prefixEnd_7579428 := by exact prefixLift 7579428
  have htrace : WordTrace (prefixWord ++ tailWord_7579428) baseStart_7579428 baseEnd_7579428 := by
    simpa [prefixWord, tailWord_7579428, baseEnd_7579428] using wordTrace_append hprefix tailTrace_7579428
  have hstable : (prefixWord ++ tailWord_7579428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579428).length < 2 ^ (prefixWord ++ tailWord_7579428).sum := by decide
  have hdescent : baseEnd_7579428 < baseStart_7579428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579432 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_7579432 : Nat := 118140960795 + 7579432 * 2 ^ 59
def prefixEnd_7579432 : Nat := 4983230072969 + 3 ^ 40 * 7579432 * 2
def baseEnd_7579432 : Nat := 3891891704068694671142833

theorem tailTrace_7579432 : CollatzResearch.WordTrace tailWord_7579432 prefixEnd_7579432 3891891704068694671142833 := by
  unfold tailWord_7579432
  simp only [CollatzResearch.WordTrace]
  refine ⟨138222297938509901386586275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184296397251346535182115033 138222297938509901386586275)
  ·
    refine ⟨207333446907764852079879413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138222297938509901386586275 207333446907764852079879413)
    ·
      refine ⟨19437510647602954882488695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207333446907764852079879413 19437510647602954882488695)
      ·
        refine ⟨29156265971404432323733043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19437510647602954882488695 29156265971404432323733043)
        ·
          refine ⟨43734398957106648485599565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29156265971404432323733043 43734398957106648485599565)
          ·
            refine ⟨16400399608914993182099837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43734398957106648485599565 16400399608914993182099837)
            ·
              refine ⟨6150149853343122443287439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16400399608914993182099837 6150149853343122443287439)
              ·
                refine ⟨9225224780014683664931159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150149853343122443287439 9225224780014683664931159)
                ·
                  refine ⟨13837837170022025497396739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225224780014683664931159 13837837170022025497396739)
                  ·
                    refine ⟨20756755755033038246095109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13837837170022025497396739 20756755755033038246095109)
                    ·
                      refine ⟨3891891704068694671142833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20756755755033038246095109 3891891704068694671142833)
                      ·
                        rfl

theorem cell23_7579432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_7579432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579432 prefixEnd_7579432 := by exact prefixLift 7579432
  have htrace : WordTrace (prefixWord ++ tailWord_7579432) baseStart_7579432 baseEnd_7579432 := by
    simpa [prefixWord, tailWord_7579432, baseEnd_7579432] using wordTrace_append hprefix tailTrace_7579432
  have hstable : (prefixWord ++ tailWord_7579432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579432).length < 2 ^ (prefixWord ++ tailWord_7579432).sum := by decide
  have hdescent : baseEnd_7579432 < baseStart_7579432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579438 : List Nat := [4, 1, 3, 2, 2, 11]
def baseStart_7579438 : Nat := 118140960795 + 7579438 * 2 ^ 59
def prefixEnd_7579438 : Nat := 4983230072969 + 3 ^ 40 * 7579438 * 2
def baseEnd_7579438 : Nat := 16016027921615726945135

theorem tailTrace_7579438 : CollatzResearch.WordTrace tailWord_7579438 prefixEnd_7579438 16016027921615726945135 := by
  unfold tailWord_7579438
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555601839374758224736371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184296543143332043865260645 34555601839374758224736371)
  ·
    refine ⟨51833402759062137337104557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34555601839374758224736371 51833402759062137337104557)
    ·
      refine ⟨19437526034648301501414209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51833402759062137337104557 19437526034648301501414209)
      ·
        refine ⟨14578144525986226126060657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19437526034648301501414209 14578144525986226126060657)
        ·
          refine ⟨10933608394489669594545493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14578144525986226126060657 10933608394489669594545493)
          ·
            refine ⟨16016027921615726945135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10933608394489669594545493 16016027921615726945135)
            ·
              rfl

theorem cell23_7579438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 11].length) (baseStart_7579438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579438 prefixEnd_7579438 := by exact prefixLift 7579438
  have htrace : WordTrace (prefixWord ++ tailWord_7579438) baseStart_7579438 baseEnd_7579438 := by
    simpa [prefixWord, tailWord_7579438, baseEnd_7579438] using wordTrace_append hprefix tailTrace_7579438
  have hstable : (prefixWord ++ tailWord_7579438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579438).length < 2 ^ (prefixWord ++ tailWord_7579438).sum := by decide
  have hdescent : baseEnd_7579438 < baseStart_7579438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579455 : List Nat := [1, 1, 2, 2, 7, 1, 1, 8]
def baseStart_7579455 : Nat := 118140960795 + 7579455 * 2 ^ 59
def prefixEnd_7579455 : Nat := 4983230072969 + 3 ^ 40 * 7579455 * 2
def baseEnd_7579455 : Nat := 144144574597175854857601

theorem tailTrace_7579455 : CollatzResearch.WordTrace tailWord_7579455 prefixEnd_7579455 144144574597175854857601 := by
  unfold tailWord_7579455
  simp only [CollatzResearch.WordTrace]
  refine ⟨276445434755936477701259819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184296956503957651800839879 276445434755936477701259819)
  ·
    refine ⟨414668152133904716551889729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276445434755936477701259819 414668152133904716551889729)
    ·
      refine ⟨311001114100428537413917297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414668152133904716551889729 311001114100428537413917297)
      ·
        refine ⟨233250835575321403060437973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311001114100428537413917297 233250835575321403060437973)
        ·
          refine ⟨5466816458796595384229015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 233250835575321403060437973 5466816458796595384229015)
          ·
            refine ⟨8200224688194893076343523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466816458796595384229015 8200224688194893076343523)
            ·
              refine ⟨12300337032292339614515285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200224688194893076343523 12300337032292339614515285)
              ·
                refine ⟨144144574597175854857601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12300337032292339614515285 144144574597175854857601)
                ·
                  rfl

theorem cell23_7579455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 8].length) (baseStart_7579455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579455 prefixEnd_7579455 := by exact prefixLift 7579455
  have htrace : WordTrace (prefixWord ++ tailWord_7579455) baseStart_7579455 baseEnd_7579455 := by
    simpa [prefixWord, tailWord_7579455, baseEnd_7579455] using wordTrace_append hprefix tailTrace_7579455
  have hstable : (prefixWord ++ tailWord_7579455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579455).length < 2 ^ (prefixWord ++ tailWord_7579455).sum := by decide
  have hdescent : baseEnd_7579455 < baseStart_7579455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579462 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7579462 : Nat := 118140960795 + 7579462 * 2 ^ 59
def prefixEnd_7579462 : Nat := 4983230072969 + 3 ^ 40 * 7579462 * 2
def baseEnd_7579462 : Nat := 3891907108488329553767695

theorem tailTrace_7579462 : CollatzResearch.WordTrace tailWord_7579462 prefixEnd_7579462 3891907108488329553767695 := by
  unfold tailWord_7579462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638927814590972434273895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184297126711274078597843093 8638927814590972434273895)
  ·
    refine ⟨12958391721886458651410843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8638927814590972434273895 12958391721886458651410843)
    ·
      refine ⟨19437587582829687977116265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958391721886458651410843 19437587582829687977116265)
      ·
        refine ⟨14578190687122265982837199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19437587582829687977116265 14578190687122265982837199)
        ·
          refine ⟨21867286030683398974255799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14578190687122265982837199 21867286030683398974255799)
          ·
            refine ⟨32800929046025098461383699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21867286030683398974255799 32800929046025098461383699)
            ·
              refine ⟨49201393569037647692075549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32800929046025098461383699 49201393569037647692075549)
              ·
                refine ⟨18450522588389117884528331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49201393569037647692075549 18450522588389117884528331)
                ·
                  refine ⟨27675783882583676826792497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18450522588389117884528331 27675783882583676826792497)
                  ·
                    refine ⟨20756837911937757620094373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27675783882583676826792497 20756837911937757620094373)
                    ·
                      refine ⟨3891907108488329553767695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20756837911937757620094373 3891907108488329553767695)
                      ·
                        rfl

theorem cell23_7579462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7579462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579462 prefixEnd_7579462 := by exact prefixLift 7579462
  have htrace : WordTrace (prefixWord ++ tailWord_7579462) baseStart_7579462 baseEnd_7579462 := by
    simpa [prefixWord, tailWord_7579462, baseEnd_7579462] using wordTrace_append hprefix tailTrace_7579462
  have hstable : (prefixWord ++ tailWord_7579462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579462).length < 2 ^ (prefixWord ++ tailWord_7579462).sum := by decide
  have hdescent : baseEnd_7579462 < baseStart_7579462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579465 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 3]
def baseStart_7579465 : Nat := 118140960795 + 7579465 * 2 ^ 59
def prefixEnd_7579465 : Nat := 4983230072969 + 3 ^ 40 * 7579465 * 2
def baseEnd_7579465 : Nat := 3891908648930293042030181

theorem tailTrace_7579465 : CollatzResearch.WordTrace tailWord_7579465 prefixEnd_7579465 3891908648930293042030181 := by
  unfold tailWord_7579465
  simp only [CollatzResearch.WordTrace]
  refine ⟨276445799485900249409123849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184297199657266832939415899 276445799485900249409123849)
  ·
    refine ⟨207334349614425187056842887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276445799485900249409123849 207334349614425187056842887)
    ·
      refine ⟨311001524421637780585264331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207334349614425187056842887 311001524421637780585264331)
      ·
        refine ⟨466502286632456670877896497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311001524421637780585264331 466502286632456670877896497)
        ·
          refine ⟨349876714974342503158422373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466502286632456670877896497 349876714974342503158422373)
          ·
            refine ⟨65601884057689219342204195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349876714974342503158422373 65601884057689219342204195)
            ·
              refine ⟨98402826086533829013306293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65601884057689219342204195 98402826086533829013306293)
              ·
                refine ⟨9225264945612546469997465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98402826086533829013306293 9225264945612546469997465)
                ·
                  refine ⟨6918948709209409852498099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9225264945612546469997465 6918948709209409852498099)
                  ·
                    refine ⟨10378423063814114778747149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6918948709209409852498099 10378423063814114778747149)
                    ·
                      refine ⟨3891908648930293042030181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10378423063814114778747149 3891908648930293042030181)
                      ·
                        rfl

theorem cell23_7579465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_7579465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579465 prefixEnd_7579465 := by exact prefixLift 7579465
  have htrace : WordTrace (prefixWord ++ tailWord_7579465) baseStart_7579465 baseEnd_7579465 := by
    simpa [prefixWord, tailWord_7579465, baseEnd_7579465] using wordTrace_append hprefix tailTrace_7579465
  have hstable : (prefixWord ++ tailWord_7579465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579465).length < 2 ^ (prefixWord ++ tailWord_7579465).sum := by decide
  have hdescent : baseEnd_7579465 < baseStart_7579465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579481 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_7579481 : Nat := 118140960795 + 7579481 * 2 ^ 59
def prefixEnd_7579481 : Nat := 4983230072969 + 3 ^ 40 * 7579481 * 2
def baseEnd_7579481 : Nat := 1297305621540254993143369

theorem tailTrace_7579481 : CollatzResearch.WordTrace tailWord_7579481 prefixEnd_7579481 1297305621540254993143369 := by
  unfold tailWord_7579481
  simp only [CollatzResearch.WordTrace]
  refine ⟨276446383053842284141706297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184297588702561522761137531 276446383053842284141706297)
  ·
    refine ⟨207334787290381713106279723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276446383053842284141706297 207334787290381713106279723)
    ·
      refine ⟨311002180935572569659419585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207334787290381713106279723 311002180935572569659419585)
      ·
        refine ⟨233251635701679427244564689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311002180935572569659419585 233251635701679427244564689)
        ·
          refine ⟨174938726776259570433423517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233251635701679427244564689 174938726776259570433423517)
          ·
            refine ⟨65602022541097338912533819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174938726776259570433423517 65602022541097338912533819)
            ·
              refine ⟨98403033811646008368800729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65602022541097338912533819 98403033811646008368800729)
              ·
                refine ⟨73802275358734506276600547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98403033811646008368800729 73802275358734506276600547)
                ·
                  refine ⟨110703413038101759414900821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73802275358734506276600547 110703413038101759414900821)
                  ·
                    refine ⟨1297305621540254993143369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110703413038101759414900821 1297305621540254993143369)
                    ·
                      rfl

theorem cell23_7579481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_7579481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579481 prefixEnd_7579481 := by exact prefixLift 7579481
  have htrace : WordTrace (prefixWord ++ tailWord_7579481) baseStart_7579481 baseEnd_7579481 := by
    simpa [prefixWord, tailWord_7579481, baseEnd_7579481] using wordTrace_append hprefix tailTrace_7579481
  have hstable : (prefixWord ++ tailWord_7579481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579481).length < 2 ^ (prefixWord ++ tailWord_7579481).sum := by decide
  have hdescent : baseEnd_7579481 < baseStart_7579481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579545 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 5]
def baseStart_7579545 : Nat := 118140960795 + 7579545 * 2 ^ 59
def prefixEnd_7579545 : Nat := 4983230072969 + 3 ^ 40 * 7579545 * 2
def baseEnd_7579545 : Nat := 432438858598072525447757

theorem tailTrace_7579545 : CollatzResearch.WordTrace tailWord_7579545 prefixEnd_7579545 432438858598072525447757 := by
  unfold tailWord_7579545
  simp only [CollatzResearch.WordTrace]
  refine ⟨276448717325610423072036089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184299144883740282048024059 276448717325610423072036089)
  ·
    refine ⟨207336537994207817304027067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276448717325610423072036089 207336537994207817304027067)
    ·
      refine ⟨311004806991311725956040601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207336537994207817304027067 311004806991311725956040601)
      ·
        refine ⟨233253605243483794467030451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311004806991311725956040601 233253605243483794467030451)
        ·
          refine ⟨349880407865225691700545677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233253605243483794467030451 349880407865225691700545677)
          ·
            refine ⟨131205152949459634387704629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349880407865225691700545677 131205152949459634387704629)
            ·
              refine ⟨12300483089011840723847309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131205152949459634387704629 12300483089011840723847309)
              ·
                refine ⟨4612681158379440271442741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12300483089011840723847309 4612681158379440271442741)
                ·
                  refine ⟨432438858598072525447757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4612681158379440271442741 432438858598072525447757)
                  ·
                    rfl

theorem cell23_7579545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 5].length) (baseStart_7579545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579545 prefixEnd_7579545 := by exact prefixLift 7579545
  have htrace : WordTrace (prefixWord ++ tailWord_7579545) baseStart_7579545 baseEnd_7579545 := by
    simpa [prefixWord, tailWord_7579545, baseEnd_7579545] using wordTrace_append hprefix tailTrace_7579545
  have hstable : (prefixWord ++ tailWord_7579545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579545).length < 2 ^ (prefixWord ++ tailWord_7579545).sum := by decide
  have hdescent : baseEnd_7579545 < baseStart_7579545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579578 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_7579578 : Nat := 118140960795 + 7579578 * 2 ^ 59
def prefixEnd_7579578 : Nat := 4983230072969 + 3 ^ 40 * 7579578 * 2
def baseEnd_7579578 : Nat := 3891966672244251099917161

theorem tailTrace_7579578 : CollatzResearch.WordTrace tailWord_7579578 prefixEnd_7579578 3891966672244251099917161 := by
  unfold tailWord_7579578
  simp only [CollatzResearch.WordTrace]
  refine ⟨69112480233622717426996847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184299947289660579805324925 69112480233622717426996847)
  ·
    refine ⟨103668720350434076140495271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69112480233622717426996847 103668720350434076140495271)
    ·
      refine ⟨155503080525651114210742907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103668720350434076140495271 155503080525651114210742907)
      ·
        refine ⟨233254620788476671316114361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155503080525651114210742907 233254620788476671316114361)
        ·
          refine ⟨174940965591357503487085771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233254620788476671316114361 174940965591357503487085771)
          ·
            refine ⟨262411448387036255230628657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174940965591357503487085771 262411448387036255230628657)
            ·
              refine ⟨196808586290277191422971493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262411448387036255230628657 196808586290277191422971493)
              ·
                refine ⟨36901609929426973391807155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196808586290277191422971493 36901609929426973391807155)
                ·
                  refine ⟨55352414894140460087710733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36901609929426973391807155 55352414894140460087710733)
                  ·
                    refine ⟨20757155585302672532891525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55352414894140460087710733 20757155585302672532891525)
                    ·
                      refine ⟨3891966672244251099917161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20757155585302672532891525 3891966672244251099917161)
                      ·
                        rfl

theorem cell23_7579578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_7579578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579578 prefixEnd_7579578 := by exact prefixLift 7579578
  have htrace : WordTrace (prefixWord ++ tailWord_7579578) baseStart_7579578 baseEnd_7579578 := by
    simpa [prefixWord, tailWord_7579578, baseEnd_7579578] using wordTrace_append hprefix tailTrace_7579578
  have hstable : (prefixWord ++ tailWord_7579578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579578).length < 2 ^ (prefixWord ++ tailWord_7579578).sum := by decide
  have hdescent : baseEnd_7579578 < baseStart_7579578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579595 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 4]
def baseStart_7579595 : Nat := 118140960795 + 7579595 * 2 ^ 59
def prefixEnd_7579595 : Nat := 4983230072969 + 3 ^ 40 * 7579595 * 2
def baseEnd_7579595 : Nat := 3891975401415377533404583

theorem tailTrace_7579595 : CollatzResearch.WordTrace tailWord_7579595 prefixEnd_7579595 3891975401415377533404583 := by
  unfold tailWord_7579595
  simp only [CollatzResearch.WordTrace]
  refine ⟨276450540975429281611356239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184300360650286187740904159 276450540975429281611356239)
  ·
    refine ⟨414675811463143922417034359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276450540975429281611356239 414675811463143922417034359)
    ·
      refine ⟨622013717194715883625551539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414675811463143922417034359 622013717194715883625551539)
      ·
        refine ⟨933020575792073825438327309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622013717194715883625551539 933020575792073825438327309)
        ·
          refine ⟨349882715922027684539372741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933020575792073825438327309 349882715922027684539372741)
          ·
            refine ⟨65603009235380190851132389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349882715922027684539372741 65603009235380190851132389)
            ·
              refine ⟨12300564231633785784587323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65603009235380190851132389 12300564231633785784587323)
              ·
                refine ⟨18450846347450678676880985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12300564231633785784587323 18450846347450678676880985)
                ·
                  refine ⟨13838134760588009007660739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18450846347450678676880985 13838134760588009007660739)
                  ·
                    refine ⟨20757202140882013511491109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13838134760588009007660739 20757202140882013511491109)
                    ·
                      refine ⟨3891975401415377533404583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20757202140882013511491109 3891975401415377533404583)
                      ·
                        rfl

theorem cell23_7579595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 4].length) (baseStart_7579595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579595 prefixEnd_7579595 := by exact prefixLift 7579595
  have htrace : WordTrace (prefixWord ++ tailWord_7579595) baseStart_7579595 baseEnd_7579595 := by
    simpa [prefixWord, tailWord_7579595, baseEnd_7579595] using wordTrace_append hprefix tailTrace_7579595
  have hstable : (prefixWord ++ tailWord_7579595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579595).length < 2 ^ (prefixWord ++ tailWord_7579595).sum := by decide
  have hdescent : baseEnd_7579595 < baseStart_7579595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579608 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_7579608 : Nat := 118140960795 + 7579608 * 2 ^ 59
def prefixEnd_7579608 : Nat := 4983230072969 + 3 ^ 40 * 7579608 * 2
def baseEnd_7579608 : Nat := 3891982076663885982542023

theorem tailTrace_7579608 : CollatzResearch.WordTrace tailWord_7579608 prefixEnd_7579608 3891982076663885982542023 := by
  unfold tailWord_7579608
  simp only [CollatzResearch.WordTrace]
  refine ⟨138225507562191092415789739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184300676749588123221052985 138225507562191092415789739)
  ·
    refine ⟨207338261343286638623684609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138225507562191092415789739 207338261343286638623684609)
    ·
      refine ⟨155503696007464978967763457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207338261343286638623684609 155503696007464978967763457)
      ·
        refine ⟨116627772005598734225822593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155503696007464978967763457 116627772005598734225822593)
        ·
          refine ⟨87470829004199050669366945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116627772005598734225822593 87470829004199050669366945)
          ·
            refine ⟨65603121753149288002025209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87470829004199050669366945 65603121753149288002025209)
            ·
              refine ⟨49202341314861966001518907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65603121753149288002025209 49202341314861966001518907)
              ·
                refine ⟨73803511972292949002278361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49202341314861966001518907 73803511972292949002278361)
                ·
                  refine ⟨55352633979219711751708771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73803511972292949002278361 55352633979219711751708771)
                  ·
                    refine ⟨83028950968829567627563157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55352633979219711751708771 83028950968829567627563157)
                    ·
                      refine ⟨3891982076663885982542023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83028950968829567627563157 3891982076663885982542023)
                      ·
                        rfl

theorem cell23_7579608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_7579608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579608 prefixEnd_7579608 := by exact prefixLift 7579608
  have htrace : WordTrace (prefixWord ++ tailWord_7579608) baseStart_7579608 baseEnd_7579608 := by
    simpa [prefixWord, tailWord_7579608, baseEnd_7579608] using wordTrace_append hprefix tailTrace_7579608
  have hstable : (prefixWord ++ tailWord_7579608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579608).length < 2 ^ (prefixWord ++ tailWord_7579608).sum := by decide
  have hdescent : baseEnd_7579608 < baseStart_7579608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579662 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7579662 : Nat := 118140960795 + 7579662 * 2 ^ 59
def prefixEnd_7579662 : Nat := 4983230072969 + 3 ^ 40 * 7579662 * 2
def baseEnd_7579662 : Nat := 3892009804619228771266775

theorem tailTrace_7579662 : CollatzResearch.WordTrace tailWord_7579662 prefixEnd_7579662 3892009804619228771266775 := by
  unfold tailWord_7579662
  simp only [CollatzResearch.WordTrace]
  refine ⟨34556623083273319006755655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184301989777457701369363493 34556623083273319006755655)
  ·
    refine ⟨51834934624909978510133483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34556623083273319006755655 51834934624909978510133483)
    ·
      refine ⟨77752401937364967765200225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51834934624909978510133483 77752401937364967765200225)
      ·
        refine ⟨58314301453023725823900169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77752401937364967765200225 58314301453023725823900169)
        ·
          refine ⟨43735726089767794367925127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58314301453023725823900169 43735726089767794367925127)
          ·
            refine ⟨65603589134651691551887691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43735726089767794367925127 65603589134651691551887691)
            ·
              refine ⟨98405383701977537327831537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65603589134651691551887691 98405383701977537327831537)
              ·
                refine ⟨73804037776483152995873653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98405383701977537327831537 73804037776483152995873653)
                ·
                  refine ⟨6919128541545295593363155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73804037776483152995873653 6919128541545295593363155)
                  ·
                    refine ⟨10378692812317943390044733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919128541545295593363155 10378692812317943390044733)
                    ·
                      refine ⟨3892009804619228771266775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10378692812317943390044733 3892009804619228771266775)
                      ·
                        rfl

theorem cell23_7579662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7579662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579662 prefixEnd_7579662 := by exact prefixLift 7579662
  have htrace : WordTrace (prefixWord ++ tailWord_7579662) baseStart_7579662 baseEnd_7579662 := by
    simpa [prefixWord, tailWord_7579662, baseEnd_7579662] using wordTrace_append hprefix tailTrace_7579662
  have hstable : (prefixWord ++ tailWord_7579662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579662).length < 2 ^ (prefixWord ++ tailWord_7579662).sum := by decide
  have hdescent : baseEnd_7579662 < baseStart_7579662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579669 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 6]
def baseStart_7579669 : Nat := 118140960795 + 7579669 * 2 ^ 59
def prefixEnd_7579669 : Nat := 4983230072969 + 3 ^ 40 * 7579669 * 2
def baseEnd_7579669 : Nat := 432445933220423360431027

theorem tailTrace_7579669 : CollatzResearch.WordTrace tailWord_7579669 prefixEnd_7579669 432445933220423360431027 := by
  unfold tailWord_7579669
  simp only [CollatzResearch.WordTrace]
  refine ⟨276453239977161192249550061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184302159984774128166366707 276453239977161192249550061)
  ·
    refine ⟨103669964991435447093581273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276453239977161192249550061 103669964991435447093581273)
    ·
      refine ⟨77752473743576585320185955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103669964991435447093581273 77752473743576585320185955)
      ·
        refine ⟨116628710615364877980278933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77752473743576585320185955 116628710615364877980278933)
        ·
          refine ⟨5466970810095228655325575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116628710615364877980278933 5466970810095228655325575)
          ·
            refine ⟨8200456215142842982988363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466970810095228655325575 8200456215142842982988363)
            ·
              refine ⟨12300684322714264474482545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200456215142842982988363 12300684322714264474482545)
              ·
                refine ⟨9225513242035698355861909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12300684322714264474482545 9225513242035698355861909)
                ·
                  refine ⟨432445933220423360431027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9225513242035698355861909 432445933220423360431027)
                  ·
                    rfl

theorem cell23_7579669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_7579669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579669 prefixEnd_7579669 := by exact prefixLift 7579669
  have htrace : WordTrace (prefixWord ++ tailWord_7579669) baseStart_7579669 baseEnd_7579669 := by
    simpa [prefixWord, tailWord_7579669, baseEnd_7579669] using wordTrace_append hprefix tailTrace_7579669
  have hstable : (prefixWord ++ tailWord_7579669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579669).length < 2 ^ (prefixWord ++ tailWord_7579669).sum := by decide
  have hdescent : baseEnd_7579669 < baseStart_7579669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579672 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 4, 3, 2]
def baseStart_7579672 : Nat := 118140960795 + 7579672 * 2 ^ 59
def prefixEnd_7579672 : Nat := 4983230072969 + 3 ^ 40 * 7579672 * 2
def baseEnd_7579672 : Nat := 3892014939425773732141729

theorem tailTrace_7579672 : CollatzResearch.WordTrace tailWord_7579672 prefixEnd_7579672 3892014939425773732141729 := by
  unfold tailWord_7579672
  simp only [CollatzResearch.WordTrace]
  refine ⟨138226674698075161880954635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184302232930766882507939513 138226674698075161880954635)
  ·
    refine ⟨207340012047112742821431953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138226674698075161880954635 207340012047112742821431953)
    ·
      refine ⟨155505009035334557116073965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207340012047112742821431953 155505009035334557116073965)
      ·
        refine ⟨58314378388250458918527737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155505009035334557116073965 58314378388250458918527737)
        ·
          refine ⟨43735783791187844188895803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58314378388250458918527737 43735783791187844188895803)
          ·
            refine ⟨65603675686781766283343705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43735783791187844188895803 65603675686781766283343705)
            ·
              refine ⟨49202756765086324712507779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65603675686781766283343705 49202756765086324712507779)
              ·
                refine ⟨73804135147629487068761669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49202756765086324712507779 73804135147629487068761669)
                ·
                  refine ⟨13838275340180528825392813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73804135147629487068761669 13838275340180528825392813)
                  ·
                    refine ⟨5189353252567698309522305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13838275340180528825392813 5189353252567698309522305)
                    ·
                      refine ⟨3892014939425773732141729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189353252567698309522305 3892014939425773732141729)
                      ·
                        rfl

theorem cell23_7579672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_7579672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579672 prefixEnd_7579672 := by exact prefixLift 7579672
  have htrace : WordTrace (prefixWord ++ tailWord_7579672) baseStart_7579672 baseEnd_7579672 := by
    simpa [prefixWord, tailWord_7579672, baseEnd_7579672] using wordTrace_append hprefix tailTrace_7579672
  have hstable : (prefixWord ++ tailWord_7579672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579672).length < 2 ^ (prefixWord ++ tailWord_7579672).sum := by decide
  have hdescent : baseEnd_7579672 < baseStart_7579672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579679 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 1, 1, 3]
def baseStart_7579679 : Nat := 118140960795 + 7579679 * 2 ^ 59
def prefixEnd_7579679 : Nat := 4983230072969 + 3 ^ 40 * 7579679 * 2
def baseEnd_7579679 : Nat := 3892018533790355204754197

theorem tailTrace_7579679 : CollatzResearch.WordTrace tailWord_7579679 prefixEnd_7579679 3892018533790355204754197 := by
  unfold tailWord_7579679
  simp only [CollatzResearch.WordTrace]
  refine ⟨276453604707124963957414091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184302403138083309304942727 276453604707124963957414091)
  ·
    refine ⟨414680407060687445936121137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276453604707124963957414091 414680407060687445936121137)
    ·
      refine ⟨311010305295515584452090853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414680407060687445936121137 311010305295515584452090853)
      ·
        refine ⟨58314432242909172084767035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311010305295515584452090853 58314432242909172084767035)
        ·
          refine ⟨87471648364363758127150553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58314432242909172084767035 87471648364363758127150553)
          ·
            refine ⟨65603736273272818595362915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87471648364363758127150553 65603736273272818595362915)
            ·
              refine ⟨98405604409909227893044373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65603736273272818595362915 98405604409909227893044373)
              ·
                refine ⟨4612762706714495057486455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98405604409909227893044373 4612762706714495057486455)
                ·
                  refine ⟨6919144060071742586229683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612762706714495057486455 6919144060071742586229683)
                  ·
                    refine ⟨10378716090107613879344525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919144060071742586229683 10378716090107613879344525)
                    ·
                      refine ⟨3892018533790355204754197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10378716090107613879344525 3892018533790355204754197)
                      ·
                        rfl

theorem cell23_7579679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_7579679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579679 prefixEnd_7579679 := by exact prefixLift 7579679
  have htrace : WordTrace (prefixWord ++ tailWord_7579679) baseStart_7579679 baseEnd_7579679 := by
    simpa [prefixWord, tailWord_7579679, baseEnd_7579679] using wordTrace_append hprefix tailTrace_7579679
  have hstable : (prefixWord ++ tailWord_7579679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579679).length < 2 ^ (prefixWord ++ tailWord_7579679).sum := by decide
  have hdescent : baseEnd_7579679 < baseStart_7579679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579713 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_7579713 : Nat := 118140960795 + 7579713 * 2 ^ 59
def prefixEnd_7579713 : Nat := 4983230072969 + 3 ^ 40 * 7579713 * 2
def baseEnd_7579713 : Nat := 3892035992132608071729041

theorem tailTrace_7579713 : CollatzResearch.WordTrace tailWord_7579713 prefixEnd_7579713 3892035992132608071729041 := by
  unfold tailWord_7579713
  simp only [CollatzResearch.WordTrace]
  refine ⟨276454844789001787764151793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184303229859334525176101195 276454844789001787764151793)
  ·
    refine ⟨207341133591751340823113845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276454844789001787764151793 207341133591751340823113845)
    ·
      refine ⟨19438231274226688202166923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207341133591751340823113845 19438231274226688202166923)
      ·
        refine ⟨29157346911340032303250385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19438231274226688202166923 29157346911340032303250385)
        ·
          refine ⟨21868010183505024227437789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29157346911340032303250385 21868010183505024227437789)
          ·
            refine ⟨8200503818814384085289171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21868010183505024227437789 8200503818814384085289171)
            ·
              refine ⟨12300755728221576127933757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200503818814384085289171 12300755728221576127933757)
              ·
                refine ⟨4612783398083091047975159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12300755728221576127933757 4612783398083091047975159)
                ·
                  refine ⟨6919175097124636571962739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612783398083091047975159 6919175097124636571962739)
                  ·
                    refine ⟨10378762645686954857944109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919175097124636571962739 10378762645686954857944109)
                    ·
                      refine ⟨3892035992132608071729041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10378762645686954857944109 3892035992132608071729041)
                      ·
                        rfl

theorem cell23_7579713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_7579713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579713 prefixEnd_7579713 := by exact prefixLift 7579713
  have htrace : WordTrace (prefixWord ++ tailWord_7579713) baseStart_7579713 baseEnd_7579713 := by
    simpa [prefixWord, tailWord_7579713, baseEnd_7579713] using wordTrace_append hprefix tailTrace_7579713
  have hstable : (prefixWord ++ tailWord_7579713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579713).length < 2 ^ (prefixWord ++ tailWord_7579713).sum := by decide
  have hdescent : baseEnd_7579713 < baseStart_7579713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579736 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 3, 2, 2]
def baseStart_7579736 : Nat := 118140960795 + 7579736 * 2 ^ 59
def prefixEnd_7579736 : Nat := 4983230072969 + 3 ^ 40 * 7579736 * 2
def baseEnd_7579736 : Nat := 3892047802187661481741435

theorem tailTrace_7579736 : CollatzResearch.WordTrace tailWord_7579736 prefixEnd_7579736 3892047802187661481741435 := by
  unfold tailWord_7579736
  simp only [CollatzResearch.WordTrace]
  refine ⟨138227841833959231346119531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184303789111945641794826041 138227841833959231346119531)
  ·
    refine ⟨207341762750938847019179297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138227841833959231346119531 207341762750938847019179297)
    ·
      refine ⟨155506322063204135264384473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207341762750938847019179297 155506322063204135264384473)
      ·
        refine ⟨116629741547403101448288355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155506322063204135264384473 116629741547403101448288355)
        ·
          refine ⟨174944612321104652172432533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116629741547403101448288355 174944612321104652172432533)
          ·
            refine ⟨8200528702551780570582775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174944612321104652172432533 8200528702551780570582775)
            ·
              refine ⟨12300793053827670855874163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200528702551780570582775 12300793053827670855874163)
              ·
                refine ⟨18451189580741506283811245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12300793053827670855874163 18451189580741506283811245)
                ·
                  refine ⟨6919196092778064856429217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18451189580741506283811245 6919196092778064856429217)
                  ·
                    refine ⟨5189397069583548642321913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6919196092778064856429217 5189397069583548642321913)
                    ·
                      refine ⟨3892047802187661481741435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189397069583548642321913 3892047802187661481741435)
                      ·
                        rfl

theorem cell23_7579736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_7579736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579736 prefixEnd_7579736 := by exact prefixLift 7579736
  have htrace : WordTrace (prefixWord ++ tailWord_7579736) baseStart_7579736 baseEnd_7579736 := by
    simpa [prefixWord, tailWord_7579736, baseEnd_7579736] using wordTrace_append hprefix tailTrace_7579736
  have hstable : (prefixWord ++ tailWord_7579736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579736).length < 2 ^ (prefixWord ++ tailWord_7579736).sum := by decide
  have hdescent : baseEnd_7579736 < baseStart_7579736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579746 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7579746 : Nat := 118140960795 + 7579746 * 2 ^ 59
def prefixEnd_7579746 : Nat := 4983230072969 + 3 ^ 40 * 7579746 * 2
def baseEnd_7579746 : Nat := 1297350978998068814205463

theorem tailTrace_7579746 : CollatzResearch.WordTrace tailWord_7579746 prefixEnd_7579746 1297350978998068814205463 := by
  unfold tailWord_7579746
  simp only [CollatzResearch.WordTrace]
  refine ⟨69114012099470558600025773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184304032265254822933402061 69114012099470558600025773)
  ·
    refine ⟨25917754537301459475009665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69114012099470558600025773 25917754537301459475009665)
    ·
      refine ⟨19438315902976094606257249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25917754537301459475009665 19438315902976094606257249)
      ·
        refine ⟨14578736927232070954692937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19438315902976094606257249 14578736927232070954692937)
        ·
          refine ⟨10934052695424053216019703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14578736927232070954692937 10934052695424053216019703)
          ·
            refine ⟨16401079043136079824029555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10934052695424053216019703 16401079043136079824029555)
            ·
              refine ⟨24601618564704119736044333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16401079043136079824029555 24601618564704119736044333)
              ·
                refine ⟨9225606961764044901016625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24601618564704119736044333 9225606961764044901016625)
                ·
                  refine ⟨6919205221323033675762469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9225606961764044901016625 6919205221323033675762469)
                  ·
                    refine ⟨1297350978998068814205463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6919205221323033675762469 1297350978998068814205463)
                    ·
                      rfl

theorem cell23_7579746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7579746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579746 prefixEnd_7579746 := by exact prefixLift 7579746
  have htrace : WordTrace (prefixWord ++ tailWord_7579746) baseStart_7579746 baseEnd_7579746 := by
    simpa [prefixWord, tailWord_7579746, baseEnd_7579746] using wordTrace_append hprefix tailTrace_7579746
  have hstable : (prefixWord ++ tailWord_7579746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579746).length < 2 ^ (prefixWord ++ tailWord_7579746).sum := by decide
  have hdescent : baseEnd_7579746 < baseStart_7579746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579785 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_7579785 : Nat := 118140960795 + 7579785 * 2 ^ 59
def prefixEnd_7579785 : Nat := 4983230072969 + 3 ^ 40 * 7579785 * 2
def baseEnd_7579785 : Nat := 1297357654246577263342903

theorem tailTrace_7579785 : CollatzResearch.WordTrace tailWord_7579785 prefixEnd_7579785 1297357654246577263342903 := by
  unfold tailWord_7579785
  simp only [CollatzResearch.WordTrace]
  refine ⟨276457470844740944060772809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184304980563160629373848539 276457470844740944060772809)
  ·
    refine ⟨207343103133555708045579607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276457470844740944060772809 207343103133555708045579607)
    ·
      refine ⟨311014654700333562068369411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207343103133555708045579607 311014654700333562068369411)
      ·
        refine ⟨466521982050500343102554117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311014654700333562068369411 466521982050500343102554117)
        ·
          refine ⟨87472871634468814331728897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466521982050500343102554117 87472871634468814331728897)
          ·
            refine ⟨65604653725851610748796673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87472871634468814331728897 65604653725851610748796673)
            ·
              refine ⟨49203490294388708061597505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65604653725851610748796673 49203490294388708061597505)
              ·
                refine ⟨36902617720791531046198129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49203490294388708061597505 36902617720791531046198129)
                ·
                  refine ⟨27676963290593648284648597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36902617720791531046198129 27676963290593648284648597)
                  ·
                    refine ⟨1297357654246577263342903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27676963290593648284648597 1297357654246577263342903)
                    ·
                      rfl

theorem cell23_7579785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_7579785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579785 prefixEnd_7579785 := by exact prefixLift 7579785
  have htrace : WordTrace (prefixWord ++ tailWord_7579785) baseStart_7579785 baseEnd_7579785 := by
    simpa [prefixWord, tailWord_7579785, baseEnd_7579785] using wordTrace_append hprefix tailTrace_7579785
  have hstable : (prefixWord ++ tailWord_7579785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579785).length < 2 ^ (prefixWord ++ tailWord_7579785).sum := by decide
  have hdescent : baseEnd_7579785 < baseStart_7579785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579786 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_7579786 : Nat := 118140960795 + 7579786 * 2 ^ 59
def prefixEnd_7579786 : Nat := 4983230072969 + 3 ^ 40 * 7579786 * 2
def baseEnd_7579786 : Nat := 3892073476220386286116205

theorem tailTrace_7579786 : CollatzResearch.WordTrace tailWord_7579786 prefixEnd_7579786 3892073476220386286116205 := by
  unfold tailWord_7579786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69114376829434330307889803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184305004878491547487706141 69114376829434330307889803)
  ·
    refine ⟨103671565244151495461834705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69114376829434330307889803 103671565244151495461834705)
    ·
      refine ⟨77753673933113621596376029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103671565244151495461834705 77753673933113621596376029)
      ·
        refine ⟨29157627724917608098641011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77753673933113621596376029 29157627724917608098641011)
        ·
          refine ⟨43736441587376412147961517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29157627724917608098641011 43736441587376412147961517)
          ·
            refine ⟨16401165595266154555485569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43736441587376412147961517 16401165595266154555485569)
            ·
              refine ⟨12300874196449615916614177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16401165595266154555485569 12300874196449615916614177)
              ·
                refine ⟨9225655647337211937460633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12300874196449615916614177 9225655647337211937460633)
                ·
                  refine ⟨6919241735502908953095475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9225655647337211937460633 6919241735502908953095475)
                  ·
                    refine ⟨10378862603254363429643213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919241735502908953095475 10378862603254363429643213)
                    ·
                      refine ⟨3892073476220386286116205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10378862603254363429643213 3892073476220386286116205)
                      ·
                        rfl

theorem cell23_7579786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_7579786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579786 prefixEnd_7579786 := by exact prefixLift 7579786
  have htrace : WordTrace (prefixWord ++ tailWord_7579786) baseStart_7579786 baseEnd_7579786 := by
    simpa [prefixWord, tailWord_7579786, baseEnd_7579786] using wordTrace_append hprefix tailTrace_7579786
  have hstable : (prefixWord ++ tailWord_7579786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579786).length < 2 ^ (prefixWord ++ tailWord_7579786).sum := by decide
  have hdescent : baseEnd_7579786 < baseStart_7579786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579792 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 3, 4, 2]
def baseStart_7579792 : Nat := 118140960795 + 7579792 * 2 ^ 59
def prefixEnd_7579792 : Nat := 4983230072969 + 3 ^ 40 * 7579792 * 2
def baseEnd_7579792 : Nat := 3892076557104313262641177

theorem tailTrace_7579792 : CollatzResearch.WordTrace tailWord_7579792 prefixEnd_7579792 3892076557104313262641177 := by
  unfold tailWord_7579792
  simp only [CollatzResearch.WordTrace]
  refine ⟨138228863077857792128138815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184305150770477056170851753 138228863077857792128138815)
  ·
    refine ⟨207343294616786688192208223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138228863077857792128138815 207343294616786688192208223)
    ·
      refine ⟨311014941925180032288312335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207343294616786688192208223 311014941925180032288312335)
      ·
        refine ⟨466522412887770048432468503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311014941925180032288312335 466522412887770048432468503)
        ·
          refine ⟨699783619331655072648702755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466522412887770048432468503 699783619331655072648702755)
          ·
            refine ⟨1049675428997482608973054133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699783619331655072648702755 1049675428997482608973054133)
            ·
              refine ⟨98407071468513994591223825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1049675428997482608973054133 98407071468513994591223825)
              ·
                refine ⟨73805303601385495943417869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98407071468513994591223825 73805303601385495943417869)
                ·
                  refine ⟨27676988850519560978781701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73805303601385495943417869 27676988850519560978781701)
                  ·
                    refine ⟨5189435409472417683521569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27676988850519560978781701 5189435409472417683521569)
                    ·
                      refine ⟨3892076557104313262641177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189435409472417683521569 3892076557104313262641177)
                      ·
                        rfl

theorem cell23_7579792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 4, 2].length) (baseStart_7579792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579792 prefixEnd_7579792 := by exact prefixLift 7579792
  have htrace : WordTrace (prefixWord ++ tailWord_7579792) baseStart_7579792 baseEnd_7579792 := by
    simpa [prefixWord, tailWord_7579792, baseEnd_7579792] using wordTrace_append hprefix tailTrace_7579792
  have hstable : (prefixWord ++ tailWord_7579792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579792).length < 2 ^ (prefixWord ++ tailWord_7579792).sum := by decide
  have hdescent : baseEnd_7579792 < baseStart_7579792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579809 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7579809 : Nat := 118140960795 + 7579809 * 2 ^ 59
def prefixEnd_7579809 : Nat := 4983230072969 + 3 ^ 40 * 7579809 * 2
def baseEnd_7579809 : Nat := 3892085286275439696128599

theorem tailTrace_7579809 : CollatzResearch.WordTrace tailWord_7579809 prefixEnd_7579809 3892085286275439696128599 := by
  unfold tailWord_7579809
  simp only [CollatzResearch.WordTrace]
  refine ⟨276458346196653996159646481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184305564131102664106430987 276458346196653996159646481)
  ·
    refine ⟨207343759647490497119734861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276458346196653996159646481 207343759647490497119734861)
    ·
      refine ⟨77753909867808936419900573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207343759647490497119734861 77753909867808936419900573)
      ·
        refine ⟨29157716200428351157462715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77753909867808936419900573 29157716200428351157462715)
        ·
          refine ⟨43736574300642526736194073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29157716200428351157462715 43736574300642526736194073)
          ·
            refine ⟨32802430725481895052145555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43736574300642526736194073 32802430725481895052145555)
            ·
              refine ⟨49203646088222842578218333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32802430725481895052145555 49203646088222842578218333)
              ·
                refine ⟨18451367283083565966831875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49203646088222842578218333 18451367283083565966831875)
                ·
                  refine ⟨27677050924625348950247813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18451367283083565966831875 27677050924625348950247813)
                  ·
                    refine ⟨5189447048367252928171465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27677050924625348950247813 5189447048367252928171465)
                    ·
                      refine ⟨3892085286275439696128599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189447048367252928171465 3892085286275439696128599)
                      ·
                        rfl

theorem cell23_7579809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7579809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579809 prefixEnd_7579809 := by exact prefixLift 7579809
  have htrace : WordTrace (prefixWord ++ tailWord_7579809) baseStart_7579809 baseEnd_7579809 := by
    simpa [prefixWord, tailWord_7579809, baseEnd_7579809] using wordTrace_append hprefix tailTrace_7579809
  have hstable : (prefixWord ++ tailWord_7579809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579809).length < 2 ^ (prefixWord ++ tailWord_7579809).sum := by decide
  have hdescent : baseEnd_7579809 < baseStart_7579809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579855 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_7579855 : Nat := 118140960795 + 7579855 * 2 ^ 59
def prefixEnd_7579855 : Nat := 4983230072969 + 3 ^ 40 * 7579855 * 2
def baseEnd_7579855 : Nat := 3892108906385546516153387

theorem tailTrace_7579855 : CollatzResearch.WordTrace tailWord_7579855 prefixEnd_7579855 3892108906385546516153387 := by
  unfold tailWord_7579855
  simp only [CollatzResearch.WordTrace]
  refine ⟨276460023954487346015821019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184306682636324897343880679 276460023954487346015821019)
  ·
    refine ⟨414690035931731019023731529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276460023954487346015821019 414690035931731019023731529)
    ·
      refine ⟨311017526948798264267798647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414690035931731019023731529 311017526948798264267798647)
      ·
        refine ⟨466526290423197396401697971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311017526948798264267798647 466526290423197396401697971)
        ·
          refine ⟨699789435634796094602546957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466526290423197396401697971 699789435634796094602546957)
          ·
            refine ⟨262421038363048535475955109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 699789435634796094602546957 262421038363048535475955109)
            ·
              refine ⟨49203944693071600401741583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262421038363048535475955109 49203944693071600401741583)
              ·
                refine ⟨73805917039607400602612375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49203944693071600401741583 73805917039607400602612375)
                ·
                  refine ⟨110708875559411100903918563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73805917039607400602612375 110708875559411100903918563)
                  ·
                    refine ⟨166063313339116651355877845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110708875559411100903918563 166063313339116651355877845)
                    ·
                      refine ⟨3892108906385546516153387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166063313339116651355877845 3892108906385546516153387)
                      ·
                        rfl

theorem cell23_7579855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_7579855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579855 prefixEnd_7579855 := by exact prefixLift 7579855
  have htrace : WordTrace (prefixWord ++ tailWord_7579855) baseStart_7579855 baseEnd_7579855 := by
    simpa [prefixWord, tailWord_7579855, baseEnd_7579855] using wordTrace_append hprefix tailTrace_7579855
  have hstable : (prefixWord ++ tailWord_7579855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579855).length < 2 ^ (prefixWord ++ tailWord_7579855).sum := by decide
  have hdescent : baseEnd_7579855 < baseStart_7579855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579882 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_7579882 : Nat := 118140960795 + 7579882 * 2 ^ 59
def prefixEnd_7579882 : Nat := 4983230072969 + 3 ^ 40 * 7579882 * 2
def baseEnd_7579882 : Nat := 3892122770363217910515763

theorem tailTrace_7579882 : CollatzResearch.WordTrace tailWord_7579882 prefixEnd_7579882 3892122770363217910515763 := by
  unfold tailWord_7579882
  simp only [CollatzResearch.WordTrace]
  refine ⟨69115252181347382406763475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184307339150259686418035933 69115252181347382406763475)
  ·
    refine ⟨103672878272021073610145213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69115252181347382406763475 103672878272021073610145213)
    ·
      refine ⟨38877329352007902603804455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103672878272021073610145213 38877329352007902603804455)
      ·
        refine ⟨58315994028011853905706683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38877329352007902603804455 58315994028011853905706683)
        ·
          refine ⟨87473991042017780858560025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58315994028011853905706683 87473991042017780858560025)
          ·
            refine ⟨65605493281513335643920019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87473991042017780858560025 65605493281513335643920019)
            ·
              refine ⟨98408239922270003465880029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65605493281513335643920019 98408239922270003465880029)
              ·
                refine ⟨36903089970851251299705011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98408239922270003465880029 36903089970851251299705011)
                ·
                  refine ⟨55354634956276876949557517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36903089970851251299705011 55354634956276876949557517)
                  ·
                    refine ⟨20757988108603828856084069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55354634956276876949557517 20757988108603828856084069)
                    ·
                      refine ⟨3892122770363217910515763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20757988108603828856084069 3892122770363217910515763)
                      ·
                        rfl

theorem cell23_7579882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_7579882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579882 prefixEnd_7579882 := by exact prefixLift 7579882
  have htrace : WordTrace (prefixWord ++ tailWord_7579882) baseStart_7579882 baseEnd_7579882 := by
    simpa [prefixWord, tailWord_7579882, baseEnd_7579882] using wordTrace_append hprefix tailTrace_7579882
  have hstable : (prefixWord ++ tailWord_7579882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579882).length < 2 ^ (prefixWord ++ tailWord_7579882).sum := by decide
  have hdescent : baseEnd_7579882 < baseStart_7579882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579936 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_7579936 : Nat := 118140960795 + 7579936 * 2 ^ 59
def prefixEnd_7579936 : Nat := 4983230072969 + 3 ^ 40 * 7579936 * 2
def baseEnd_7579936 : Nat := 3892150498318560699240515

theorem tailTrace_7579936 : CollatzResearch.WordTrace tailWord_7579936 prefixEnd_7579936 3892150498318560699240515 := by
  unfold tailWord_7579936
  simp only [CollatzResearch.WordTrace]
  refine ⟨138231489133596948424759831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184308652178129264566346441 138231489133596948424759831)
  ·
    refine ⟨207347233700395422637139747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138231489133596948424759831 207347233700395422637139747)
    ·
      refine ⟨311020850550593133955709621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207347233700395422637139747 311020850550593133955709621)
      ·
        refine ⟨29158204739118106308347777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311020850550593133955709621 29158204739118106308347777)
        ·
          refine ⟨21868653554338579731260833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29158204739118106308347777 21868653554338579731260833)
          ·
            refine ⟨16401490165753934798445625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21868653554338579731260833 16401490165753934798445625)
            ·
              refine ⟨12301117624315451098834219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16401490165753934798445625 12301117624315451098834219)
              ·
                refine ⟨18451676436473176648251329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12301117624315451098834219 18451676436473176648251329)
                ·
                  refine ⟨13838757327354882486188497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18451676436473176648251329 13838757327354882486188497)
                  ·
                    refine ⟨10379067995516161864641373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13838757327354882486188497 10379067995516161864641373)
                    ·
                      refine ⟨3892150498318560699240515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10379067995516161864641373 3892150498318560699240515)
                      ·
                        rfl

theorem cell23_7579936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_7579936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579936 prefixEnd_7579936 := by exact prefixLift 7579936
  have htrace : WordTrace (prefixWord ++ tailWord_7579936) baseStart_7579936 baseEnd_7579936 := by
    simpa [prefixWord, tailWord_7579936, baseEnd_7579936] using wordTrace_append hprefix tailTrace_7579936
  have hstable : (prefixWord ++ tailWord_7579936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579936).length < 2 ^ (prefixWord ++ tailWord_7579936).sum := by decide
  have hdescent : baseEnd_7579936 < baseStart_7579936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579956 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 6]
def baseStart_7579956 : Nat := 118140960795 + 7579956 * 2 ^ 59
def prefixEnd_7579956 : Nat := 4983230072969 + 3 ^ 40 * 7579956 * 2
def baseEnd_7579956 : Nat := 432462307547961180110047

theorem tailTrace_7579956 : CollatzResearch.WordTrace tailWord_7579956 prefixEnd_7579956 432462307547961180110047 := by
  unfold tailWord_7579956
  simp only [CollatzResearch.WordTrace]
  refine ⟨138231853863560720132623861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184309138484747626843498481 138231853863560720132623861)
  ·
    refine ⟨12959236299708817512433487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138231853863560720132623861 12959236299708817512433487)
    ·
      refine ⟨19438854449563226268650231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12959236299708817512433487 19438854449563226268650231)
      ·
        refine ⟨29158281674344839402975347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19438854449563226268650231 29158281674344839402975347)
        ·
          refine ⟨43737422511517259104463021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29158281674344839402975347 43737422511517259104463021)
          ·
            refine ⟨16401533441818972164173633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43737422511517259104463021 16401533441818972164173633)
            ·
              refine ⟨12301150081364229123130225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16401533441818972164173633 12301150081364229123130225)
              ·
                refine ⟨9225862561023171842347669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12301150081364229123130225 9225862561023171842347669)
                ·
                  refine ⟨432462307547961180110047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9225862561023171842347669 432462307547961180110047)
                  ·
                    rfl

theorem cell23_7579956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_7579956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579956 prefixEnd_7579956 := by exact prefixLift 7579956
  have htrace : WordTrace (prefixWord ++ tailWord_7579956) baseStart_7579956 baseEnd_7579956 := by
    simpa [prefixWord, tailWord_7579956, baseEnd_7579956] using wordTrace_append hprefix tailTrace_7579956
  have hstable : (prefixWord ++ tailWord_7579956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579956).length < 2 ^ (prefixWord ++ tailWord_7579956).sum := by decide
  have hdescent : baseEnd_7579956 < baseStart_7579956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7579992 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_7579992 : Nat := 118140960795 + 7579992 * 2 ^ 59
def prefixEnd_7579992 : Nat := 4983230072969 + 3 ^ 40 * 7579992 * 2
def baseEnd_7579992 : Nat := 3892179253235212480140257

theorem tailTrace_7579992 : CollatzResearch.WordTrace tailWord_7579992 prefixEnd_7579992 3892179253235212480140257 := by
  unfold tailWord_7579992
  simp only [CollatzResearch.WordTrace]
  refine ⟨138232510377495509206779115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184310013836660678942372153 138232510377495509206779115)
  ·
    refine ⟨207348765566243263810168673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138232510377495509206779115 207348765566243263810168673)
    ·
      refine ⟨155511574174682447857626505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207348765566243263810168673 155511574174682447857626505)
      ·
        refine ⟨116633680631011835893219879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155511574174682447857626505 116633680631011835893219879)
        ·
          refine ⟨174950520946517753839829819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116633680631011835893219879 174950520946517753839829819)
          ·
            refine ⟨262425781419776630759744729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174950520946517753839829819 262425781419776630759744729)
            ·
              refine ⟨196819336064832473069808547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262425781419776630759744729 196819336064832473069808547)
              ·
                refine ⟨295229004097248709604712821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196819336064832473069808547 295229004097248709604712821)
                ·
                  refine ⟨27677719134117066525441827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295229004097248709604712821 27677719134117066525441827)
                  ·
                    refine ⟨41516578701175599788162741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27677719134117066525441827 41516578701175599788162741)
                    ·
                      refine ⟨3892179253235212480140257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41516578701175599788162741 3892179253235212480140257)
                      ·
                        rfl

theorem cell23_7579992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_7579992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7579992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7579992 prefixEnd_7579992 := by exact prefixLift 7579992
  have htrace : WordTrace (prefixWord ++ tailWord_7579992) baseStart_7579992 baseEnd_7579992 := by
    simpa [prefixWord, tailWord_7579992, baseEnd_7579992] using wordTrace_append hprefix tailTrace_7579992
  have hstable : (prefixWord ++ tailWord_7579992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7579992).length < 2 ^ (prefixWord ++ tailWord_7579992).sum := by decide
  have hdescent : baseEnd_7579992 < baseStart_7579992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7579992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580000 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 1, 1, 3]
def baseStart_7580000 : Nat := 118140960795 + 7580000 * 2 ^ 59
def prefixEnd_7580000 : Nat := 4983230072969 + 3 ^ 40 * 7580000 * 2
def baseEnd_7580000 : Nat := 3892183361080448448840221

theorem tailTrace_7580000 : CollatzResearch.WordTrace tailWord_7580000 prefixEnd_7580000 3892183361080448448840221 := by
  unfold tailWord_7580000
  simp only [CollatzResearch.WordTrace]
  refine ⟨138232656269481017889924727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184310208359308023853232969 138232656269481017889924727)
  ·
    refine ⟨207348984404221526834887091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138232656269481017889924727 207348984404221526834887091)
    ·
      refine ⟨311023476606332290252330637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207348984404221526834887091 311023476606332290252330637)
      ·
        refine ⟨116633803727374608844623989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311023476606332290252330637 116633803727374608844623989)
        ·
          refine ⟨10934419099441369579183499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116633803727374608844623989 10934419099441369579183499)
          ·
            refine ⟨16401628649162054368775249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10934419099441369579183499 16401628649162054368775249)
            ·
              refine ⟨12301221486871540776581437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16401628649162054368775249 12301221486871540776581437)
              ·
                refine ⟨4612958057576827791218039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12301221486871540776581437 4612958057576827791218039)
                ·
                  refine ⟨6919437086365241686827059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612958057576827791218039 6919437086365241686827059)
                  ·
                    refine ⟨10379155629547862530240589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919437086365241686827059 10379155629547862530240589)
                    ·
                      refine ⟨3892183361080448448840221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10379155629547862530240589 3892183361080448448840221)
                      ·
                        rfl

theorem cell23_7580000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_7580000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580000 prefixEnd_7580000 := by exact prefixLift 7580000
  have htrace : WordTrace (prefixWord ++ tailWord_7580000) baseStart_7580000 baseEnd_7580000 := by
    simpa [prefixWord, tailWord_7580000, baseEnd_7580000] using wordTrace_append hprefix tailTrace_7580000
  have hstable : (prefixWord ++ tailWord_7580000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580000).length < 2 ^ (prefixWord ++ tailWord_7580000).sum := by decide
  have hdescent : baseEnd_7580000 < baseStart_7580000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580016 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 2, 4]
def baseStart_7580016 : Nat := 118140960795 + 7580016 * 2 ^ 59
def prefixEnd_7580016 : Nat := 4983230072969 + 3 ^ 40 * 7580016 * 2
def baseEnd_7580016 : Nat := 1297397192256973462080049

theorem tailTrace_7580016 : CollatzResearch.WordTrace tailWord_7580016 prefixEnd_7580016 1297397192256973462080049 := by
  unfold tailWord_7580016
  simp only [CollatzResearch.WordTrace]
  refine ⟨138232948053452035256215951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184310597404602713674954601 138232948053452035256215951)
  ·
    refine ⟨207349422080178052884323927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138232948053452035256215951 207349422080178052884323927)
    ·
      refine ⟨311024133120267079326485891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207349422080178052884323927 311024133120267079326485891)
      ·
        refine ⟨466536199680400618989728837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311024133120267079326485891 466536199680400618989728837)
        ·
          refine ⟨87475537440075116060574157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466536199680400618989728837 87475537440075116060574157)
          ·
            refine ⟨32803326540028168522715309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87475537440075116060574157 32803326540028168522715309)
            ·
              refine ⟨12301247452510563196018241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32803326540028168522715309 12301247452510563196018241)
              ·
                refine ⟨9225935589382922397013681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12301247452510563196018241 9225935589382922397013681)
                ·
                  refine ⟨6919451692037191797760261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9225935589382922397013681 6919451692037191797760261)
                  ·
                    refine ⟨1297397192256973462080049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6919451692037191797760261 1297397192256973462080049)
                    ·
                      rfl

theorem cell23_7580016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_7580016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580016 prefixEnd_7580016 := by exact prefixLift 7580016
  have htrace : WordTrace (prefixWord ++ tailWord_7580016) baseStart_7580016 baseEnd_7580016 := by
    simpa [prefixWord, tailWord_7580016, baseEnd_7580016] using wordTrace_append hprefix tailTrace_7580016
  have hstable : (prefixWord ++ tailWord_7580016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580016).length < 2 ^ (prefixWord ++ tailWord_7580016).sum := by decide
  have hdescent : baseEnd_7580016 < baseStart_7580016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580046 : List Nat := [4, 1, 1, 4, 1, 1, 4, 7]
def baseStart_7580046 : Nat := 118140960795 + 7580046 * 2 ^ 59
def prefixEnd_7580046 : Nat := 4983230072969 + 3 ^ 40 * 7580046 * 2
def baseEnd_7580046 : Nat := 144155814118168713661667

theorem tailTrace_7580046 : CollatzResearch.WordTrace tailWord_7580046 prefixEnd_7580046 144155814118168713661667 := by
  unfold tailWord_7580046
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558373787099423204502999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184311326864530257090682661 34558373787099423204502999)
  ·
    refine ⟨51837560680649134806754499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34558373787099423204502999 51837560680649134806754499)
    ·
      refine ⟨77756341020973702210131749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51837560680649134806754499 77756341020973702210131749)
      ·
        refine ⟨14579313941432569164399703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77756341020973702210131749 14579313941432569164399703)
        ·
          refine ⟨21868970912148853746599555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14579313941432569164399703 21868970912148853746599555)
          ·
            refine ⟨32803456368223280619899333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21868970912148853746599555 32803456368223280619899333)
            ·
              refine ⟨6150648069041865116231125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32803456368223280619899333 6150648069041865116231125)
              ·
                refine ⟨144155814118168713661667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6150648069041865116231125 144155814118168713661667)
                ·
                  rfl

theorem cell23_7580046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_7580046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580046 prefixEnd_7580046 := by exact prefixLift 7580046
  have htrace : WordTrace (prefixWord ++ tailWord_7580046) baseStart_7580046 baseEnd_7580046 := by
    simpa [prefixWord, tailWord_7580046, baseEnd_7580046] using wordTrace_append hprefix tailTrace_7580046
  have hstable : (prefixWord ++ tailWord_7580046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580046).length < 2 ^ (prefixWord ++ tailWord_7580046).sum := by decide
  have hdescent : baseEnd_7580046 < baseStart_7580046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580084 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7580084 : Nat := 118140960795 + 7580084 * 2 ^ 59
def prefixEnd_7580084 : Nat := 4983230072969 + 3 ^ 40 * 7580084 * 2
def baseEnd_7580084 : Nat := 1297408831151808706729945

theorem tailTrace_7580084 : CollatzResearch.WordTrace tailWord_7580084 prefixEnd_7580084 1297408831151808706729945 := by
  unfold tailWord_7580084
  simp only [CollatzResearch.WordTrace]
  refine ⟨138234188135328859062953653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184312250847105145417271537 138234188135328859062953653)
  ·
    refine ⟨12959455137687080537151905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138234188135328859062953653 12959455137687080537151905)
    ·
      refine ⟨9719591353265310402863929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12959455137687080537151905 9719591353265310402863929)
      ·
        refine ⟨7289693514948982802147947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9719591353265310402863929 7289693514948982802147947)
        ·
          refine ⟨10934540272423474203221921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7289693514948982802147947 10934540272423474203221921)
          ·
            refine ⟨8200905204317605652416441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10934540272423474203221921 8200905204317605652416441)
            ·
              refine ⟨6150678903238204239312331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8200905204317605652416441 6150678903238204239312331)
              ·
                refine ⟨9226018354857306358968497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150678903238204239312331 9226018354857306358968497)
                ·
                  refine ⟨6919513766142979769226373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9226018354857306358968497 6919513766142979769226373)
                  ·
                    refine ⟨1297408831151808706729945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6919513766142979769226373 1297408831151808706729945)
                    ·
                      rfl

theorem cell23_7580084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7580084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580084 prefixEnd_7580084 := by exact prefixLift 7580084
  have htrace : WordTrace (prefixWord ++ tailWord_7580084) baseStart_7580084 baseEnd_7580084 := by
    simpa [prefixWord, tailWord_7580084, baseEnd_7580084] using wordTrace_append hprefix tailTrace_7580084
  have hstable : (prefixWord ++ tailWord_7580084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580084).length < 2 ^ (prefixWord ++ tailWord_7580084).sum := by decide
  have hdescent : baseEnd_7580084 < baseStart_7580084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580096 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 1, 4, 2]
def baseStart_7580096 : Nat := 118140960795 + 7580096 * 2 ^ 59
def prefixEnd_7580096 : Nat := 4983230072969 + 3 ^ 40 * 7580096 * 2
def baseEnd_7580096 : Nat := 3892232655223280073239779

theorem tailTrace_7580096 : CollatzResearch.WordTrace tailWord_7580096 prefixEnd_7580096 3892232655223280073239779 := by
  unfold tailWord_7580096
  simp only [CollatzResearch.WordTrace]
  refine ⟨138234406973307122087672071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184312542631076162783562761 138234406973307122087672071)
  ·
    refine ⟨207351610459960683131508107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138234406973307122087672071 207351610459960683131508107)
    ·
      refine ⟨311027415689941024697262161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207351610459960683131508107 311027415689941024697262161)
      ·
        refine ⟨233270561767455768522946621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311027415689941024697262161 233270561767455768522946621)
        ·
          refine ⟨87476460662795913196104983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233270561767455768522946621 87476460662795913196104983)
          ·
            refine ⟨131214690994193869794157475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87476460662795913196104983 131214690994193869794157475)
            ·
              refine ⟨196822036491290804691236213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131214690994193869794157475 196822036491290804691236213)
              ·
                refine ⟨18452065921058512939803395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196822036491290804691236213 18452065921058512939803395)
                ·
                  refine ⟨27678098881587769409705093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18452065921058512939803395 27678098881587769409705093)
                  ·
                    refine ⟨5189643540297706764319705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27678098881587769409705093 5189643540297706764319705)
                    ·
                      refine ⟨3892232655223280073239779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189643540297706764319705 3892232655223280073239779)
                      ·
                        rfl

theorem cell23_7580096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_7580096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580096 prefixEnd_7580096 := by exact prefixLift 7580096
  have htrace : WordTrace (prefixWord ++ tailWord_7580096) baseStart_7580096 baseEnd_7580096 := by
    simpa [prefixWord, tailWord_7580096, baseEnd_7580096] using wordTrace_append hprefix tailTrace_7580096
  have hstable : (prefixWord ++ tailWord_7580096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580096).length < 2 ^ (prefixWord ++ tailWord_7580096).sum := by decide
  have hdescent : baseEnd_7580096 < baseStart_7580096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580100 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7580100 : Nat := 118140960795 + 7580100 * 2 ^ 59
def prefixEnd_7580100 : Nat := 4983230072969 + 3 ^ 40 * 7580100 * 2
def baseEnd_7580100 : Nat := 3892234709145898057589761

theorem tailTrace_7580100 : CollatzResearch.WordTrace tailWord_7580100 prefixEnd_7580100 3892234709145898057589761 := by
  unfold tailWord_7580100
  simp only [CollatzResearch.WordTrace]
  refine ⟨138234479919299876429244877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184312639892399835238993169 138234479919299876429244877)
  ·
    refine ⟨51837929969737453660966829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138234479919299876429244877 51837929969737453660966829)
    ·
      refine ⟨19439223738651545122862561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51837929969737453660966829 19439223738651545122862561)
      ·
        refine ⟨14579417803988658842146921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19439223738651545122862561 14579417803988658842146921)
        ·
          refine ⟨10934563352991494131610191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14579417803988658842146921 10934563352991494131610191)
          ·
            refine ⟨16401845029487241197415287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10934563352991494131610191 16401845029487241197415287)
            ·
              refine ⟨24602767544230861796122931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16401845029487241197415287 24602767544230861796122931)
              ·
                refine ⟨36904151316346292694184397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24602767544230861796122931 36904151316346292694184397)
                ·
                  refine ⟨13839056743629859760319149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36904151316346292694184397 13839056743629859760319149)
                  ·
                    refine ⟨5189646278861197410119681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13839056743629859760319149 5189646278861197410119681)
                    ·
                      refine ⟨3892234709145898057589761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189646278861197410119681 3892234709145898057589761)
                      ·
                        rfl

theorem cell23_7580100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7580100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580100 prefixEnd_7580100 := by exact prefixLift 7580100
  have htrace : WordTrace (prefixWord ++ tailWord_7580100) baseStart_7580100 baseEnd_7580100 := by
    simpa [prefixWord, tailWord_7580100, baseEnd_7580100] using wordTrace_append hprefix tailTrace_7580100
  have hstable : (prefixWord ++ tailWord_7580100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580100).length < 2 ^ (prefixWord ++ tailWord_7580100).sum := by decide
  have hdescent : baseEnd_7580100 < baseStart_7580100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580116 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7580116 : Nat := 118140960795 + 7580116 * 2 ^ 59
def prefixEnd_7580116 : Nat := 4983230072969 + 3 ^ 40 * 7580116 * 2
def baseEnd_7580116 : Nat := 3892242924836369994989687

theorem tailTrace_7580116 : CollatzResearch.WordTrace tailWord_7580116 prefixEnd_7580116 3892242924836369994989687 := by
  unfold tailWord_7580116
  simp only [CollatzResearch.WordTrace]
  refine ⟨138234771703270893795536101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184313028937694525060714801 138234771703270893795536101)
  ·
    refine ⟨25919019694363292586663019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138234771703270893795536101 25919019694363292586663019)
    ·
      refine ⟨38878529541544938879994529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25919019694363292586663019 38878529541544938879994529)
      ·
        refine ⟨29158897156158704159995897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38878529541544938879994529 29158897156158704159995897)
        ·
          refine ⟨21869172867119028119996923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29158897156158704159995897 21869172867119028119996923)
          ·
            refine ⟨32803759300678542179995385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21869172867119028119996923 32803759300678542179995385)
            ·
              refine ⟨24602819475508906634996539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32803759300678542179995385 24602819475508906634996539)
              ·
                refine ⟨36904229213263359952494809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24602819475508906634996539 36904229213263359952494809)
                ·
                  refine ⟨27678171909947519964371107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36904229213263359952494809 27678171909947519964371107)
                  ·
                    refine ⟨41517257864921279946556661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27678171909947519964371107 41517257864921279946556661)
                    ·
                      refine ⟨3892242924836369994989687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41517257864921279946556661 3892242924836369994989687)
                      ·
                        rfl

theorem cell23_7580116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7580116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580116 prefixEnd_7580116 := by exact prefixLift 7580116
  have htrace : WordTrace (prefixWord ++ tailWord_7580116) baseStart_7580116 baseEnd_7580116 := by
    simpa [prefixWord, tailWord_7580116, baseEnd_7580116] using wordTrace_append hprefix tailTrace_7580116
  have hstable : (prefixWord ++ tailWord_7580116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580116).length < 2 ^ (prefixWord ++ tailWord_7580116).sum := by decide
  have hdescent : baseEnd_7580116 < baseStart_7580116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580156 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_7580156 : Nat := 118140960795 + 7580156 * 2 ^ 59
def prefixEnd_7580156 : Nat := 4983230072969 + 3 ^ 40 * 7580156 * 2
def baseEnd_7580156 : Nat := 3892263464062549838489503

theorem tailTrace_7580156 : CollatzResearch.WordTrace tailWord_7580156 prefixEnd_7580156 3892263464062549838489503 := by
  unfold tailWord_7580156
  simp only [CollatzResearch.WordTrace]
  refine ⟨138235501163198437211264161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184314001550931249615018881 138235501163198437211264161)
  ·
    refine ⟨103676625872398827908448121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138235501163198437211264161 103676625872398827908448121)
    ·
      refine ⟨77757469404299120931336091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103676625872398827908448121 77757469404299120931336091)
      ·
        refine ⟨116636204106448681397004137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77757469404299120931336091 116636204106448681397004137)
        ·
          refine ⟨87477153079836511047753103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116636204106448681397004137 87477153079836511047753103)
          ·
            refine ⟨131215729619754766571629655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87477153079836511047753103 131215729619754766571629655)
            ·
              refine ⟨196823594429632149857444483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131215729619754766571629655 196823594429632149857444483)
              ·
                refine ⟨295235391644448224786166725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196823594429632149857444483 295235391644448224786166725)
                ·
                  refine ⟨55356635933334042147406261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295235391644448224786166725 55356635933334042147406261)
                  ·
                    refine ⟨5189684618750066451319337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55356635933334042147406261 5189684618750066451319337)
                    ·
                      refine ⟨3892263464062549838489503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189684618750066451319337 3892263464062549838489503)
                      ·
                        rfl

theorem cell23_7580156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_7580156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580156 prefixEnd_7580156 := by exact prefixLift 7580156
  have htrace : WordTrace (prefixWord ++ tailWord_7580156) baseStart_7580156 baseEnd_7580156 := by
    simpa [prefixWord, tailWord_7580156, baseEnd_7580156] using wordTrace_append hprefix tailTrace_7580156
  have hstable : (prefixWord ++ tailWord_7580156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580156).length < 2 ^ (prefixWord ++ tailWord_7580156).sum := by decide
  have hdescent : baseEnd_7580156 < baseStart_7580156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580186 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_7580186 : Nat := 118140960795 + 7580186 * 2 ^ 59
def prefixEnd_7580186 : Nat := 4983230072969 + 3 ^ 40 * 7580186 * 2
def baseEnd_7580186 : Nat := 3892278868482184721114365

theorem tailTrace_7580186 : CollatzResearch.WordTrace tailWord_7580186 prefixEnd_7580186 3892278868482184721114365 := by
  unfold tailWord_7580186
  simp only [CollatzResearch.WordTrace]
  refine ⟨69118024129072047386530103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184314731010858793030746941 69118024129072047386530103)
  ·
    refine ⟨103677036193608071079795155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69118024129072047386530103 103677036193608071079795155)
    ·
      refine ⟨155515554290412106619692733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103677036193608071079795155 155515554290412106619692733)
      ·
        refine ⟨58318332858904539982384775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155515554290412106619692733 58318332858904539982384775)
        ·
          refine ⟨87477499288356809973577163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58318332858904539982384775 87477499288356809973577163)
          ·
            refine ⟨131216248932535214960365745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87477499288356809973577163 131216248932535214960365745)
            ·
              refine ⟨98412186699401411220274309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131216248932535214960365745 98412186699401411220274309)
              ·
                refine ⟨18452285006137764603801433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98412186699401411220274309 18452285006137764603801433)
                ·
                  refine ⟨13839213754603323452851075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18452285006137764603801433 13839213754603323452851075)
                  ·
                    refine ⟨20758820631904985179276613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13839213754603323452851075 20758820631904985179276613)
                    ·
                      refine ⟨3892278868482184721114365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20758820631904985179276613 3892278868482184721114365)
                      ·
                        rfl

theorem cell23_7580186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_7580186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580186 prefixEnd_7580186 := by exact prefixLift 7580186
  have htrace : WordTrace (prefixWord ++ tailWord_7580186) baseStart_7580186 baseEnd_7580186 := by
    simpa [prefixWord, tailWord_7580186, baseEnd_7580186] using wordTrace_append hprefix tailTrace_7580186
  have hstable : (prefixWord ++ tailWord_7580186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580186).length < 2 ^ (prefixWord ++ tailWord_7580186).sum := by decide
  have hdescent : baseEnd_7580186 < baseStart_7580186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580249 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_7580249 : Nat := 118140960795 + 7580249 * 2 ^ 59
def prefixEnd_7580249 : Nat := 4983230072969 + 3 ^ 40 * 7580249 * 2
def baseEnd_7580249 : Nat := 3892311217763417974626575

theorem tailTrace_7580249 : CollatzResearch.WordTrace tailWord_7580249 prefixEnd_7580249 3892311217763417974626575 := by
  unfold tailWord_7580249
  simp only [CollatzResearch.WordTrace]
  refine ⟨276474394315059951305663801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184316262876706634203775867 276474394315059951305663801)
  ·
    refine ⟨207355795736294963479247851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276474394315059951305663801 207355795736294963479247851)
    ·
      refine ⟨311033693604442445218871777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207355795736294963479247851 311033693604442445218871777)
      ·
        refine ⟨233275270203331833914153833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311033693604442445218871777 233275270203331833914153833)
        ·
          refine ⟨174956452652498875435615375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233275270203331833914153833 174956452652498875435615375)
          ·
            refine ⟨262434678978748313153423063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174956452652498875435615375 262434678978748313153423063)
            ·
              refine ⟨393652018468122469730134595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262434678978748313153423063 393652018468122469730134595)
              ·
                refine ⟨590478027702183704595201893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393652018468122469730134595 590478027702183704595201893)
                ·
                  refine ⟨110714630194159444611600355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590478027702183704595201893 110714630194159444611600355)
                  ·
                    refine ⟨166071945291239166917400533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110714630194159444611600355 166071945291239166917400533)
                    ·
                      refine ⟨3892311217763417974626575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166071945291239166917400533 3892311217763417974626575)
                      ·
                        rfl

theorem cell23_7580249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_7580249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580249 prefixEnd_7580249 := by exact prefixLift 7580249
  have htrace : WordTrace (prefixWord ++ tailWord_7580249) baseStart_7580249 baseEnd_7580249 := by
    simpa [prefixWord, tailWord_7580249, baseEnd_7580249] using wordTrace_append hprefix tailTrace_7580249
  have hstable : (prefixWord ++ tailWord_7580249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580249).length < 2 ^ (prefixWord ++ tailWord_7580249).sum := by decide
  have hdescent : baseEnd_7580249 < baseStart_7580249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580263 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_7580263 : Nat := 118140960795 + 7580263 * 2 ^ 59
def prefixEnd_7580263 : Nat := 4983230072969 + 3 ^ 40 * 7580263 * 2
def baseEnd_7580263 : Nat := 3892318406492580919851511

theorem tailTrace_7580263 : CollatzResearch.WordTrace tailWord_7580263 prefixEnd_7580263 3892318406492580919851511 := by
  unfold tailWord_7580263
  simp only [CollatzResearch.WordTrace]
  refine ⟨276474904937009231696673443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184316603291339487797782295 276474904937009231696673443)
  ·
    refine ⟨414712357405513847545010165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276474904937009231696673443 414712357405513847545010165)
    ·
      refine ⟨38879283506766923207344703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 414712357405513847545010165 38879283506766923207344703)
      ·
        refine ⟨58318925260150384811017055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38879283506766923207344703 58318925260150384811017055)
        ·
          refine ⟨87478387890225577216525583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58318925260150384811017055 87478387890225577216525583)
          ·
            refine ⟨131217581835338365824788375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87478387890225577216525583 131217581835338365824788375)
            ·
              refine ⟨196826372753007548737182563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131217581835338365824788375 196826372753007548737182563)
              ·
                refine ⟨295239559129511323105773845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196826372753007548737182563 295239559129511323105773845)
                ·
                  refine ⟨13839354334195843270583149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 295239559129511323105773845 13839354334195843270583149)
                  ·
                    refine ⟨5189757875323441226468681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13839354334195843270583149 5189757875323441226468681)
                    ·
                      refine ⟨3892318406492580919851511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189757875323441226468681 3892318406492580919851511)
                      ·
                        rfl

theorem cell23_7580263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_7580263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580263 prefixEnd_7580263 := by exact prefixLift 7580263
  have htrace : WordTrace (prefixWord ++ tailWord_7580263) baseStart_7580263 baseEnd_7580263 := by
    simpa [prefixWord, tailWord_7580263, baseEnd_7580263] using wordTrace_append hprefix tailTrace_7580263
  have hstable : (prefixWord ++ tailWord_7580263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580263).length < 2 ^ (prefixWord ++ tailWord_7580263).sum := by decide
  have hdescent : baseEnd_7580263 < baseStart_7580263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580360 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_7580360 : Nat := 118140960795 + 7580360 * 2 ^ 59
def prefixEnd_7580360 : Nat := 4983230072969 + 3 ^ 40 * 7580360 * 2
def baseEnd_7580360 : Nat := 3892368214116067040338565

theorem tailTrace_7580360 : CollatzResearch.WordTrace tailWord_7580360 prefixEnd_7580360 3892368214116067040338565 := by
  unfold tailWord_7580360
  simp only [CollatzResearch.WordTrace]
  refine ⟨138239221408828908631477267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184318961878438544841969689 138239221408828908631477267)
  ·
    refine ⟨207358832113243362947215901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138239221408828908631477267 207358832113243362947215901)
    ·
      refine ⟨77759562042466261105205963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207358832113243362947215901 77759562042466261105205963)
      ·
        refine ⟨116639343063699391657808945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77759562042466261105205963 116639343063699391657808945)
        ·
          refine ⟨87479507297774543743356709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116639343063699391657808945 87479507297774543743356709)
          ·
            refine ⟨16402407618332726951879383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87479507297774543743356709 16402407618332726951879383)
            ·
              refine ⟨24603611427499090427819075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16402407618332726951879383 24603611427499090427819075)
              ·
                refine ⟨36905417141248635641728613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24603611427499090427819075 36905417141248635641728613)
                ·
                  refine ⟨6919765713984119182824115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36905417141248635641728613 6919765713984119182824115)
                  ·
                    refine ⟨10379648570976178774236173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919765713984119182824115 10379648570976178774236173)
                    ·
                      refine ⟨3892368214116067040338565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10379648570976178774236173 3892368214116067040338565)
                      ·
                        rfl

theorem cell23_7580360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_7580360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580360 prefixEnd_7580360 := by exact prefixLift 7580360
  have htrace : WordTrace (prefixWord ++ tailWord_7580360) baseStart_7580360 baseEnd_7580360 := by
    simpa [prefixWord, tailWord_7580360, baseEnd_7580360] using wordTrace_append hprefix tailTrace_7580360
  have hstable : (prefixWord ++ tailWord_7580360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580360).length < 2 ^ (prefixWord ++ tailWord_7580360).sum := by decide
  have hdescent : baseEnd_7580360 < baseStart_7580360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580377 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 2, 1, 3]
def baseStart_7580377 : Nat := 118140960795 + 7580377 * 2 ^ 59
def prefixEnd_7580377 : Nat := 4983230072969 + 3 ^ 40 * 7580377 * 2
def baseEnd_7580377 : Nat := 3892376943287193473825987

theorem tailTrace_7580377 : CollatzResearch.WordTrace tailWord_7580377 prefixEnd_7580377 3892376943287193473825987 := by
  unfold tailWord_7580377
  simp only [CollatzResearch.WordTrace]
  refine ⟨276479062858596229166323385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184319375239064152777548923 276479062858596229166323385)
  ·
    refine ⟨207359297143947171874742539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276479062858596229166323385 207359297143947171874742539)
    ·
      refine ⟨311038945715920757812113809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207359297143947171874742539 311038945715920757812113809)
      ·
        refine ⟨233279209286940568359085357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311038945715920757812113809 233279209286940568359085357)
        ·
          refine ⟨87479703482602713134657009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233279209286940568359085357 87479703482602713134657009)
          ·
            refine ⟨65609777611952034850992757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87479703482602713134657009 65609777611952034850992757)
            ·
              refine ⟨6150916651120503267280571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65609777611952034850992757 6150916651120503267280571)
              ·
                refine ⟨9226374976680754900920857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150916651120503267280571 9226374976680754900920857)
                ·
                  refine ⟨6919781232510566175690643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9226374976680754900920857 6919781232510566175690643)
                  ·
                    refine ⟨10379671848765849263535965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919781232510566175690643 10379671848765849263535965)
                    ·
                      refine ⟨3892376943287193473825987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10379671848765849263535965 3892376943287193473825987)
                      ·
                        rfl

theorem cell23_7580377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_7580377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580377 prefixEnd_7580377 := by exact prefixLift 7580377
  have htrace : WordTrace (prefixWord ++ tailWord_7580377) baseStart_7580377 baseEnd_7580377 := by
    simpa [prefixWord, tailWord_7580377, baseEnd_7580377] using wordTrace_append hprefix tailTrace_7580377
  have hstable : (prefixWord ++ tailWord_7580377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580377).length < 2 ^ (prefixWord ++ tailWord_7580377).sum := by decide
  have hdescent : baseEnd_7580377 < baseStart_7580377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580387 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7580387 : Nat := 118140960795 + 7580387 * 2 ^ 59
def prefixEnd_7580387 : Nat := 4983230072969 + 3 ^ 40 * 7580387 * 2
def baseEnd_7580387 : Nat := 3892382078093738434700941

theorem tailTrace_7580387 : CollatzResearch.WordTrace tailWord_7580387 prefixEnd_7580387 3892382078093738434700941 := by
  unfold tailWord_7580387
  simp only [CollatzResearch.WordTrace]
  refine ⟨276479427588560000874187415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184319618392373333916124943 276479427588560000874187415)
  ·
    refine ⟨414719141382840001311281123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276479427588560000874187415 414719141382840001311281123)
    ·
      refine ⟨622078712074260001966921685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414719141382840001311281123 622078712074260001966921685)
      ·
        refine ⟨14579969814240468796099727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 622078712074260001966921685 14579969814240468796099727)
        ·
          refine ⟨21869954721360703194149591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14579969814240468796099727 21869954721360703194149591)
          ·
            refine ⟨32804932082041054791224387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21869954721360703194149591 32804932082041054791224387)
            ·
              refine ⟨49207398123061582186836581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32804932082041054791224387 49207398123061582186836581)
              ·
                refine ⟨9226387148074046660031859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49207398123061582186836581 9226387148074046660031859)
                ·
                  refine ⟨13839580722111069990047789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9226387148074046660031859 13839580722111069990047789)
                  ·
                    refine ⟨5189842770791651246267921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13839580722111069990047789 5189842770791651246267921)
                    ·
                      refine ⟨3892382078093738434700941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189842770791651246267921 3892382078093738434700941)
                      ·
                        rfl

theorem cell23_7580387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7580387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580387 prefixEnd_7580387 := by exact prefixLift 7580387
  have htrace : WordTrace (prefixWord ++ tailWord_7580387) baseStart_7580387 baseEnd_7580387 := by
    simpa [prefixWord, tailWord_7580387, baseEnd_7580387] using wordTrace_append hprefix tailTrace_7580387
  have hstable : (prefixWord ++ tailWord_7580387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580387).length < 2 ^ (prefixWord ++ tailWord_7580387).sum := by decide
  have hdescent : baseEnd_7580387 < baseStart_7580387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580400 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 6, 2, 2]
def baseStart_7580400 : Nat := 118140960795 + 7580400 * 2 ^ 59
def prefixEnd_7580400 : Nat := 4983230072969 + 3 ^ 40 * 7580400 * 2
def baseEnd_7580400 : Nat := 3892388753342246883838381

theorem tailTrace_7580400 : CollatzResearch.WordTrace tailWord_7580400 prefixEnd_7580400 3892388753342246883838381 := by
  unfold tailWord_7580400
  simp only [CollatzResearch.WordTrace]
  refine ⟨138239950868756452047205327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184319934491675269396273769 138239950868756452047205327)
  ·
    refine ⟨207359926303134678070807991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138239950868756452047205327 207359926303134678070807991)
    ·
      refine ⟨311039889454702017106211987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207359926303134678070807991 311039889454702017106211987)
      ·
        refine ⟨466559834182053025659317981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311039889454702017106211987 466559834182053025659317981)
        ·
          refine ⟨174959937818269884622244243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466559834182053025659317981 174959937818269884622244243)
          ·
            refine ⟨262439906727404826933366365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174959937818269884622244243 262439906727404826933366365)
            ·
              refine ⟨98414965022776810100012387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262439906727404826933366365 98414965022776810100012387)
              ·
                refine ⟨147622447534165215150018581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98414965022776810100012387 147622447534165215150018581)
                ·
                  refine ⟨6919802228163994460157121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147622447534165215150018581 6919802228163994460157121)
                  ·
                    refine ⟨5189851671122995845117841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6919802228163994460157121 5189851671122995845117841)
                    ·
                      refine ⟨3892388753342246883838381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189851671122995845117841 3892388753342246883838381)
                      ·
                        rfl

theorem cell23_7580400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 2, 2].length) (baseStart_7580400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580400 prefixEnd_7580400 := by exact prefixLift 7580400
  have htrace : WordTrace (prefixWord ++ tailWord_7580400) baseStart_7580400 baseEnd_7580400 := by
    simpa [prefixWord, tailWord_7580400, baseEnd_7580400] using wordTrace_append hprefix tailTrace_7580400
  have hstable : (prefixWord ++ tailWord_7580400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580400).length < 2 ^ (prefixWord ++ tailWord_7580400).sum := by decide
  have hdescent : baseEnd_7580400 < baseStart_7580400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580417 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_7580417 : Nat := 118140960795 + 7580417 * 2 ^ 59
def prefixEnd_7580417 : Nat := 4983230072969 + 3 ^ 40 * 7580417 * 2
def baseEnd_7580417 : Nat := 3892397482513373317325803

theorem tailTrace_7580417 : CollatzResearch.WordTrace tailWord_7580417 prefixEnd_7580417 3892397482513373317325803 := by
  unfold tailWord_7580417
  simp only [CollatzResearch.WordTrace]
  refine ⟨276480521778451315997779505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184320347852300877331853003 276480521778451315997779505)
  ·
    refine ⟨207360391333838486998334629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276480521778451315997779505 207360391333838486998334629)
    ·
      refine ⟨38880073375094716312187743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207360391333838486998334629 38880073375094716312187743)
      ·
        refine ⟨58320110062642074468281615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38880073375094716312187743 58320110062642074468281615)
        ·
          refine ⟨87480165093963111702422423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58320110062642074468281615 87480165093963111702422423)
          ·
            refine ⟨131220247640944667553633635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87480165093963111702422423 131220247640944667553633635)
            ·
              refine ⟨196830371461417001330450453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131220247640944667553633635 196830371461417001330450453)
              ·
                refine ⟨9226423662253921937364865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196830371461417001330450453 9226423662253921937364865)
                ·
                  refine ⟨6919817746690441453023649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9226423662253921937364865 6919817746690441453023649)
                  ·
                    refine ⟨5189863310017831089767737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6919817746690441453023649 5189863310017831089767737)
                    ·
                      refine ⟨3892397482513373317325803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189863310017831089767737 3892397482513373317325803)
                      ·
                        rfl

theorem cell23_7580417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_7580417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580417 prefixEnd_7580417 := by exact prefixLift 7580417
  have htrace : WordTrace (prefixWord ++ tailWord_7580417) baseStart_7580417 baseEnd_7580417 := by
    simpa [prefixWord, tailWord_7580417, baseEnd_7580417] using wordTrace_append hprefix tailTrace_7580417
  have hstable : (prefixWord ++ tailWord_7580417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580417).length < 2 ^ (prefixWord ++ tailWord_7580417).sum := by decide
  have hdescent : baseEnd_7580417 < baseStart_7580417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580433 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_7580433 : Nat := 118140960795 + 7580433 * 2 ^ 59
def prefixEnd_7580433 : Nat := 4983230072969 + 3 ^ 40 * 7580433 * 2
def baseEnd_7580433 : Nat := 3892405698203845254725729

theorem tailTrace_7580433 : CollatzResearch.WordTrace tailWord_7580433 prefixEnd_7580433 3892405698203845254725729 := by
  unfold tailWord_7580433
  simp only [CollatzResearch.WordTrace]
  refine ⟨276481105346393350730361953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184320736897595567153574635 276481105346393350730361953)
  ·
    refine ⟨207360829009795013047771465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276481105346393350730361953 207360829009795013047771465)
    ·
      refine ⟨155520621757346259785828599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207360829009795013047771465 155520621757346259785828599)
      ·
        refine ⟨233280932636019389678742899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155520621757346259785828599 233280932636019389678742899)
        ·
          refine ⟨349921398954029084518114349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233280932636019389678742899 349921398954029084518114349)
          ·
            refine ⟨131220524607760906694292881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349921398954029084518114349 131220524607760906694292881)
            ·
              refine ⟨98415393455820680020719661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131220524607760906694292881 98415393455820680020719661)
              ·
                refine ⟨36905772545932755007769873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98415393455820680020719661 36905772545932755007769873)
                ·
                  refine ⟨27679329409449566255827405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36905772545932755007769873 27679329409449566255827405)
                  ·
                    refine ⟨10379748528543587345935277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27679329409449566255827405 10379748528543587345935277)
                    ·
                      refine ⟨3892405698203845254725729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10379748528543587345935277 3892405698203845254725729)
                      ·
                        rfl

theorem cell23_7580433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_7580433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580433 prefixEnd_7580433 := by exact prefixLift 7580433
  have htrace : WordTrace (prefixWord ++ tailWord_7580433) baseStart_7580433 baseEnd_7580433 := by
    simpa [prefixWord, tailWord_7580433, baseEnd_7580433] using wordTrace_append hprefix tailTrace_7580433
  have hstable : (prefixWord ++ tailWord_7580433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580433).length < 2 ^ (prefixWord ++ tailWord_7580433).sum := by decide
  have hdescent : baseEnd_7580433 < baseStart_7580433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580474 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_7580474 : Nat := 118140960795 + 7580474 * 2 ^ 59
def prefixEnd_7580474 : Nat := 4983230072969 + 3 ^ 40 * 7580474 * 2
def baseEnd_7580474 : Nat := 432491861212297732701449

theorem tailTrace_7580474 : CollatzResearch.WordTrace tailWord_7580474 prefixEnd_7580474 432491861212297732701449 := by
  unfold tailWord_7580474
  simp only [CollatzResearch.WordTrace]
  refine ⟨69120650184811203683151119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184321733826163209821736317 69120650184811203683151119)
  ·
    refine ⟨103680975277216805524726679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69120650184811203683151119 103680975277216805524726679)
    ·
      refine ⟨155521462915825208287090019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103680975277216805524726679 155521462915825208287090019)
      ·
        refine ⟨233282194373737812430635029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155521462915825208287090019 233282194373737812430635029)
        ·
          refine ⟨10935102861268959957686017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233282194373737812430635029 10935102861268959957686017)
          ·
            refine ⟨8201327145951719968264513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10935102861268959957686017 8201327145951719968264513)
            ·
              refine ⟨6150995359463789976198385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8201327145951719968264513 6150995359463789976198385)
              ·
                refine ⟨4613246519597842482148789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6150995359463789976198385 4613246519597842482148789)
                ·
                  refine ⟨432491861212297732701449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4613246519597842482148789 432491861212297732701449)
                  ·
                    rfl

theorem cell23_7580474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_7580474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580474 prefixEnd_7580474 := by exact prefixLift 7580474
  have htrace : WordTrace (prefixWord ++ tailWord_7580474) baseStart_7580474 baseEnd_7580474 := by
    simpa [prefixWord, tailWord_7580474, baseEnd_7580474] using wordTrace_append hprefix tailTrace_7580474
  have hstable : (prefixWord ++ tailWord_7580474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580474).length < 2 ^ (prefixWord ++ tailWord_7580474).sum := by decide
  have hdescent : baseEnd_7580474 < baseStart_7580474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580484 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7580484 : Nat := 118140960795 + 7580484 * 2 ^ 59
def prefixEnd_7580484 : Nat := 4983230072969 + 3 ^ 40 * 7580484 * 2
def baseEnd_7580484 : Nat := 3892431885717224555187995

theorem tailTrace_7580484 : CollatzResearch.WordTrace tailWord_7580484 prefixEnd_7580484 3892431885717224555187995 := by
  unfold tailWord_7580484
  simp only [CollatzResearch.WordTrace]
  refine ⟨138241482734604293220234253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184321976979472390960312337 138241482734604293220234253)
  ·
    refine ⟨51840556025476609957587845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138241482734604293220234253 51840556025476609957587845)
    ·
      refine ⟨9720104254776864367047721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51840556025476609957587845 9720104254776864367047721)
      ·
        refine ⟨7290078191082648275285791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9720104254776864367047721 7290078191082648275285791)
        ·
          refine ⟨10935117286623972412928687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7290078191082648275285791 10935117286623972412928687)
          ·
            refine ⟨16402675929935958619393031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10935117286623972412928687 16402675929935958619393031)
            ·
              refine ⟨24604013894903937929089547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16402675929935958619393031 24604013894903937929089547)
              ·
                refine ⟨36906020842355906893634321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24604013894903937929089547 36906020842355906893634321)
                ·
                  refine ⟨27679515631766930170225741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36906020842355906893634321 27679515631766930170225741)
                  ·
                    refine ⟨10379818361912598813834653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27679515631766930170225741 10379818361912598813834653)
                    ·
                      refine ⟨3892431885717224555187995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10379818361912598813834653 3892431885717224555187995)
                      ·
                        rfl

theorem cell23_7580484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7580484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580484 prefixEnd_7580484 := by exact prefixLift 7580484
  have htrace : WordTrace (prefixWord ++ tailWord_7580484) baseStart_7580484 baseEnd_7580484 := by
    simpa [prefixWord, tailWord_7580484, baseEnd_7580484] using wordTrace_append hprefix tailTrace_7580484
  have hstable : (prefixWord ++ tailWord_7580484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580484).length < 2 ^ (prefixWord ++ tailWord_7580484).sum := by decide
  have hdescent : baseEnd_7580484 < baseStart_7580484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580517 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_7580517 : Nat := 118140960795 + 7580517 * 2 ^ 59
def prefixEnd_7580517 : Nat := 4983230072969 + 3 ^ 40 * 7580517 * 2
def baseEnd_7580517 : Nat := 1297482943526274308691781

theorem tailTrace_7580517 : CollatzResearch.WordTrace tailWord_7580517 prefixEnd_7580517 1297482943526274308691781 := by
  unfold tailWord_7580517
  simp only [CollatzResearch.WordTrace]
  refine ⟨276484169078089033076419805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184322779385392688717613203 276484169078089033076419805)
  ·
    refine ⟨103681563404283387403657427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276484169078089033076419805 103681563404283387403657427)
    ·
      refine ⟨155522345106425081105486141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103681563404283387403657427 155522345106425081105486141)
      ·
        refine ⟨58320879414909405414557303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155522345106425081105486141 58320879414909405414557303)
        ·
          refine ⟨87481319122364108121835955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58320879414909405414557303 87481319122364108121835955)
          ·
            refine ⟨131221978683546162182753933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87481319122364108121835955 131221978683546162182753933)
            ·
              refine ⟨49208242006329810818532725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131221978683546162182753933 49208242006329810818532725)
              ·
                refine ⟨4613272688093419764237443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49208242006329810818532725 4613272688093419764237443)
                ·
                  refine ⟨6919909032140129646356165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613272688093419764237443 6919909032140129646356165)
                  ·
                    refine ⟨1297482943526274308691781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6919909032140129646356165 1297482943526274308691781)
                    ·
                      rfl

theorem cell23_7580517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_7580517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580517 prefixEnd_7580517 := by exact prefixLift 7580517
  have htrace : WordTrace (prefixWord ++ tailWord_7580517) baseStart_7580517 baseEnd_7580517 := by
    simpa [prefixWord, tailWord_7580517, baseEnd_7580517] using wordTrace_append hprefix tailTrace_7580517
  have hstable : (prefixWord ++ tailWord_7580517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580517).length < 2 ^ (prefixWord ++ tailWord_7580517).sum := by decide
  have hdescent : baseEnd_7580517 < baseStart_7580517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580530 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_7580530 : Nat := 118140960795 + 7580530 * 2 ^ 59
def prefixEnd_7580530 : Nat := 4983230072969 + 3 ^ 40 * 7580530 * 2
def baseEnd_7580530 : Nat := 432495056203036819468087

theorem tailTrace_7580530 : CollatzResearch.WordTrace tailWord_7580530 prefixEnd_7580530 432495056203036819468087 := by
  unfold tailWord_7580530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69121160806760484074160761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184323095484694624197762029 69121160806760484074160761)
  ·
    refine ⟨51840870605070363055620571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69121160806760484074160761 51840870605070363055620571)
    ·
      refine ⟨77761305907605544583430857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51840870605070363055620571 77761305907605544583430857)
      ·
        refine ⟨58320979430704158437573143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77761305907605544583430857 58320979430704158437573143)
        ·
          refine ⟨87481469146056237656359715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58320979430704158437573143 87481469146056237656359715)
          ·
            refine ⟨131222203719084356484539573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87481469146056237656359715 131222203719084356484539573)
            ·
              refine ⟨12302081598664158420425585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131222203719084356484539573 12302081598664158420425585)
              ·
                refine ⟨9226561198998118815319189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12302081598664158420425585 9226561198998118815319189)
                ·
                  refine ⟨432495056203036819468087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9226561198998118815319189 432495056203036819468087)
                  ·
                    rfl

theorem cell23_7580530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_7580530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580530 prefixEnd_7580530 := by exact prefixLift 7580530
  have htrace : WordTrace (prefixWord ++ tailWord_7580530) baseStart_7580530 baseEnd_7580530 := by
    simpa [prefixWord, tailWord_7580530, baseEnd_7580530] using wordTrace_append hprefix tailTrace_7580530
  have hstable : (prefixWord ++ tailWord_7580530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580530).length < 2 ^ (prefixWord ++ tailWord_7580530).sum := by decide
  have hdescent : baseEnd_7580530 < baseStart_7580530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580534 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_7580534 : Nat := 118140960795 + 7580534 * 2 ^ 59
def prefixEnd_7580534 : Nat := 4983230072969 + 3 ^ 40 * 7580534 * 2
def baseEnd_7580534 : Nat := 1297485853249983119854255

theorem tailTrace_7580534 : CollatzResearch.WordTrace tailWord_7580534 prefixEnd_7580534 1297485853249983119854255 := by
  unfold tailWord_7580534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17280299319939215311236791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184323192746018296653192437 17280299319939215311236791)
  ·
    refine ⟨25920448979908822966855187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17280299319939215311236791 25920448979908822966855187)
    ·
      refine ⟨38880673469863234450282781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25920448979908822966855187 38880673469863234450282781)
      ·
        refine ⟨14580252551198712918856043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38880673469863234450282781 14580252551198712918856043)
        ·
          refine ⟨21870378826798069378284065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580252551198712918856043 21870378826798069378284065)
          ·
            refine ⟨16402784120098552033713049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21870378826798069378284065 16402784120098552033713049)
            ·
              refine ⟨12302088090073914025284787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16402784120098552033713049 12302088090073914025284787)
              ·
                refine ⟨18453132135110871037927181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12302088090073914025284787 18453132135110871037927181)
                ·
                  refine ⟨6919924550666576639222693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18453132135110871037927181 6919924550666576639222693)
                  ·
                    refine ⟨1297485853249983119854255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6919924550666576639222693 1297485853249983119854255)
                    ·
                      rfl

theorem cell23_7580534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_7580534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580534 prefixEnd_7580534 := by exact prefixLift 7580534
  have htrace : WordTrace (prefixWord ++ tailWord_7580534) baseStart_7580534 baseEnd_7580534 := by
    simpa [prefixWord, tailWord_7580534, baseEnd_7580534] using wordTrace_append hprefix tailTrace_7580534
  have hstable : (prefixWord ++ tailWord_7580534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580534).length < 2 ^ (prefixWord ++ tailWord_7580534).sum := by decide
  have hdescent : baseEnd_7580534 < baseStart_7580534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580543 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 5, 5]
def baseStart_7580543 : Nat := 118140960795 + 7580543 * 2 ^ 59
def prefixEnd_7580543 : Nat := 4983230072969 + 3 ^ 40 * 7580543 * 2
def baseEnd_7580543 : Nat := 1297487393691946608116741

theorem tailTrace_7580543 : CollatzResearch.WordTrace tailWord_7580543 prefixEnd_7580543 1297487393691946608116741 := by
  unfold tailWord_7580543
  simp only [CollatzResearch.WordTrace]
  refine ⟨276485117375994839516866283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184323411583996559677910855 276485117375994839516866283)
  ·
    refine ⟨414727676063992259275299425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276485117375994839516866283 414727676063992259275299425)
    ·
      refine ⟨311045757047994194456474569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414727676063992259275299425 311045757047994194456474569)
      ·
        refine ⟨233284317785995645842355927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311045757047994194456474569 233284317785995645842355927)
        ·
          refine ⟨349926476678993468763533891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233284317785995645842355927 349926476678993468763533891)
          ·
            refine ⟨524889715018490203145300837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349926476678993468763533891 524889715018490203145300837)
            ·
              refine ⟨98416821565966913089743907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 524889715018490203145300837 98416821565966913089743907)
              ·
                refine ⟨147625232348950369634615861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98416821565966913089743907 147625232348950369634615861)
                ·
                  refine ⟨13839865532714097153245237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147625232348950369634615861 13839865532714097153245237)
                  ·
                    refine ⟨1297487393691946608116741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13839865532714097153245237 1297487393691946608116741)
                    ·
                      rfl

theorem cell23_7580543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_7580543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580543 prefixEnd_7580543 := by exact prefixLift 7580543
  have htrace : WordTrace (prefixWord ++ tailWord_7580543) baseStart_7580543 baseEnd_7580543 := by
    simpa [prefixWord, tailWord_7580543, baseEnd_7580543] using wordTrace_append hprefix tailTrace_7580543
  have hstable : (prefixWord ++ tailWord_7580543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580543).length < 2 ^ (prefixWord ++ tailWord_7580543).sum := by decide
  have hdescent : baseEnd_7580543 < baseStart_7580543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580567 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 2, 3, 2]
def baseStart_7580567 : Nat := 118140960795 + 7580567 * 2 ^ 59
def prefixEnd_7580567 : Nat := 4983230072969 + 3 ^ 40 * 7580567 * 2
def baseEnd_7580567 : Nat := 3892474504611547730450113

theorem tailTrace_7580567 : CollatzResearch.WordTrace tailWord_7580567 prefixEnd_7580567 3892474504611547730450113 := by
  unfold tailWord_7580567
  simp only [CollatzResearch.WordTrace]
  refine ⟨276485992727907891615739955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184323995151938594410493303 276485992727907891615739955)
  ·
    refine ⟨414728989091861837423609933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276485992727907891615739955 414728989091861837423609933)
    ·
      refine ⟨155523370909448189033853725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414728989091861837423609933 155523370909448189033853725)
      ·
        refine ⟨58321264091043070887695147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155523370909448189033853725 58321264091043070887695147)
        ·
          refine ⟨87481896136564606331542721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58321264091043070887695147 87481896136564606331542721)
          ·
            refine ⟨65611422102423454748657041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87481896136564606331542721 65611422102423454748657041)
            ·
              refine ⟨49208566576817591061492781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65611422102423454748657041 49208566576817591061492781)
              ·
                refine ⟨18453212466306596648059793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49208566576817591061492781 18453212466306596648059793)
                ·
                  refine ⟨13839909349729947486044845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18453212466306596648059793 13839909349729947486044845)
                  ·
                    refine ⟨5189966006148730307266817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13839909349729947486044845 5189966006148730307266817)
                    ·
                      refine ⟨3892474504611547730450113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189966006148730307266817 3892474504611547730450113)
                      ·
                        rfl

theorem cell23_7580567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_7580567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580567 prefixEnd_7580567 := by exact prefixLift 7580567
  have htrace : WordTrace (prefixWord ++ tailWord_7580567) baseStart_7580567 baseEnd_7580567 := by
    simpa [prefixWord, tailWord_7580567, baseEnd_7580567] using wordTrace_append hprefix tailTrace_7580567
  have hstable : (prefixWord ++ tailWord_7580567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580567).length < 2 ^ (prefixWord ++ tailWord_7580567).sum := by decide
  have hdescent : baseEnd_7580567 < baseStart_7580567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580577 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 1, 5]
def baseStart_7580577 : Nat := 118140960795 + 7580577 * 2 ^ 59
def prefixEnd_7580577 : Nat := 4983230072969 + 3 ^ 40 * 7580577 * 2
def baseEnd_7580577 : Nat := 1297493213139364230441689

theorem tailTrace_7580577 : CollatzResearch.WordTrace tailWord_7580577 prefixEnd_7580577 1297493213139364230441689 := by
  unfold tailWord_7580577
  simp only [CollatzResearch.WordTrace]
  refine ⟨276486357457871663323603985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184324238305247775549069323 276486357457871663323603985)
  ·
    refine ⟨207364768093403747492702989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276486357457871663323603985 207364768093403747492702989)
    ·
      refine ⟨77761788035026405309763621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207364768093403747492702989 77761788035026405309763621)
      ·
        refine ⟨14580335256567450995580679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77761788035026405309763621 14580335256567450995580679)
        ·
          refine ⟨21870502884851176493371019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580335256567450995580679 21870502884851176493371019)
          ·
            refine ⟨32805754327276764740056529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21870502884851176493371019 32805754327276764740056529)
            ·
              refine ⟨24604315745457573555042397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32805754327276764740056529 24604315745457573555042397)
              ·
                refine ⟨9226618404546590083140899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24604315745457573555042397 9226618404546590083140899)
                ·
                  refine ⟨13839927606819885124711349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9226618404546590083140899 13839927606819885124711349)
                  ·
                    refine ⟨1297493213139364230441689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13839927606819885124711349 1297493213139364230441689)
                    ·
                      rfl

theorem cell23_7580577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_7580577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580577 prefixEnd_7580577 := by exact prefixLift 7580577
  have htrace : WordTrace (prefixWord ++ tailWord_7580577) baseStart_7580577 baseEnd_7580577 := by
    simpa [prefixWord, tailWord_7580577, baseEnd_7580577] using wordTrace_append hprefix tailTrace_7580577
  have hstable : (prefixWord ++ tailWord_7580577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580577).length < 2 ^ (prefixWord ++ tailWord_7580577).sum := by decide
  have hdescent : baseEnd_7580577 < baseStart_7580577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580600 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_7580600 : Nat := 118140960795 + 7580600 * 2 ^ 59
def prefixEnd_7580600 : Nat := 4983230072969 + 3 ^ 40 * 7580600 * 2
def baseEnd_7580600 : Nat := 3892491449473146101337461

theorem tailTrace_7580600 : CollatzResearch.WordTrace tailWord_7580600 prefixEnd_7580600 3892491449473146101337461 := by
  unfold tailWord_7580600
  simp only [CollatzResearch.WordTrace]
  refine ⟨138243598168394169125845627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184324797557858892167794169 138243598168394169125845627)
  ·
    refine ⟨207365397252591253688768441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138243598168394169125845627 207365397252591253688768441)
    ·
      refine ⟨155524047939443440266576331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207365397252591253688768441 155524047939443440266576331)
      ·
        refine ⟨233286071909165160399864497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155524047939443440266576331 233286071909165160399864497)
        ·
          refine ⟨174964553931873870299898373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233286071909165160399864497 174964553931873870299898373)
          ·
            refine ⟨32805853862226350681230945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174964553931873870299898373 32805853862226350681230945)
            ·
              refine ⟨24604390396669763010923209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32805853862226350681230945 24604390396669763010923209)
              ·
                refine ⟨18453292797502322258192407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24604390396669763010923209 18453292797502322258192407)
                ·
                  refine ⟨27679939196253483387288611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18453292797502322258192407 27679939196253483387288611)
                  ·
                    refine ⟨41519908794380225080932917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27679939196253483387288611 41519908794380225080932917)
                    ·
                      refine ⟨3892491449473146101337461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41519908794380225080932917 3892491449473146101337461)
                      ·
                        rfl

theorem cell23_7580600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_7580600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580600 prefixEnd_7580600 := by exact prefixLift 7580600
  have htrace : WordTrace (prefixWord ++ tailWord_7580600) baseStart_7580600 baseEnd_7580600 := by
    simpa [prefixWord, tailWord_7580600, baseEnd_7580600] using wordTrace_append hprefix tailTrace_7580600
  have hstable : (prefixWord ++ tailWord_7580600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580600).length < 2 ^ (prefixWord ++ tailWord_7580600).sum := by decide
  have hdescent : baseEnd_7580600 < baseStart_7580600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580648 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_7580648 : Nat := 118140960795 + 7580648 * 2 ^ 59
def prefixEnd_7580648 : Nat := 4983230072969 + 3 ^ 40 * 7580648 * 2
def baseEnd_7580648 : Nat := 3892516096544561913537241

theorem tailTrace_7580648 : CollatzResearch.WordTrace tailWord_7580648 prefixEnd_7580648 3892516096544561913537241 := by
  unfold tailWord_7580648
  simp only [CollatzResearch.WordTrace]
  refine ⟨138244473520307221224719299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184325964693742961632959065 138244473520307221224719299)
  ·
    refine ⟨207366710280460831837078949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138244473520307221224719299 207366710280460831837078949)
    ·
      refine ⟨38881258177586405969452303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207366710280460831837078949 38881258177586405969452303)
      ·
        refine ⟨58321887266379608954178455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38881258177586405969452303 58321887266379608954178455)
        ·
          refine ⟨87482830899569413431267683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58321887266379608954178455 87482830899569413431267683)
          ·
            refine ⟨131224246349354120146901525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87482830899569413431267683 131224246349354120146901525)
            ·
              refine ⟨6151136547625974381886009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131224246349354120146901525 6151136547625974381886009)
              ·
                refine ⟨4613352410719480786414507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6151136547625974381886009 4613352410719480786414507)
                ·
                  refine ⟨6920028616079221179621761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613352410719480786414507 6920028616079221179621761)
                  ·
                    refine ⟨5190021462059415884716321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6920028616079221179621761 5190021462059415884716321)
                    ·
                      refine ⟨3892516096544561913537241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190021462059415884716321 3892516096544561913537241)
                      ·
                        rfl

theorem cell23_7580648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_7580648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580648 prefixEnd_7580648 := by exact prefixLift 7580648
  have htrace : WordTrace (prefixWord ++ tailWord_7580648) baseStart_7580648 baseEnd_7580648 := by
    simpa [prefixWord, tailWord_7580648, baseEnd_7580648] using wordTrace_append hprefix tailTrace_7580648
  have hstable : (prefixWord ++ tailWord_7580648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580648).length < 2 ^ (prefixWord ++ tailWord_7580648).sum := by decide
  have hdescent : baseEnd_7580648 < baseStart_7580648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580650 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_7580650 : Nat := 118140960795 + 7580650 * 2 ^ 59
def prefixEnd_7580650 : Nat := 4983230072969 + 3 ^ 40 * 7580650 * 2
def baseEnd_7580650 : Nat := 1297505707835290301904077

theorem tailTrace_7580650 : CollatzResearch.WordTrace tailWord_7580650 prefixEnd_7580650 1297505707835290301904077 := by
  unfold tailWord_7580650
  simp only [CollatzResearch.WordTrace]
  refine ⟨69122254996651799197752851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184326013324404797860674269 69122254996651799197752851)
  ·
    refine ⟨103683382494977698796629277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69122254996651799197752851 103683382494977698796629277)
    ·
      refine ⟨38881268435616637048735979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103683382494977698796629277 38881268435616637048735979)
      ·
        refine ⟨58321902653424955573103969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38881268435616637048735979 58321902653424955573103969)
        ·
          refine ⟨43741426990068716679827977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58321902653424955573103969 43741426990068716679827977)
          ·
            refine ⟨32806070242551537509870983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43741426990068716679827977 32806070242551537509870983)
            ·
              refine ⟨49209105363827306264806475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32806070242551537509870983 49209105363827306264806475)
              ·
                refine ⟨73813658045740959397209713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49209105363827306264806475 73813658045740959397209713)
                ·
                  refine ⟨55360243534305719547907285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73813658045740959397209713 55360243534305719547907285)
                  ·
                    refine ⟨1297505707835290301904077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55360243534305719547907285 1297505707835290301904077)
                    ·
                      rfl

theorem cell23_7580650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_7580650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580650 prefixEnd_7580650 := by exact prefixLift 7580650
  have htrace : WordTrace (prefixWord ++ tailWord_7580650) baseStart_7580650 baseEnd_7580650 := by
    simpa [prefixWord, tailWord_7580650, baseEnd_7580650] using wordTrace_append hprefix tailTrace_7580650
  have hstable : (prefixWord ++ tailWord_7580650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580650).length < 2 ^ (prefixWord ++ tailWord_7580650).sum := by decide
  have hdescent : baseEnd_7580650 < baseStart_7580650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580654 : List Nat := [4, 1, 2, 1, 5, 1, 1, 8]
def baseStart_7580654 : Nat := 118140960795 + 7580654 * 2 ^ 59
def prefixEnd_7580654 : Nat := 4983230072969 + 3 ^ 40 * 7580654 * 2
def baseEnd_7580654 : Nat := 144167376941795884817119

theorem tailTrace_7580654 : CollatzResearch.WordTrace tailWord_7580654 prefixEnd_7580654 144167376941795884817119 := by
  unfold tailWord_7580654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34561145734824088184269627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184326110585728470316104677 34561145734824088184269627)
  ·
    refine ⟨51841718602236132276404441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34561145734824088184269627 51841718602236132276404441)
    ·
      refine ⟨38881288951677099207303331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51841718602236132276404441 38881288951677099207303331)
      ·
        refine ⟨58321933427515648810954997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38881288951677099207303331 58321933427515648810954997)
        ·
          refine ⟨5467681258829592076027031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58321933427515648810954997 5467681258829592076027031)
          ·
            refine ⟨8201521888244388114040547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467681258829592076027031 8201521888244388114040547)
            ·
              refine ⟨12302282832366582171060821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201521888244388114040547 12302282832366582171060821)
              ·
                refine ⟨144167376941795884817119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12302282832366582171060821 144167376941795884817119)
                ·
                  rfl

theorem cell23_7580654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_7580654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580654 prefixEnd_7580654 := by exact prefixLift 7580654
  have htrace : WordTrace (prefixWord ++ tailWord_7580654) baseStart_7580654 baseEnd_7580654 := by
    simpa [prefixWord, tailWord_7580654, baseEnd_7580654] using wordTrace_append hprefix tailTrace_7580654
  have hstable : (prefixWord ++ tailWord_7580654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580654).length < 2 ^ (prefixWord ++ tailWord_7580654).sum := by decide
  have hdescent : baseEnd_7580654 < baseStart_7580654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580661 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7580661 : Nat := 118140960795 + 7580661 * 2 ^ 59
def prefixEnd_7580661 : Nat := 4983230072969 + 3 ^ 40 * 7580661 * 2
def baseEnd_7580661 : Nat := 3892522771793070362674681

theorem tailTrace_7580661 : CollatzResearch.WordTrace tailWord_7580661 prefixEnd_7580661 3892522771793070362674681 := by
  unfold tailWord_7580661
  simp only [CollatzResearch.WordTrace]
  refine ⟨276489421189567345669661837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184326280793044897113107891 276489421189567345669661837)
  ·
    refine ⟨103683532946087754626123189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276489421189567345669661837 103683532946087754626123189)
    ·
      refine ⟨9720331213695726996199049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103683532946087754626123189 9720331213695726996199049)
      ·
        refine ⟨7290248410271795247149287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9720331213695726996199049 7290248410271795247149287)
        ·
          refine ⟨10935372615407692870723931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7290248410271795247149287 10935372615407692870723931)
          ·
            refine ⟨16403058923111539306085897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10935372615407692870723931 16403058923111539306085897)
            ·
              refine ⟨12302294192333654479564423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16403058923111539306085897 12302294192333654479564423)
              ·
                refine ⟨18453441288500481719346635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12302294192333654479564423 18453441288500481719346635)
                ·
                  refine ⟨27680161932750722579019953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18453441288500481719346635 27680161932750722579019953)
                  ·
                    refine ⟨20760121449563041934264965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27680161932750722579019953 20760121449563041934264965)
                    ·
                      refine ⟨3892522771793070362674681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20760121449563041934264965 3892522771793070362674681)
                      ·
                        rfl

theorem cell23_7580661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7580661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580661 prefixEnd_7580661 := by exact prefixLift 7580661
  have htrace : WordTrace (prefixWord ++ tailWord_7580661) baseStart_7580661 baseEnd_7580661 := by
    simpa [prefixWord, tailWord_7580661, baseEnd_7580661] using wordTrace_append hprefix tailTrace_7580661
  have hstable : (prefixWord ++ tailWord_7580661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580661).length < 2 ^ (prefixWord ++ tailWord_7580661).sum := by decide
  have hdescent : baseEnd_7580661 < baseStart_7580661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580757 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_7580757 : Nat := 118140960795 + 7580757 * 2 ^ 59
def prefixEnd_7580757 : Nat := 4983230072969 + 3 ^ 40 * 7580757 * 2
def baseEnd_7580757 : Nat := 1297524021978633995691413

theorem tailTrace_7580757 : CollatzResearch.WordTrace tailWord_7580757 prefixEnd_7580757 1297524021978633995691413 := by
  unfold tailWord_7580757
  simp only [CollatzResearch.WordTrace]
  refine ⟨276492922597219554065156525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184328615064813036043437683 276492922597219554065156525)
  ·
    refine ⟨103684845973957332774433697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276492922597219554065156525 103684845973957332774433697)
    ·
      refine ⟨77763634480467999580825273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103684845973957332774433697 77763634480467999580825273)
      ·
        refine ⟨58322725860350999685618955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77763634480467999580825273 58322725860350999685618955)
        ·
          refine ⟨87484088790526499528428433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58322725860350999685618955 87484088790526499528428433)
          ·
            refine ⟨65613066592894874646321325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87484088790526499528428433 65613066592894874646321325)
            ·
              refine ⟨24604899972335577992370497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65613066592894874646321325 24604899972335577992370497)
              ·
                refine ⟨18453674979251683494277873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24604899972335577992370497 18453674979251683494277873)
                ·
                  refine ⟨13840256234438762620708405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18453674979251683494277873 13840256234438762620708405)
                  ·
                    refine ⟨1297524021978633995691413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13840256234438762620708405 1297524021978633995691413)
                    ·
                      rfl

theorem cell23_7580757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_7580757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580757 prefixEnd_7580757 := by exact prefixLift 7580757
  have htrace : WordTrace (prefixWord ++ tailWord_7580757) baseStart_7580757 baseEnd_7580757 := by
    simpa [prefixWord, tailWord_7580757, baseEnd_7580757] using wordTrace_append hprefix tailTrace_7580757
  have hstable : (prefixWord ++ tailWord_7580757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580757).length < 2 ^ (prefixWord ++ tailWord_7580757).sum := by decide
  have hdescent : baseEnd_7580757 < baseStart_7580757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580764 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_7580764 : Nat := 118140960795 + 7580764 * 2 ^ 59
def prefixEnd_7580764 : Nat := 4983230072969 + 3 ^ 40 * 7580764 * 2
def baseEnd_7580764 : Nat := 3892575660300483459686707

theorem tailTrace_7580764 : CollatzResearch.WordTrace tailWord_7580764 prefixEnd_7580764 3892575660300483459686707 := by
  unfold tailWord_7580764
  simp only [CollatzResearch.WordTrace]
  refine ⟨138246588954097097130330673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184328785272129462840440897 138246588954097097130330673)
  ·
    refine ⟨103684941715572822847748005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138246588954097097130330673 103684941715572822847748005)
    ·
      refine ⟨19440926571669904283952751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103684941715572822847748005 19440926571669904283952751)
      ·
        refine ⟨29161389857504856425929127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19440926571669904283952751 29161389857504856425929127)
        ·
          refine ⟨43742084786257284638893691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29161389857504856425929127 43742084786257284638893691)
          ·
            refine ⟨65613127179385926958340537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43742084786257284638893691 65613127179385926958340537)
            ·
              refine ⟨49209845384539445218755403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65613127179385926958340537 49209845384539445218755403)
              ·
                refine ⟨73814768076809167828133105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49209845384539445218755403 73814768076809167828133105)
                ·
                  refine ⟨55361076057606875871099829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73814768076809167828133105 55361076057606875871099829)
                  ·
                    refine ⟨5190100880400644612915609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55361076057606875871099829 5190100880400644612915609)
                    ·
                      refine ⟨3892575660300483459686707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190100880400644612915609 3892575660300483459686707)
                      ·
                        rfl

theorem cell23_7580764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_7580764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580764 prefixEnd_7580764 := by exact prefixLift 7580764
  have htrace : WordTrace (prefixWord ++ tailWord_7580764) baseStart_7580764 baseEnd_7580764 := by
    simpa [prefixWord, tailWord_7580764, baseEnd_7580764] using wordTrace_append hprefix tailTrace_7580764
  have hstable : (prefixWord ++ tailWord_7580764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580764).length < 2 ^ (prefixWord ++ tailWord_7580764).sum := by decide
  have hdescent : baseEnd_7580764 < baseStart_7580764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580800 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 10]
def baseStart_7580800 : Nat := 118140960795 + 7580800 * 2 ^ 59
def prefixEnd_7580800 : Nat := 4983230072969 + 3 ^ 40 * 7580800 * 2
def baseEnd_7580800 : Nat := 432510460622671702092949

theorem tailTrace_7580800 : CollatzResearch.WordTrace tailWord_7580800 prefixEnd_7580800 432510460622671702092949 := by
  unfold tailWord_7580800
  simp only [CollatzResearch.WordTrace]
  refine ⟨138247245468031886204485927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184329660624042514939314569 138247245468031886204485927)
  ·
    refine ⟨207370868202047829306728891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138247245468031886204485927 207370868202047829306728891)
    ·
      refine ⟨311056302303071743960093337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207370868202047829306728891 311056302303071743960093337)
      ·
        refine ⟨233292226727303807970070003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311056302303071743960093337 233292226727303807970070003)
        ·
          refine ⟨349938340090955711955105005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233292226727303807970070003 349938340090955711955105005)
          ·
            refine ⟨131226877534108391983164377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349938340090955711955105005 131226877534108391983164377)
            ·
              refine ⟨98420158150581293987373283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131226877534108391983164377 98420158150581293987373283)
              ·
                refine ⟨147630237225871940981059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98420158150581293987373283 147630237225871940981059925)
                ·
                  refine ⟨432510460622671702092949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 147630237225871940981059925 432510460622671702092949)
                  ·
                    rfl

theorem cell23_7580800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_7580800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580800 prefixEnd_7580800 := by exact prefixLift 7580800
  have htrace : WordTrace (prefixWord ++ tailWord_7580800) baseStart_7580800 baseEnd_7580800 := by
    simpa [prefixWord, tailWord_7580800, baseEnd_7580800] using wordTrace_append hprefix tailTrace_7580800
  have hstable : (prefixWord ++ tailWord_7580800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580800).length < 2 ^ (prefixWord ++ tailWord_7580800).sum := by decide
  have hdescent : baseEnd_7580800 < baseStart_7580800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580847 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 3, 5]
def baseStart_7580847 : Nat := 118140960795 + 7580847 * 2 ^ 59
def prefixEnd_7580847 : Nat := 4983230072969 + 3 ^ 40 * 7580847 * 2
def baseEnd_7580847 : Nat := 1297539426398268878316275

theorem tailTrace_7580847 : CollatzResearch.WordTrace tailWord_7580847 prefixEnd_7580847 1297539426398268878316275 := by
  unfold tailWord_7580847
  simp only [CollatzResearch.WordTrace]
  refine ⟨276496205166893499435932795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184330803444595666290621863 276496205166893499435932795)
  ·
    refine ⟨414744307750340249153899193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276496205166893499435932795 414744307750340249153899193)
    ·
      refine ⟨311058230812755186865424395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414744307750340249153899193 311058230812755186865424395)
      ·
        refine ⟨466587346219132780298136593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311058230812755186865424395 466587346219132780298136593)
        ·
          refine ⟨349940509664349585223602445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466587346219132780298136593 349940509664349585223602445)
          ·
            refine ⟨131227691124131094458850917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349940509664349585223602445 131227691124131094458850917)
            ·
              refine ⟨24605192085774580211034547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131227691124131094458850917 24605192085774580211034547)
              ·
                refine ⟨36907788128661870316551821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24605192085774580211034547 36907788128661870316551821)
                ·
                  refine ⟨13840420548248201368706933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36907788128661870316551821 13840420548248201368706933)
                  ·
                    refine ⟨1297539426398268878316275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13840420548248201368706933 1297539426398268878316275)
                    ·
                      rfl

theorem cell23_7580847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_7580847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580847 prefixEnd_7580847 := by exact prefixLift 7580847
  have htrace : WordTrace (prefixWord ++ tailWord_7580847) baseStart_7580847 baseEnd_7580847 := by
    simpa [prefixWord, tailWord_7580847, baseEnd_7580847] using wordTrace_append hprefix tailTrace_7580847
  have hstable : (prefixWord ++ tailWord_7580847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580847).length < 2 ^ (prefixWord ++ tailWord_7580847).sum := by decide
  have hdescent : baseEnd_7580847 < baseStart_7580847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580867 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 4]
def baseStart_7580867 : Nat := 118140960795 + 7580867 * 2 ^ 59
def prefixEnd_7580867 : Nat := 4983230072969 + 3 ^ 40 * 7580867 * 2
def baseEnd_7580867 : Nat := 3892628548807896556698733

theorem tailTrace_7580867 : CollatzResearch.WordTrace tailWord_7580867 prefixEnd_7580867 3892628548807896556698733 := by
  unfold tailWord_7580867
  simp only [CollatzResearch.WordTrace]
  refine ⟨276496934626821042851660855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184331289751214028567773903 276496934626821042851660855)
  ·
    refine ⟨414745401940231564277491283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276496934626821042851660855 414745401940231564277491283)
    ·
      refine ⟨622118102910347346416236925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414745401940231564277491283 622118102910347346416236925)
      ·
        refine ⟨233294288591380254906088847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622118102910347346416236925 233294288591380254906088847)
        ·
          refine ⟨349941432887070382359133271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233294288591380254906088847 349941432887070382359133271)
          ·
            refine ⟨524912149330605573538699907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349941432887070382359133271 524912149330605573538699907)
            ·
              refine ⟨787368223995908360308049861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524912149330605573538699907 787368223995908360308049861)
              ·
                refine ⟨147631541999232817557759349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 787368223995908360308049861 147631541999232817557759349)
                ·
                  refine ⟨13840457062428076646039939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147631541999232817557759349 13840457062428076646039939)
                  ·
                    refine ⟨20760685593642114969059909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13840457062428076646039939 20760685593642114969059909)
                    ·
                      refine ⟨3892628548807896556698733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20760685593642114969059909 3892628548807896556698733)
                      ·
                        rfl

theorem cell23_7580867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_7580867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580867 prefixEnd_7580867 := by exact prefixLift 7580867
  have htrace : WordTrace (prefixWord ++ tailWord_7580867) baseStart_7580867 baseEnd_7580867 := by
    simpa [prefixWord, tailWord_7580867, baseEnd_7580867] using wordTrace_append hprefix tailTrace_7580867
  have hstable : (prefixWord ++ tailWord_7580867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580867).length < 2 ^ (prefixWord ++ tailWord_7580867).sum := by decide
  have hdescent : baseEnd_7580867 < baseStart_7580867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580868 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 6]
def baseStart_7580868 : Nat := 118140960795 + 7580868 * 2 ^ 59
def prefixEnd_7580868 : Nat := 4983230072969 + 3 ^ 40 * 7580868 * 2
def baseEnd_7580868 : Nat := 432514340254283450309581

theorem tailTrace_7580868 : CollatzResearch.WordTrace tailWord_7580868 prefixEnd_7580868 432514340254283450309581 := by
  unfold tailWord_7580868
  simp only [CollatzResearch.WordTrace]
  refine ⟨138248485549908710011223629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184331314066544946681631505 138248485549908710011223629)
  ·
    refine ⟨51843182081215766254208861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138248485549908710011223629 51843182081215766254208861)
    ·
      refine ⟨19441193280455912345328323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51843182081215766254208861 19441193280455912345328323)
      ·
        refine ⟨29161789920683868517992485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19441193280455912345328323 29161789920683868517992485)
        ·
          refine ⟨5467835610128225347123591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29161789920683868517992485 5467835610128225347123591)
          ·
            refine ⟨8201753415192338020685387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467835610128225347123591 8201753415192338020685387)
            ·
              refine ⟨12302630122788507031028081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201753415192338020685387 12302630122788507031028081)
              ·
                refine ⟨9226972592091380273271061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12302630122788507031028081 9226972592091380273271061)
                ·
                  refine ⟨432514340254283450309581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9226972592091380273271061 432514340254283450309581)
                  ·
                    rfl

theorem cell23_7580868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_7580868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580868 prefixEnd_7580868 := by exact prefixLift 7580868
  have htrace : WordTrace (prefixWord ++ tailWord_7580868) baseStart_7580868 baseEnd_7580868 := by
    simpa [prefixWord, tailWord_7580868, baseEnd_7580868] using wordTrace_append hprefix tailTrace_7580868
  have hstable : (prefixWord ++ tailWord_7580868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580868).length < 2 ^ (prefixWord ++ tailWord_7580868).sum := by decide
  have hdescent : baseEnd_7580868 < baseStart_7580868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580878 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_7580878 : Nat := 118140960795 + 7580878 * 2 ^ 59
def prefixEnd_7580878 : Nat := 4983230072969 + 3 ^ 40 * 7580878 * 2
def baseEnd_7580878 : Nat := 3892634197095096013661183

theorem tailTrace_7580878 : CollatzResearch.WordTrace tailWord_7580878 prefixEnd_7580878 3892634197095096013661183 := by
  unfold tailWord_7580878
  simp only [CollatzResearch.WordTrace]
  refine ⟨34562166978722648966288911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184331557219854127820207525 34562166978722648966288911)
  ·
    refine ⟨51843250468083973449433367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34562166978722648966288911 51843250468083973449433367)
    ·
      refine ⟨77764875702125960174150051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51843250468083973449433367 77764875702125960174150051)
      ·
        refine ⟨116647313553188940261225077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77764875702125960174150051 116647313553188940261225077)
        ·
          refine ⟨10935685645611463149489851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116647313553188940261225077 10935685645611463149489851)
          ·
            refine ⟨16403528468417194724234777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10935685645611463149489851 16403528468417194724234777)
            ·
              refine ⟨12302646351312896043176083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16403528468417194724234777 12302646351312896043176083)
              ·
                refine ⟨18453969526969344064764125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12302646351312896043176083 18453969526969344064764125)
                ·
                  refine ⟨6920238572613504024286547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18453969526969344064764125 6920238572613504024286547)
                  ·
                    refine ⟨10380357858920256036429821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6920238572613504024286547 10380357858920256036429821)
                    ·
                      refine ⟨3892634197095096013661183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10380357858920256036429821 3892634197095096013661183)
                      ·
                        rfl

theorem cell23_7580878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_7580878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580878 prefixEnd_7580878 := by exact prefixLift 7580878
  have htrace : WordTrace (prefixWord ++ tailWord_7580878) baseStart_7580878 baseEnd_7580878 := by
    simpa [prefixWord, tailWord_7580878, baseEnd_7580878] using wordTrace_append hprefix tailTrace_7580878
  have hstable : (prefixWord ++ tailWord_7580878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580878).length < 2 ^ (prefixWord ++ tailWord_7580878).sum := by decide
  have hdescent : baseEnd_7580878 < baseStart_7580878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580887 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_7580887 : Nat := 118140960795 + 7580887 * 2 ^ 59
def prefixEnd_7580887 : Nat := 4983230072969 + 3 ^ 40 * 7580887 * 2
def baseEnd_7580887 : Nat := 3892638818420986478448641

theorem tailTrace_7580887 : CollatzResearch.WordTrace tailWord_7580887 prefixEnd_7580887 3892638818420986478448641 := by
  unfold tailWord_7580887
  simp only [CollatzResearch.WordTrace]
  refine ⟨276497664086748586267388915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184331776057832390844925943 276497664086748586267388915)
  ·
    refine ⟨414746496130122879401083373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276497664086748586267388915 414746496130122879401083373)
    ·
      refine ⟨155529936048796079775406265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414746496130122879401083373 155529936048796079775406265)
      ·
        refine ⟨116647452036597059831554699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155529936048796079775406265 116647452036597059831554699)
        ·
          refine ⟨174971178054895589747332049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116647452036597059831554699 174971178054895589747332049)
          ·
            refine ⟨131228383541171692310499037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174971178054895589747332049 131228383541171692310499037)
            ·
              refine ⟨49210643827939384616437139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131228383541171692310499037 49210643827939384616437139)
              ·
                refine ⟨73815965741909076924655709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49210643827939384616437139 73815965741909076924655709)
                ·
                  refine ⟨27680987153215903846745891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73815965741909076924655709 27680987153215903846745891)
                  ·
                    refine ⟨41521480729823855770118837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27680987153215903846745891 41521480729823855770118837)
                    ·
                      refine ⟨3892638818420986478448641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41521480729823855770118837 3892638818420986478448641)
                      ·
                        rfl

theorem cell23_7580887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_7580887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580887 prefixEnd_7580887 := by exact prefixLift 7580887
  have htrace : WordTrace (prefixWord ++ tailWord_7580887) baseStart_7580887 baseEnd_7580887 := by
    simpa [prefixWord, tailWord_7580887, baseEnd_7580887] using wordTrace_append hprefix tailTrace_7580887
  have hstable : (prefixWord ++ tailWord_7580887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580887).length < 2 ^ (prefixWord ++ tailWord_7580887).sum := by decide
  have hdescent : baseEnd_7580887 < baseStart_7580887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580907 : List Nat := [1, 1, 1, 1, 2, 7, 1, 9]
def baseStart_7580907 : Nat := 118140960795 + 7580907 * 2 ^ 59
def prefixEnd_7580907 : Nat := 4983230072969 + 3 ^ 40 * 7580907 * 2
def baseEnd_7580907 : Nat := 144172188445706533340687

theorem tailTrace_7580907 : CollatzResearch.WordTrace tailWord_7580907 prefixEnd_7580907 144172188445706533340687 := by
  unfold tailWord_7580907
  simp only [CollatzResearch.WordTrace]
  refine ⟨276498393546676129683116975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184332262364450753122077983 276498393546676129683116975)
  ·
    refine ⟨414747590320014194524675463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276498393546676129683116975 414747590320014194524675463)
    ·
      refine ⟨622121385480021291787013195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414747590320014194524675463 622121385480021291787013195)
      ·
        refine ⟨933182078220031937680519793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622121385480021291787013195 933182078220031937680519793)
        ·
          refine ⟨699886558665023953260389845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933182078220031937680519793 699886558665023953260389845)
          ·
            refine ⟨16403591218711498904540387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 699886558665023953260389845 16403591218711498904540387)
            ·
              refine ⟨24605386828067248356810581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16403591218711498904540387 24605386828067248356810581)
              ·
                refine ⟨144172188445706533340687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24605386828067248356810581 144172188445706533340687)
                ·
                  rfl

theorem cell23_7580907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 9].length) (baseStart_7580907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580907 prefixEnd_7580907 := by exact prefixLift 7580907
  have htrace : WordTrace (prefixWord ++ tailWord_7580907) baseStart_7580907 baseEnd_7580907 := by
    simpa [prefixWord, tailWord_7580907, baseEnd_7580907] using wordTrace_append hprefix tailTrace_7580907
  have hstable : (prefixWord ++ tailWord_7580907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580907).length < 2 ^ (prefixWord ++ tailWord_7580907).sum := by decide
  have hdescent : baseEnd_7580907 < baseStart_7580907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580924 : List Nat := [2, 2, 2, 1, 5, 2, 9]
def baseStart_7580924 : Nat := 118140960795 + 7580924 * 2 ^ 59
def prefixEnd_7580924 : Nat := 4983230072969 + 3 ^ 40 * 7580924 * 2
def baseEnd_7580924 : Nat := 48057503916113615230691

theorem tailTrace_7580924 : CollatzResearch.WordTrace tailWord_7580924 prefixEnd_7580924 48057503916113615230691 := by
  unfold tailWord_7580924
  simp only [CollatzResearch.WordTrace]
  refine ⟨138249506793807270793242913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184332675725076361057657217 138249506793807270793242913)
  ·
    refine ⟨103687130095355453094932185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138249506793807270793242913 103687130095355453094932185)
    ·
      refine ⟨77765347571516589821199139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103687130095355453094932185 77765347571516589821199139)
      ·
        refine ⟨116648021357274884731798709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77765347571516589821199139 116648021357274884731798709)
        ·
          refine ⟨10935752002244520443606129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116648021357274884731798709 10935752002244520443606129)
          ·
            refine ⟨8201814001683390332704597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10935752002244520443606129 8201814001683390332704597)
            ·
              refine ⟨48057503916113615230691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8201814001683390332704597 48057503916113615230691)
              ·
                rfl

theorem cell23_7580924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 9].length) (baseStart_7580924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580924 prefixEnd_7580924 := by exact prefixLift 7580924
  have htrace : WordTrace (prefixWord ++ tailWord_7580924) baseStart_7580924 baseEnd_7580924 := by
    simpa [prefixWord, tailWord_7580924, baseEnd_7580924] using wordTrace_append hprefix tailTrace_7580924
  have hstable : (prefixWord ++ tailWord_7580924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580924).length < 2 ^ (prefixWord ++ tailWord_7580924).sum := by decide
  have hdescent : baseEnd_7580924 < baseStart_7580924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580937 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_7580937 : Nat := 118140960795 + 7580937 * 2 ^ 59
def prefixEnd_7580937 : Nat := 4983230072969 + 3 ^ 40 * 7580937 * 2
def baseEnd_7580937 : Nat := 1297554830817903760941137

theorem tailTrace_7580937 : CollatzResearch.WordTrace tailWord_7580937 prefixEnd_7580937 1297554830817903760941137 := by
  unfold tailWord_7580937
  simp only [CollatzResearch.WordTrace]
  refine ⟨276499487736567444806709065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184332991824378296537806043 276499487736567444806709065)
  ·
    refine ⟨207374615802425583605031799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276499487736567444806709065 207374615802425583605031799)
    ·
      refine ⟨311061923703638375407547699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207374615802425583605031799 311061923703638375407547699)
      ·
        refine ⟨466592885555457563111321549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311061923703638375407547699 466592885555457563111321549)
        ·
          refine ⟨174972332083296586166745581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466592885555457563111321549 174972332083296586166745581)
          ·
            refine ⟨65614624531236219812529593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174972332083296586166745581 65614624531236219812529593)
            ·
              refine ⟨49210968398427164859397195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65614624531236219812529593 49210968398427164859397195)
              ·
                refine ⟨73816452597640747289095793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49210968398427164859397195 73816452597640747289095793)
                ·
                  refine ⟨55362339448230560466821845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73816452597640747289095793 55362339448230560466821845)
                  ·
                    refine ⟨1297554830817903760941137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55362339448230560466821845 1297554830817903760941137)
                    ·
                      rfl

theorem cell23_7580937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_7580937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580937 prefixEnd_7580937 := by exact prefixLift 7580937
  have htrace : WordTrace (prefixWord ++ tailWord_7580937) baseStart_7580937 baseEnd_7580937 := by
    simpa [prefixWord, tailWord_7580937, baseEnd_7580937] using wordTrace_append hprefix tailTrace_7580937
  have hstable : (prefixWord ++ tailWord_7580937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580937).length < 2 ^ (prefixWord ++ tailWord_7580937).sum := by decide
  have hdescent : baseEnd_7580937 < baseStart_7580937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580985 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7580985 : Nat := 118140960795 + 7580985 * 2 ^ 59
def prefixEnd_7580985 : Nat := 4983230072969 + 3 ^ 40 * 7580985 * 2
def baseEnd_7580985 : Nat := 3892689139525127095023191

theorem tailTrace_7580985 : CollatzResearch.WordTrace tailWord_7580985 prefixEnd_7580985 3892689139525127095023191 := by
  unfold tailWord_7580985
  simp only [CollatzResearch.WordTrace]
  refine ⟨276501238440393549004456409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184334158960262366002970939 276501238440393549004456409)
  ·
    refine ⟨207375928830295161753342307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276501238440393549004456409 207375928830295161753342307)
    ·
      refine ⟨311063893245442742630013461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207375928830295161753342307 311063893245442742630013461)
      ·
        refine ⟨14581119995880128560781881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 311063893245442742630013461 14581119995880128560781881)
        ·
          refine ⟨10935839996910096420586411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14581119995880128560781881 10935839996910096420586411)
          ·
            refine ⟨16403759995365144630879617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10935839996910096420586411 16403759995365144630879617)
            ·
              refine ⟨12302819996523858473159713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16403759995365144630879617 12302819996523858473159713)
              ·
                refine ⟨9227114997392893854869785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12302819996523858473159713 9227114997392893854869785)
                ·
                  refine ⟨6920336248044670391152339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9227114997392893854869785 6920336248044670391152339)
                  ·
                    refine ⟨10380504372067005586728509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6920336248044670391152339 10380504372067005586728509)
                    ·
                      refine ⟨3892689139525127095023191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10380504372067005586728509 3892689139525127095023191)
                      ·
                        rfl

theorem cell23_7580985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7580985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580985 prefixEnd_7580985 := by exact prefixLift 7580985
  have htrace : WordTrace (prefixWord ++ tailWord_7580985) baseStart_7580985 baseEnd_7580985 := by
    simpa [prefixWord, tailWord_7580985, baseEnd_7580985] using wordTrace_append hprefix tailTrace_7580985
  have hstable : (prefixWord ++ tailWord_7580985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580985).length < 2 ^ (prefixWord ++ tailWord_7580985).sum := by decide
  have hdescent : baseEnd_7580985 < baseStart_7580985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580997 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 11]
def baseStart_7580997 : Nat := 118140960795 + 7580997 * 2 ^ 59
def prefixEnd_7580997 : Nat := 4983230072969 + 3 ^ 40 * 7580997 * 2
def baseEnd_7580997 : Nat := 432521700143664560897015

theorem tailTrace_7580997 : CollatzResearch.WordTrace tailWord_7580997 prefixEnd_7580997 432521700143664560897015 := by
  unfold tailWord_7580997
  simp only [CollatzResearch.WordTrace]
  refine ⟨276501676116350075053893245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184334450744233383369262163 276501676116350075053893245)
  ·
    refine ⟨103688128543631278145209967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276501676116350075053893245 103688128543631278145209967)
    ·
      refine ⟨155532192815446917217814951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103688128543631278145209967 155532192815446917217814951)
      ·
        refine ⟨233298289223170375826722427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155532192815446917217814951 233298289223170375826722427)
        ·
          refine ⟨349947433834755563740083641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233298289223170375826722427 349947433834755563740083641)
          ·
            refine ⟨262460575376066672805062731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349947433834755563740083641 262460575376066672805062731)
            ·
              refine ⟨393690863064100009207594097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262460575376066672805062731 393690863064100009207594097)
              ·
                refine ⟨295268147298075006905695573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393690863064100009207594097 295268147298075006905695573)
                ·
                  refine ⟨432521700143664560897015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 295268147298075006905695573 432521700143664560897015)
                  ·
                    rfl

theorem cell23_7580997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_7580997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580997 prefixEnd_7580997 := by exact prefixLift 7580997
  have htrace : WordTrace (prefixWord ++ tailWord_7580997) baseStart_7580997 baseEnd_7580997 := by
    simpa [prefixWord, tailWord_7580997, baseEnd_7580997] using wordTrace_append hprefix tailTrace_7580997
  have hstable : (prefixWord ++ tailWord_7580997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580997).length < 2 ^ (prefixWord ++ tailWord_7580997).sum := by decide
  have hdescent : baseEnd_7580997 < baseStart_7580997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581004 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7581004 : Nat := 118140960795 + 7581004 * 2 ^ 59
def prefixEnd_7581004 : Nat := 4983230072969 + 3 ^ 40 * 7581004 * 2
def baseEnd_7581004 : Nat := 3892698895657562520685603

theorem tailTrace_7581004 : CollatzResearch.WordTrace tailWord_7581004 prefixEnd_7581004 3892698895657562520685603 := by
  unfold tailWord_7581004
  simp only [CollatzResearch.WordTrace]
  refine ⟨138250965713662357624699033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184334620951549810166265377 138250965713662357624699033)
  ·
    refine ⟨103688224285246768218524275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138250965713662357624699033 103688224285246768218524275)
    ·
      refine ⟨155532336427870152327786413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103688224285246768218524275 155532336427870152327786413)
      ·
        refine ⟨58324626160451307122919905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155532336427870152327786413 58324626160451307122919905)
        ·
          refine ⟨43743469620338480342189929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58324626160451307122919905 43743469620338480342189929)
          ·
            refine ⟨32807602215253860256642447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43743469620338480342189929 32807602215253860256642447)
            ·
              refine ⟨49211403322880790384963671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32807602215253860256642447 49211403322880790384963671)
              ·
                refine ⟨73817104984321185577445507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49211403322880790384963671 73817104984321185577445507)
                ·
                  refine ⟨110725657476481778366168261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73817104984321185577445507 110725657476481778366168261)
                  ·
                    refine ⟨20761060776840333443656549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110725657476481778366168261 20761060776840333443656549)
                    ·
                      refine ⟨3892698895657562520685603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20761060776840333443656549 3892698895657562520685603)
                      ·
                        rfl

theorem cell23_7581004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7581004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581004 prefixEnd_7581004 := by exact prefixLift 7581004
  have htrace : WordTrace (prefixWord ++ tailWord_7581004) baseStart_7581004 baseEnd_7581004 := by
    simpa [prefixWord, tailWord_7581004, baseEnd_7581004] using wordTrace_append hprefix tailTrace_7581004
  have hstable : (prefixWord ++ tailWord_7581004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581004).length < 2 ^ (prefixWord ++ tailWord_7581004).sum := by decide
  have hdescent : baseEnd_7581004 < baseStart_7581004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581007 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_7581007 : Nat := 118140960795 + 7581007 * 2 ^ 59
def prefixEnd_7581007 : Nat := 4983230072969 + 3 ^ 40 * 7581007 * 2
def baseEnd_7581007 : Nat := 3892700436099526008948089

theorem tailTrace_7581007 : CollatzResearch.WordTrace tailWord_7581007 prefixEnd_7581007 3892700436099526008948089 := by
  unfold tailWord_7581007
  simp only [CollatzResearch.WordTrace]
  refine ⟨276502040846313846761757275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184334693897542564507838183 276502040846313846761757275)
  ·
    refine ⟨414753061269470770142635913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276502040846313846761757275 414753061269470770142635913)
    ·
      refine ⟨311064795952103077606976935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414753061269470770142635913 311064795952103077606976935)
      ·
        refine ⟨466597193928154616410465403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311064795952103077606976935 466597193928154616410465403)
        ·
          refine ⟨699895790892231924615698105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466597193928154616410465403 699895790892231924615698105)
          ·
            refine ⟨524921843169173943461773579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699895790892231924615698105 524921843169173943461773579)
            ·
              refine ⟨787382764753760915192660369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524921843169173943461773579 787382764753760915192660369)
              ·
                refine ⟨590537073565320686394495277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787382764753760915192660369 590537073565320686394495277)
                ·
                  refine ⟨221451402586995257397935729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590537073565320686394495277 221451402586995257397935729)
                  ·
                    refine ⟨166088551940246443048451797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221451402586995257397935729 166088551940246443048451797)
                    ·
                      refine ⟨3892700436099526008948089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166088551940246443048451797 3892700436099526008948089)
                      ·
                        rfl

theorem cell23_7581007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_7581007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581007 prefixEnd_7581007 := by exact prefixLift 7581007
  have htrace : WordTrace (prefixWord ++ tailWord_7581007) baseStart_7581007 baseEnd_7581007 := by
    simpa [prefixWord, tailWord_7581007, baseEnd_7581007] using wordTrace_append hprefix tailTrace_7581007
  have hstable : (prefixWord ++ tailWord_7581007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581007).length < 2 ^ (prefixWord ++ tailWord_7581007).sum := by decide
  have hdescent : baseEnd_7581007 < baseStart_7581007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581008 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 2, 2, 2]
def baseStart_7581008 : Nat := 118140960795 + 7581008 * 2 ^ 59
def prefixEnd_7581008 : Nat := 4983230072969 + 3 ^ 40 * 7581008 * 2
def baseEnd_7581008 : Nat := 3892700949580180505035585

theorem tailTrace_7581008 : CollatzResearch.WordTrace tailWord_7581008 prefixEnd_7581008 3892700949580180505035585 := by
  unfold tailWord_7581008
  simp only [CollatzResearch.WordTrace]
  refine ⟨138251038659655111966271839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184334718212873482621695785 138251038659655111966271839)
  ·
    refine ⟨207376557989482667949407759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138251038659655111966271839 207376557989482667949407759)
    ·
      refine ⟨311064836984224001924111639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207376557989482667949407759 311064836984224001924111639)
      ·
        refine ⟨466597255476336002886167459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311064836984224001924111639 466597255476336002886167459)
        ·
          refine ⟨699895883214504004329251189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466597255476336002886167459 699895883214504004329251189)
          ·
            refine ⟨65615239051359750405867299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 699895883214504004329251189 65615239051359750405867299)
            ·
              refine ⟨98422858577039625608800949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65615239051359750405867299 98422858577039625608800949)
              ·
                refine ⟨9227142991597464900825089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98422858577039625608800949 9227142991597464900825089)
                ·
                  refine ⟨6920357243698098675618817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9227142991597464900825089 6920357243698098675618817)
                  ·
                    refine ⟨5190267932773574006714113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6920357243698098675618817 5190267932773574006714113)
                    ·
                      refine ⟨3892700949580180505035585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190267932773574006714113 3892700949580180505035585)
                      ·
                        rfl

theorem cell23_7581008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 2, 2].length) (baseStart_7581008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581008 prefixEnd_7581008 := by exact prefixLift 7581008
  have htrace : WordTrace (prefixWord ++ tailWord_7581008) baseStart_7581008 baseEnd_7581008 := by
    simpa [prefixWord, tailWord_7581008, baseEnd_7581008] using wordTrace_append hprefix tailTrace_7581008
  have hstable : (prefixWord ++ tailWord_7581008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581008).length < 2 ^ (prefixWord ++ tailWord_7581008).sum := by decide
  have hdescent : baseEnd_7581008 < baseStart_7581008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581181 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_7581181 : Nat := 118140960795 + 7581181 * 2 ^ 59
def prefixEnd_7581181 : Nat := 4983230072969 + 3 ^ 40 * 7581181 * 2
def baseEnd_7581181 : Nat := 1297596593911136109390763

theorem tailTrace_7581181 : CollatzResearch.WordTrace tailWord_7581181 prefixEnd_7581181 1297596593911136109390763 := by
  unfold tailWord_7581181
  simp only [CollatzResearch.WordTrace]
  refine ⟨276508387147683474478591397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184338924765122316319060931 276508387147683474478591397)
  ·
    refine ⟨51845322590190651464735887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276508387147683474478591397 51845322590190651464735887)
    ·
      refine ⟨77767983885285977197103831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51845322590190651464735887 77767983885285977197103831)
      ·
        refine ⟨116651975827928965795655747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77767983885285977197103831 116651975827928965795655747)
        ·
          refine ⟨174977963741893448693483621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116651975827928965795655747 174977963741893448693483621)
          ·
            refine ⟨32808368201605021630028179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174977963741893448693483621 32808368201605021630028179)
            ·
              refine ⟨49212552302407532445042269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32808368201605021630028179 49212552302407532445042269)
              ·
                refine ⟨18454707113402824666890851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49212552302407532445042269 18454707113402824666890851)
                ·
                  refine ⟨27682060670104237000336277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18454707113402824666890851 27682060670104237000336277)
                  ·
                    refine ⟨1297596593911136109390763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27682060670104237000336277 1297596593911136109390763)
                    ·
                      rfl

theorem cell23_7581181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_7581181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581181 prefixEnd_7581181 := by exact prefixLift 7581181
  have htrace : WordTrace (prefixWord ++ tailWord_7581181) baseStart_7581181 baseEnd_7581181 := by
    simpa [prefixWord, tailWord_7581181, baseEnd_7581181] using wordTrace_append hprefix tailTrace_7581181
  have hstable : (prefixWord ++ tailWord_7581181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581181).length < 2 ^ (prefixWord ++ tailWord_7581181).sum := by decide
  have hdescent : baseEnd_7581181 < baseStart_7581181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581201 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_7581201 : Nat := 118140960795 + 7581201 * 2 ^ 59
def prefixEnd_7581201 : Nat := 4983230072969 + 3 ^ 40 * 7581201 * 2
def baseEnd_7581201 : Nat := 3892800051346498249922197

theorem tailTrace_7581201 : CollatzResearch.WordTrace tailWord_7581201 prefixEnd_7581201 3892800051346498249922197 := by
  unfold tailWord_7581201
  simp only [CollatzResearch.WordTrace]
  refine ⟨276509116607611017894319457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184339411071740678596212971 276509116607611017894319457)
  ·
    refine ⟨207381837455708263420739593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276509116607611017894319457 207381837455708263420739593)
    ·
      refine ⟨155536378091781197565554695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207381837455708263420739593 155536378091781197565554695)
      ·
        refine ⟨233304567137671796348332043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155536378091781197565554695 233304567137671796348332043)
        ·
          refine ⟨349956850706507694522498065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233304567137671796348332043 349956850706507694522498065)
          ·
            refine ⟨262467638029880770891873549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349956850706507694522498065 262467638029880770891873549)
            ·
              refine ⟨98425364261205289084452581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262467638029880770891873549 98425364261205289084452581)
              ·
                refine ⟨18454755798975991703334859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98425364261205289084452581 18454755798975991703334859)
                ·
                  refine ⟨27682133698463987555002289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18454755798975991703334859 27682133698463987555002289)
                  ·
                    refine ⟨20761600273847990666251717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27682133698463987555002289 20761600273847990666251717)
                    ·
                      refine ⟨3892800051346498249922197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20761600273847990666251717 3892800051346498249922197)
                      ·
                        rfl

theorem cell23_7581201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_7581201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581201 prefixEnd_7581201 := by exact prefixLift 7581201
  have htrace : WordTrace (prefixWord ++ tailWord_7581201) baseStart_7581201 baseEnd_7581201 := by
    simpa [prefixWord, tailWord_7581201, baseEnd_7581201] using wordTrace_append hprefix tailTrace_7581201
  have hstable : (prefixWord ++ tailWord_7581201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581201).length < 2 ^ (prefixWord ++ tailWord_7581201).sum := by decide
  have hdescent : baseEnd_7581201 < baseStart_7581201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581205 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_7581205 : Nat := 118140960795 + 7581205 * 2 ^ 59
def prefixEnd_7581205 : Nat := 4983230072969 + 3 ^ 40 * 7581205 * 2
def baseEnd_7581205 : Nat := 3892802105269116234272179

theorem tailTrace_7581205 : CollatzResearch.WordTrace tailWord_7581205 prefixEnd_7581205 3892802105269116234272179 := by
  unfold tailWord_7581205
  simp only [CollatzResearch.WordTrace]
  refine ⟨276509262499596526577465069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184339508333064351051643379 276509262499596526577465069)
  ·
    refine ⟨103690973437348697466549401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276509262499596526577465069 103690973437348697466549401)
    ·
      refine ⟨77768230078011523099912051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103690973437348697466549401 77768230078011523099912051)
      ·
        refine ⟨116652345117017284649868077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77768230078011523099912051 116652345117017284649868077)
        ·
          refine ⟨43744629418881481743700529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116652345117017284649868077 43744629418881481743700529)
          ·
            refine ⟨32808472064161111307775397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43744629418881481743700529 32808472064161111307775397)
            ·
              refine ⟨6151588512030208370207887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32808472064161111307775397 6151588512030208370207887)
              ·
                refine ⟨9227382768045312555311831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151588512030208370207887 9227382768045312555311831)
                ·
                  refine ⟨13841074152067968832967747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227382768045312555311831 13841074152067968832967747)
                  ·
                    refine ⟨20761611228101953249451621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13841074152067968832967747 20761611228101953249451621)
                    ·
                      refine ⟨3892802105269116234272179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20761611228101953249451621 3892802105269116234272179)
                      ·
                        rfl

theorem cell23_7581205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_7581205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581205 prefixEnd_7581205 := by exact prefixLift 7581205
  have htrace : WordTrace (prefixWord ++ tailWord_7581205) baseStart_7581205 baseEnd_7581205 := by
    simpa [prefixWord, tailWord_7581205, baseEnd_7581205] using wordTrace_append hprefix tailTrace_7581205
  have hstable : (prefixWord ++ tailWord_7581205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581205).length < 2 ^ (prefixWord ++ tailWord_7581205).sum := by decide
  have hdescent : baseEnd_7581205 < baseStart_7581205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581245 : List Nat := [1, 4, 1, 3, 3, 2, 2, 7]
def baseStart_7581245 : Nat := 118140960795 + 7581245 * 2 ^ 59
def prefixEnd_7581245 : Nat := 4983230072969 + 3 ^ 40 * 7581245 * 2
def baseEnd_7581245 : Nat := 144178616462788743621185

theorem tailTrace_7581245 : CollatzResearch.WordTrace tailWord_7581245 prefixEnd_7581245 144178616462788743621185 := by
  unfold tailWord_7581245
  simp only [CollatzResearch.WordTrace]
  refine ⟨276510721419451613408921189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184340480946301075605947459 276510721419451613408921189)
  ·
    refine ⟨51845760266147177514172723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276510721419451613408921189 51845760266147177514172723)
    ·
      refine ⟨77768640399220766271259085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51845760266147177514172723 77768640399220766271259085)
      ·
        refine ⟨29163240149707787351722157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77768640399220766271259085 29163240149707787351722157)
        ·
          refine ⟨10936215056140420256895809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29163240149707787351722157 10936215056140420256895809)
          ·
            refine ⟨8202161292105315192671857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10936215056140420256895809 8202161292105315192671857)
            ·
              refine ⟨6151620969078986394503893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8202161292105315192671857 6151620969078986394503893)
              ·
                refine ⟨144178616462788743621185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6151620969078986394503893 144178616462788743621185)
                ·
                  rfl

theorem cell23_7581245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 7].length) (baseStart_7581245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581245 prefixEnd_7581245 := by exact prefixLift 7581245
  have htrace : WordTrace (prefixWord ++ tailWord_7581245) baseStart_7581245 baseEnd_7581245 := by
    simpa [prefixWord, tailWord_7581245, baseEnd_7581245] using wordTrace_append hprefix tailTrace_7581245
  have hstable : (prefixWord ++ tailWord_7581245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581245).length < 2 ^ (prefixWord ++ tailWord_7581245).sum := by decide
  have hdescent : baseEnd_7581245 < baseStart_7581245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581265 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 1, 3, 2]
def baseStart_7581265 : Nat := 118140960795 + 7581265 * 2 ^ 59
def prefixEnd_7581265 : Nat := 4983230072969 + 3 ^ 40 * 7581265 * 2
def baseEnd_7581265 : Nat := 3892832914108385999521903

theorem tailTrace_7581265 : CollatzResearch.WordTrace tailWord_7581265 prefixEnd_7581265 3892832914108385999521903 := by
  unfold tailWord_7581265
  simp only [CollatzResearch.WordTrace]
  refine ⟨276511450879379156824649249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184340967252919437883099499 276511450879379156824649249)
  ·
    refine ⟨207383588159534367618486937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276511450879379156824649249 207383588159534367618486937)
    ·
      refine ⟨155537691119650775713865203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207383588159534367618486937 155537691119650775713865203)
      ·
        refine ⟨233306536679476163570797805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155537691119650775713865203 233306536679476163570797805)
        ·
          refine ⟨87489951254803561339049177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233306536679476163570797805 87489951254803561339049177)
          ·
            refine ⟨65617463441102671004286883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87489951254803561339049177 65617463441102671004286883)
            ·
              refine ⟨98426195161654006506430325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65617463441102671004286883 98426195161654006506430325)
              ·
                refine ⟨9227455796405063109977843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98426195161654006506430325 9227455796405063109977843)
                ·
                  refine ⟨13841183694607594664966765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227455796405063109977843 13841183694607594664966765)
                  ·
                    refine ⟨5190443885477847999362537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13841183694607594664966765 5190443885477847999362537)
                    ·
                      refine ⟨3892832914108385999521903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190443885477847999362537 3892832914108385999521903)
                      ·
                        rfl

theorem cell23_7581265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_7581265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581265 prefixEnd_7581265 := by exact prefixLift 7581265
  have htrace : WordTrace (prefixWord ++ tailWord_7581265) baseStart_7581265 baseEnd_7581265 := by
    simpa [prefixWord, tailWord_7581265, baseEnd_7581265] using wordTrace_append hprefix tailTrace_7581265
  have hstable : (prefixWord ++ tailWord_7581265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581265).length < 2 ^ (prefixWord ++ tailWord_7581265).sum := by decide
  have hdescent : baseEnd_7581265 < baseStart_7581265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581281 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_7581281 : Nat := 118140960795 + 7581281 * 2 ^ 59
def prefixEnd_7581281 : Nat := 4983230072969 + 3 ^ 40 * 7581281 * 2
def baseEnd_7581281 : Nat := 3892841129798857936921829

theorem tailTrace_7581281 : CollatzResearch.WordTrace tailWord_7581281 prefixEnd_7581281 3892841129798857936921829 := by
  unfold tailWord_7581281
  simp only [CollatzResearch.WordTrace]
  refine ⟨276512034447321191557231697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184341356298214127704821131 276512034447321191557231697)
  ·
    refine ⟨207384025835490893667923773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276512034447321191557231697 207384025835490893667923773)
    ·
      refine ⟨77769009688309085125471415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207384025835490893667923773 77769009688309085125471415)
      ·
        refine ⟨116653514532463627688207123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77769009688309085125471415 116653514532463627688207123)
        ·
          refine ⟨174980271798695441532310685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116653514532463627688207123 174980271798695441532310685)
          ·
            refine ⟨65617601924510790574616507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174980271798695441532310685 65617601924510790574616507)
            ·
              refine ⟨98426402886766185861924761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65617601924510790574616507 98426402886766185861924761)
              ·
                refine ⟨73819802165074639396443571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98426402886766185861924761 73819802165074639396443571)
                ·
                  refine ⟨110729703247611959094665357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73819802165074639396443571 110729703247611959094665357)
                  ·
                    refine ⟨41523638717854484660499509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110729703247611959094665357 41523638717854484660499509)
                    ·
                      refine ⟨3892841129798857936921829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41523638717854484660499509 3892841129798857936921829)
                      ·
                        rfl

theorem cell23_7581281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_7581281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581281 prefixEnd_7581281 := by exact prefixLift 7581281
  have htrace : WordTrace (prefixWord ++ tailWord_7581281) baseStart_7581281 baseEnd_7581281 := by
    simpa [prefixWord, tailWord_7581281, baseEnd_7581281] using wordTrace_append hprefix tailTrace_7581281
  have hstable : (prefixWord ++ tailWord_7581281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581281).length < 2 ^ (prefixWord ++ tailWord_7581281).sum := by decide
  have hdescent : baseEnd_7581281 < baseStart_7581281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581291 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4]
def baseStart_7581291 : Nat := 118140960795 + 7581291 * 2 ^ 59
def prefixEnd_7581291 : Nat := 4983230072969 + 3 ^ 40 * 7581291 * 2
def baseEnd_7581291 : Nat := 3892846264605402897796783

theorem tailTrace_7581291 : CollatzResearch.WordTrace tailWord_7581291 prefixEnd_7581291 3892846264605402897796783 := by
  unfold tailWord_7581291
  simp only [CollatzResearch.WordTrace]
  refine ⟨276512399177284963265095727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184341599451523308843397151 276512399177284963265095727)
  ·
    refine ⟨414768598765927444897643591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276512399177284963265095727 414768598765927444897643591)
    ·
      refine ⟨622152898148891167346465387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414768598765927444897643591 622152898148891167346465387)
      ·
        refine ⟨933229347223336751019698081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622152898148891167346465387 933229347223336751019698081)
        ·
          refine ⟨699922010417502563264773561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933229347223336751019698081 699922010417502563264773561)
          ·
            refine ⟨524941507813126922448580171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699922010417502563264773561 524941507813126922448580171)
            ·
              refine ⟨787412261719690383672870257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524941507813126922448580171 787412261719690383672870257)
              ·
                refine ⟨590559196289767787754652693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787412261719690383672870257 590559196289767787754652693)
                ·
                  refine ⟨27682462326082865050999345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 590559196289767787754652693 27682462326082865050999345)
                  ·
                    refine ⟨20761846744562148788249509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27682462326082865050999345 20761846744562148788249509)
                    ·
                      refine ⟨3892846264605402897796783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20761846744562148788249509 3892846264605402897796783)
                      ·
                        rfl

theorem cell23_7581291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_7581291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581291 prefixEnd_7581291 := by exact prefixLift 7581291
  have htrace : WordTrace (prefixWord ++ tailWord_7581291) baseStart_7581291 baseEnd_7581291 := by
    simpa [prefixWord, tailWord_7581291, baseEnd_7581291] using wordTrace_append hprefix tailTrace_7581291
  have hstable : (prefixWord ++ tailWord_7581291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581291).length < 2 ^ (prefixWord ++ tailWord_7581291).sum := by decide
  have hdescent : baseEnd_7581291 < baseStart_7581291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581298 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_7581298 : Nat := 118140960795 + 7581298 * 2 ^ 59
def prefixEnd_7581298 : Nat := 4983230072969 + 3 ^ 40 * 7581298 * 2
def baseEnd_7581298 : Nat := 3892849858969984370409251

theorem tailTrace_7581298 : CollatzResearch.WordTrace tailWord_7581298 prefixEnd_7581298 3892849858969984370409251 := by
  unfold tailWord_7581298
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128163622064900865150137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184341769658839735640400365 69128163622064900865150137)
  ·
    refine ⟨51846122716548675648862603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69128163622064900865150137 51846122716548675648862603)
    ·
      refine ⟨77769184074823013473293905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51846122716548675648862603 77769184074823013473293905)
      ·
        refine ⟨58326888056117260104970429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77769184074823013473293905 58326888056117260104970429)
        ·
          refine ⟨21872583021043972539363911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58326888056117260104970429 21872583021043972539363911)
          ·
            refine ⟨32808874531565958809045867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21872583021043972539363911 32808874531565958809045867)
            ·
              refine ⟨49213311797348938213568801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32808874531565958809045867 49213311797348938213568801)
              ·
                refine ⟨36909983848011703660176601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49213311797348938213568801 36909983848011703660176601)
                ·
                  refine ⟨27682487886008777745132451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36909983848011703660176601 27682487886008777745132451)
                  ·
                    refine ⟨41523731829013166617698677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27682487886008777745132451 41523731829013166617698677)
                    ·
                      refine ⟨3892849858969984370409251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41523731829013166617698677 3892849858969984370409251)
                      ·
                        rfl

theorem cell23_7581298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_7581298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581298 prefixEnd_7581298 := by exact prefixLift 7581298
  have htrace : WordTrace (prefixWord ++ tailWord_7581298) baseStart_7581298 baseEnd_7581298 := by
    simpa [prefixWord, tailWord_7581298, baseEnd_7581298] using wordTrace_append hprefix tailTrace_7581298
  have hstable : (prefixWord ++ tailWord_7581298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581298).length < 2 ^ (prefixWord ++ tailWord_7581298).sum := by decide
  have hdescent : baseEnd_7581298 < baseStart_7581298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581335 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 5]
def baseStart_7581335 : Nat := 118140960795 + 7581335 * 2 ^ 59
def prefixEnd_7581335 : Nat := 4983230072969 + 3 ^ 40 * 7581335 * 2
def baseEnd_7581335 : Nat := 432540984194911191738509

theorem tailTrace_7581335 : CollatzResearch.WordTrace tailWord_7581335 prefixEnd_7581335 432540984194911191738509 := by
  unfold tailWord_7581335
  simp only [CollatzResearch.WordTrace]
  refine ⟨276514003989125558779697459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184342669326083705853131639 276514003989125558779697459)
  ·
    refine ⟨414771005983688338169546189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276514003989125558779697459 414771005983688338169546189)
    ·
      refine ⟨155539127243883126813579821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414771005983688338169546189 155539127243883126813579821)
      ·
        refine ⟨58327172716456172555092433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155539127243883126813579821 58327172716456172555092433)
        ·
          refine ⟨43745379537342129416319325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58327172716456172555092433 43745379537342129416319325)
          ·
            refine ⟨16404517326503298531119747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43745379537342129416319325 16404517326503298531119747)
            ·
              refine ⟨24606775989754947796679621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16404517326503298531119747 24606775989754947796679621)
              ·
                refine ⟨4613770498079052711877429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24606775989754947796679621 4613770498079052711877429)
                ·
                  refine ⟨432540984194911191738509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4613770498079052711877429 432540984194911191738509)
                  ·
                    rfl

theorem cell23_7581335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 5].length) (baseStart_7581335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581335 prefixEnd_7581335 := by exact prefixLift 7581335
  have htrace : WordTrace (prefixWord ++ tailWord_7581335) baseStart_7581335 baseEnd_7581335 := by
    simpa [prefixWord, tailWord_7581335, baseEnd_7581335] using wordTrace_append hprefix tailTrace_7581335
  have hstable : (prefixWord ++ tailWord_7581335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581335).length < 2 ^ (prefixWord ++ tailWord_7581335).sum := by decide
  have hdescent : baseEnd_7581335 < baseStart_7581335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581345 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7581345 : Nat := 118140960795 + 7581345 * 2 ^ 59
def prefixEnd_7581345 : Nat := 4983230072969 + 3 ^ 40 * 7581345 * 2
def baseEnd_7581345 : Nat := 3892873992560745686521535

theorem tailTrace_7581345 : CollatzResearch.WordTrace tailWord_7581345 prefixEnd_7581345 3892873992560745686521535 := by
  unfold tailWord_7581345
  simp only [CollatzResearch.WordTrace]
  refine ⟨276514368719089330487561489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184342912479392886991707659 276514368719089330487561489)
  ·
    refine ⟨207385776539316997865671117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276514368719089330487561489 207385776539316997865671117)
    ·
      refine ⟨77769666202243874199626669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207385776539316997865671117 77769666202243874199626669)
      ·
        refine ⟨29163624825841452824860001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77769666202243874199626669 29163624825841452824860001)
        ·
          refine ⟨21872718619381089618645001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29163624825841452824860001 21872718619381089618645001)
          ·
            refine ⟨16404538964535817213983751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21872718619381089618645001 16404538964535817213983751)
            ·
              refine ⟨24606808446803725820975627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16404538964535817213983751 24606808446803725820975627)
              ·
                refine ⟨36910212670205588731463441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24606808446803725820975627 36910212670205588731463441)
                ·
                  refine ⟨27682659502654191548597581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36910212670205588731463441 27682659502654191548597581)
                  ·
                    refine ⟨10380997313495321830724093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27682659502654191548597581 10380997313495321830724093)
                    ·
                      refine ⟨3892873992560745686521535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10380997313495321830724093 3892873992560745686521535)
                      ·
                        rfl

theorem cell23_7581345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7581345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581345 prefixEnd_7581345 := by exact prefixLift 7581345
  have htrace : WordTrace (prefixWord ++ tailWord_7581345) baseStart_7581345 baseEnd_7581345 := by
    simpa [prefixWord, tailWord_7581345, baseEnd_7581345] using wordTrace_append hprefix tailTrace_7581345
  have hstable : (prefixWord ++ tailWord_7581345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581345).length < 2 ^ (prefixWord ++ tailWord_7581345).sum := by decide
  have hdescent : baseEnd_7581345 < baseStart_7581345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581365 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_7581365 : Nat := 118140960795 + 7581365 * 2 ^ 59
def prefixEnd_7581365 : Nat := 4983230072969 + 3 ^ 40 * 7581365 * 2
def baseEnd_7581365 : Nat := 1297628087391278536090481

theorem tailTrace_7581365 : CollatzResearch.WordTrace tailWord_7581365 prefixEnd_7581365 1297628087391278536090481 := by
  unfold tailWord_7581365
  simp only [CollatzResearch.WordTrace]
  refine ⟨276515098179016873903289549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184343398786011249268859699 276515098179016873903289549)
  ·
    refine ⟨103693161817131327713733581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276515098179016873903289549 103693161817131327713733581)
    ·
      refine ⟨38884935681424247892650093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103693161817131327713733581 38884935681424247892650093)
      ·
        refine ⟨14581850880534092959743785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38884935681424247892650093 14581850880534092959743785)
        ·
          refine ⟨10936388160400569719807839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14581850880534092959743785 10936388160400569719807839)
          ·
            refine ⟨16404582240600854579711759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936388160400569719807839 16404582240600854579711759)
            ·
              refine ⟨24606873360901281869567639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16404582240600854579711759 24606873360901281869567639)
              ·
                refine ⟨36910310041351922804351459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24606873360901281869567639 36910310041351922804351459)
                ·
                  refine ⟨55365465062027884206527189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36910310041351922804351459 55365465062027884206527189)
                  ·
                    refine ⟨1297628087391278536090481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55365465062027884206527189 1297628087391278536090481)
                    ·
                      rfl

theorem cell23_7581365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_7581365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581365 prefixEnd_7581365 := by exact prefixLift 7581365
  have htrace : WordTrace (prefixWord ++ tailWord_7581365) baseStart_7581365 baseEnd_7581365 := by
    simpa [prefixWord, tailWord_7581365, baseEnd_7581365] using wordTrace_append hprefix tailTrace_7581365
  have hstable : (prefixWord ++ tailWord_7581365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581365).length < 2 ^ (prefixWord ++ tailWord_7581365).sum := by decide
  have hdescent : baseEnd_7581365 < baseStart_7581365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581408 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 6]
def baseStart_7581408 : Nat := 118140960795 + 7581408 * 2 ^ 59
def prefixEnd_7581408 : Nat := 4983230072969 + 3 ^ 40 * 7581408 * 2
def baseEnd_7581408 : Nat := 432545149093553215559305

theorem tailTrace_7581408 : CollatzResearch.WordTrace tailWord_7581408 prefixEnd_7581408 432545149093553215559305 := by
  unfold tailWord_7581408
  simp only [CollatzResearch.WordTrace]
  refine ⟨138258333258930546123552439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184344444345240728164736585 138258333258930546123552439)
  ·
    refine ⟨207387499888395819185328659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138258333258930546123552439 207387499888395819185328659)
    ·
      refine ⟨311081249832593728777992989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207387499888395819185328659 311081249832593728777992989)
      ·
        refine ⟨116655468687222648291747371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311081249832593728777992989 116655468687222648291747371)
        ·
          refine ⟨174983203030833972437621057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116655468687222648291747371 174983203030833972437621057)
          ·
            refine ⟨131237402273125479328215793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174983203030833972437621057 131237402273125479328215793)
            ·
              refine ⟨98428051704844109496161845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131237402273125479328215793 98428051704844109496161845)
              ·
                refine ⟨9227629847329135265265173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98428051704844109496161845 9227629847329135265265173)
                ·
                  refine ⟨432545149093553215559305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9227629847329135265265173 432545149093553215559305)
                  ·
                    rfl

theorem cell23_7581408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_7581408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581408 prefixEnd_7581408 := by exact prefixLift 7581408
  have htrace : WordTrace (prefixWord ++ tailWord_7581408) baseStart_7581408 baseEnd_7581408 := by
    simpa [prefixWord, tailWord_7581408, baseEnd_7581408] using wordTrace_append hprefix tailTrace_7581408
  have hstable : (prefixWord ++ tailWord_7581408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581408).length < 2 ^ (prefixWord ++ tailWord_7581408).sum := by decide
  have hdescent : baseEnd_7581408 < baseStart_7581408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581452 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_7581452 : Nat := 118140960795 + 7581452 * 2 ^ 59
def prefixEnd_7581452 : Nat := 4983230072969 + 3 ^ 40 * 7581452 * 2
def baseEnd_7581452 : Nat := 3892928934990776767883543

theorem tailTrace_7581452 : CollatzResearch.WordTrace tailWord_7581452 prefixEnd_7581452 3892928934990776767883543 := by
  unfold tailWord_7581452
  simp only [CollatzResearch.WordTrace]
  refine ⟨138259135664850843880853305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184345514219801125174471073 138259135664850843880853305)
  ·
    refine ⟨103694351748638132910639979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138259135664850843880853305 103694351748638132910639979)
    ·
      refine ⟨155541527622957199365959969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103694351748638132910639979 155541527622957199365959969)
      ·
        refine ⟨116656145717217899524469977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155541527622957199365959969 116656145717217899524469977)
        ·
          refine ⟨87492109287913424643352483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116656145717217899524469977 87492109287913424643352483)
          ·
            refine ⟨131238163931870136965028725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87492109287913424643352483 131238163931870136965028725)
            ·
              refine ⟨12303577868612825340471443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131238163931870136965028725 12303577868612825340471443)
              ·
                refine ⟨18455366802919238010707165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12303577868612825340471443 18455366802919238010707165)
                ·
                  refine ⟨6920762551094714254015187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18455366802919238010707165 6920762551094714254015187)
                  ·
                    refine ⟨10381143826642071381022781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6920762551094714254015187 10381143826642071381022781)
                    ·
                      refine ⟨3892928934990776767883543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381143826642071381022781 3892928934990776767883543)
                      ·
                        rfl

theorem cell23_7581452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_7581452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581452 prefixEnd_7581452 := by exact prefixLift 7581452
  have htrace : WordTrace (prefixWord ++ tailWord_7581452) baseStart_7581452 baseEnd_7581452 := by
    simpa [prefixWord, tailWord_7581452, baseEnd_7581452] using wordTrace_append hprefix tailTrace_7581452
  have hstable : (prefixWord ++ tailWord_7581452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581452).length < 2 ^ (prefixWord ++ tailWord_7581452).sum := by decide
  have hdescent : baseEnd_7581452 < baseStart_7581452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581475 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 6, 2]
def baseStart_7581475 : Nat := 118140960795 + 7581475 * 2 ^ 59
def prefixEnd_7581475 : Nat := 4983230072969 + 3 ^ 40 * 7581475 * 2
def baseEnd_7581475 : Nat := 3892940745045830177895937

theorem tailTrace_7581475 : CollatzResearch.WordTrace tailWord_7581475 prefixEnd_7581475 3892940745045830177895937 := by
  unfold tailWord_7581475
  simp only [CollatzResearch.WordTrace]
  refine ⟨276519110208618362689793879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184346073472412241793195919 276519110208618362689793879)
  ·
    refine ⟨414778665312927544034690819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276519110208618362689793879 414778665312927544034690819)
    ·
      refine ⟨622167997969391316052036229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414778665312927544034690819 622167997969391316052036229)
      ·
        refine ⟨116656499619260871759756793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 622167997969391316052036229 116656499619260871759756793)
        ·
          refine ⟨87492374714445653819817595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116656499619260871759756793 87492374714445653819817595)
          ·
            refine ⟨131238562071668480729726393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87492374714445653819817595 131238562071668480729726393)
            ·
              refine ⟨98428921553751360547294795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131238562071668480729726393 98428921553751360547294795)
              ·
                refine ⟨147643382330627040820942193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98428921553751360547294795 147643382330627040820942193)
                ·
                  refine ⟨110732536747970280615706645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147643382330627040820942193 110732536747970280615706645)
                  ·
                    refine ⟨5190587660061106903861249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110732536747970280615706645 5190587660061106903861249)
                    ·
                      refine ⟨3892940745045830177895937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190587660061106903861249 3892940745045830177895937)
                      ·
                        rfl

theorem cell23_7581475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_7581475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581475 prefixEnd_7581475 := by exact prefixLift 7581475
  have htrace : WordTrace (prefixWord ++ tailWord_7581475) baseStart_7581475 baseEnd_7581475 := by
    simpa [prefixWord, tailWord_7581475, baseEnd_7581475] using wordTrace_append hprefix tailTrace_7581475
  have hstable : (prefixWord ++ tailWord_7581475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581475).length < 2 ^ (prefixWord ++ tailWord_7581475).sum := by decide
  have hdescent : baseEnd_7581475 < baseStart_7581475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581498 : List Nat := [3, 1, 1, 1, 5, 12]
def baseStart_7581498 : Nat := 118140960795 + 7581498 * 2 ^ 59
def prefixEnd_7581498 : Nat := 4983230072969 + 3 ^ 40 * 7581498 * 2
def baseEnd_7581498 : Nat := 16020380885188821349417

theorem tailTrace_7581498 : CollatzResearch.WordTrace tailWord_7581498 prefixEnd_7581498 16020380885188821349417 := by
  unfold tailWord_7581498
  simp only [CollatzResearch.WordTrace]
  refine ⟨69129987271883759404470287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184346632725023358411920765 69129987271883759404470287)
  ·
    refine ⟨103694980907825639106705431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69129987271883759404470287 103694980907825639106705431)
    ·
      refine ⟨155542471361738458660058147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103694980907825639106705431 155542471361738458660058147)
      ·
        refine ⟨233313707042607687990087221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155542471361738458660058147 233313707042607687990087221)
        ·
          refine ⟨21873160035244470749070677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233313707042607687990087221 21873160035244470749070677)
          ·
            refine ⟨16020380885188821349417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21873160035244470749070677 16020380885188821349417)
            ·
              rfl

theorem cell23_7581498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 12].length) (baseStart_7581498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581498 prefixEnd_7581498 := by exact prefixLift 7581498
  have htrace : WordTrace (prefixWord ++ tailWord_7581498) baseStart_7581498 baseEnd_7581498 := by
    simpa [prefixWord, tailWord_7581498, baseEnd_7581498] using wordTrace_append hprefix tailTrace_7581498
  have hstable : (prefixWord ++ tailWord_7581498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581498).length < 2 ^ (prefixWord ++ tailWord_7581498).sum := by decide
  have hdescent : baseEnd_7581498 < baseStart_7581498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581503 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 1, 1, 3]
def baseStart_7581503 : Nat := 118140960795 + 7581503 * 2 ^ 59
def prefixEnd_7581503 : Nat := 4983230072969 + 3 ^ 40 * 7581503 * 2
def baseEnd_7581503 : Nat := 3892955122504156068345809

theorem tailTrace_7581503 : CollatzResearch.WordTrace tailWord_7581503 prefixEnd_7581503 3892955122504156068345809 := by
  unfold tailWord_7581503
  simp only [CollatzResearch.WordTrace]
  refine ⟨276520131452516923471813163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184346754301677948981208775 276520131452516923471813163)
  ·
    refine ⟨414780197178775385207719745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276520131452516923471813163 414780197178775385207719745)
    ·
      refine ⟨311085147884081538905789809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414780197178775385207719745 311085147884081538905789809)
      ·
        refine ⟨233313860913061154179342357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311085147884081538905789809 233313860913061154179342357)
        ·
          refine ⟨10936587230299741602156673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233313860913061154179342357 10936587230299741602156673)
          ·
            refine ⟨8202440422724806201617505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10936587230299741602156673 8202440422724806201617505)
            ·
              refine ⟨6151830317043604651213129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8202440422724806201617505 6151830317043604651213129)
              ·
                refine ⟨4613872737782703488409847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6151830317043604651213129 4613872737782703488409847)
                ·
                  refine ⟨6920809106674055232614771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613872737782703488409847 6920809106674055232614771)
                  ·
                    refine ⟨10381213660011082848922157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6920809106674055232614771 10381213660011082848922157)
                    ·
                      refine ⟨3892955122504156068345809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381213660011082848922157 3892955122504156068345809)
                      ·
                        rfl

theorem cell23_7581503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_7581503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581503 prefixEnd_7581503 := by exact prefixLift 7581503
  have htrace : WordTrace (prefixWord ++ tailWord_7581503) baseStart_7581503 baseEnd_7581503 := by
    simpa [prefixWord, tailWord_7581503, baseEnd_7581503] using wordTrace_append hprefix tailTrace_7581503
  have hstable : (prefixWord ++ tailWord_7581503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581503).length < 2 ^ (prefixWord ++ tailWord_7581503).sum := by decide
  have hdescent : baseEnd_7581503 < baseStart_7581503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581522 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_7581522 : Nat := 118140960795 + 7581522 * 2 ^ 59
def prefixEnd_7581522 : Nat := 4983230072969 + 3 ^ 40 * 7581522 * 2
def baseEnd_7581522 : Nat := 3892964878636591494008221

theorem tailTrace_7581522 : CollatzResearch.WordTrace tailWord_7581522 prefixEnd_7581522 3892964878636591494008221 := by
  unfold tailWord_7581522
  simp only [CollatzResearch.WordTrace]
  refine ⟨69130206109862022429188705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184347216292965393144503213 69130206109862022429188705)
  ·
    refine ⟨51847654582396516821891529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69130206109862022429188705 51847654582396516821891529)
    ·
      refine ⟨38885740936797387616418647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51847654582396516821891529 38885740936797387616418647)
      ·
        refine ⟨58328611405196081424627971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38885740936797387616418647 58328611405196081424627971)
        ·
          refine ⟨87492917107794122136941957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58328611405196081424627971 87492917107794122136941957)
          ·
            refine ⟨16404921957711397900676617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87492917107794122136941957 16404921957711397900676617)
            ·
              refine ⟨12303691468283548425507463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16404921957711397900676617 12303691468283548425507463)
              ·
                refine ⟨18455537202425322638261195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12303691468283548425507463 18455537202425322638261195)
                ·
                  refine ⟨27683305803637983957391793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18455537202425322638261195 27683305803637983957391793)
                  ·
                    refine ⟨20762479352728487968043845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27683305803637983957391793 20762479352728487968043845)
                    ·
                      refine ⟨3892964878636591494008221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20762479352728487968043845 3892964878636591494008221)
                      ·
                        rfl

theorem cell23_7581522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_7581522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581522 prefixEnd_7581522 := by exact prefixLift 7581522
  have htrace : WordTrace (prefixWord ++ tailWord_7581522) baseStart_7581522 baseEnd_7581522 := by
    simpa [prefixWord, tailWord_7581522, baseEnd_7581522] using wordTrace_append hprefix tailTrace_7581522
  have hstable : (prefixWord ++ tailWord_7581522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581522).length < 2 ^ (prefixWord ++ tailWord_7581522).sum := by decide
  have hdescent : baseEnd_7581522 < baseStart_7581522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581546 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7581546 : Nat := 118140960795 + 7581546 * 2 ^ 59
def prefixEnd_7581546 : Nat := 4983230072969 + 3 ^ 40 * 7581546 * 2
def baseEnd_7581546 : Nat := 3892977202172299400108111

theorem tailTrace_7581546 : CollatzResearch.WordTrace tailWord_7581546 prefixEnd_7581546 3892977202172299400108111 := by
  unfold tailWord_7581546
  simp only [CollatzResearch.WordTrace]
  refine ⟨69130424947840285453907123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184347799860907427877085661 69130424947840285453907123)
  ·
    refine ⟨103695637421760428180860685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69130424947840285453907123 103695637421760428180860685)
    ·
      refine ⟨38885864033160160567822757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103695637421760428180860685 38885864033160160567822757)
      ·
        refine ⟨7291099506217530106466767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38885864033160160567822757 7291099506217530106466767)
        ·
          refine ⟨10936649259326295159700151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291099506217530106466767 10936649259326295159700151)
          ·
            refine ⟨16404973888989442739550227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936649259326295159700151 16404973888989442739550227)
            ·
              refine ⟨24607460833484164109325341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16404973888989442739550227 24607460833484164109325341)
              ·
                refine ⟨9227797812556561540997003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24607460833484164109325341 9227797812556561540997003)
                ·
                  refine ⟨13841696718834842311495505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227797812556561540997003 13841696718834842311495505)
                  ·
                    refine ⟨10381272539126131733621629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13841696718834842311495505 10381272539126131733621629)
                    ·
                      refine ⟨3892977202172299400108111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381272539126131733621629 3892977202172299400108111)
                      ·
                        rfl

theorem cell23_7581546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7581546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581546 prefixEnd_7581546 := by exact prefixLift 7581546
  have htrace : WordTrace (prefixWord ++ tailWord_7581546) baseStart_7581546 baseEnd_7581546 := by
    simpa [prefixWord, tailWord_7581546, baseEnd_7581546] using wordTrace_append hprefix tailTrace_7581546
  have hstable : (prefixWord ++ tailWord_7581546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581546).length < 2 ^ (prefixWord ++ tailWord_7581546).sum := by decide
  have hdescent : baseEnd_7581546 < baseStart_7581546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581576 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7581576 : Nat := 118140960795 + 7581576 * 2 ^ 59
def prefixEnd_7581576 : Nat := 4983230072969 + 3 ^ 40 * 7581576 * 2
def baseEnd_7581576 : Nat := 3892992606591934282732973

theorem tailTrace_7581576 : CollatzResearch.WordTrace tailWord_7581576 prefixEnd_7581576 3892992606591934282732973 := by
  unfold tailWord_7581576
  simp only [CollatzResearch.WordTrace]
  refine ⟨138261396990626228469610291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184348529320834971292813721 138261396990626228469610291)
  ·
    refine ⟨207392095485939342704415437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138261396990626228469610291 207392095485939342704415437)
    ·
      refine ⟨77772035807227253514155789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207392095485939342704415437 77772035807227253514155789)
      ·
        refine ⟨29164513427710220067808421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77772035807227253514155789 29164513427710220067808421)
        ·
          refine ⟨5468346267695666262714079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29164513427710220067808421 5468346267695666262714079)
          ·
            refine ⟨8202519401543499394071119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468346267695666262714079 8202519401543499394071119)
            ·
              refine ⟨12303779102315249091106679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202519401543499394071119 12303779102315249091106679)
              ·
                refine ⟨18455668653472873636660019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12303779102315249091106679 18455668653472873636660019)
                ·
                  refine ⟨27683502980209310454990029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18455668653472873636660019 27683502980209310454990029)
                  ·
                    refine ⟨10381313617578491420621261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27683502980209310454990029 10381313617578491420621261)
                    ·
                      refine ⟨3892992606591934282732973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381313617578491420621261 3892992606591934282732973)
                      ·
                        rfl

theorem cell23_7581576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7581576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581576 prefixEnd_7581576 := by exact prefixLift 7581576
  have htrace : WordTrace (prefixWord ++ tailWord_7581576) baseStart_7581576 baseEnd_7581576 := by
    simpa [prefixWord, tailWord_7581576, baseEnd_7581576] using wordTrace_append hprefix tailTrace_7581576
  have hstable : (prefixWord ++ tailWord_7581576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581576).length < 2 ^ (prefixWord ++ tailWord_7581576).sum := by decide
  have hdescent : baseEnd_7581576 < baseStart_7581576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581585 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_7581585 : Nat := 118140960795 + 7581585 * 2 ^ 59
def prefixEnd_7581585 : Nat := 4983230072969 + 3 ^ 40 * 7581585 * 2
def baseEnd_7581585 : Nat := 3892997227917824747520431

theorem tailTrace_7581585 : CollatzResearch.WordTrace tailWord_7581585 prefixEnd_7581585 3892997227917824747520431 := by
  unfold tailWord_7581585
  simp only [CollatzResearch.WordTrace]
  refine ⟨276523122238219851476298209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184348748158813234317532139 276523122238219851476298209)
  ·
    refine ⟨207392341678664888607223657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276523122238219851476298209 207392341678664888607223657)
    ·
      refine ⟨155544256258998666455417743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207392341678664888607223657 155544256258998666455417743)
      ·
        refine ⟨233316384388497999683126615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155544256258998666455417743 233316384388497999683126615)
        ·
          refine ⟨349974576582746999524689923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233316384388497999683126615 349974576582746999524689923)
          ·
            refine ⟨524961864874120499287034885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349974576582746999524689923 524961864874120499287034885)
            ·
              refine ⟨98430349663897593616319041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 524961864874120499287034885 98430349663897593616319041)
              ·
                refine ⟨73822762247923195212239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98430349663897593616319041 73822762247923195212239281)
                ·
                  refine ⟨55367071685942396409179461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73822762247923195212239281 55367071685942396409179461)
                  ·
                    refine ⟨10381325941114199326721149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55367071685942396409179461 10381325941114199326721149)
                    ·
                      refine ⟨3892997227917824747520431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381325941114199326721149 3892997227917824747520431)
                      ·
                        rfl

theorem cell23_7581585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_7581585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581585 prefixEnd_7581585 := by exact prefixLift 7581585
  have htrace : WordTrace (prefixWord ++ tailWord_7581585) baseStart_7581585 baseEnd_7581585 := by
    simpa [prefixWord, tailWord_7581585, baseEnd_7581585] using wordTrace_append hprefix tailTrace_7581585
  have hstable : (prefixWord ++ tailWord_7581585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581585).length < 2 ^ (prefixWord ++ tailWord_7581585).sum := by decide
  have hdescent : baseEnd_7581585 < baseStart_7581585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581586 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7581586 : Nat := 118140960795 + 7581586 * 2 ^ 59
def prefixEnd_7581586 : Nat := 4983230072969 + 3 ^ 40 * 7581586 * 2
def baseEnd_7581586 : Nat := 3892997741398479243607927

theorem tailTrace_7581586 : CollatzResearch.WordTrace tailWord_7581586 prefixEnd_7581586 3892997741398479243607927 := by
  unfold tailWord_7581586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69130789677804057161771153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184348772474144152431389741 69130789677804057161771153)
  ·
    refine ⟨51848092258353042871328365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69130789677804057161771153 51848092258353042871328365)
    ·
      refine ⟨19443034596882391076748137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51848092258353042871328365 19443034596882391076748137)
      ·
        refine ⟨14582275947661793307561103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19443034596882391076748137 14582275947661793307561103)
        ·
          refine ⟨21873413921492689961341655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14582275947661793307561103 21873413921492689961341655)
          ·
            refine ⟨32810120882239034942012483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21873413921492689961341655 32810120882239034942012483)
            ·
              refine ⟨49215181323358552413018725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32810120882239034942012483 49215181323358552413018725)
              ·
                refine ⟨9227846498129728577441011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49215181323358552413018725 9227846498129728577441011)
                ·
                  refine ⟨13841769747194592866161517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227846498129728577441011 13841769747194592866161517)
                  ·
                    refine ⟨5190663655197972324810569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13841769747194592866161517 5190663655197972324810569)
                    ·
                      refine ⟨3892997741398479243607927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190663655197972324810569 3892997741398479243607927)
                      ·
                        rfl

theorem cell23_7581586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7581586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581586 prefixEnd_7581586 := by exact prefixLift 7581586
  have htrace : WordTrace (prefixWord ++ tailWord_7581586) baseStart_7581586 baseEnd_7581586 := by
    simpa [prefixWord, tailWord_7581586, baseEnd_7581586] using wordTrace_append hprefix tailTrace_7581586
  have hstable : (prefixWord ++ tailWord_7581586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581586).length < 2 ^ (prefixWord ++ tailWord_7581586).sum := by decide
  have hdescent : baseEnd_7581586 < baseStart_7581586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581689 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 2, 4, 2]
def baseStart_7581689 : Nat := 118140960795 + 7581689 * 2 ^ 59
def prefixEnd_7581689 : Nat := 4983230072969 + 3 ^ 40 * 7581689 * 2
def baseEnd_7581689 : Nat := 3893050629905892340619953

theorem tailTrace_7581689 : CollatzResearch.WordTrace tailWord_7581689 prefixEnd_7581689 3893050629905892340619953 := by
  unfold tailWord_7581689
  simp only [CollatzResearch.WordTrace]
  refine ⟨276526915429843077238084121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184351276953228718158722747 276526915429843077238084121)
  ·
    refine ⟨207395186572382307928563091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276526915429843077238084121 207395186572382307928563091)
    ·
      refine ⟨311092779858573461892844637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207395186572382307928563091 311092779858573461892844637)
      ·
        refine ⟨116659792446965048209816739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311092779858573461892844637 116659792446965048209816739)
        ·
          refine ⟨174989688670447572314725109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116659792446965048209816739 174989688670447572314725109)
          ·
            refine ⟨16405283312854459904505479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174989688670447572314725109 16405283312854459904505479)
            ·
              refine ⟨24607924969281689856758219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16405283312854459904505479 24607924969281689856758219)
              ·
                refine ⟨36911887453922534785137329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24607924969281689856758219 36911887453922534785137329)
                ·
                  refine ⟨27683915590441901088852997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36911887453922534785137329 27683915590441901088852997)
                  ·
                    refine ⟨5190734173207856454159937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27683915590441901088852997 5190734173207856454159937)
                    ·
                      refine ⟨3893050629905892340619953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190734173207856454159937 3893050629905892340619953)
                      ·
                        rfl

theorem cell23_7581689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_7581689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581689 prefixEnd_7581689 := by exact prefixLift 7581689
  have htrace : WordTrace (prefixWord ++ tailWord_7581689) baseStart_7581689 baseEnd_7581689 := by
    simpa [prefixWord, tailWord_7581689, baseEnd_7581689] using wordTrace_append hprefix tailTrace_7581689
  have hstable : (prefixWord ++ tailWord_7581689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581689).length < 2 ^ (prefixWord ++ tailWord_7581689).sum := by decide
  have hdescent : baseEnd_7581689 < baseStart_7581689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581692 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_7581692 : Nat := 118140960795 + 7581692 * 2 ^ 59
def prefixEnd_7581692 : Nat := 4983230072969 + 3 ^ 40 * 7581692 * 2
def baseEnd_7581692 : Nat := 3893052170347855828882439

theorem tailTrace_7581692 : CollatzResearch.WordTrace tailWord_7581692 prefixEnd_7581692 3893052170347855828882439 := by
  unfold tailWord_7581692
  simp only [CollatzResearch.WordTrace]
  refine ⟨138263512424416104375221665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184351349899221472500295553 138263512424416104375221665)
  ·
    refine ⟨103697634318312078281416249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138263512424416104375221665 103697634318312078281416249)
    ·
      refine ⟨77773225738734058711062187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103697634318312078281416249 77773225738734058711062187)
      ·
        refine ⟨116659838608101088066593281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77773225738734058711062187 116659838608101088066593281)
        ·
          refine ⟨87494878956075816049944961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116659838608101088066593281 87494878956075816049944961)
          ·
            refine ⟨65621159217056862037458721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87494878956075816049944961 65621159217056862037458721)
            ·
              refine ⟨49215869412792646528094041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65621159217056862037458721 49215869412792646528094041)
              ·
                refine ⟨36911902059594484896070531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49215869412792646528094041 36911902059594484896070531)
                ·
                  refine ⟨55367853089391727344105797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36911902059594484896070531 55367853089391727344105797)
                  ·
                    refine ⟨10381472454260948877019837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55367853089391727344105797 10381472454260948877019837)
                    ·
                      refine ⟨3893052170347855828882439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381472454260948877019837 3893052170347855828882439)
                      ·
                        rfl

theorem cell23_7581692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_7581692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581692 prefixEnd_7581692 := by exact prefixLift 7581692
  have htrace : WordTrace (prefixWord ++ tailWord_7581692) baseStart_7581692 baseEnd_7581692 := by
    simpa [prefixWord, tailWord_7581692, baseEnd_7581692] using wordTrace_append hprefix tailTrace_7581692
  have hstable : (prefixWord ++ tailWord_7581692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581692).length < 2 ^ (prefixWord ++ tailWord_7581692).sum := by decide
  have hdescent : baseEnd_7581692 < baseStart_7581692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581706 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_7581706 : Nat := 118140960795 + 7581706 * 2 ^ 59
def prefixEnd_7581706 : Nat := 4983230072969 + 3 ^ 40 * 7581706 * 2
def baseEnd_7581706 : Nat := 3893059359077018774107375

theorem tailTrace_7581706 : CollatzResearch.WordTrace tailWord_7581706 prefixEnd_7581706 3893059359077018774107375 := by
  unfold tailWord_7581706
  simp only [CollatzResearch.WordTrace]
  refine ⟨69131883867695372285363243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184351690313854326094301981 69131883867695372285363243)
  ·
    refine ⟨103697825801543058428044865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69131883867695372285363243 103697825801543058428044865)
    ·
      refine ⟨77773369351157293821033649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103697825801543058428044865 77773369351157293821033649)
      ·
        refine ⟨58330027013367970365775237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77773369351157293821033649 58330027013367970365775237)
        ·
          refine ⟨10936880065006494443582857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58330027013367970365775237 10936880065006494443582857)
          ·
            refine ⟨8202660048754870832687143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10936880065006494443582857 8202660048754870832687143)
            ·
              refine ⟨12303990073132306249030715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202660048754870832687143 12303990073132306249030715)
              ·
                refine ⟨18455985109698459373546073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12303990073132306249030715 18455985109698459373546073)
                ·
                  refine ⟨13841988832273844530159555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18455985109698459373546073 13841988832273844530159555)
                  ·
                    refine ⟨20762983248410766795239333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13841988832273844530159555 20762983248410766795239333)
                    ·
                      refine ⟨3893059359077018774107375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20762983248410766795239333 3893059359077018774107375)
                      ·
                        rfl

theorem cell23_7581706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_7581706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581706 prefixEnd_7581706 := by exact prefixLift 7581706
  have htrace : WordTrace (prefixWord ++ tailWord_7581706) baseStart_7581706 baseEnd_7581706 := by
    simpa [prefixWord, tailWord_7581706, baseEnd_7581706] using wordTrace_append hprefix tailTrace_7581706
  have hstable : (prefixWord ++ tailWord_7581706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581706).length < 2 ^ (prefixWord ++ tailWord_7581706).sum := by decide
  have hdescent : baseEnd_7581706 < baseStart_7581706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581749 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_7581749 : Nat := 118140960795 + 7581749 * 2 ^ 59
def prefixEnd_7581749 : Nat := 4983230072969 + 3 ^ 40 * 7581749 * 2
def baseEnd_7581749 : Nat := 3893081438745162105869677

theorem tailTrace_7581749 : CollatzResearch.WordTrace tailWord_7581749 prefixEnd_7581749 3893081438745162105869677 := by
  unfold tailWord_7581749
  simp only [CollatzResearch.WordTrace]
  refine ⟨276529103809625707485268301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184352735873083804990178867 276529103809625707485268301)
  ·
    refine ⟨103698413928609640306975613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276529103809625707485268301 103698413928609640306975613)
    ·
      refine ⟨38886905223228615115115855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103698413928609640306975613 38886905223228615115115855)
      ·
        refine ⟨58330357834842922672673783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38886905223228615115115855 58330357834842922672673783)
        ·
          refine ⟨87495536752264384009010675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58330357834842922672673783 87495536752264384009010675)
          ·
            refine ⟨131243305128396576013516013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87495536752264384009010675 131243305128396576013516013)
            ·
              refine ⟨49216239423148716005068505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131243305128396576013516013 49216239423148716005068505)
              ·
                refine ⟨36912179567361537003801379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49216239423148716005068505 36912179567361537003801379)
                ·
                  refine ⟨55368269351042305505702069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36912179567361537003801379 55368269351042305505702069)
                  ·
                    refine ⟨5190775251660216141159569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55368269351042305505702069 5190775251660216141159569)
                    ·
                      refine ⟨3893081438745162105869677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190775251660216141159569 3893081438745162105869677)
                      ·
                        rfl

theorem cell23_7581749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_7581749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581749 prefixEnd_7581749 := by exact prefixLift 7581749
  have htrace : WordTrace (prefixWord ++ tailWord_7581749) baseStart_7581749 baseEnd_7581749 := by
    simpa [prefixWord, tailWord_7581749, baseEnd_7581749] using wordTrace_append hprefix tailTrace_7581749
  have hstable : (prefixWord ++ tailWord_7581749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581749).length < 2 ^ (prefixWord ++ tailWord_7581749).sum := by decide
  have hdescent : baseEnd_7581749 < baseStart_7581749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581772 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_7581772 : Nat := 118140960795 + 7581772 * 2 ^ 59
def prefixEnd_7581772 : Nat := 4983230072969 + 3 ^ 40 * 7581772 * 2
def baseEnd_7581772 : Nat := 1297697749600071838627357

theorem tailTrace_7581772 : CollatzResearch.WordTrace tailWord_7581772 prefixEnd_7581772 1297697749600071838627357 := by
  unfold tailWord_7581772
  simp only [CollatzResearch.WordTrace]
  refine ⟨138264971344271191206677785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184353295125694921608903713 138264971344271191206677785)
  ·
    refine ⟨103698728508203393405008339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138264971344271191206677785 103698728508203393405008339)
    ·
      refine ⟨155548092762305090107512509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103698728508203393405008339 155548092762305090107512509)
      ·
        refine ⟨58330534785864408790317191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155548092762305090107512509 58330534785864408790317191)
        ·
          refine ⟨87495802178796613185475787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58330534785864408790317191 87495802178796613185475787)
          ·
            refine ⟨131243703268194919778213681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87495802178796613185475787 131243703268194919778213681)
            ·
              refine ⟨98432777451146189833660261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131243703268194919778213681 98432777451146189833660261)
              ·
                refine ⟨18456145772089910593811299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98432777451146189833660261 18456145772089910593811299)
                ·
                  refine ⟨27684218658134865890716949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18456145772089910593811299 27684218658134865890716949)
                  ·
                    refine ⟨1297697749600071838627357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27684218658134865890716949 1297697749600071838627357)
                    ·
                      rfl

theorem cell23_7581772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_7581772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581772 prefixEnd_7581772 := by exact prefixLift 7581772
  have htrace : WordTrace (prefixWord ++ tailWord_7581772) baseStart_7581772 baseEnd_7581772 := by
    simpa [prefixWord, tailWord_7581772, baseEnd_7581772] using wordTrace_append hprefix tailTrace_7581772
  have hstable : (prefixWord ++ tailWord_7581772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581772).length < 2 ^ (prefixWord ++ tailWord_7581772).sum := by decide
  have hdescent : baseEnd_7581772 < baseStart_7581772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581792 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_7581792 : Nat := 118140960795 + 7581792 * 2 ^ 59
def prefixEnd_7581792 : Nat := 4983230072969 + 3 ^ 40 * 7581792 * 2
def baseEnd_7581792 : Nat := 3893103518413305437631979

theorem tailTrace_7581792 : CollatzResearch.WordTrace tailWord_7581792 prefixEnd_7581792 3893103518413305437631979 := by
  unfold tailWord_7581792
  simp only [CollatzResearch.WordTrace]
  refine ⟨138265336074234962914541815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184353781432313283886055753 138265336074234962914541815)
  ·
    refine ⟨207398004111352444371812723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138265336074234962914541815 207398004111352444371812723)
    ·
      refine ⟨311097006167028666557719085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207398004111352444371812723 311097006167028666557719085)
      ·
        refine ⟨116661377312635749959144657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311097006167028666557719085 116661377312635749959144657)
        ·
          refine ⟨87496032984476812469358493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116661377312635749959144657 87496032984476812469358493)
          ·
            refine ⟨32811012369178804676009435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87496032984476812469358493 32811012369178804676009435)
            ·
              refine ⟨49216518553768207014014153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32811012369178804676009435 49216518553768207014014153)
              ·
                refine ⟨36912388915326155260510615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49216518553768207014014153 36912388915326155260510615)
                ·
                  refine ⟨55368583372989232890765923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36912388915326155260510615 55368583372989232890765923)
                  ·
                    refine ⟨83052875059483849336148885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55368583372989232890765923 83052875059483849336148885)
                    ·
                      refine ⟨3893103518413305437631979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83052875059483849336148885 3893103518413305437631979)
                      ·
                        rfl

theorem cell23_7581792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_7581792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581792 prefixEnd_7581792 := by exact prefixLift 7581792
  have htrace : WordTrace (prefixWord ++ tailWord_7581792) baseStart_7581792 baseEnd_7581792 := by
    simpa [prefixWord, tailWord_7581792, baseEnd_7581792] using wordTrace_append hprefix tailTrace_7581792
  have hstable : (prefixWord ++ tailWord_7581792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581792).length < 2 ^ (prefixWord ++ tailWord_7581792).sum := by decide
  have hdescent : baseEnd_7581792 < baseStart_7581792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581799 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_7581799 : Nat := 118140960795 + 7581799 * 2 ^ 59
def prefixEnd_7581799 : Nat := 4983230072969 + 3 ^ 40 * 7581799 * 2
def baseEnd_7581799 : Nat := 3893107112777886910244447

theorem tailTrace_7581799 : CollatzResearch.WordTrace tailWord_7581799 prefixEnd_7581799 3893107112777886910244447 := by
  unfold tailWord_7581799
  simp only [CollatzResearch.WordTrace]
  refine ⟨276530927459444566024588451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184353951639629710683058967 276530927459444566024588451)
  ·
    refine ⟨414796391189166849036882677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276530927459444566024588451 414796391189166849036882677)
    ·
      refine ⟨38887161673984392097207751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 414796391189166849036882677 38887161673984392097207751)
      ·
        refine ⟨58330742510976588145811627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38887161673984392097207751 58330742510976588145811627)
        ·
          refine ⟨87496113766464882218717441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58330742510976588145811627 87496113766464882218717441)
          ·
            refine ⟨65622085324848661664038081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87496113766464882218717441 65622085324848661664038081)
            ·
              refine ⟨49216563993636496248028561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65622085324848661664038081 49216563993636496248028561)
              ·
                refine ⟨36912422995227372186021421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49216563993636496248028561 36912422995227372186021421)
                ·
                  refine ⟨13842158623210264569758033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36912422995227372186021421 13842158623210264569758033)
                  ·
                    refine ⟨10381618967407698427318525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13842158623210264569758033 10381618967407698427318525)
                    ·
                      refine ⟨3893107112777886910244447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381618967407698427318525 3893107112777886910244447)
                      ·
                        rfl

theorem cell23_7581799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_7581799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581799 prefixEnd_7581799 := by exact prefixLift 7581799
  have htrace : WordTrace (prefixWord ++ tailWord_7581799) baseStart_7581799 baseEnd_7581799 := by
    simpa [prefixWord, tailWord_7581799, baseEnd_7581799] using wordTrace_append hprefix tailTrace_7581799
  have hstable : (prefixWord ++ tailWord_7581799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581799).length < 2 ^ (prefixWord ++ tailWord_7581799).sum := by decide
  have hdescent : baseEnd_7581799 < baseStart_7581799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581806 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_7581806 : Nat := 118140960795 + 7581806 * 2 ^ 59
def prefixEnd_7581806 : Nat := 4983230072969 + 3 ^ 40 * 7581806 * 2
def baseEnd_7581806 : Nat := 1297703569047489460952305

theorem tailTrace_7581806 : CollatzResearch.WordTrace tailWord_7581806 prefixEnd_7581806 1297703569047489460952305 := by
  unfold tailWord_7581806
  simp only [CollatzResearch.WordTrace]
  refine ⟨34566397846302400777511659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184354121846946137480062181 34566397846302400777511659)
  ·
    refine ⟨51849596769453601166267489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34566397846302400777511659 51849596769453601166267489)
    ·
      refine ⟨38887197577090200874700617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51849596769453601166267489 38887197577090200874700617)
      ·
        refine ⟨29165398182817650656025463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38887197577090200874700617 29165398182817650656025463)
        ·
          refine ⟨43748097274226475984038195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29165398182817650656025463 43748097274226475984038195)
          ·
            refine ⟨65622145911339713976057293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43748097274226475984038195 65622145911339713976057293)
            ·
              refine ⟨24608304716752392741021485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65622145911339713976057293 24608304716752392741021485)
              ·
                refine ⟨9228114268782147277883057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24608304716752392741021485 9228114268782147277883057)
                ·
                  refine ⟨6921085701586610458412293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9228114268782147277883057 6921085701586610458412293)
                  ·
                    refine ⟨1297703569047489460952305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6921085701586610458412293 1297703569047489460952305)
                    ·
                      rfl

theorem cell23_7581806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_7581806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581806 prefixEnd_7581806 := by exact prefixLift 7581806
  have htrace : WordTrace (prefixWord ++ tailWord_7581806) baseStart_7581806 baseEnd_7581806 := by
    simpa [prefixWord, tailWord_7581806, baseEnd_7581806] using wordTrace_append hprefix tailTrace_7581806
  have hstable : (prefixWord ++ tailWord_7581806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581806).length < 2 ^ (prefixWord ++ tailWord_7581806).sum := by decide
  have hdescent : baseEnd_7581806 < baseStart_7581806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581829 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_7581829 : Nat := 118140960795 + 7581829 * 2 ^ 59
def prefixEnd_7581829 : Nat := 4983230072969 + 3 ^ 40 * 7581829 * 2
def baseEnd_7581829 : Nat := 3893122517197521792869309

theorem tailTrace_7581829 : CollatzResearch.WordTrace tailWord_7581829 prefixEnd_7581829 3893122517197521792869309 := by
  unfold tailWord_7581829
  simp only [CollatzResearch.WordTrace]
  refine ⟨276532021649335881148180541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184354681099557254098787027 276532021649335881148180541)
  ·
    refine ⟨103699508118500955430567703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276532021649335881148180541 103699508118500955430567703)
    ·
      refine ⟨155549262177751433145851555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103699508118500955430567703 155549262177751433145851555)
      ·
        refine ⟨233323893266627149718777333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155549262177751433145851555 233323893266627149718777333)
        ·
          refine ⟨21874114993746295286135375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233323893266627149718777333 21874114993746295286135375)
          ·
            refine ⟨32811172490619442929203063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21874114993746295286135375 32811172490619442929203063)
            ·
              refine ⟨49216758735929164393804595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32811172490619442929203063 49216758735929164393804595)
              ·
                refine ⟨73825138103893746590706893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49216758735929164393804595 73825138103893746590706893)
                ·
                  refine ⟨27684426788960154971515085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73825138103893746590706893 27684426788960154971515085)
                  ·
                    refine ⟨10381660045860058114318157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27684426788960154971515085 10381660045860058114318157)
                    ·
                      refine ⟨3893122517197521792869309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381660045860058114318157 3893122517197521792869309)
                      ·
                        rfl

theorem cell23_7581829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_7581829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581829 prefixEnd_7581829 := by exact prefixLift 7581829
  have htrace : WordTrace (prefixWord ++ tailWord_7581829) baseStart_7581829 baseEnd_7581829 := by
    simpa [prefixWord, tailWord_7581829, baseEnd_7581829] using wordTrace_append hprefix tailTrace_7581829
  have hstable : (prefixWord ++ tailWord_7581829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581829).length < 2 ^ (prefixWord ++ tailWord_7581829).sum := by decide
  have hdescent : baseEnd_7581829 < baseStart_7581829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581856 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 3, 3, 2]
def baseStart_7581856 : Nat := 118140960795 + 7581856 * 2 ^ 59
def prefixEnd_7581856 : Nat := 4983230072969 + 3 ^ 40 * 7581856 * 2
def baseEnd_7581856 : Nat := 3893136381175193187231685

theorem tailTrace_7581856 : CollatzResearch.WordTrace tailWord_7581856 prefixEnd_7581856 3893136381175193187231685 := by
  unfold tailWord_7581856
  simp only [CollatzResearch.WordTrace]
  refine ⟨138266503210119032379706711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184355337613492043172942281 138266503210119032379706711)
  ·
    refine ⟨207399754815178548569560067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138266503210119032379706711 207399754815178548569560067)
    ·
      refine ⟨311099632222767822854340101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207399754815178548569560067 311099632222767822854340101)
      ·
        refine ⟨58331181041768966785188769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311099632222767822854340101 58331181041768966785188769)
        ·
          refine ⟨43748385781326725088891577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58331181041768966785188769 43748385781326725088891577)
          ·
            refine ⟨32811289335995043816668683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43748385781326725088891577 32811289335995043816668683)
            ·
              refine ⟨49216934003992565725003025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32811289335995043816668683 49216934003992565725003025)
              ·
                refine ⟨36912700502994424293752269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49216934003992565725003025 36912700502994424293752269)
                ·
                  refine ⟨13842262688622909110157101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36912700502994424293752269 13842262688622909110157101)
                  ·
                    refine ⟨5190848508233590916308913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13842262688622909110157101 5190848508233590916308913)
                    ·
                      refine ⟨3893136381175193187231685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190848508233590916308913 3893136381175193187231685)
                      ·
                        rfl

theorem cell23_7581856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_7581856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581856 prefixEnd_7581856 := by exact prefixLift 7581856
  have htrace : WordTrace (prefixWord ++ tailWord_7581856) baseStart_7581856 baseEnd_7581856 := by
    simpa [prefixWord, tailWord_7581856, baseEnd_7581856] using wordTrace_append hprefix tailTrace_7581856
  have hstable : (prefixWord ++ tailWord_7581856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581856).length < 2 ^ (prefixWord ++ tailWord_7581856).sum := by decide
  have hdescent : baseEnd_7581856 < baseStart_7581856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581863 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7581863 : Nat := 118140960795 + 7581863 * 2 ^ 59
def prefixEnd_7581863 : Nat := 4983230072969 + 3 ^ 40 * 7581863 * 2
def baseEnd_7581863 : Nat := 3893139975539774659844153

theorem tailTrace_7581863 : CollatzResearch.WordTrace tailWord_7581863 prefixEnd_7581863 3893139975539774659844153 := by
  unfold tailWord_7581863
  simp only [CollatzResearch.WordTrace]
  refine ⟨276533261731212704954918243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184355507820808469969945495 276533261731212704954918243)
  ·
    refine ⟨414799892596819057432377365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276533261731212704954918243 414799892596819057432377365)
    ·
      refine ⟨19443744965475893317142689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 414799892596819057432377365 19443744965475893317142689)
      ·
        refine ⟨14582808724106919987857017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19443744965475893317142689 14582808724106919987857017)
        ·
          refine ⟨10937106543080189990892763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14582808724106919987857017 10937106543080189990892763)
          ·
            refine ⟨16405659814620284986339145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937106543080189990892763 16405659814620284986339145)
            ·
              refine ⟨12304244860965213739754359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16405659814620284986339145 12304244860965213739754359)
              ·
                refine ⟨18456367291447820609631539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12304244860965213739754359 18456367291447820609631539)
                ·
                  refine ⟨27684550937171730914447309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18456367291447820609631539 27684550937171730914447309)
                  ·
                    refine ⟨10381706601439399092917741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27684550937171730914447309 10381706601439399092917741)
                    ·
                      refine ⟨3893139975539774659844153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381706601439399092917741 3893139975539774659844153)
                      ·
                        rfl

theorem cell23_7581863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7581863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581863 prefixEnd_7581863 := by exact prefixLift 7581863
  have htrace : WordTrace (prefixWord ++ tailWord_7581863) baseStart_7581863 baseEnd_7581863 := by
    simpa [prefixWord, tailWord_7581863, baseEnd_7581863] using wordTrace_append hprefix tailTrace_7581863
  have hstable : (prefixWord ++ tailWord_7581863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581863).length < 2 ^ (prefixWord ++ tailWord_7581863).sum := by decide
  have hdescent : baseEnd_7581863 < baseStart_7581863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581920 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 2, 2, 2]
def baseStart_7581920 : Nat := 118140960795 + 7581920 * 2 ^ 59
def prefixEnd_7581920 : Nat := 4983230072969 + 3 ^ 40 * 7581920 * 2
def baseEnd_7581920 : Nat := 3893169243937080936831391

theorem tailTrace_7581920 : CollatzResearch.WordTrace tailWord_7581920 prefixEnd_7581920 3893169243937080936831391 := by
  unfold tailWord_7581920
  simp only [CollatzResearch.WordTrace]
  refine ⟨138267670346003101844871607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184356893794670802459828809 138267670346003101844871607)
  ·
    refine ⟨207401505519004652767307411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138267670346003101844871607 207401505519004652767307411)
    ·
      refine ⟨311102258278506979150961117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207401505519004652767307411 311102258278506979150961117)
      ·
        refine ⟨116663346854440117181610419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311102258278506979150961117 116663346854440117181610419)
        ·
          refine ⟨174995020281660175772415629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116663346854440117181610419 174995020281660175772415629)
          ·
            refine ⟨65623132605622565914655861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174995020281660175772415629 65623132605622565914655861)
            ·
              refine ⟨6152168681777115554498987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65623132605622565914655861 6152168681777115554498987)
              ·
                refine ⟨9228253022665673331748481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152168681777115554498987 9228253022665673331748481)
                ·
                  refine ⟨6921189766999254998811361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9228253022665673331748481 6921189766999254998811361)
                  ·
                    refine ⟨5190892325249441249108521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6921189766999254998811361 5190892325249441249108521)
                    ·
                      refine ⟨3893169243937080936831391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190892325249441249108521 3893169243937080936831391)
                      ·
                        rfl

theorem cell23_7581920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_7581920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581920 prefixEnd_7581920 := by exact prefixLift 7581920
  have htrace : WordTrace (prefixWord ++ tailWord_7581920) baseStart_7581920 baseEnd_7581920 := by
    simpa [prefixWord, tailWord_7581920, baseEnd_7581920] using wordTrace_append hprefix tailTrace_7581920
  have hstable : (prefixWord ++ tailWord_7581920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581920).length < 2 ^ (prefixWord ++ tailWord_7581920).sum := by decide
  have hdescent : baseEnd_7581920 < baseStart_7581920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581939 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 2, 5]
def baseStart_7581939 : Nat := 118140960795 + 7581939 * 2 ^ 59
def prefixEnd_7581939 : Nat := 4983230072969 + 3 ^ 40 * 7581939 * 2
def baseEnd_7581939 : Nat := 1297726333356505454164601

theorem tailTrace_7581939 : CollatzResearch.WordTrace tailWord_7581939 prefixEnd_7581939 1297726333356505454164601 := by
  unfold tailWord_7581939
  simp only [CollatzResearch.WordTrace]
  refine ⟨276536033678937369934684871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184357355785958246623123247 276536033678937369934684871)
  ·
    refine ⟨414804050518406054902027307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276536033678937369934684871 414804050518406054902027307)
    ·
      refine ⟨622206075777609082353040961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414804050518406054902027307 622206075777609082353040961)
      ·
        refine ⟨466654556833206811764780721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622206075777609082353040961 466654556833206811764780721)
        ·
          refine ⟨349990917624905108823585541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466654556833206811764780721 349990917624905108823585541)
          ·
            refine ⟨65623297054669707904422289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349990917624905108823585541 65623297054669707904422289)
            ·
              refine ⟨49217472791002280928316717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65623297054669707904422289 49217472791002280928316717)
              ·
                refine ⟨18456552296625855348118769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49217472791002280928316717 18456552296625855348118769)
                ·
                  refine ⟨13842414222469391511089077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18456552296625855348118769 13842414222469391511089077)
                  ·
                    refine ⟨1297726333356505454164601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13842414222469391511089077 1297726333356505454164601)
                    ·
                      rfl

theorem cell23_7581939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 5].length) (baseStart_7581939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581939 prefixEnd_7581939 := by exact prefixLift 7581939
  have htrace : WordTrace (prefixWord ++ tailWord_7581939) baseStart_7581939 baseEnd_7581939 := by
    simpa [prefixWord, tailWord_7581939, baseEnd_7581939] using wordTrace_append hprefix tailTrace_7581939
  have hstable : (prefixWord ++ tailWord_7581939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581939).length < 2 ^ (prefixWord ++ tailWord_7581939).sum := by decide
  have hdescent : baseEnd_7581939 < baseStart_7581939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581976 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 6, 2]
def baseStart_7581976 : Nat := 118140960795 + 7581976 * 2 ^ 59
def prefixEnd_7581976 : Nat := 4983230072969 + 3 ^ 40 * 7581976 * 2
def baseEnd_7581976 : Nat := 3893197998853732717731133

theorem tailTrace_7581976 : CollatzResearch.WordTrace tailWord_7581976 prefixEnd_7581976 3893197998853732717731133 := by
  unfold tailWord_7581976
  simp only [CollatzResearch.WordTrace]
  refine ⟨138268691589901662626890891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184358255453202216835854521 138268691589901662626890891)
  ·
    refine ⟨207403037384852493940336337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138268691589901662626890891 207403037384852493940336337)
    ·
      refine ⟨155552278038639370455252253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207403037384852493940336337 155552278038639370455252253)
      ·
        refine ⟨58332104264489763920719595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155552278038639370455252253 58332104264489763920719595)
        ·
          refine ⟨87498156396734645881079393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58332104264489763920719595 87498156396734645881079393)
          ·
            refine ⟨65623617297550984410809545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87498156396734645881079393 65623617297550984410809545)
            ·
              refine ⟨49217712973163238308107159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65623617297550984410809545 49217712973163238308107159)
              ·
                refine ⟨73826569459744857462160739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49217712973163238308107159 73826569459744857462160739)
                ·
                  refine ⟨110739854189617286193241109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73826569459744857462160739 110739854189617286193241109)
                  ·
                    refine ⟨5190930665138310290308177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110739854189617286193241109 5190930665138310290308177)
                    ·
                      refine ⟨3893197998853732717731133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190930665138310290308177 3893197998853732717731133)
                      ·
                        rfl

theorem cell23_7581976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_7581976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581976 prefixEnd_7581976 := by exact prefixLift 7581976
  have htrace : WordTrace (prefixWord ++ tailWord_7581976) baseStart_7581976 baseEnd_7581976 := by
    simpa [prefixWord, tailWord_7581976, baseEnd_7581976] using wordTrace_append hprefix tailTrace_7581976
  have hstable : (prefixWord ++ tailWord_7581976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581976).length < 2 ^ (prefixWord ++ tailWord_7581976).sum := by decide
  have hdescent : baseEnd_7581976 < baseStart_7581976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581979 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 3]
def baseStart_7581979 : Nat := 118140960795 + 7581979 * 2 ^ 59
def prefixEnd_7581979 : Nat := 4983230072969 + 3 ^ 40 * 7581979 * 2
def baseEnd_7581979 : Nat := 3893199539295696205993619

theorem tailTrace_7581979 : CollatzResearch.WordTrace tailWord_7581979 prefixEnd_7581979 3893199539295696205993619 := by
  unfold tailWord_7581979
  simp only [CollatzResearch.WordTrace]
  refine ⟨276537492598792456766140991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184358328399194971177427327 276537492598792456766140991)
  ·
    refine ⟨414806238898188685149211487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276537492598792456766140991 414806238898188685149211487)
    ·
      refine ⟨622209358347283027723817231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414806238898188685149211487 622209358347283027723817231)
      ·
        refine ⟨933314037520924541585725847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622209358347283027723817231 933314037520924541585725847)
        ·
          refine ⟨1399971056281386812378588771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933314037520924541585725847 1399971056281386812378588771)
          ·
            refine ⟨2099956584422080218567883157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399971056281386812378588771 2099956584422080218567883157)
            ·
              refine ⟨98435464894785010245369523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2099956584422080218567883157 98435464894785010245369523)
              ·
                refine ⟨147653197342177515368054285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98435464894785010245369523 147653197342177515368054285)
                ·
                  refine ⟨55369949003316568263020357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147653197342177515368054285 55369949003316568263020357)
                  ·
                    refine ⟨10381865438121856549316317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55369949003316568263020357 10381865438121856549316317)
                    ·
                      refine ⟨3893199539295696205993619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381865438121856549316317 3893199539295696205993619)
                      ·
                        rfl

theorem cell23_7581979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 3].length) (baseStart_7581979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581979 prefixEnd_7581979 := by exact prefixLift 7581979
  have htrace : WordTrace (prefixWord ++ tailWord_7581979) baseStart_7581979 baseEnd_7581979 := by
    simpa [prefixWord, tailWord_7581979, baseEnd_7581979] using wordTrace_append hprefix tailTrace_7581979
  have hstable : (prefixWord ++ tailWord_7581979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581979).length < 2 ^ (prefixWord ++ tailWord_7581979).sum := by decide
  have hdescent : baseEnd_7581979 < baseStart_7581979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7581996 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_7581996 : Nat := 118140960795 + 7581996 * 2 ^ 59
def prefixEnd_7581996 : Nat := 4983230072969 + 3 ^ 40 * 7581996 * 2
def baseEnd_7581996 : Nat := 3893208268466822639481041

theorem tailTrace_7581996 : CollatzResearch.WordTrace tailWord_7581996 prefixEnd_7581996 3893208268466822639481041 := by
  unfold tailWord_7581996
  simp only [CollatzResearch.WordTrace]
  refine ⟨138269056319865434334754921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184358741759820579113006561 138269056319865434334754921)
  ·
    refine ⟨103701792239899075751066191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138269056319865434334754921 103701792239899075751066191)
    ·
      refine ⟨155552688359848613626599287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103701792239899075751066191 155552688359848613626599287)
      ·
        refine ⟨233329032539772920439898931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155552688359848613626599287 233329032539772920439898931)
        ·
          refine ⟨349993548809659380659848397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233329032539772920439898931 349993548809659380659848397)
          ·
            refine ⟨131247580803622267747443149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349993548809659380659848397 131247580803622267747443149)
            ·
              refine ⟨49217842801358350405291181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131247580803622267747443149 49217842801358350405291181)
              ·
                refine ⟨18456691050509381401984193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49217842801358350405291181 18456691050509381401984193)
                ·
                  refine ⟨13842518287882036051488145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18456691050509381401984193 13842518287882036051488145)
                  ·
                    refine ⟨10381888715911527038616109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13842518287882036051488145 10381888715911527038616109)
                    ·
                      refine ⟨3893208268466822639481041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10381888715911527038616109 3893208268466822639481041)
                      ·
                        rfl

theorem cell23_7581996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_7581996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7581996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7581996 prefixEnd_7581996 := by exact prefixLift 7581996
  have htrace : WordTrace (prefixWord ++ tailWord_7581996) baseStart_7581996 baseEnd_7581996 := by
    simpa [prefixWord, tailWord_7581996, baseEnd_7581996] using wordTrace_append hprefix tailTrace_7581996
  have hstable : (prefixWord ++ tailWord_7581996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7581996).length < 2 ^ (prefixWord ++ tailWord_7581996).sum := by decide
  have hdescent : baseEnd_7581996 < baseStart_7581996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7581996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582003 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 1, 4]
def baseStart_7582003 : Nat := 118140960795 + 7582003 * 2 ^ 59
def prefixEnd_7582003 : Nat := 4983230072969 + 3 ^ 40 * 7582003 * 2
def baseEnd_7582003 : Nat := 1297737287610468037364503

theorem tailTrace_7582003 : CollatzResearch.WordTrace tailWord_7582003 prefixEnd_7582003 1297737287610468037364503 := by
  unfold tailWord_7582003
  simp only [CollatzResearch.WordTrace]
  refine ⟨276538367950705508865014663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184358911967137005910009775 276538367950705508865014663)
  ·
    refine ⟨414807551926058263297521995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276538367950705508865014663 414807551926058263297521995)
    ·
      refine ⟨622211327889087394946282993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414807551926058263297521995 622211327889087394946282993)
      ·
        refine ⟨466658495916815546209712245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622211327889087394946282993 466658495916815546209712245)
        ·
          refine ⟨43749233992201457457160523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 466658495916815546209712245 43749233992201457457160523)
          ·
            refine ⟨65623850988302186185740785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43749233992201457457160523 65623850988302186185740785)
            ·
              refine ⟨49217888241226639639305589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65623850988302186185740785 49217888241226639639305589)
              ·
                refine ⟨4614177022614997466184899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49217888241226639639305589 4614177022614997466184899)
                ·
                  refine ⟨6921265533922496199277349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614177022614997466184899 6921265533922496199277349)
                  ·
                    refine ⟨1297737287610468037364503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6921265533922496199277349 1297737287610468037364503)
                    ·
                      rfl

theorem cell23_7582003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 4].length) (baseStart_7582003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582003 prefixEnd_7582003 := by exact prefixLift 7582003
  have htrace : WordTrace (prefixWord ++ tailWord_7582003) baseStart_7582003 baseEnd_7582003 := by
    simpa [prefixWord, tailWord_7582003, baseEnd_7582003] using wordTrace_append hprefix tailTrace_7582003
  have hstable : (prefixWord ++ tailWord_7582003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582003).length < 2 ^ (prefixWord ++ tailWord_7582003).sum := by decide
  have hdescent : baseEnd_7582003 < baseStart_7582003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582039 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_7582039 : Nat := 118140960795 + 7582039 * 2 ^ 59
def prefixEnd_7582039 : Nat := 4983230072969 + 3 ^ 40 * 7582039 * 2
def baseEnd_7582039 : Nat := 3893230348134965971243343

theorem tailTrace_7582039 : CollatzResearch.WordTrace tailWord_7582039 prefixEnd_7582039 3893230348134965971243343 := by
  unfold tailWord_7582039
  simp only [CollatzResearch.WordTrace]
  refine ⟨276539680978575087013325171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184359787319050058008883447 276539680978575087013325171)
  ·
    refine ⟨414809521467862630519987757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276539680978575087013325171 414809521467862630519987757)
    ·
      refine ⟨155553570550448486444995409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414809521467862630519987757 155553570550448486444995409)
      ·
        refine ⟨116665177912836364833746557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155553570550448486444995409 116665177912836364833746557)
        ·
          refine ⟨43749441717313636812654959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116665177912836364833746557 43749441717313636812654959)
          ·
            refine ⟨65624162575970455218982439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43749441717313636812654959 65624162575970455218982439)
            ·
              refine ⟨98436243863955682828473659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65624162575970455218982439 98436243863955682828473659)
              ·
                refine ⟨147654365795933524242710489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98436243863955682828473659 147654365795933524242710489)
                ·
                  refine ⟨110740774346950143182032867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147654365795933524242710489 110740774346950143182032867)
                  ·
                    refine ⟨166111161520425214773049301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110740774346950143182032867 166111161520425214773049301)
                    ·
                      refine ⟨3893230348134965971243343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166111161520425214773049301 3893230348134965971243343)
                      ·
                        rfl

theorem cell23_7582039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_7582039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582039 prefixEnd_7582039 := by exact prefixLift 7582039
  have htrace : WordTrace (prefixWord ++ tailWord_7582039) baseStart_7582039 baseEnd_7582039 := by
    simpa [prefixWord, tailWord_7582039, baseEnd_7582039] using wordTrace_append hprefix tailTrace_7582039
  have hstable : (prefixWord ++ tailWord_7582039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582039).length < 2 ^ (prefixWord ++ tailWord_7582039).sum := by decide
  have hdescent : baseEnd_7582039 < baseStart_7582039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582053 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 1, 5, 2]
def baseStart_7582053 : Nat := 118140960795 + 7582053 * 2 ^ 59
def prefixEnd_7582053 : Nat := 4983230072969 + 3 ^ 40 * 7582053 * 2
def baseEnd_7582053 : Nat := 3893237536864128916468279

theorem tailTrace_7582053 : CollatzResearch.WordTrace tailWord_7582053 prefixEnd_7582053 3893237536864128916468279 := by
  unfold tailWord_7582053
  simp only [CollatzResearch.WordTrace]
  refine ⟨276540191600524367404334813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184360127733682911602889875 276540191600524367404334813)
  ·
    refine ⟨103702571850196637776625555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276540191600524367404334813 103702571850196637776625555)
    ·
      refine ⟨155553857775294956664938333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103702571850196637776625555 155553857775294956664938333)
      ·
        refine ⟨58332696665735608749351875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155553857775294956664938333 58332696665735608749351875)
        ·
          refine ⟨87499044998603413124027813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58332696665735608749351875 87499044998603413124027813)
          ·
            refine ⟨16406070937238139960755215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87499044998603413124027813 16406070937238139960755215)
            ·
              refine ⟨24609106405857209941132823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16406070937238139960755215 24609106405857209941132823)
              ·
                refine ⟨36913659608785814911699235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24609106405857209941132823 36913659608785814911699235)
                ·
                  refine ⟨55370489413178722367548853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36913659608785814911699235 55370489413178722367548853)
                  ·
                    refine ⟨5190983382485505221957705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55370489413178722367548853 5190983382485505221957705)
                    ·
                      refine ⟨3893237536864128916468279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5190983382485505221957705 3893237536864128916468279)
                      ·
                        rfl

theorem cell23_7582053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_7582053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582053 prefixEnd_7582053 := by exact prefixLift 7582053
  have htrace : WordTrace (prefixWord ++ tailWord_7582053) baseStart_7582053 baseEnd_7582053 := by
    simpa [prefixWord, tailWord_7582053, baseEnd_7582053] using wordTrace_append hprefix tailTrace_7582053
  have hstable : (prefixWord ++ tailWord_7582053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582053).length < 2 ^ (prefixWord ++ tailWord_7582053).sum := by decide
  have hdescent : baseEnd_7582053 < baseStart_7582053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582079 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_7582079 : Nat := 118140960795 + 7582079 * 2 ^ 59
def prefixEnd_7582079 : Nat := 4983230072969 + 3 ^ 40 * 7582079 * 2
def baseEnd_7582079 : Nat := 3893250887361145814743159

theorem tailTrace_7582079 : CollatzResearch.WordTrace tailWord_7582079 prefixEnd_7582079 3893250887361145814743159 := by
  unfold tailWord_7582079
  simp only [CollatzResearch.WordTrace]
  refine ⟨276541139898430173844781291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184360759932286782563187527 276541139898430173844781291)
  ·
    refine ⟨414811709847645260767171937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276541139898430173844781291 414811709847645260767171937)
    ·
      refine ⟨311108782385733945575378953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414811709847645260767171937 311108782385733945575378953)
      ·
        refine ⟨233331586789300459181534215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311108782385733945575378953 233331586789300459181534215)
        ·
          refine ⟨349997380183950688772301323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233331586789300459181534215 349997380183950688772301323)
          ·
            refine ⟨524996070275926033158451985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349997380183950688772301323 524996070275926033158451985)
            ·
              refine ⟨393747052706944524868838989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524996070275926033158451985 393747052706944524868838989)
              ·
                refine ⟨147655144765104196825814621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393747052706944524868838989 147655144765104196825814621)
                ·
                  refine ⟨55370679286914073809680483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147655144765104196825814621 55370679286914073809680483)
                  ·
                    refine ⟨83056018930371110714520725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55370679286914073809680483 83056018930371110714520725)
                    ·
                      refine ⟨3893250887361145814743159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83056018930371110714520725 3893250887361145814743159)
                      ·
                        rfl

theorem cell23_7582079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_7582079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582079 prefixEnd_7582079 := by exact prefixLift 7582079
  have htrace : WordTrace (prefixWord ++ tailWord_7582079) baseStart_7582079 baseEnd_7582079 := by
    simpa [prefixWord, tailWord_7582079, baseEnd_7582079] using wordTrace_append hprefix tailTrace_7582079
  have hstable : (prefixWord ++ tailWord_7582079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582079).length < 2 ^ (prefixWord ++ tailWord_7582079).sum := by decide
  have hdescent : baseEnd_7582079 < baseStart_7582079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582103 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_7582103 : Nat := 118140960795 + 7582103 * 2 ^ 59
def prefixEnd_7582103 : Nat := 4983230072969 + 3 ^ 40 * 7582103 * 2
def baseEnd_7582103 : Nat := 3893263210896853720843049

theorem tailTrace_7582103 : CollatzResearch.WordTrace tailWord_7582103 prefixEnd_7582103 3893263210896853720843049 := by
  unfold tailWord_7582103
  simp only [CollatzResearch.WordTrace]
  refine ⟨276542015250343225943654963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184361343500228817295769975 276542015250343225943654963)
  ·
    refine ⟨414813022875514838915482445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276542015250343225943654963 414813022875514838915482445)
    ·
      refine ⟨155554883578318064593305917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414813022875514838915482445 155554883578318064593305917)
      ·
        refine ⟨58333081341869274222489719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155554883578318064593305917 58333081341869274222489719)
        ·
          refine ⟨87499622012803911333734579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58333081341869274222489719 87499622012803911333734579)
          ·
            refine ⟨131249433019205867000601869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87499622012803911333734579 131249433019205867000601869)
            ·
              refine ⟨49218537382202200125225701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131249433019205867000601869 49218537382202200125225701)
              ·
                refine ⟨9228475759162912523479819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49218537382202200125225701 9228475759162912523479819)
                ·
                  refine ⟨13842713638744368785219729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9228475759162912523479819 13842713638744368785219729)
                  ·
                    refine ⟨10382035229058276588914797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13842713638744368785219729 10382035229058276588914797)
                    ·
                      refine ⟨3893263210896853720843049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10382035229058276588914797 3893263210896853720843049)
                      ·
                        rfl

theorem cell23_7582103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_7582103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582103 prefixEnd_7582103 := by exact prefixLift 7582103
  have htrace : WordTrace (prefixWord ++ tailWord_7582103) baseStart_7582103 baseEnd_7582103 := by
    simpa [prefixWord, tailWord_7582103, baseEnd_7582103] using wordTrace_append hprefix tailTrace_7582103
  have hstable : (prefixWord ++ tailWord_7582103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582103).length < 2 ^ (prefixWord ++ tailWord_7582103).sum := by decide
  have hdescent : baseEnd_7582103 < baseStart_7582103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582106 : List Nat := [3, 1, 1, 4, 1, 3, 1, 9]
def baseStart_7582106 : Nat := 118140960795 + 7582106 * 2 ^ 59
def prefixEnd_7582106 : Nat := 4983230072969 + 3 ^ 40 * 7582106 * 2
def baseEnd_7582106 : Nat := 144194990790326563300205

theorem tailTrace_7582106 : CollatzResearch.WordTrace tailWord_7582106 prefixEnd_7582106 144194990790326563300205 := by
  unfold tailWord_7582106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69135531167333089364003543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184361416446221571637342781 69135531167333089364003543)
  ·
    refine ⟨103703296750999634046005315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69135531167333089364003543 103703296750999634046005315)
    ·
      refine ⟨155554945126499451069007973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103703296750999634046005315 155554945126499451069007973)
      ·
        refine ⟨29166552211218647075438995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155554945126499451069007973 29166552211218647075438995)
        ·
          refine ⟨43749828316827970613158493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29166552211218647075438995 43749828316827970613158493)
          ·
            refine ⟨16406185618810488979934435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43749828316827970613158493 16406185618810488979934435)
            ·
              refine ⟨24609278428215733469901653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16406185618810488979934435 24609278428215733469901653)
              ·
                refine ⟨144194990790326563300205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24609278428215733469901653 144194990790326563300205)
                ·
                  rfl

theorem cell23_7582106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_7582106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582106 prefixEnd_7582106 := by exact prefixLift 7582106
  have htrace : WordTrace (prefixWord ++ tailWord_7582106) baseStart_7582106 baseEnd_7582106 := by
    simpa [prefixWord, tailWord_7582106, baseEnd_7582106] using wordTrace_append hprefix tailTrace_7582106
  have hstable : (prefixWord ++ tailWord_7582106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582106).length < 2 ^ (prefixWord ++ tailWord_7582106).sum := by decide
  have hdescent : baseEnd_7582106 < baseStart_7582106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582110 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_7582110 : Nat := 118140960795 + 7582110 * 2 ^ 59
def prefixEnd_7582110 : Nat := 4983230072969 + 3 ^ 40 * 7582110 * 2
def baseEnd_7582110 : Nat := 1297755601753811731151839

theorem tailTrace_7582110 : CollatzResearch.WordTrace tailWord_7582110 prefixEnd_7582110 1297755601753811731151839 := by
  unfold tailWord_7582110
  simp only [CollatzResearch.WordTrace]
  refine ⟨34567783820164733267394973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184361513707545244092773189 34567783820164733267394973)
  ·
    refine ⟨12962918932561774975273115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34567783820164733267394973 12962918932561774975273115)
    ·
      refine ⟨19444378398842662462909673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12962918932561774975273115 19444378398842662462909673)
      ·
        refine ⟨14583283799131996847182255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19444378398842662462909673 14583283799131996847182255)
        ·
          refine ⟨21874925698697995270773383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14583283799131996847182255 21874925698697995270773383)
          ·
            refine ⟨32812388548046992906160075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21874925698697995270773383 32812388548046992906160075)
            ·
              refine ⟨49218582822070489359240113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32812388548046992906160075 49218582822070489359240113)
              ·
                refine ⟨36913937116552867019430085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49218582822070489359240113 36913937116552867019430085)
                ·
                  refine ⟨6921363209353662566143141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36913937116552867019430085 6921363209353662566143141)
                  ·
                    refine ⟨1297755601753811731151839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6921363209353662566143141 1297755601753811731151839)
                    ·
                      rfl

theorem cell23_7582110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_7582110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582110 prefixEnd_7582110 := by exact prefixLift 7582110
  have htrace : WordTrace (prefixWord ++ tailWord_7582110) baseStart_7582110 baseEnd_7582110 := by
    simpa [prefixWord, tailWord_7582110, baseEnd_7582110] using wordTrace_append hprefix tailTrace_7582110
  have hstable : (prefixWord ++ tailWord_7582110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582110).length < 2 ^ (prefixWord ++ tailWord_7582110).sum := by decide
  have hdescent : baseEnd_7582110 < baseStart_7582110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582120 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7582120 : Nat := 118140960795 + 7582120 * 2 ^ 59
def prefixEnd_7582120 : Nat := 4983230072969 + 3 ^ 40 * 7582120 * 2
def baseEnd_7582120 : Nat := 3893271940067980154330471

theorem tailTrace_7582120 : CollatzResearch.WordTrace tailWord_7582120 prefixEnd_7582120 3893271940067980154330471 := by
  unfold tailWord_7582120
  simp only [CollatzResearch.WordTrace]
  refine ⟨138271317645640818923511907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184361756860854425231349209 138271317645640818923511907)
  ·
    refine ⟨207406976468461228385267861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138271317645640818923511907 207406976468461228385267861)
    ·
      refine ⟨9722202021959120080559431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207406976468461228385267861 9722202021959120080559431)
      ·
        refine ⟨14583303032938680120839147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722202021959120080559431 14583303032938680120839147)
        ·
          refine ⟨21874954549408020181258721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14583303032938680120839147 21874954549408020181258721)
          ·
            refine ⟨16406215912056015135944041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21874954549408020181258721 16406215912056015135944041)
            ·
              refine ⟨12304661934042011351958031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16406215912056015135944041 12304661934042011351958031)
              ·
                refine ⟨18456992901063017027937047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12304661934042011351958031 18456992901063017027937047)
                ·
                  refine ⟨27685489351594525541905571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18456992901063017027937047 27685489351594525541905571)
                  ·
                    refine ⟨41528234027391788312858357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27685489351594525541905571 41528234027391788312858357)
                    ·
                      refine ⟨3893271940067980154330471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41528234027391788312858357 3893271940067980154330471)
                      ·
                        rfl

theorem cell23_7582120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7582120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582120 prefixEnd_7582120 := by exact prefixLift 7582120
  have htrace : WordTrace (prefixWord ++ tailWord_7582120) baseStart_7582120 baseEnd_7582120 := by
    simpa [prefixWord, tailWord_7582120, baseEnd_7582120] using wordTrace_append hprefix tailTrace_7582120
  have hstable : (prefixWord ++ tailWord_7582120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582120).length < 2 ^ (prefixWord ++ tailWord_7582120).sum := by decide
  have hdescent : baseEnd_7582120 < baseStart_7582120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582176 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_7582176 : Nat := 118140960795 + 7582176 * 2 ^ 59
def prefixEnd_7582176 : Nat := 4983230072969 + 3 ^ 40 * 7582176 * 2
def baseEnd_7582176 : Nat := 3893300694984631935230213

theorem tailTrace_7582176 : CollatzResearch.WordTrace tailWord_7582176 prefixEnd_7582176 3893300694984631935230213 := by
  unfold tailWord_7582176
  simp only [CollatzResearch.WordTrace]
  refine ⟨138272338889539379705531191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184363118519385839607374921 138272338889539379705531191)
  ·
    refine ⟨207408508334309069558296787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138272338889539379705531191 207408508334309069558296787)
    ·
      refine ⟨311112762501463604337445181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207408508334309069558296787 311112762501463604337445181)
      ·
        refine ⟨116667285938048851626541943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311112762501463604337445181 116667285938048851626541943)
        ·
          refine ⟨175000928907073277439812915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116667285938048851626541943 175000928907073277439812915)
          ·
            refine ⟨262501393360609916159719373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175000928907073277439812915 262501393360609916159719373)
            ·
              refine ⟨98438022510228718559894765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262501393360609916159719373 98438022510228718559894765)
              ·
                refine ⟨36914258441335769459960537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98438022510228718559894765 36914258441335769459960537)
                ·
                  refine ⟨27685693831001827094970403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36914258441335769459960537 27685693831001827094970403)
                  ·
                    refine ⟨41528540746502740642455605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27685693831001827094970403 41528540746502740642455605)
                    ·
                      refine ⟨3893300694984631935230213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41528540746502740642455605 3893300694984631935230213)
                      ·
                        rfl

theorem cell23_7582176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_7582176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582176 prefixEnd_7582176 := by exact prefixLift 7582176
  have htrace : WordTrace (prefixWord ++ tailWord_7582176) baseStart_7582176 baseEnd_7582176 := by
    simpa [prefixWord, tailWord_7582176, baseEnd_7582176] using wordTrace_append hprefix tailTrace_7582176
  have hstable : (prefixWord ++ tailWord_7582176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582176).length < 2 ^ (prefixWord ++ tailWord_7582176).sum := by decide
  have hdescent : baseEnd_7582176 < baseStart_7582176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582177 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_7582177 : Nat := 118140960795 + 7582177 * 2 ^ 59
def prefixEnd_7582177 : Nat := 4983230072969 + 3 ^ 40 * 7582177 * 2
def baseEnd_7582177 : Nat := 3893301208465286431317709

theorem tailTrace_7582177 : CollatzResearch.WordTrace tailWord_7582177 prefixEnd_7582177 3893301208465286431317709 := by
  unfold tailWord_7582177
  simp only [CollatzResearch.WordTrace]
  refine ⟨276544714252075136581848785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184363142834716757721232523 276544714252075136581848785)
  ·
    refine ⟨207408535689056352436386589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276544714252075136581848785 207408535689056352436386589)
    ·
      refine ⟨77778200883396132163644971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207408535689056352436386589 77778200883396132163644971)
      ·
        refine ⟨116667301325094198245467457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77778200883396132163644971 116667301325094198245467457)
        ·
          refine ⟨87500475993820648684100593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116667301325094198245467457 87500475993820648684100593)
          ·
            refine ⟨65625356995365486513075445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87500475993820648684100593 65625356995365486513075445)
            ·
              refine ⟨6152377218315514360600823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65625356995365486513075445 6152377218315514360600823)
              ·
                refine ⟨9228565827473271540901235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152377218315514360600823 9228565827473271540901235)
                ·
                  refine ⟨13842848741209907311351853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9228565827473271540901235 13842848741209907311351853)
                  ·
                    refine ⟨5191068277953715241756945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13842848741209907311351853 5191068277953715241756945)
                    ·
                      refine ⟨3893301208465286431317709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191068277953715241756945 3893301208465286431317709)
                      ·
                        rfl

theorem cell23_7582177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_7582177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582177 prefixEnd_7582177 := by exact prefixLift 7582177
  have htrace : WordTrace (prefixWord ++ tailWord_7582177) baseStart_7582177 baseEnd_7582177 := by
    simpa [prefixWord, tailWord_7582177, baseEnd_7582177] using wordTrace_append hprefix tailTrace_7582177
  have hstable : (prefixWord ++ tailWord_7582177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582177).length < 2 ^ (prefixWord ++ tailWord_7582177).sum := by decide
  have hdescent : baseEnd_7582177 < baseStart_7582177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582233 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 4, 5, 2]
def baseStart_7582233 : Nat := 118140960795 + 7582233 * 2 ^ 59
def prefixEnd_7582233 : Nat := 4983230072969 + 3 ^ 40 * 7582233 * 2
def baseEnd_7582233 : Nat := 3893329963381938212217451

theorem tailTrace_7582233 : CollatzResearch.WordTrace tailWord_7582233 prefixEnd_7582233 3893329963381938212217451 := by
  unfold tailWord_7582233
  simp only [CollatzResearch.WordTrace]
  refine ⟨276546756739872258145887353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184364504493248172097258235 276546756739872258145887353)
  ·
    refine ⟨207410067554904193609415515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276546756739872258145887353 207410067554904193609415515)
    ·
      refine ⟨311115101332356290414123273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207410067554904193609415515 311115101332356290414123273)
      ·
        refine ⟨233336325999267217810592455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311115101332356290414123273 233336325999267217810592455)
        ·
          refine ⟨350004488998900826715888683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233336325999267217810592455 350004488998900826715888683)
          ·
            refine ⟨525006733498351240073833025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350004488998900826715888683 525006733498351240073833025)
            ·
              refine ⟨393755050123763430055374769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525006733498351240073833025 393755050123763430055374769)
              ·
                refine ⟨295316287592822572541531077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393755050123763430055374769 295316287592822572541531077)
                ·
                  refine ⟨55371803923654232351537077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295316287592822572541531077 55371803923654232351537077)
                  ·
                    refine ⟨5191106617842584282956601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55371803923654232351537077 5191106617842584282956601)
                    ·
                      refine ⟨3893329963381938212217451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191106617842584282956601 3893329963381938212217451)
                      ·
                        rfl

theorem cell23_7582233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_7582233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582233 prefixEnd_7582233 := by exact prefixLift 7582233
  have htrace : WordTrace (prefixWord ++ tailWord_7582233) baseStart_7582233 baseEnd_7582233 := by
    simpa [prefixWord, tailWord_7582233, baseEnd_7582233] using wordTrace_append hprefix tailTrace_7582233
  have hstable : (prefixWord ++ tailWord_7582233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582233).length < 2 ^ (prefixWord ++ tailWord_7582233).sum := by decide
  have hdescent : baseEnd_7582233 < baseStart_7582233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582247 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 7]
def baseStart_7582247 : Nat := 118140960795 + 7582247 * 2 ^ 59
def prefixEnd_7582247 : Nat := 4983230072969 + 3 ^ 40 * 7582247 * 2
def baseEnd_7582247 : Nat := 432593016901233461938043

theorem tailTrace_7582247 : CollatzResearch.WordTrace tailWord_7582247 prefixEnd_7582247 432593016901233461938043 := by
  unfold tailWord_7582247
  simp only [CollatzResearch.WordTrace]
  refine ⟨276547267361821538536896995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184364844907881025691264663 276547267361821538536896995)
  ·
    refine ⟨414820901042732307805345493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276547267361821538536896995 414820901042732307805345493)
    ·
      refine ⟨9722364868189038464187785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 414820901042732307805345493 9722364868189038464187785)
      ·
        refine ⟨7291773651141778848140839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9722364868189038464187785 7291773651141778848140839)
        ·
          refine ⟨10937660476712668272211259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291773651141778848140839 10937660476712668272211259)
          ·
            refine ⟨16406490715069002408316889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937660476712668272211259 16406490715069002408316889)
            ·
              refine ⟨12304868036301751806237667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16406490715069002408316889 12304868036301751806237667)
              ·
                refine ⟨18457302054452627709356501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12304868036301751806237667 18457302054452627709356501)
                ·
                  refine ⟨432593016901233461938043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18457302054452627709356501 432593016901233461938043)
                  ·
                    rfl

theorem cell23_7582247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 7].length) (baseStart_7582247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582247 prefixEnd_7582247 := by exact prefixLift 7582247
  have htrace : WordTrace (prefixWord ++ tailWord_7582247) baseStart_7582247 baseEnd_7582247 := by
    simpa [prefixWord, tailWord_7582247, baseEnd_7582247] using wordTrace_append hprefix tailTrace_7582247
  have hstable : (prefixWord ++ tailWord_7582247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582247).length < 2 ^ (prefixWord ++ tailWord_7582247).sum := by decide
  have hdescent : baseEnd_7582247 < baseStart_7582247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582283 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 3]
def baseStart_7582283 : Nat := 118140960795 + 7582283 * 2 ^ 59
def prefixEnd_7582283 : Nat := 4983230072969 + 3 ^ 40 * 7582283 * 2
def baseEnd_7582283 : Nat := 3893355637414663016592221

theorem tailTrace_7582283 : CollatzResearch.WordTrace tailWord_7582283 prefixEnd_7582283 3893355637414663016592221 := by
  unfold tailWord_7582283
  simp only [CollatzResearch.WordTrace]
  refine ⟨276548580389691116685207503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184365720259794077790138335 276548580389691116685207503)
  ·
    refine ⟨414822870584536675027811255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276548580389691116685207503 414822870584536675027811255)
    ·
      refine ⟨622234305876805012541716883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414822870584536675027811255 622234305876805012541716883)
      ·
        refine ⟨933351458815207518812575325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622234305876805012541716883 933351458815207518812575325)
        ·
          refine ⟨350006797055702819554715747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933351458815207518812575325 350006797055702819554715747)
          ·
            refine ⟨525010195583554229332073621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350006797055702819554715747 525010195583554229332073621)
            ·
              refine ⟨24609852917979104499940951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 525010195583554229332073621 24609852917979104499940951)
              ·
                refine ⟨36914779376968656749911427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24609852917979104499940951 36914779376968656749911427)
                ·
                  refine ⟨55372169065452985124867141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36914779376968656749911427 55372169065452985124867141)
                  ·
                    refine ⟨10382281699772434710912589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55372169065452985124867141 10382281699772434710912589)
                    ·
                      refine ⟨3893355637414663016592221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10382281699772434710912589 3893355637414663016592221)
                      ·
                        rfl

theorem cell23_7582283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 3].length) (baseStart_7582283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582283 prefixEnd_7582283 := by exact prefixLift 7582283
  have htrace : WordTrace (prefixWord ++ tailWord_7582283) baseStart_7582283 baseEnd_7582283 := by
    simpa [prefixWord, tailWord_7582283, baseEnd_7582283] using wordTrace_append hprefix tailTrace_7582283
  have hstable : (prefixWord ++ tailWord_7582283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582283).length < 2 ^ (prefixWord ++ tailWord_7582283).sum := by decide
  have hdescent : baseEnd_7582283 < baseStart_7582283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582320 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 6]
def baseStart_7582320 : Nat := 118140960795 + 7582320 * 2 ^ 59
def prefixEnd_7582320 : Nat := 4983230072969 + 3 ^ 40 * 7582320 * 2
def baseEnd_7582320 : Nat := 432597181799875485758839

theorem tailTrace_7582320 : CollatzResearch.WordTrace tailWord_7582320 prefixEnd_7582320 432597181799875485758839 := by
  unfold tailWord_7582320
  simp only [CollatzResearch.WordTrace]
  refine ⟨138274964945278536002152207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184366619927038048002869609 138274964945278536002152207)
  ·
    refine ⟨207412447417917804003228311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138274964945278536002152207 207412447417917804003228311)
    ·
      refine ⟨311118671126876706004842467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207412447417917804003228311 311118671126876706004842467)
      ·
        refine ⟨466678006690315059007263701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311118671126876706004842467 466678006690315059007263701)
        ·
          refine ⟨10937765781804259195482743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 466678006690315059007263701 10937765781804259195482743)
          ·
            refine ⟨16406648672706388793224115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937765781804259195482743 16406648672706388793224115)
            ·
              refine ⟨24609973009059583189836173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16406648672706388793224115 24609973009059583189836173)
              ·
                refine ⟨9228739878397343696188565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24609973009059583189836173 9228739878397343696188565)
                ·
                  refine ⟨432597181799875485758839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9228739878397343696188565 432597181799875485758839)
                  ·
                    rfl

theorem cell23_7582320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_7582320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582320 prefixEnd_7582320 := by exact prefixLift 7582320
  have htrace : WordTrace (prefixWord ++ tailWord_7582320) baseStart_7582320 baseEnd_7582320 := by
    simpa [prefixWord, tailWord_7582320, baseEnd_7582320] using wordTrace_append hprefix tailTrace_7582320
  have hstable : (prefixWord ++ tailWord_7582320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582320).length < 2 ^ (prefixWord ++ tailWord_7582320).sum := by decide
  have hdescent : baseEnd_7582320 < baseStart_7582320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582373 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_7582373 : Nat := 118140960795 + 7582373 * 2 ^ 59
def prefixEnd_7582373 : Nat := 4983230072969 + 3 ^ 40 * 7582373 * 2
def baseEnd_7582373 : Nat := 3893401850673567664466807

theorem tailTrace_7582373 : CollatzResearch.WordTrace tailWord_7582373 prefixEnd_7582373 3893401850673567664466807 := by
  unfold tailWord_7582373
  simp only [CollatzResearch.WordTrace]
  refine ⟨276551862959365062055983773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184367908639576708037322515 276551862959365062055983773)
  ·
    refine ⟨103706948609761898270993915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276551862959365062055983773 103706948609761898270993915)
    ·
      refine ⟨155560422914642847406490873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103706948609761898270993915 155560422914642847406490873)
      ·
        refine ⟨116670317185982135554868155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155560422914642847406490873 116670317185982135554868155)
        ·
          refine ⟨175005475778973203332302233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116670317185982135554868155 175005475778973203332302233)
          ·
            refine ⟨131254106834229902499226675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175005475778973203332302233 131254106834229902499226675)
            ·
              refine ⟨196881160251344853748840013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131254106834229902499226675 196881160251344853748840013)
              ·
                refine ⟨73830435094254320155815005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196881160251344853748840013 73830435094254320155815005)
                ·
                  refine ⟨27686413160345370058430627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73830435094254320155815005 27686413160345370058430627)
                  ·
                    refine ⟨41529619740518055087645941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27686413160345370058430627 41529619740518055087645941)
                    ·
                      refine ⟨3893401850673567664466807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41529619740518055087645941 3893401850673567664466807)
                      ·
                        rfl

theorem cell23_7582373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_7582373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582373 prefixEnd_7582373 := by exact prefixLift 7582373
  have htrace : WordTrace (prefixWord ++ tailWord_7582373) baseStart_7582373 baseEnd_7582373 := by
    simpa [prefixWord, tailWord_7582373, baseEnd_7582373] using wordTrace_append hprefix tailTrace_7582373
  have hstable : (prefixWord ++ tailWord_7582373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582373).length < 2 ^ (prefixWord ++ tailWord_7582373).sum := by decide
  have hdescent : baseEnd_7582373 < baseStart_7582373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582387 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 5, 2, 2]
def baseStart_7582387 : Nat := 118140960795 + 7582387 * 2 ^ 59
def prefixEnd_7582387 : Nat := 4983230072969 + 3 ^ 40 * 7582387 * 2
def baseEnd_7582387 : Nat := 3893409039402730609691743

theorem tailTrace_7582387 : CollatzResearch.WordTrace tailWord_7582387 prefixEnd_7582387 3893409039402730609691743 := by
  unfold tailWord_7582387
  simp only [CollatzResearch.WordTrace]
  refine ⟨276552373581314342446993415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184368249054209561631328943 276552373581314342446993415)
  ·
    refine ⟨414828560371971513670490123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276552373581314342446993415 414828560371971513670490123)
    ·
      refine ⟨622242840557957270505735185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414828560371971513670490123 622242840557957270505735185)
      ·
        refine ⟨466682130418467952879301389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622242840557957270505735185 466682130418467952879301389)
        ·
          refine ⟨175005798906925482329738021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466682130418467952879301389 175005798906925482329738021)
          ·
            refine ⟨32813587295048527936825879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175005798906925482329738021 32813587295048527936825879)
            ·
              refine ⟨49220380942572791905238819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32813587295048527936825879 49220380942572791905238819)
              ·
                refine ⟨73830571413859187857858229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49220380942572791905238819 73830571413859187857858229)
                ·
                  refine ⟨6921616070049298861674209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73830571413859187857858229 6921616070049298861674209)
                  ·
                    refine ⟨5191212052536974146255657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6921616070049298861674209 5191212052536974146255657)
                    ·
                      refine ⟨3893409039402730609691743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191212052536974146255657 3893409039402730609691743)
                      ·
                        rfl

theorem cell23_7582387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 2, 2].length) (baseStart_7582387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582387 prefixEnd_7582387 := by exact prefixLift 7582387
  have htrace : WordTrace (prefixWord ++ tailWord_7582387) baseStart_7582387 baseEnd_7582387 := by
    simpa [prefixWord, tailWord_7582387, baseEnd_7582387] using wordTrace_append hprefix tailTrace_7582387
  have hstable : (prefixWord ++ tailWord_7582387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582387).length < 2 ^ (prefixWord ++ tailWord_7582387).sum := by decide
  have hdescent : baseEnd_7582387 < baseStart_7582387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582391 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 2, 3, 2]
def baseStart_7582391 : Nat := 118140960795 + 7582391 * 2 ^ 59
def prefixEnd_7582391 : Nat := 4983230072969 + 3 ^ 40 * 7582391 * 2
def baseEnd_7582391 : Nat := 3893411093325348594041725

theorem tailTrace_7582391 : CollatzResearch.WordTrace tailWord_7582391 prefixEnd_7582391 3893411093325348594041725 := by
  unfold tailWord_7582391
  simp only [CollatzResearch.WordTrace]
  refine ⟨276552519473299851130139027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184368346315533234086759351 276552519473299851130139027)
  ·
    refine ⟨414828779209949776695208541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276552519473299851130139027 414828779209949776695208541)
    ·
      refine ⟨155560792203731166260703203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414828779209949776695208541 155560792203731166260703203)
      ·
        refine ⟨233341188305596749391054805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155560792203731166260703203 233341188305596749391054805)
        ·
          refine ⟨5468934100912423813852847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 233341188305596749391054805 5468934100912423813852847)
          ·
            refine ⟨8203401151368635720779271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468934100912423813852847 8203401151368635720779271)
            ·
              refine ⟨12305101727052953581168907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203401151368635720779271 12305101727052953581168907)
              ·
                refine ⟨18457652590579430371753361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12305101727052953581168907 18457652590579430371753361)
                ·
                  refine ⟨13843239442934572778815021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18457652590579430371753361 13843239442934572778815021)
                  ·
                    refine ⟨5191214791100464792055633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13843239442934572778815021 5191214791100464792055633)
                    ·
                      refine ⟨3893411093325348594041725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191214791100464792055633 3893411093325348594041725)
                      ·
                        rfl

theorem cell23_7582391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_7582391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582391 prefixEnd_7582391 := by exact prefixLift 7582391
  have htrace : WordTrace (prefixWord ++ tailWord_7582391) baseStart_7582391 baseEnd_7582391 := by
    simpa [prefixWord, tailWord_7582391, baseEnd_7582391] using wordTrace_append hprefix tailTrace_7582391
  have hstable : (prefixWord ++ tailWord_7582391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582391).length < 2 ^ (prefixWord ++ tailWord_7582391).sum := by decide
  have hdescent : baseEnd_7582391 < baseStart_7582391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582400 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_7582400 : Nat := 118140960795 + 7582400 * 2 ^ 59
def prefixEnd_7582400 : Nat := 4983230072969 + 3 ^ 40 * 7582400 * 2
def baseEnd_7582400 : Nat := 3893415714651239058829183

theorem tailTrace_7582400 : CollatzResearch.WordTrace tailWord_7582400 prefixEnd_7582400 3893415714651239058829183 := by
  unfold tailWord_7582400
  simp only [CollatzResearch.WordTrace]
  refine ⟨138276423865133622833608327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184368565153511497111477769 138276423865133622833608327)
  ·
    refine ⟨207414635797700434250412491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138276423865133622833608327 207414635797700434250412491)
    ·
      refine ⟨311121953696550651375618737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207414635797700434250412491 311121953696550651375618737)
      ·
        refine ⟨233341465272412988531714053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311121953696550651375618737 233341465272412988531714053)
        ·
          refine ⟨43751524738577435349696385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233341465272412988531714053 43751524738577435349696385)
          ·
            refine ⟨32813643553933076512272289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43751524738577435349696385 32813643553933076512272289)
            ·
              refine ⟨24610232665449807384204217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32813643553933076512272289 24610232665449807384204217)
              ·
                refine ⟨18457674499087355538153163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24610232665449807384204217 18457674499087355538153163)
                ·
                  refine ⟨27686511748631033307229745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18457674499087355538153163 27686511748631033307229745)
                  ·
                    refine ⟨20764883811473274980422309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27686511748631033307229745 20764883811473274980422309)
                    ·
                      refine ⟨3893415714651239058829183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20764883811473274980422309 3893415714651239058829183)
                      ·
                        rfl

theorem cell23_7582400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_7582400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582400 prefixEnd_7582400 := by exact prefixLift 7582400
  have htrace : WordTrace (prefixWord ++ tailWord_7582400) baseStart_7582400 baseEnd_7582400 := by
    simpa [prefixWord, tailWord_7582400, baseEnd_7582400] using wordTrace_append hprefix tailTrace_7582400
  have hstable : (prefixWord ++ tailWord_7582400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582400).length < 2 ^ (prefixWord ++ tailWord_7582400).sum := by decide
  have hdescent : baseEnd_7582400 < baseStart_7582400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582404 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_7582404 : Nat := 118140960795 + 7582404 * 2 ^ 59
def prefixEnd_7582404 : Nat := 4983230072969 + 3 ^ 40 * 7582404 * 2
def baseEnd_7582404 : Nat := 3893417768573857043179165

theorem tailTrace_7582404 : CollatzResearch.WordTrace tailWord_7582404 prefixEnd_7582404 3893417768573857043179165 := by
  unfold tailWord_7582404
  simp only [CollatzResearch.WordTrace]
  refine ⟨138276496811126377175181133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184368662414835169566908177 138276496811126377175181133)
  ·
    refine ⟨51853686304172391440692925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138276496811126377175181133 51853686304172391440692925)
    ·
      refine ⟨19445132364064646790259847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51853686304172391440692925 19445132364064646790259847)
      ·
        refine ⟨29167698546096970185389771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19445132364064646790259847 29167698546096970185389771)
        ·
          refine ⟨43751547819145455278084657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29167698546096970185389771 43751547819145455278084657)
          ·
            refine ⟨32813660864359091458563493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43751547819145455278084657 32813660864359091458563493)
            ·
              refine ⟨6152561412067329648480655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32813660864359091458563493 6152561412067329648480655)
              ·
                refine ⟨9228842118100994472720983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152561412067329648480655 9228842118100994472720983)
                ·
                  refine ⟨13843263177151491709081475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9228842118100994472720983 13843263177151491709081475)
                  ·
                    refine ⟨20764894765727237563622213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13843263177151491709081475 20764894765727237563622213)
                    ·
                      refine ⟨3893417768573857043179165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20764894765727237563622213 3893417768573857043179165)
                      ·
                        rfl

theorem cell23_7582404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_7582404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582404 prefixEnd_7582404 := by exact prefixLift 7582404
  have htrace : WordTrace (prefixWord ++ tailWord_7582404) baseStart_7582404 baseEnd_7582404 := by
    simpa [prefixWord, tailWord_7582404, baseEnd_7582404] using wordTrace_append hprefix tailTrace_7582404
  have hstable : (prefixWord ++ tailWord_7582404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582404).length < 2 ^ (prefixWord ++ tailWord_7582404).sum := by decide
  have hdescent : baseEnd_7582404 < baseStart_7582404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582414 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_7582414 : Nat := 118140960795 + 7582414 * 2 ^ 59
def prefixEnd_7582414 : Nat := 4983230072969 + 3 ^ 40 * 7582414 * 2
def baseEnd_7582414 : Nat := 1297807634460134001351373

theorem tailTrace_7582414 : CollatzResearch.WordTrace tailWord_7582414 prefixEnd_7582414 1297807634460134001351373 := by
  unfold tailWord_7582414
  simp only [CollatzResearch.WordTrace]
  refine ⟨34569169794027065757278287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184368905568144350705484197 34569169794027065757278287)
  ·
    refine ⟨51853754691040598635917431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34569169794027065757278287 51853754691040598635917431)
    ·
      refine ⟨77780632036560897953876147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51853754691040598635917431 77780632036560897953876147)
      ·
        refine ⟨116670948054841346930814221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77780632036560897953876147 116670948054841346930814221)
        ·
          refine ⟨43751605520565505099055333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116670948054841346930814221 43751605520565505099055333)
          ·
            refine ⟨8203426035106032206072875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43751605520565505099055333 8203426035106032206072875)
            ·
              refine ⟨12305139052659048309109313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203426035106032206072875 12305139052659048309109313)
              ·
                refine ⟨9228854289494286231831985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12305139052659048309109313 9228854289494286231831985)
                ·
                  refine ⟨6921640717120714673873989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9228854289494286231831985 6921640717120714673873989)
                  ·
                    refine ⟨1297807634460134001351373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6921640717120714673873989 1297807634460134001351373)
                    ·
                      rfl

theorem cell23_7582414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_7582414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582414 prefixEnd_7582414 := by exact prefixLift 7582414
  have htrace : WordTrace (prefixWord ++ tailWord_7582414) baseStart_7582414 baseEnd_7582414 := by
    simpa [prefixWord, tailWord_7582414, baseEnd_7582414] using wordTrace_append hprefix tailTrace_7582414
  have hstable : (prefixWord ++ tailWord_7582414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582414).length < 2 ^ (prefixWord ++ tailWord_7582414).sum := by decide
  have hdescent : baseEnd_7582414 < baseStart_7582414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582437 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7582437 : Nat := 118140960795 + 7582437 * 2 ^ 59
def prefixEnd_7582437 : Nat := 4983230072969 + 3 ^ 40 * 7582437 * 2
def baseEnd_7582437 : Nat := 3893434713435455414066513

theorem tailTrace_7582437 : CollatzResearch.WordTrace tailWord_7582437 prefixEnd_7582437 3893434713435455414066513 := by
  unfold tailWord_7582437
  simp only [CollatzResearch.WordTrace]
  refine ⟨276554197231133200986313565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184369464820755467324209043 276554197231133200986313565)
  ·
    refine ⟨103707823961674950369867587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276554197231133200986313565 103707823961674950369867587)
    ·
      refine ⟨155561735942512425554801381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103707823961674950369867587 155561735942512425554801381)
      ·
        refine ⟨29167825489221079791525259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155561735942512425554801381 29167825489221079791525259)
        ·
          refine ⟨43751738233831619687287889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29167825489221079791525259 43751738233831619687287889)
          ·
            refine ⟨32813803675373714765465917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43751738233831619687287889 32813803675373714765465917)
            ·
              refine ⟨12305176378265143037049719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32813803675373714765465917 12305176378265143037049719)
              ·
                refine ⟨18457764567397714555574579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12305176378265143037049719 18457764567397714555574579)
                ·
                  refine ⟨27686646851096571833361869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18457764567397714555574579 27686646851096571833361869)
                  ·
                    refine ⟨10382492569161214437510701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27686646851096571833361869 10382492569161214437510701)
                    ·
                      refine ⟨3893434713435455414066513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10382492569161214437510701 3893434713435455414066513)
                      ·
                        rfl

theorem cell23_7582437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7582437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582437 prefixEnd_7582437 := by exact prefixLift 7582437
  have htrace : WordTrace (prefixWord ++ tailWord_7582437) baseStart_7582437 baseEnd_7582437 := by
    simpa [prefixWord, tailWord_7582437, baseEnd_7582437] using wordTrace_append hprefix tailTrace_7582437
  have hstable : (prefixWord ++ tailWord_7582437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582437).length < 2 ^ (prefixWord ++ tailWord_7582437).sum := by decide
  have hdescent : baseEnd_7582437 < baseStart_7582437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582450 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7582450 : Nat := 118140960795 + 7582450 * 2 ^ 59
def prefixEnd_7582450 : Nat := 4983230072969 + 3 ^ 40 * 7582450 * 2
def baseEnd_7582450 : Nat := 3893441388683963863203953

theorem tailTrace_7582450 : CollatzResearch.WordTrace tailWord_7582450 prefixEnd_7582450 3893441388683963863203953 := by
  unfold tailWord_7582450
  simp only [CollatzResearch.WordTrace]
  refine ⟨69138667845021526051634201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184369780920057402804357869 69138667845021526051634201)
  ·
    refine ⟨51854000883766144538725651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69138667845021526051634201 51854000883766144538725651)
    ·
      refine ⟨77781001325649216808088477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51854000883766144538725651 77781001325649216808088477)
      ·
        refine ⟨29167875497118456303033179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77781001325649216808088477 29167875497118456303033179)
        ·
          refine ⟨43751813245677684454549769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29167875497118456303033179 43751813245677684454549769)
          ·
            refine ⟨32813859934258263340912327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43751813245677684454549769 32813859934258263340912327)
            ·
              refine ⟨49220789901387395011368491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32813859934258263340912327 49220789901387395011368491)
              ·
                refine ⟨73831184852081092517052737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49220789901387395011368491 73831184852081092517052737)
                ·
                  refine ⟨55373388639060819387789553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73831184852081092517052737 55373388639060819387789553)
                  ·
                    refine ⟨41530041479295614540842165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55373388639060819387789553 41530041479295614540842165)
                    ·
                      refine ⟨3893441388683963863203953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41530041479295614540842165 3893441388683963863203953)
                      ·
                        rfl

theorem cell23_7582450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7582450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582450 prefixEnd_7582450 := by exact prefixLift 7582450
  have htrace : WordTrace (prefixWord ++ tailWord_7582450) baseStart_7582450 baseEnd_7582450 := by
    simpa [prefixWord, tailWord_7582450, baseEnd_7582450] using wordTrace_append hprefix tailTrace_7582450
  have hstable : (prefixWord ++ tailWord_7582450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582450).length < 2 ^ (prefixWord ++ tailWord_7582450).sum := by decide
  have hdescent : baseEnd_7582450 < baseStart_7582450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582490 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_7582490 : Nat := 118140960795 + 7582490 * 2 ^ 59
def prefixEnd_7582490 : Nat := 4983230072969 + 3 ^ 40 * 7582490 * 2
def baseEnd_7582490 : Nat := 3893461927910143706703769

theorem tailTrace_7582490 : CollatzResearch.WordTrace tailWord_7582490 prefixEnd_7582490 3893461927910143706703769 := by
  unfold tailWord_7582490
  simp only [CollatzResearch.WordTrace]
  refine ⟨69139032574985297759498231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184370753533294127358661949 69139032574985297759498231)
  ·
    refine ⟨103708548862477946639247347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69139032574985297759498231 103708548862477946639247347)
    ·
      refine ⟨155562823293716919958871021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103708548862477946639247347 155562823293716919958871021)
      ·
        refine ⟨58336058735143844984576633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155562823293716919958871021 58336058735143844984576633)
        ·
          refine ⟨43752044051357883738432475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58336058735143844984576633 43752044051357883738432475)
          ·
            refine ⟨65628066077036825607648713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43752044051357883738432475 65628066077036825607648713)
            ·
              refine ⟨49221049557777619205736535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65628066077036825607648713 49221049557777619205736535)
              ·
                refine ⟨73831574336666428808604803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49221049557777619205736535 73831574336666428808604803)
                ·
                  refine ⟨110747361504999643212907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73831574336666428808604803 110747361504999643212907205)
                  ·
                    refine ⟨20765130282187433102420101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110747361504999643212907205 20765130282187433102420101)
                    ·
                      refine ⟨3893461927910143706703769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20765130282187433102420101 3893461927910143706703769)
                      ·
                        rfl

theorem cell23_7582490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_7582490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582490 prefixEnd_7582490 := by exact prefixLift 7582490
  have htrace : WordTrace (prefixWord ++ tailWord_7582490) baseStart_7582490 baseEnd_7582490 := by
    simpa [prefixWord, tailWord_7582490, baseEnd_7582490] using wordTrace_append hprefix tailTrace_7582490
  have hstable : (prefixWord ++ tailWord_7582490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582490).length < 2 ^ (prefixWord ++ tailWord_7582490).sum := by decide
  have hdescent : baseEnd_7582490 < baseStart_7582490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582537 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 2, 5, 2]
def baseStart_7582537 : Nat := 118140960795 + 7582537 * 2 ^ 59
def prefixEnd_7582537 : Nat := 4983230072969 + 3 ^ 40 * 7582537 * 2
def baseEnd_7582537 : Nat := 3893486061500905022816053

theorem tailTrace_7582537 : CollatzResearch.WordTrace tailWord_7582537 prefixEnd_7582537 3893486061500905022816053 := by
  unfold tailWord_7582537
  simp only [CollatzResearch.WordTrace]
  refine ⟨276557844530770918064953865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184371896353847278709969243 276557844530770918064953865)
  ·
    refine ⟨207418383398078188548715399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276557844530770918064953865 207418383398078188548715399)
    ·
      refine ⟨311127575097117282823073099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207418383398078188548715399 311127575097117282823073099)
      ·
        refine ⟨466691362645675924234609649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311127575097117282823073099 466691362645675924234609649)
        ·
          refine ⟨350018521984256943175957237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466691362645675924234609649 350018521984256943175957237)
          ·
            refine ⟨32814236436024088422745991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350018521984256943175957237 32814236436024088422745991)
            ·
              refine ⟨49221354654036132634118987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32814236436024088422745991 49221354654036132634118987)
              ·
                refine ⟨73832031981054198951178481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49221354654036132634118987 73832031981054198951178481)
                ·
                  refine ⟨55374023985790649213383861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73832031981054198951178481 55374023985790649213383861)
                  ·
                    refine ⟨5191314748667873363754737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55374023985790649213383861 5191314748667873363754737)
                    ·
                      refine ⟨3893486061500905022816053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191314748667873363754737 3893486061500905022816053)
                      ·
                        rfl

theorem cell23_7582537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 5, 2].length) (baseStart_7582537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582537 prefixEnd_7582537 := by exact prefixLift 7582537
  have htrace : WordTrace (prefixWord ++ tailWord_7582537) baseStart_7582537 baseEnd_7582537 := by
    simpa [prefixWord, tailWord_7582537, baseEnd_7582537] using wordTrace_append hprefix tailTrace_7582537
  have hstable : (prefixWord ++ tailWord_7582537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582537).length < 2 ^ (prefixWord ++ tailWord_7582537).sum := by decide
  have hdescent : baseEnd_7582537 < baseStart_7582537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582564 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_7582564 : Nat := 118140960795 + 7582564 * 2 ^ 59
def prefixEnd_7582564 : Nat := 4983230072969 + 3 ^ 40 * 7582564 * 2
def baseEnd_7582564 : Nat := 1297833308492858805726143

theorem tailTrace_7582564 : CollatzResearch.WordTrace tailWord_7582564 prefixEnd_7582564 1297833308492858805726143 := by
  unfold tailWord_7582564
  simp only [CollatzResearch.WordTrace]
  refine ⟨138279414650836550838093373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184372552867782067784124497 138279414650836550838093373)
  ·
    refine ⟨51854780494063706564285015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138279414650836550838093373 51854780494063706564285015)
    ·
      refine ⟨77782170741095559846427523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51854780494063706564285015 77782170741095559846427523)
      ·
        refine ⟨116673256111643339769641285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77782170741095559846427523 116673256111643339769641285)
        ·
          refine ⟨21876235520933126206807741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116673256111643339769641285 21876235520933126206807741)
          ·
            refine ⟨8203588320349922327552903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21876235520933126206807741 8203588320349922327552903)
            ·
              refine ⟨12305382480524883491329355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203588320349922327552903 12305382480524883491329355)
              ·
                refine ⟨18458073720787325236994033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12305382480524883491329355 18458073720787325236994033)
                ·
                  refine ⟨13843555290590493927745525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18458073720787325236994033 13843555290590493927745525)
                  ·
                    refine ⟨1297833308492858805726143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13843555290590493927745525 1297833308492858805726143)
                    ·
                      rfl

theorem cell23_7582564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_7582564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582564 prefixEnd_7582564 := by exact prefixLift 7582564
  have htrace : WordTrace (prefixWord ++ tailWord_7582564) baseStart_7582564 baseEnd_7582564 := by
    simpa [prefixWord, tailWord_7582564, baseEnd_7582564] using wordTrace_append hprefix tailTrace_7582564
  have hstable : (prefixWord ++ tailWord_7582564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582564).length < 2 ^ (prefixWord ++ tailWord_7582564).sum := by decide
  have hdescent : baseEnd_7582564 < baseStart_7582564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582567 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_7582567 : Nat := 118140960795 + 7582567 * 2 ^ 59
def prefixEnd_7582567 : Nat := 4983230072969 + 3 ^ 40 * 7582567 * 2
def baseEnd_7582567 : Nat := 3893501465920539905440915

theorem tailTrace_7582567 : CollatzResearch.WordTrace tailWord_7582567 prefixEnd_7582567 3893501465920539905440915 := by
  unfold tailWord_7582567
  simp only [CollatzResearch.WordTrace]
  refine ⟨276558938720662233188545955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184372625813774822125697303 276558938720662233188545955)
  ·
    refine ⟨414838408080993349782818933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276558938720662233188545955 414838408080993349782818933)
    ·
      refine ⟨38891100757593126542139275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 414838408080993349782818933 38891100757593126542139275)
      ·
        refine ⟨58336651136389689813208913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38891100757593126542139275 58336651136389689813208913)
        ·
          refine ⟨43752488352292267359906685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58336651136389689813208913 43752488352292267359906685)
          ·
            refine ⟨16407183132109600259965007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43752488352292267359906685 16407183132109600259965007)
            ·
              refine ⟨24610774698164400389947511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16407183132109600259965007 24610774698164400389947511)
              ·
                refine ⟨36916162047246600584921267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24610774698164400389947511 36916162047246600584921267)
                ·
                  refine ⟨55374243070869900877381901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36916162047246600584921267 55374243070869900877381901)
                  ·
                    refine ⟨20765341151576212829018213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55374243070869900877381901 20765341151576212829018213)
                    ·
                      refine ⟨3893501465920539905440915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20765341151576212829018213 3893501465920539905440915)
                      ·
                        rfl

theorem cell23_7582567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_7582567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582567 prefixEnd_7582567 := by exact prefixLift 7582567
  have htrace : WordTrace (prefixWord ++ tailWord_7582567) baseStart_7582567 baseEnd_7582567 := by
    simpa [prefixWord, tailWord_7582567, baseEnd_7582567] using wordTrace_append hprefix tailTrace_7582567
  have hstable : (prefixWord ++ tailWord_7582567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582567).length < 2 ^ (prefixWord ++ tailWord_7582567).sum := by decide
  have hdescent : baseEnd_7582567 < baseStart_7582567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582587 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 3]
def baseStart_7582587 : Nat := 118140960795 + 7582587 * 2 ^ 59
def prefixEnd_7582587 : Nat := 4983230072969 + 3 ^ 40 * 7582587 * 2
def baseEnd_7582587 : Nat := 3893511735533629827190823

theorem tailTrace_7582587 : CollatzResearch.WordTrace tailWord_7582587 prefixEnd_7582587 3893511735533629827190823 := by
  unfold tailWord_7582587
  simp only [CollatzResearch.WordTrace]
  refine ⟨276559668180589776604274015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184373112120393184402849343 276559668180589776604274015)
  ·
    refine ⟨414839502270884664906411023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276559668180589776604274015 414839502270884664906411023)
    ·
      refine ⟨622259253406326997359616535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414839502270884664906411023 622259253406326997359616535)
      ·
        refine ⟨933388880109490496039424803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622259253406326997359616535 933388880109490496039424803)
        ·
          refine ⟨1400083320164235744059137205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933388880109490496039424803 1400083320164235744059137205)
          ·
            refine ⟨131257811265397101005544113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1400083320164235744059137205 131257811265397101005544113)
            ·
              refine ⟨98443358449047825754158085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131257811265397101005544113 98443358449047825754158085)
              ·
                refine ⟨18458129709196467328904641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98443358449047825754158085 18458129709196467328904641)
                ·
                  refine ⟨13843597281897350496678481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18458129709196467328904641 13843597281897350496678481)
                  ·
                    refine ⟨10382697961423012872508861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13843597281897350496678481 10382697961423012872508861)
                    ·
                      refine ⟨3893511735533629827190823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10382697961423012872508861 3893511735533629827190823)
                      ·
                        rfl

theorem cell23_7582587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 3].length) (baseStart_7582587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582587 prefixEnd_7582587 := by exact prefixLift 7582587
  have htrace : WordTrace (prefixWord ++ tailWord_7582587) baseStart_7582587 baseEnd_7582587 := by
    simpa [prefixWord, tailWord_7582587, baseEnd_7582587] using wordTrace_append hprefix tailTrace_7582587
  have hstable : (prefixWord ++ tailWord_7582587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582587).length < 2 ^ (prefixWord ++ tailWord_7582587).sum := by decide
  have hdescent : baseEnd_7582587 < baseStart_7582587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582678 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_7582678 : Nat := 118140960795 + 7582678 * 2 ^ 59
def prefixEnd_7582678 : Nat := 4983230072969 + 3 ^ 40 * 7582678 * 2
def baseEnd_7582678 : Nat := 3893558462273188971152905

theorem tailTrace_7582678 : CollatzResearch.WordTrace tailWord_7582678 prefixEnd_7582678 3893558462273188971152905 := by
  unfold tailWord_7582678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17285186701453756196614793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184375324815506732763891125 17285186701453756196614793)
  ·
    refine ⟨12963890026090317147461095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17285186701453756196614793 12963890026090317147461095)
    ·
      refine ⟨19445835039135475721191643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12963890026090317147461095 19445835039135475721191643)
      ·
        refine ⟨29168752558703213581787465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19445835039135475721191643 29168752558703213581787465)
        ·
          refine ⟨21876564419027410186340599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29168752558703213581787465 21876564419027410186340599)
          ·
            refine ⟨32814846628541115279510899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21876564419027410186340599 32814846628541115279510899)
            ·
              refine ⟨49222269942811672919266349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32814846628541115279510899 49222269942811672919266349)
              ·
                refine ⟨18458351228554377344724881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49222269942811672919266349 18458351228554377344724881)
                ·
                  refine ⟨13843763421415783008543661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18458351228554377344724881 13843763421415783008543661)
                  ·
                    refine ⟨5191411283030918628203873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13843763421415783008543661 5191411283030918628203873)
                    ·
                      refine ⟨3893558462273188971152905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191411283030918628203873 3893558462273188971152905)
                      ·
                        rfl

theorem cell23_7582678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_7582678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582678 prefixEnd_7582678 := by exact prefixLift 7582678
  have htrace : WordTrace (prefixWord ++ tailWord_7582678) baseStart_7582678 baseEnd_7582678 := by
    simpa [prefixWord, tailWord_7582678, baseEnd_7582678] using wordTrace_append hprefix tailTrace_7582678
  have hstable : (prefixWord ++ tailWord_7582678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582678).length < 2 ^ (prefixWord ++ tailWord_7582678).sum := by decide
  have hdescent : baseEnd_7582678 < baseStart_7582678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582691 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7582691 : Nat := 118140960795 + 7582691 * 2 ^ 59
def prefixEnd_7582691 : Nat := 4983230072969 + 3 ^ 40 * 7582691 * 2
def baseEnd_7582691 : Nat := 3893565137521697420290345

theorem tailTrace_7582691 : CollatzResearch.WordTrace tailWord_7582691 prefixEnd_7582691 3893565137521697420290345 := by
  unfold tailWord_7582691
  simp only [CollatzResearch.WordTrace]
  refine ⟨276563461372213002366059927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184375640914808668244039951 276563461372213002366059927)
  ·
    refine ⟨414845192058319503549089891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276563461372213002366059927 414845192058319503549089891)
    ·
      refine ⟨622267788087479255323634837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414845192058319503549089891 622267788087479255323634837)
      ·
        refine ⟨29168802566600590093295383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 622267788087479255323634837 29168802566600590093295383)
        ·
          refine ⟨43753203849900885139943075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29168802566600590093295383 43753203849900885139943075)
          ·
            refine ⟨65629805774851327709914613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43753203849900885139943075 65629805774851327709914613)
            ·
              refine ⟨6152794291392311972804495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65629805774851327709914613 6152794291392311972804495)
              ·
                refine ⟨9229191437088467959206743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152794291392311972804495 9229191437088467959206743)
                ·
                  refine ⟨13843787155632701938810115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9229191437088467959206743 13843787155632701938810115)
                  ·
                    refine ⟨20765680733449052908215173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13843787155632701938810115 20765680733449052908215173)
                    ·
                      refine ⟨3893565137521697420290345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20765680733449052908215173 3893565137521697420290345)
                      ·
                        rfl

theorem cell23_7582691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7582691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582691 prefixEnd_7582691 := by exact prefixLift 7582691
  have htrace : WordTrace (prefixWord ++ tailWord_7582691) baseStart_7582691 baseEnd_7582691 := by
    simpa [prefixWord, tailWord_7582691, baseEnd_7582691] using wordTrace_append hprefix tailTrace_7582691
  have hstable : (prefixWord ++ tailWord_7582691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582691).length < 2 ^ (prefixWord ++ tailWord_7582691).sum := by decide
  have hdescent : baseEnd_7582691 < baseStart_7582691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582702 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_7582702 : Nat := 118140960795 + 7582702 * 2 ^ 59
def prefixEnd_7582702 : Nat := 4983230072969 + 3 ^ 40 * 7582702 * 2
def baseEnd_7582702 : Nat := 3893570785808896877252795

theorem tailTrace_7582702 : CollatzResearch.WordTrace tailWord_7582702 prefixEnd_7582702 3893570785808896877252795 := by
  unfold tailWord_7582702
  simp only [CollatzResearch.WordTrace]
  refine ⟨34570482821896643905588795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184375908383448767496473573 34570482821896643905588795)
  ·
    refine ⟨51855724232844965858383193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34570482821896643905588795 51855724232844965858383193)
    ·
      refine ⟨38891793174633724393787395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51855724232844965858383193 38891793174633724393787395)
      ·
        refine ⟨58337689761950586590681093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38891793174633724393787395 58337689761950586590681093)
        ·
          refine ⟨10938316830365734985752705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58337689761950586590681093 10938316830365734985752705)
          ·
            refine ⟨8203737622774301239314529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10938316830365734985752705 8203737622774301239314529)
            ·
              refine ⟨6152803217080725929485897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8203737622774301239314529 6152803217080725929485897)
              ·
                refine ⟨4614602412810544447114423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6152803217080725929485897 4614602412810544447114423)
                ·
                  refine ⟨6921903619215816670671635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614602412810544447114423 6921903619215816670671635)
                  ·
                    refine ⟨10382855428823725006007453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6921903619215816670671635 10382855428823725006007453)
                    ·
                      refine ⟨3893570785808896877252795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10382855428823725006007453 3893570785808896877252795)
                      ·
                        rfl

theorem cell23_7582702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_7582702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582702 prefixEnd_7582702 := by exact prefixLift 7582702
  have htrace : WordTrace (prefixWord ++ tailWord_7582702) baseStart_7582702 baseEnd_7582702 := by
    simpa [prefixWord, tailWord_7582702, baseEnd_7582702] using wordTrace_append hprefix tailTrace_7582702
  have hstable : (prefixWord ++ tailWord_7582702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582702).length < 2 ^ (prefixWord ++ tailWord_7582702).sum := by decide
  have hdescent : baseEnd_7582702 < baseStart_7582702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582727 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 2, 7]
def baseStart_7582727 : Nat := 118140960795 + 7582727 * 2 ^ 59
def prefixEnd_7582727 : Nat := 4983230072969 + 3 ^ 40 * 7582727 * 2
def baseEnd_7582727 : Nat := 1297861207608419759813393

theorem tailTrace_7582727 : CollatzResearch.WordTrace tailWord_7582727 prefixEnd_7582727 1297861207608419759813393 := by
  unfold tailWord_7582727
  simp only [CollatzResearch.WordTrace]
  refine ⟨276564774400082580514370435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184376516266721720342913623 276564774400082580514370435)
  ·
    refine ⟨414847161600123870771555653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276564774400082580514370435 414847161600123870771555653)
    ·
      refine ⟨77783842800023225769666685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414847161600123870771555653 77783842800023225769666685)
      ·
        refine ⟨29168941050008709663625007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77783842800023225769666685 29168941050008709663625007)
        ·
          refine ⟨43753411575013064495437511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29168941050008709663625007 43753411575013064495437511)
          ·
            refine ⟨65630117362519596743156267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43753411575013064495437511 65630117362519596743156267)
            ·
              refine ⟨98445176043779395114734401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65630117362519596743156267 98445176043779395114734401)
              ·
                refine ⟨73833882032834546336050801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98445176043779395114734401 73833882032834546336050801)
                ·
                  refine ⟨55375411524625909752038101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73833882032834546336050801 55375411524625909752038101)
                  ·
                    refine ⟨1297861207608419759813393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55375411524625909752038101 1297861207608419759813393)
                    ·
                      rfl

theorem cell23_7582727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_7582727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582727 prefixEnd_7582727 := by exact prefixLift 7582727
  have htrace : WordTrace (prefixWord ++ tailWord_7582727) baseStart_7582727 baseEnd_7582727 := by
    simpa [prefixWord, tailWord_7582727, baseEnd_7582727] using wordTrace_append hprefix tailTrace_7582727
  have hstable : (prefixWord ++ tailWord_7582727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582727).length < 2 ^ (prefixWord ++ tailWord_7582727).sum := by decide
  have hdescent : baseEnd_7582727 < baseStart_7582727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582757 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_7582757 : Nat := 118140960795 + 7582757 * 2 ^ 59
def prefixEnd_7582757 : Nat := 4983230072969 + 3 ^ 40 * 7582757 * 2
def baseEnd_7582757 : Nat := 1297866342414964720688347

theorem tailTrace_7582757 : CollatzResearch.WordTrace tailWord_7582757 prefixEnd_7582757 1297866342414964720688347 := by
  unfold tailWord_7582757
  simp only [CollatzResearch.WordTrace]
  refine ⟨276565868589973895637962525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184377245726649263758641683 276565868589973895637962525)
  ·
    refine ⟨103712200721240210864235947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276565868589973895637962525 103712200721240210864235947)
    ·
      refine ⟨155568301081860316296353921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103712200721240210864235947 155568301081860316296353921)
      ·
        refine ⟨116676225811395237222265441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155568301081860316296353921 116676225811395237222265441)
        ·
          refine ⟨87507169358546427916699081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116676225811395237222265441 87507169358546427916699081)
          ·
            refine ⟨65630377018909820937524311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87507169358546427916699081 65630377018909820937524311)
            ·
              refine ⟨98445565528364731406286467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65630377018909820937524311 98445565528364731406286467)
              ·
                refine ⟨147668348292547097109429701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98445565528364731406286467 147668348292547097109429701)
                ·
                  refine ⟨27687815304852580708018069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147668348292547097109429701 27687815304852580708018069)
                  ·
                    refine ⟨1297866342414964720688347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27687815304852580708018069 1297866342414964720688347)
                    ·
                      rfl

theorem cell23_7582757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_7582757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582757 prefixEnd_7582757 := by exact prefixLift 7582757
  have htrace : WordTrace (prefixWord ++ tailWord_7582757) baseStart_7582757 baseEnd_7582757 := by
    simpa [prefixWord, tailWord_7582757, baseEnd_7582757] using wordTrace_append hprefix tailTrace_7582757
  have hstable : (prefixWord ++ tailWord_7582757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582757).length < 2 ^ (prefixWord ++ tailWord_7582757).sum := by decide
  have hdescent : baseEnd_7582757 < baseStart_7582757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582785 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_7582785 : Nat := 118140960795 + 7582785 * 2 ^ 59
def prefixEnd_7582785 : Nat := 4983230072969 + 3 ^ 40 * 7582785 * 2
def baseEnd_7582785 : Nat := 3893613404703220052514913

theorem tailTrace_7582785 : CollatzResearch.WordTrace tailWord_7582785 prefixEnd_7582785 3893613404703220052514913 := by
  unfold tailWord_7582785
  simp only [CollatzResearch.WordTrace]
  refine ⟨276566889833872456419981809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184377926555914970946654539 276566889833872456419981809)
  ·
    refine ⟨207425167375404342314986357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276566889833872456419981809 207425167375404342314986357)
    ·
      refine ⟨19446109441444157092029971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207425167375404342314986357 19446109441444157092029971)
      ·
        refine ⟨29169164162166235638044957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19446109441444157092029971 29169164162166235638044957)
        ·
          refine ⟨10938436560812338364266859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29169164162166235638044957 10938436560812338364266859)
          ·
            refine ⟨16407654841218507546400289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938436560812338364266859 16407654841218507546400289)
            ·
              refine ⟨12305741130913880659800217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16407654841218507546400289 12305741130913880659800217)
              ·
                refine ⟨9229305848185410494850163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12305741130913880659800217 9229305848185410494850163)
                ·
                  refine ⟨13843958772278115742275245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9229305848185410494850163 13843958772278115742275245)
                  ·
                    refine ⟨5191484539604293403353217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13843958772278115742275245 5191484539604293403353217)
                    ·
                      refine ⟨3893613404703220052514913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191484539604293403353217 3893613404703220052514913)
                      ·
                        rfl

theorem cell23_7582785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_7582785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582785 prefixEnd_7582785 := by exact prefixLift 7582785
  have htrace : WordTrace (prefixWord ++ tailWord_7582785) baseStart_7582785 baseEnd_7582785 := by
    simpa [prefixWord, tailWord_7582785, baseEnd_7582785] using wordTrace_append hprefix tailTrace_7582785
  have hstable : (prefixWord ++ tailWord_7582785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582785).length < 2 ^ (prefixWord ++ tailWord_7582785).sum := by decide
  have hdescent : baseEnd_7582785 < baseStart_7582785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582787 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 7]
def baseStart_7582787 : Nat := 118140960795 + 7582787 * 2 ^ 59
def prefixEnd_7582787 : Nat := 4983230072969 + 3 ^ 40 * 7582787 * 2
def baseEnd_7582787 : Nat := 432623825740503227187767

theorem tailTrace_7582787 : CollatzResearch.WordTrace tailWord_7582787 prefixEnd_7582787 432623825740503227187767 := by
  unfold tailWord_7582787
  simp only [CollatzResearch.WordTrace]
  refine ⟨276566962779865210761554615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184377975186576807174369743 276566962779865210761554615)
  ·
    refine ⟨414850444169797816142331923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276566962779865210761554615 414850444169797816142331923)
    ·
      refine ⟨622275666254696724213497885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414850444169797816142331923 622275666254696724213497885)
      ·
        refine ⟨233353374845511271580061707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622275666254696724213497885 233353374845511271580061707)
        ·
          refine ⟨350030062268266907370092561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233353374845511271580061707 350030062268266907370092561)
          ·
            refine ⟨262522546701200180527569421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350030062268266907370092561 262522546701200180527569421)
            ·
              refine ⟨98445955012950067697838533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262522546701200180527569421 98445955012950067697838533)
              ·
                refine ⟨18458616564928137693344725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98445955012950067697838533 18458616564928137693344725)
                ·
                  refine ⟨432623825740503227187767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18458616564928137693344725 432623825740503227187767)
                  ·
                    rfl

theorem cell23_7582787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 7].length) (baseStart_7582787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582787 prefixEnd_7582787 := by exact prefixLift 7582787
  have htrace : WordTrace (prefixWord ++ tailWord_7582787) baseStart_7582787 baseEnd_7582787 := by
    simpa [prefixWord, tailWord_7582787, baseEnd_7582787] using wordTrace_append hprefix tailTrace_7582787
  have hstable : (prefixWord ++ tailWord_7582787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582787).length < 2 ^ (prefixWord ++ tailWord_7582787).sum := by decide
  have hdescent : baseEnd_7582787 < baseStart_7582787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582834 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_7582834 : Nat := 118140960795 + 7582834 * 2 ^ 59
def prefixEnd_7582834 : Nat := 4983230072969 + 3 ^ 40 * 7582834 * 2
def baseEnd_7582834 : Nat := 1297879521751763453600729

theorem tailTrace_7582834 : CollatzResearch.WordTrace tailWord_7582834 prefixEnd_7582834 1297879521751763453600729 := by
  unfold tailWord_7582834
  simp only [CollatzResearch.WordTrace]
  refine ⟨69142169252673734447128889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184379118007129958525677037 69142169252673734447128889)
  ·
    refine ⟨51856626939505300835346667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69142169252673734447128889 51856626939505300835346667)
    ·
      refine ⟨77784940409257951253020001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51856626939505300835346667 77784940409257951253020001)
      ·
        refine ⟨58338705306943463439765001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77784940409257951253020001 58338705306943463439765001)
        ·
          refine ⟨43754028980207597579823751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58338705306943463439765001 43754028980207597579823751)
          ·
            refine ⟨65631043470311396369735627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43754028980207597579823751 65631043470311396369735627)
            ·
              refine ⟨98446565205467094554603441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65631043470311396369735627 98446565205467094554603441)
              ·
                refine ⟨73834923904100320915952581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98446565205467094554603441 73834923904100320915952581)
                ·
                  refine ⟨13844048232018810171741109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73834923904100320915952581 13844048232018810171741109)
                  ·
                    refine ⟨1297879521751763453600729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13844048232018810171741109 1297879521751763453600729)
                    ·
                      rfl

theorem cell23_7582834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_7582834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582834 prefixEnd_7582834 := by exact prefixLift 7582834
  have htrace : WordTrace (prefixWord ++ tailWord_7582834) baseStart_7582834 baseEnd_7582834 := by
    simpa [prefixWord, tailWord_7582834, baseEnd_7582834] using wordTrace_append hprefix tailTrace_7582834
  have hstable : (prefixWord ++ tailWord_7582834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582834).length < 2 ^ (prefixWord ++ tailWord_7582834).sum := by decide
  have hdescent : baseEnd_7582834 < baseStart_7582834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582864 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 7, 4]
def baseStart_7582864 : Nat := 118140960795 + 7582864 * 2 ^ 59
def prefixEnd_7582864 : Nat := 4983230072969 + 3 ^ 40 * 7582864 * 2
def baseEnd_7582864 : Nat := 1297884656558308414475683

theorem tailTrace_7582864 : CollatzResearch.WordTrace tailWord_7582864 prefixEnd_7582864 1297884656558308414475683 := by
  unfold tailWord_7582864
  simp only [CollatzResearch.WordTrace]
  refine ⟨138284885600293126456053823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184379847467057501941405097 138284885600293126456053823)
  ·
    refine ⟨207427328400439689684080735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138284885600293126456053823 207427328400439689684080735)
    ·
      refine ⟨311140992600659534526121103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207427328400439689684080735 311140992600659534526121103)
      ·
        refine ⟨466711488900989301789181655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311140992600659534526121103 466711488900989301789181655)
        ·
          refine ⟨700067233351483952683772483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466711488900989301789181655 700067233351483952683772483)
          ·
            refine ⟨1050100850027225929025658725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700067233351483952683772483 1050100850027225929025658725)
            ·
              refine ⟨196893909380104861692311011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1050100850027225929025658725 196893909380104861692311011)
              ·
                refine ⟨295340864070157292538466517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196893909380104861692311011 295340864070157292538466517)
                ·
                  refine ⟨6922051501644311543870309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 295340864070157292538466517 6922051501644311543870309)
                  ·
                    refine ⟨1297884656558308414475683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6922051501644311543870309 1297884656558308414475683)
                    ·
                      rfl

theorem cell23_7582864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_7582864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582864 prefixEnd_7582864 := by exact prefixLift 7582864
  have htrace : WordTrace (prefixWord ++ tailWord_7582864) baseStart_7582864 baseEnd_7582864 := by
    simpa [prefixWord, tailWord_7582864, baseEnd_7582864] using wordTrace_append hprefix tailTrace_7582864
  have hstable : (prefixWord ++ tailWord_7582864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582864).length < 2 ^ (prefixWord ++ tailWord_7582864).sum := by decide
  have hdescent : baseEnd_7582864 < baseStart_7582864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582871 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7582871 : Nat := 118140960795 + 7582871 * 2 ^ 59
def prefixEnd_7582871 : Nat := 4983230072969 + 3 ^ 40 * 7582871 * 2
def baseEnd_7582871 : Nat := 3893657564039506716039517

theorem tailTrace_7582871 : CollatzResearch.WordTrace tailWord_7582871 prefixEnd_7582871 3893657564039506716039517 := by
  unfold tailWord_7582871
  simp only [CollatzResearch.WordTrace]
  refine ⟨276570026511560893107612467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184380017674373928738408311 276570026511560893107612467)
  ·
    refine ⟨414855039767341339661418701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276570026511560893107612467 414855039767341339661418701)
    ·
      refine ⟨155570639912753002373032013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414855039767341339661418701 155570639912753002373032013)
      ·
        refine ⟨58338989967282375889887005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155570639912753002373032013 58338989967282375889887005)
        ·
          refine ⟨21877121237730890958707627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58338989967282375889887005 21877121237730890958707627)
          ·
            refine ⟨32815681856596336438061441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21877121237730890958707627 32815681856596336438061441)
            ·
              refine ⟨24611761392447252328546081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32815681856596336438061441 24611761392447252328546081)
              ·
                refine ⟨18458821044335439246409561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24611761392447252328546081 18458821044335439246409561)
                ·
                  refine ⟨13844115783251579434807171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18458821044335439246409561 13844115783251579434807171)
                  ·
                    refine ⟨20766173674877369152210757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13844115783251579434807171 20766173674877369152210757)
                    ·
                      refine ⟨3893657564039506716039517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20766173674877369152210757 3893657564039506716039517)
                      ·
                        rfl

theorem cell23_7582871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7582871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582871 prefixEnd_7582871 := by exact prefixLift 7582871
  have htrace : WordTrace (prefixWord ++ tailWord_7582871) baseStart_7582871 baseEnd_7582871 := by
    simpa [prefixWord, tailWord_7582871, baseEnd_7582871] using wordTrace_append hprefix tailTrace_7582871
  have hstable : (prefixWord ++ tailWord_7582871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582871).length < 2 ^ (prefixWord ++ tailWord_7582871).sum := by decide
  have hdescent : baseEnd_7582871 < baseStart_7582871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582881 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 3, 4]
def baseStart_7582881 : Nat := 118140960795 + 7582881 * 2 ^ 59
def prefixEnd_7582881 : Nat := 4983230072969 + 3 ^ 40 * 7582881 * 2
def baseEnd_7582881 : Nat := 1297887566282017225638157

theorem tailTrace_7582881 : CollatzResearch.WordTrace tailWord_7582881 prefixEnd_7582881 1297887566282017225638157 := by
  unfold tailWord_7582881
  simp only [CollatzResearch.WordTrace]
  refine ⟨276570391241524664815476497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184380260827683109876984331 276570391241524664815476497)
  ·
    refine ⟨207427793431143498611607373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276570391241524664815476497 207427793431143498611607373)
    ·
      refine ⟨77785422536678811979352765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207427793431143498611607373 77785422536678811979352765)
      ·
        refine ⟨29169533451254554492257287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77785422536678811979352765 29169533451254554492257287)
        ·
          refine ⟨43754300176881831738385931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29169533451254554492257287 43754300176881831738385931)
          ·
            refine ⟨65631450265322747607578897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43754300176881831738385931 65631450265322747607578897)
            ·
              refine ⟨49223587698992060705684173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65631450265322747607578897 49223587698992060705684173)
              ·
                refine ⟨18458845387122022764631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49223587698992060705684173 18458845387122022764631565)
                ·
                  refine ⟨6922067020170758536736837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18458845387122022764631565 6922067020170758536736837)
                  ·
                    refine ⟨1297887566282017225638157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6922067020170758536736837 1297887566282017225638157)
                    ·
                      rfl

theorem cell23_7582881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_7582881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582881 prefixEnd_7582881 := by exact prefixLift 7582881
  have htrace : WordTrace (prefixWord ++ tailWord_7582881) baseStart_7582881 baseEnd_7582881 := by
    simpa [prefixWord, tailWord_7582881, baseEnd_7582881] using wordTrace_append hprefix tailTrace_7582881
  have hstable : (prefixWord ++ tailWord_7582881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582881).length < 2 ^ (prefixWord ++ tailWord_7582881).sum := by decide
  have hdescent : baseEnd_7582881 < baseStart_7582881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582902 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7582902 : Nat := 118140960795 + 7582902 * 2 ^ 59
def prefixEnd_7582902 : Nat := 4983230072969 + 3 ^ 40 * 7582902 * 2
def baseEnd_7582902 : Nat := 1297891160646598698250625

theorem tailTrace_7582902 : CollatzResearch.WordTrace tailWord_7582902 prefixEnd_7582902 1297891160646598698250625 := by
  unfold tailWord_7582902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17285697323403036587624435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184380771449632390267993973 17285697323403036587624435)
  ·
    refine ⟨25928545985104554881436653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17285697323403036587624435 25928545985104554881436653)
    ·
      refine ⟨9723204744414208080538745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25928545985104554881436653 9723204744414208080538745)
      ·
        refine ⟨7292403558310656060404059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9723204744414208080538745 7292403558310656060404059)
        ·
          refine ⟨10938605337465984090606089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292403558310656060404059 10938605337465984090606089)
          ·
            refine ⟨8203954003099488067954567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10938605337465984090606089 8203954003099488067954567)
            ·
              refine ⟨12305931004649232101931851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203954003099488067954567 12305931004649232101931851)
              ·
                refine ⟨18458896506973848152897777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12305931004649232101931851 18458896506973848152897777)
                ·
                  refine ⟨13844172380230386114673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18458896506973848152897777 13844172380230386114673333)
                  ·
                    refine ⟨1297891160646598698250625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13844172380230386114673333 1297891160646598698250625)
                    ·
                      rfl

theorem cell23_7582902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7582902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582902 prefixEnd_7582902 := by exact prefixLift 7582902
  have htrace : WordTrace (prefixWord ++ tailWord_7582902) baseStart_7582902 baseEnd_7582902 := by
    simpa [prefixWord, tailWord_7582902, baseEnd_7582902] using wordTrace_append hprefix tailTrace_7582902
  have hstable : (prefixWord ++ tailWord_7582902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582902).length < 2 ^ (prefixWord ++ tailWord_7582902).sum := by decide
  have hdescent : baseEnd_7582902 < baseStart_7582902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582904 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_7582904 : Nat := 118140960795 + 7582904 * 2 ^ 59
def prefixEnd_7582904 : Nat := 4983230072969 + 3 ^ 40 * 7582904 * 2
def baseEnd_7582904 : Nat := 3893674508901105086926865

theorem tailTrace_7582904 : CollatzResearch.WordTrace tailWord_7582904 prefixEnd_7582904 3893674508901105086926865 := by
  unfold tailWord_7582904
  simp only [CollatzResearch.WordTrace]
  refine ⟨138285615060220669871781883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184380820080294226495709177 138285615060220669871781883)
  ·
    refine ⟨207428422590331004807672825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138285615060220669871781883 207428422590331004807672825)
    ·
      refine ⟨155571316942748253605754619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207428422590331004807672825 155571316942748253605754619)
      ·
        refine ⟨233356975414122380408631929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155571316942748253605754619 233356975414122380408631929)
        ·
          refine ⟨175017731560591785306473947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233356975414122380408631929 175017731560591785306473947)
          ·
            refine ⟨262526597340887677959710921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175017731560591785306473947 262526597340887677959710921)
            ·
              refine ⟨196894948005665758469783191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262526597340887677959710921 196894948005665758469783191)
              ·
                refine ⟨295342422008498637704674787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196894948005665758469783191 295342422008498637704674787)
                ·
                  refine ⟨443013633012747956557012181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295342422008498637704674787 443013633012747956557012181)
                  ·
                    refine ⟨10383132023736280231804973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 443013633012747956557012181 10383132023736280231804973)
                    ·
                      refine ⟨3893674508901105086926865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10383132023736280231804973 3893674508901105086926865)
                      ·
                        rfl

theorem cell23_7582904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_7582904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582904 prefixEnd_7582904 := by exact prefixLift 7582904
  have htrace : WordTrace (prefixWord ++ tailWord_7582904) baseStart_7582904 baseEnd_7582904 := by
    simpa [prefixWord, tailWord_7582904, baseEnd_7582904] using wordTrace_append hprefix tailTrace_7582904
  have hstable : (prefixWord ++ tailWord_7582904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582904).length < 2 ^ (prefixWord ++ tailWord_7582904).sum := by decide
  have hdescent : baseEnd_7582904 < baseStart_7582904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582908 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_7582908 : Nat := 118140960795 + 7582908 * 2 ^ 59
def prefixEnd_7582908 : Nat := 4983230072969 + 3 ^ 40 * 7582908 * 2
def baseEnd_7582908 : Nat := 3893676562823723071276847

theorem tailTrace_7582908 : CollatzResearch.WordTrace tailWord_7582908 prefixEnd_7582908 3893676562823723071276847 := by
  unfold tailWord_7582908
  simp only [CollatzResearch.WordTrace]
  refine ⟨138285688006213424213354689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184380917341617898951139585 138285688006213424213354689)
  ·
    refine ⟨103714266004660068160016017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138285688006213424213354689 103714266004660068160016017)
    ·
      refine ⟨77785699503495051120012013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103714266004660068160016017 77785699503495051120012013)
      ·
        refine ⟨29169637313810644170004505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77785699503495051120012013 29169637313810644170004505)
        ·
          refine ⟨21877227985357983127503379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29169637313810644170004505 21877227985357983127503379)
          ·
            refine ⟨32815841978036974691255069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21877227985357983127503379 32815841978036974691255069)
            ·
              refine ⟨12305940741763865509220651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32815841978036974691255069 12305940741763865509220651)
              ·
                refine ⟨18458911112645798263830977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12305940741763865509220651 18458911112645798263830977)
                ·
                  refine ⟨13844183334484348697873233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18458911112645798263830977 13844183334484348697873233)
                  ·
                    refine ⟨10383137500863261523404925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13844183334484348697873233 10383137500863261523404925)
                    ·
                      refine ⟨3893676562823723071276847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10383137500863261523404925 3893676562823723071276847)
                      ·
                        rfl

theorem cell23_7582908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_7582908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582908 prefixEnd_7582908 := by exact prefixLift 7582908
  have htrace : WordTrace (prefixWord ++ tailWord_7582908) baseStart_7582908 baseEnd_7582908 := by
    simpa [prefixWord, tailWord_7582908, baseEnd_7582908] using wordTrace_append hprefix tailTrace_7582908
  have hstable : (prefixWord ++ tailWord_7582908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582908).length < 2 ^ (prefixWord ++ tailWord_7582908).sum := by decide
  have hdescent : baseEnd_7582908 < baseStart_7582908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582961 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 8, 2]
def baseStart_7582961 : Nat := 118140960795 + 7582961 * 2 ^ 59
def prefixEnd_7582961 : Nat := 4983230072969 + 3 ^ 40 * 7582961 * 2
def baseEnd_7582961 : Nat := 3893703777298411363914103

theorem tailTrace_7582961 : CollatzResearch.WordTrace tailWord_7582961 prefixEnd_7582961 3893703777298411363914103 := by
  unfold tailWord_7582961
  simp only [CollatzResearch.WordTrace]
  refine ⟨276573309081234838478388737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184382206054156558985592491 276573309081234838478388737)
  ·
    refine ⟨207429981810926128858791553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276573309081234838478388737 207429981810926128858791553)
    ·
      refine ⟨155572486358194596644093665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207429981810926128858791553 155572486358194596644093665)
      ·
        refine ⟨116679364768645947483070249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155572486358194596644093665 116679364768645947483070249)
        ·
          refine ⟨87509523576484460612302687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116679364768645947483070249 87509523576484460612302687)
          ·
            refine ⟨131264285364726690918454031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87509523576484460612302687 131264285364726690918454031)
            ·
              refine ⟨196896428047090036377681047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131264285364726690918454031 196896428047090036377681047)
              ·
                refine ⟨295344642070635054566521571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196896428047090036377681047 295344642070635054566521571)
                ·
                  refine ⟨443016963105952581849782357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295344642070635054566521571 443016963105952581849782357)
                  ·
                    refine ⟨5191605036397881818552137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 443016963105952581849782357 5191605036397881818552137)
                    ·
                      refine ⟨3893703777298411363914103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191605036397881818552137 3893703777298411363914103)
                      ·
                        rfl

theorem cell23_7582961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_7582961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582961 prefixEnd_7582961 := by exact prefixLift 7582961
  have htrace : WordTrace (prefixWord ++ tailWord_7582961) baseStart_7582961 baseEnd_7582961 := by
    simpa [prefixWord, tailWord_7582961, baseEnd_7582961] using wordTrace_append hprefix tailTrace_7582961
  have hstable : (prefixWord ++ tailWord_7582961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582961).length < 2 ^ (prefixWord ++ tailWord_7582961).sum := by decide
  have hdescent : baseEnd_7582961 < baseStart_7582961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7582981 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_7582981 : Nat := 118140960795 + 7582981 * 2 ^ 59
def prefixEnd_7582981 : Nat := 4983230072969 + 3 ^ 40 * 7582981 * 2
def baseEnd_7582981 : Nat := 3893714046911501285664011

theorem tailTrace_7582981 : CollatzResearch.WordTrace tailWord_7582981 prefixEnd_7582981 3893714046911501285664011 := by
  unfold tailWord_7582981
  simp only [CollatzResearch.WordTrace]
  refine ⟨276574038541162381894116797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184382692360774921262744531 276574038541162381894116797)
  ·
    refine ⟨103715264452935893210293799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276574038541162381894116797 103715264452935893210293799)
    ·
      refine ⟨155572896679403839815440699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103715264452935893210293799 155572896679403839815440699)
      ·
        refine ⟨233359345019105759723161049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155572896679403839815440699 233359345019105759723161049)
        ·
          refine ⟨175019508764329319792370787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233359345019105759723161049 175019508764329319792370787)
          ·
            refine ⟨262529263146493979688556181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175019508764329319792370787 262529263146493979688556181)
            ·
              refine ⟨12306059209991905297901071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262529263146493979688556181 12306059209991905297901071)
              ·
                refine ⟨18459088814987857946851607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306059209991905297901071 18459088814987857946851607)
                ·
                  refine ⟨27688633222481786920277411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18459088814987857946851607 27688633222481786920277411)
                  ·
                    refine ⟨41532949833722680380416117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27688633222481786920277411 41532949833722680380416117)
                    ·
                      refine ⟨3893714046911501285664011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41532949833722680380416117 3893714046911501285664011)
                      ·
                        rfl

theorem cell23_7582981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_7582981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7582981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7582981 prefixEnd_7582981 := by exact prefixLift 7582981
  have htrace : WordTrace (prefixWord ++ tailWord_7582981) baseStart_7582981 baseEnd_7582981 := by
    simpa [prefixWord, tailWord_7582981, baseEnd_7582981] using wordTrace_append hprefix tailTrace_7582981
  have hstable : (prefixWord ++ tailWord_7582981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7582981).length < 2 ^ (prefixWord ++ tailWord_7582981).sum := by decide
  have hdescent : baseEnd_7582981 < baseStart_7582981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7582981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583005 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_7583005 : Nat := 118140960795 + 7583005 * 2 ^ 59
def prefixEnd_7583005 : Nat := 4983230072969 + 3 ^ 40 * 7583005 * 2
def baseEnd_7583005 : Nat := 1297908790149069730587967

theorem tailTrace_7583005 : CollatzResearch.WordTrace tailWord_7583005 prefixEnd_7583005 1297908790149069730587967 := by
  unfold tailWord_7583005
  simp only [CollatzResearch.WordTrace]
  refine ⟨276574913893075433992990469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184383275928716955995326979 276574913893075433992990469)
  ·
    refine ⟨51857796354951643873685713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276574913893075433992990469 51857796354951643873685713)
    ·
      refine ⟨38893347266213732905264285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51857796354951643873685713 38893347266213732905264285)
      ·
        refine ⟨14585005224830149839474107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38893347266213732905264285 14585005224830149839474107)
        ·
          refine ⟨21877507837245224759211161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585005224830149839474107 21877507837245224759211161)
          ·
            refine ⟨16408130877933918569408371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21877507837245224759211161 16408130877933918569408371)
            ·
              refine ⟨24612196316900877854112557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16408130877933918569408371 24612196316900877854112557)
              ·
                refine ⟨9229573618837829195292209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24612196316900877854112557 9229573618837829195292209)
                ·
                  refine ⟨6922180214128371896469157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9229573618837829195292209 6922180214128371896469157)
                  ·
                    refine ⟨1297908790149069730587967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6922180214128371896469157 1297908790149069730587967)
                    ·
                      rfl

theorem cell23_7583005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_7583005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583005 prefixEnd_7583005 := by exact prefixLift 7583005
  have htrace : WordTrace (prefixWord ++ tailWord_7583005) baseStart_7583005 baseEnd_7583005 := by
    simpa [prefixWord, tailWord_7583005, baseEnd_7583005] using wordTrace_append hprefix tailTrace_7583005
  have hstable : (prefixWord ++ tailWord_7583005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583005).length < 2 ^ (prefixWord ++ tailWord_7583005).sum := by decide
  have hdescent : baseEnd_7583005 < baseStart_7583005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583061 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_7583061 : Nat := 118140960795 + 7583061 * 2 ^ 59
def prefixEnd_7583061 : Nat := 4983230072969 + 3 ^ 40 * 7583061 * 2
def baseEnd_7583061 : Nat := 1297918375121286990887881

theorem tailTrace_7583061 : CollatzResearch.WordTrace tailWord_7583061 prefixEnd_7583061 1297918375121286990887881 := by
  unfold tailWord_7583061
  simp only [CollatzResearch.WordTrace]
  refine ⟨276576956380872555557029037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184384637587248370371352691 276576956380872555557029037)
  ·
    refine ⟨103716358642827208333885889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276576956380872555557029037 103716358642827208333885889)
    ·
      refine ⟨77787268982120406250414417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103716358642827208333885889 77787268982120406250414417)
      ·
        refine ⟨58340451736590304687810813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77787268982120406250414417 58340451736590304687810813)
        ·
          refine ⟨21877669401221364257929055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58340451736590304687810813 21877669401221364257929055)
          ·
            refine ⟨32816504101832046386893583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21877669401221364257929055 32816504101832046386893583)
            ·
              refine ⟨49224756152748069580340375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32816504101832046386893583 49224756152748069580340375)
              ·
                refine ⟨73837134229122104370510563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49224756152748069580340375 73837134229122104370510563)
                ·
                  refine ⟨110755701343683156555765845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73837134229122104370510563 110755701343683156555765845)
                  ·
                    refine ⟨1297918375121286990887881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110755701343683156555765845 1297918375121286990887881)
                    ·
                      rfl

theorem cell23_7583061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_7583061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583061 prefixEnd_7583061 := by exact prefixLift 7583061
  have htrace : WordTrace (prefixWord ++ tailWord_7583061) baseStart_7583061 baseEnd_7583061 := by
    simpa [prefixWord, tailWord_7583061, baseEnd_7583061] using wordTrace_append hprefix tailTrace_7583061
  have hstable : (prefixWord ++ tailWord_7583061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583061).length < 2 ^ (prefixWord ++ tailWord_7583061).sum := by decide
  have hdescent : baseEnd_7583061 < baseStart_7583061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583071 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_7583071 : Nat := 118140960795 + 7583071 * 2 ^ 59
def prefixEnd_7583071 : Nat := 4983230072969 + 3 ^ 40 * 7583071 * 2
def baseEnd_7583071 : Nat := 3893760260170405933538597

theorem tailTrace_7583071 : CollatzResearch.WordTrace tailWord_7583071 prefixEnd_7583071 3893760260170405933538597 := by
  unfold tailWord_7583071
  simp only [CollatzResearch.WordTrace]
  refine ⟨276577321110836327264893067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184384880740557551509928711 276577321110836327264893067)
  ·
    refine ⟨414865981666254490897339601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276577321110836327264893067 414865981666254490897339601)
    ·
      refine ⟨311149486249690868173004701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414865981666254490897339601 311149486249690868173004701)
      ·
        refine ⟨116681057343634075564876763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311149486249690868173004701 116681057343634075564876763)
        ·
          refine ⟨175021586015451113347315145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116681057343634075564876763 175021586015451113347315145)
          ·
            refine ⟨131266189511588335010486359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175021586015451113347315145 131266189511588335010486359)
            ·
              refine ⟨196899284267382502515729539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131266189511588335010486359 196899284267382502515729539)
              ·
                refine ⟨295348926401073753773594309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196899284267382502515729539 295348926401073753773594309)
                ·
                  refine ⟨55377923700201328832548933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295348926401073753773594309 55377923700201328832548933)
                  ·
                    refine ⟨10383360693787749156102925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55377923700201328832548933 10383360693787749156102925)
                    ·
                      refine ⟨3893760260170405933538597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10383360693787749156102925 3893760260170405933538597)
                      ·
                        rfl

theorem cell23_7583071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_7583071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583071 prefixEnd_7583071 := by exact prefixLift 7583071
  have htrace : WordTrace (prefixWord ++ tailWord_7583071) baseStart_7583071 baseEnd_7583071 := by
    simpa [prefixWord, tailWord_7583071, baseEnd_7583071] using wordTrace_append hprefix tailTrace_7583071
  have hstable : (prefixWord ++ tailWord_7583071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583071).length < 2 ^ (prefixWord ++ tailWord_7583071).sum := by decide
  have hdescent : baseEnd_7583071 < baseStart_7583071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583085 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_7583085 : Nat := 118140960795 + 7583085 * 2 ^ 59
def prefixEnd_7583085 : Nat := 4983230072969 + 3 ^ 40 * 7583085 * 2
def baseEnd_7583085 : Nat := 3893767448899568878763533

theorem tailTrace_7583085 : CollatzResearch.WordTrace tailWord_7583085 prefixEnd_7583085 3893767448899568878763533 := by
  unfold tailWord_7583085
  simp only [CollatzResearch.WordTrace]
  refine ⟨276577831732785607655902709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184385221155190405103935139 276577831732785607655902709)
  ·
    refine ⟨25929171724948650717740879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276577831732785607655902709 25929171724948650717740879)
    ·
      refine ⟨38893757587422976076611319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25929171724948650717740879 38893757587422976076611319)
      ·
        refine ⟨58340636381134464114916979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38893757587422976076611319 58340636381134464114916979)
        ·
          refine ⟨87510954571701696172375469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58340636381134464114916979 87510954571701696172375469)
          ·
            refine ⟨32816607964388136064640801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87510954571701696172375469 32816607964388136064640801)
            ·
              refine ⟨24612455973291102048480601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32816607964388136064640801 24612455973291102048480601)
              ·
                refine ⟨18459341979968326536360451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24612455973291102048480601 18459341979968326536360451)
                ·
                  refine ⟨27689012969952489804540677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18459341979968326536360451 27689012969952489804540677)
                  ·
                    refine ⟨5191689931866091838351377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27689012969952489804540677 5191689931866091838351377)
                    ·
                      refine ⟨3893767448899568878763533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191689931866091838351377 3893767448899568878763533)
                      ·
                        rfl

theorem cell23_7583085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_7583085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583085 prefixEnd_7583085 := by exact prefixLift 7583085
  have htrace : WordTrace (prefixWord ++ tailWord_7583085) baseStart_7583085 baseEnd_7583085 := by
    simpa [prefixWord, tailWord_7583085, baseEnd_7583085] using wordTrace_append hprefix tailTrace_7583085
  have hstable : (prefixWord ++ tailWord_7583085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583085).length < 2 ^ (prefixWord ++ tailWord_7583085).sum := by decide
  have hdescent : baseEnd_7583085 < baseStart_7583085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583108 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 7]
def baseStart_7583108 : Nat := 118140960795 + 7583108 * 2 ^ 59
def prefixEnd_7583108 : Nat := 4983230072969 + 3 ^ 40 * 7583108 * 2
def baseEnd_7583108 : Nat := 432642139883846920975103

theorem tailTrace_7583108 : CollatzResearch.WordTrace tailWord_7583108 prefixEnd_7583108 432642139883846920975103 := by
  unfold tailWord_7583108
  simp only [CollatzResearch.WordTrace]
  refine ⟨138289335305851141291994989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184385780407801521722659985 138289335305851141291994989)
  ·
    refine ⟨51858500739694177984498121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138289335305851141291994989 51858500739694177984498121)
    ·
      refine ⟨38893875554770633488373591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51858500739694177984498121 38893875554770633488373591)
      ·
        refine ⟨58340813332155950232560387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38893875554770633488373591 58340813332155950232560387)
        ·
          refine ⟨87511219998233925348840581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58340813332155950232560387 87511219998233925348840581)
          ·
            refine ⟨16408353749668861002907609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87511219998233925348840581 16408353749668861002907609)
            ·
              refine ⟨12306265312251645752180707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16408353749668861002907609 12306265312251645752180707)
              ·
                refine ⟨18459397968377468628271061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306265312251645752180707 18459397968377468628271061)
                ·
                  refine ⟨432642139883846920975103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18459397968377468628271061 432642139883846920975103)
                  ·
                    rfl

theorem cell23_7583108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_7583108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583108 prefixEnd_7583108 := by exact prefixLift 7583108
  have htrace : WordTrace (prefixWord ++ tailWord_7583108) baseStart_7583108 baseEnd_7583108 := by
    simpa [prefixWord, tailWord_7583108, baseEnd_7583108] using wordTrace_append hprefix tailTrace_7583108
  have hstable : (prefixWord ++ tailWord_7583108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583108).length < 2 ^ (prefixWord ++ tailWord_7583108).sum := by decide
  have hdescent : baseEnd_7583108 < baseStart_7583108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583121 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_7583121 : Nat := 118140960795 + 7583121 * 2 ^ 59
def prefixEnd_7583121 : Nat := 4983230072969 + 3 ^ 40 * 7583121 * 2
def baseEnd_7583121 : Nat := 1297928644734376912637789

theorem tailTrace_7583121 : CollatzResearch.WordTrace tailWord_7583121 prefixEnd_7583121 1297928644734376912637789 := by
  unfold tailWord_7583121
  simp only [CollatzResearch.WordTrace]
  refine ⟨276579144760655185804213217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184386096507103457202808811 276579144760655185804213217)
  ·
    refine ⟨207434358570491389353159913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276579144760655185804213217 207434358570491389353159913)
    ·
      refine ⟨155575768927868542014869935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207434358570491389353159913 155575768927868542014869935)
      ·
        refine ⟨233363653391802813022304903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155575768927868542014869935 233363653391802813022304903)
        ·
          refine ⟨350045480087704219533457355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233363653391802813022304903 350045480087704219533457355)
          ·
            refine ⟨525068220131556329300186033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350045480087704219533457355 525068220131556329300186033)
            ·
              refine ⟨393801165098667246975139525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525068220131556329300186033 393801165098667246975139525)
              ·
                refine ⟨73837718456000108807838661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393801165098667246975139525 73837718456000108807838661)
                ·
                  refine ⟨13844572210500020401469749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73837718456000108807838661 13844572210500020401469749)
                  ·
                    refine ⟨1297928644734376912637789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13844572210500020401469749 1297928644734376912637789)
                    ·
                      rfl

theorem cell23_7583121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_7583121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583121 prefixEnd_7583121 := by exact prefixLift 7583121
  have htrace : WordTrace (prefixWord ++ tailWord_7583121) baseStart_7583121 baseEnd_7583121 := by
    simpa [prefixWord, tailWord_7583121, baseEnd_7583121] using wordTrace_append hprefix tailTrace_7583121
  have hstable : (prefixWord ++ tailWord_7583121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583121).length < 2 ^ (prefixWord ++ tailWord_7583121).sum := by decide
  have hdescent : baseEnd_7583121 < baseStart_7583121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583138 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7583138 : Nat := 118140960795 + 7583138 * 2 ^ 59
def prefixEnd_7583138 : Nat := 4983230072969 + 3 ^ 40 * 7583138 * 2
def baseEnd_7583138 : Nat := 1297931554458085723800263

theorem tailTrace_7583138 : CollatzResearch.WordTrace tailWord_7583138 prefixEnd_7583138 1297931554458085723800263 := by
  unfold tailWord_7583138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69144941200398399426895517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184386509867729065138388045 69144941200398399426895517)
  ·
    refine ⟨25929352950149399785085819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69144941200398399426895517 25929352950149399785085819)
    ·
      refine ⟨38894029425224099677628729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25929352950149399785085819 38894029425224099677628729)
      ·
        refine ⟨29170522068918074758221547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38894029425224099677628729 29170522068918074758221547)
        ·
          refine ⟨43755783103377112137332321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29170522068918074758221547 43755783103377112137332321)
          ·
            refine ⟨32816837327532834102999241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43755783103377112137332321 32816837327532834102999241)
            ·
              refine ⟨24612627995649625577249431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32816837327532834102999241 24612627995649625577249431)
              ·
                refine ⟨36918941993474438365874147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24612627995649625577249431 36918941993474438365874147)
                ·
                  refine ⟨55378412990211657548811221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36918941993474438365874147 55378412990211657548811221)
                  ·
                    refine ⟨1297931554458085723800263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55378412990211657548811221 1297931554458085723800263)
                    ·
                      rfl

theorem cell23_7583138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7583138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583138 prefixEnd_7583138 := by exact prefixLift 7583138
  have htrace : WordTrace (prefixWord ++ tailWord_7583138) baseStart_7583138 baseEnd_7583138 := by
    simpa [prefixWord, tailWord_7583138, baseEnd_7583138] using wordTrace_append hprefix tailTrace_7583138
  have hstable : (prefixWord ++ tailWord_7583138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583138).length < 2 ^ (prefixWord ++ tailWord_7583138).sum := by decide
  have hdescent : baseEnd_7583138 < baseStart_7583138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583170 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7583170 : Nat := 118140960795 + 7583170 * 2 ^ 59
def prefixEnd_7583170 : Nat := 4983230072969 + 3 ^ 40 * 7583170 * 2
def baseEnd_7583170 : Nat := 3893811094755201046200643

theorem tailTrace_7583170 : CollatzResearch.WordTrace tailWord_7583170 prefixEnd_7583170 3893811094755201046200643 := by
  unfold tailWord_7583170
  simp only [CollatzResearch.WordTrace]
  refine ⟨69145232984369416793186741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184387287958318444781831309 69145232984369416793186741)
  ·
    refine ⟨6482365592284632824361257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69145232984369416793186741 6482365592284632824361257)
    ·
      refine ⟨4861774194213474618270943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6482365592284632824361257 4861774194213474618270943)
      ·
        refine ⟨7292661291320211927406415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861774194213474618270943 7292661291320211927406415)
        ·
          refine ⟨10938991936980317891109623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292661291320211927406415 10938991936980317891109623)
          ·
            refine ⟨16408487905470476836664435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938991936980317891109623 16408487905470476836664435)
            ·
              refine ⟨24612731858205715254996653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16408487905470476836664435 24612731858205715254996653)
              ·
                refine ⟨9229774446827143220623745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24612731858205715254996653 9229774446827143220623745)
                ·
                  refine ⟨6922330835120357415467809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9229774446827143220623745 6922330835120357415467809)
                  ·
                    refine ⟨5191748126340268061600857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6922330835120357415467809 5191748126340268061600857)
                    ·
                      refine ⟨3893811094755201046200643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5191748126340268061600857 3893811094755201046200643)
                      ·
                        rfl

theorem cell23_7583170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7583170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583170 prefixEnd_7583170 := by exact prefixLift 7583170
  have htrace : WordTrace (prefixWord ++ tailWord_7583170) baseStart_7583170 baseEnd_7583170 := by
    simpa [prefixWord, tailWord_7583170, baseEnd_7583170] using wordTrace_append hprefix tailTrace_7583170
  have hstable : (prefixWord ++ tailWord_7583170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583170).length < 2 ^ (prefixWord ++ tailWord_7583170).sum := by decide
  have hdescent : baseEnd_7583170 < baseStart_7583170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583171 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_7583171 : Nat := 118140960795 + 7583171 * 2 ^ 59
def prefixEnd_7583171 : Nat := 4983230072969 + 3 ^ 40 * 7583171 * 2
def baseEnd_7583171 : Nat := 3893811608235855542288137

theorem tailTrace_7583171 : CollatzResearch.WordTrace tailWord_7583171 prefixEnd_7583171 3893811608235855542288137 := by
  unfold tailWord_7583171
  simp only [CollatzResearch.WordTrace]
  refine ⟨276580968410474044343533367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184387312273649362895688911 276580968410474044343533367)
  ·
    refine ⟨414871452615711066515300051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276580968410474044343533367 414871452615711066515300051)
    ·
      refine ⟨622307178923566599772950077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414871452615711066515300051 622307178923566599772950077)
      ·
        refine ⟨233365192096337474914856279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622307178923566599772950077 233365192096337474914856279)
        ·
          refine ⟨350047788144506212372284419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233365192096337474914856279 350047788144506212372284419)
          ·
            refine ⟨525071682216759318558426629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350047788144506212372284419 525071682216759318558426629)
            ·
              refine ⟨98450940415642372229704993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525071682216759318558426629 98450940415642372229704993)
              ·
                refine ⟨73838205311731779172278745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98450940415642372229704993 73838205311731779172278745)
                ·
                  refine ⟨55378653983798834379209059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73838205311731779172278745 55378653983798834379209059)
                  ·
                    refine ⟨83067980975698251568813589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55378653983798834379209059 83067980975698251568813589)
                    ·
                      refine ⟨3893811608235855542288137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83067980975698251568813589 3893811608235855542288137)
                      ·
                        rfl

theorem cell23_7583171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_7583171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583171 prefixEnd_7583171 := by exact prefixLift 7583171
  have htrace : WordTrace (prefixWord ++ tailWord_7583171) baseStart_7583171 baseEnd_7583171 := by
    simpa [prefixWord, tailWord_7583171, baseEnd_7583171] using wordTrace_append hprefix tailTrace_7583171
  have hstable : (prefixWord ++ tailWord_7583171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583171).length < 2 ^ (prefixWord ++ tailWord_7583171).sum := by decide
  have hdescent : baseEnd_7583171 < baseStart_7583171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583225 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 3]
def baseStart_7583225 : Nat := 118140960795 + 7583225 * 2 ^ 59
def prefixEnd_7583225 : Nat := 4983230072969 + 3 ^ 40 * 7583225 * 2
def baseEnd_7583225 : Nat := 3893839336191198331012889

theorem tailTrace_7583225 : CollatzResearch.WordTrace tailWord_7583225 prefixEnd_7583225 3893839336191198331012889 := by
  unfold tailWord_7583225
  simp only [CollatzResearch.WordTrace]
  refine ⟨276582937952278411565999129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184388625301518941043999419 276582937952278411565999129)
  ·
    refine ⟨207437203464208808674499347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276582937952278411565999129 207437203464208808674499347)
    ·
      refine ⟨311155805196313213011749021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207437203464208808674499347 311155805196313213011749021)
      ·
        refine ⟨116683426948617454879405883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311155805196313213011749021 116683426948617454879405883)
        ·
          refine ⟨175025140422926182319108825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116683426948617454879405883 175025140422926182319108825)
          ·
            refine ⟨131268855317194636739331619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175025140422926182319108825 131268855317194636739331619)
            ·
              refine ⟨196903282975791955108997429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131268855317194636739331619 196903282975791955108997429)
              ·
                refine ⟨18459682778980495791468509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196903282975791955108997429 18459682778980495791468509)
                ·
                  refine ⟨6922381042117685921800691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18459682778980495791468509 6922381042117685921800691)
                  ·
                    refine ⟨10383571563176528882701037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6922381042117685921800691 10383571563176528882701037)
                    ·
                      refine ⟨3893839336191198331012889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10383571563176528882701037 3893839336191198331012889)
                      ·
                        rfl

theorem cell23_7583225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_7583225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583225 prefixEnd_7583225 := by exact prefixLift 7583225
  have htrace : WordTrace (prefixWord ++ tailWord_7583225) baseStart_7583225 baseEnd_7583225 := by
    simpa [prefixWord, tailWord_7583225, baseEnd_7583225] using wordTrace_append hprefix tailTrace_7583225
  have hstable : (prefixWord ++ tailWord_7583225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583225).length < 2 ^ (prefixWord ++ tailWord_7583225).sum := by decide
  have hdescent : baseEnd_7583225 < baseStart_7583225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583228 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_7583228 : Nat := 118140960795 + 7583228 * 2 ^ 59
def prefixEnd_7583228 : Nat := 4983230072969 + 3 ^ 40 * 7583228 * 2
def baseEnd_7583228 : Nat := 1297946958877720606425125

theorem tailTrace_7583228 : CollatzResearch.WordTrace tailWord_7583228 prefixEnd_7583228 1297946958877720606425125 := by
  unfold tailWord_7583228
  simp only [CollatzResearch.WordTrace]
  refine ⟨138291523685633771539179169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184388698247511695385572225 138291523685633771539179169)
  ·
    refine ⟨103718642764225328654384377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138291523685633771539179169 103718642764225328654384377)
    ·
      refine ⟨77788982073168996490788283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103718642764225328654384377 77788982073168996490788283)
      ·
        refine ⟨116683473109753494736182425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77788982073168996490788283 116683473109753494736182425)
        ·
          refine ⟨87512604832315121052136819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116683473109753494736182425 87512604832315121052136819)
          ·
            refine ⟨131268907248472681578205229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87512604832315121052136819 131268907248472681578205229)
            ·
              refine ⟨49225840218177255591826961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131268907248472681578205229 49225840218177255591826961)
              ·
                refine ⟨36919380163632941693870221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49225840218177255591826961 36919380163632941693870221)
                ·
                  refine ⟨13844767561362353135201333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36919380163632941693870221 13844767561362353135201333)
                  ·
                    refine ⟨1297946958877720606425125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13844767561362353135201333 1297946958877720606425125)
                    ·
                      rfl

theorem cell23_7583228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_7583228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583228 prefixEnd_7583228 := by exact prefixLift 7583228
  have htrace : WordTrace (prefixWord ++ tailWord_7583228) baseStart_7583228 baseEnd_7583228 := by
    simpa [prefixWord, tailWord_7583228, baseEnd_7583228] using wordTrace_append hprefix tailTrace_7583228
  have hstable : (prefixWord ++ tailWord_7583228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583228).length < 2 ^ (prefixWord ++ tailWord_7583228).sum := by decide
  have hdescent : baseEnd_7583228 < baseStart_7583228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583242 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_7583242 : Nat := 118140960795 + 7583242 * 2 ^ 59
def prefixEnd_7583242 : Nat := 4983230072969 + 3 ^ 40 * 7583242 * 2
def baseEnd_7583242 : Nat := 3893848065362324764500311

theorem tailTrace_7583242 : CollatzResearch.WordTrace tailWord_7583242 prefixEnd_7583242 3893848065362324764500311 := by
  unfold tailWord_7583242
  simp only [CollatzResearch.WordTrace]
  refine ⟨69145889498304205867341995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184389038662144548979578653 69145889498304205867341995)
  ·
    refine ⟨103718834247456308801012993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69145889498304205867341995 103718834247456308801012993)
    ·
      refine ⟨77789125685592231600759745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103718834247456308801012993 77789125685592231600759745)
      ·
        refine ⟨58341844264194173700569809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77789125685592231600759745 58341844264194173700569809)
        ·
          refine ⟨43756383198145630275427357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58341844264194173700569809 43756383198145630275427357)
          ·
            refine ⟨16408643699304611353285259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43756383198145630275427357 16408643699304611353285259)
            ·
              refine ⟨24612965548956917029927889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16408643699304611353285259 24612965548956917029927889)
              ·
                refine ⟨18459724161717687772445917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24612965548956917029927889 18459724161717687772445917)
                ·
                  refine ⟨6922396560644132914667219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18459724161717687772445917 6922396560644132914667219)
                  ·
                    refine ⟨10383594840966199372000829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6922396560644132914667219 10383594840966199372000829)
                    ·
                      refine ⟨3893848065362324764500311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10383594840966199372000829 3893848065362324764500311)
                      ·
                        rfl

theorem cell23_7583242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_7583242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583242 prefixEnd_7583242 := by exact prefixLift 7583242
  have htrace : WordTrace (prefixWord ++ tailWord_7583242) baseStart_7583242 baseEnd_7583242 := by
    simpa [prefixWord, tailWord_7583242, baseEnd_7583242] using wordTrace_append hprefix tailTrace_7583242
  have hstable : (prefixWord ++ tailWord_7583242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583242).length < 2 ^ (prefixWord ++ tailWord_7583242).sum := by decide
  have hdescent : baseEnd_7583242 < baseStart_7583242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583285 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_7583285 : Nat := 118140960795 + 7583285 * 2 ^ 59
def prefixEnd_7583285 : Nat := 4983230072969 + 3 ^ 40 * 7583285 * 2
def baseEnd_7583285 : Nat := 3893870145030468096262613

theorem tailTrace_7583285 : CollatzResearch.WordTrace tailWord_7583285 prefixEnd_7583285 3893870145030468096262613 := by
  unfold tailWord_7583285
  simp only [CollatzResearch.WordTrace]
  refine ⟨276585126332061041813183309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184390084221374027875455539 276585126332061041813183309)
  ·
    refine ⟨103719422374522890679943741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276585126332061041813183309 103719422374522890679943741)
    ·
      refine ⟨38894783390446084004978903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103719422374522890679943741 38894783390446084004978903)
      ·
        refine ⟨58342175085669126007468355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38894783390446084004978903 58342175085669126007468355)
        ·
          refine ⟨87513262628503689011202533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58342175085669126007468355 87513262628503689011202533)
          ·
            refine ⟨16408736742844441689600475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87513262628503689011202533 16408736742844441689600475)
            ·
              refine ⟨24613105114266662534400713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16408736742844441689600475 24613105114266662534400713)
              ·
                refine ⟨18459828835699996900800535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24613105114266662534400713 18459828835699996900800535)
                ·
                  refine ⟨27689743253549995351200803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18459828835699996900800535 27689743253549995351200803)
                  ·
                    refine ⟨41534614880324993026801205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27689743253549995351200803 41534614880324993026801205)
                    ·
                      refine ⟨3893870145030468096262613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41534614880324993026801205 3893870145030468096262613)
                      ·
                        rfl

theorem cell23_7583285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_7583285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583285 prefixEnd_7583285 := by exact prefixLift 7583285
  have htrace : WordTrace (prefixWord ++ tailWord_7583285) baseStart_7583285 baseEnd_7583285 := by
    simpa [prefixWord, tailWord_7583285, baseEnd_7583285] using wordTrace_append hprefix tailTrace_7583285
  have hstable : (prefixWord ++ tailWord_7583285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583285).length < 2 ^ (prefixWord ++ tailWord_7583285).sum := by decide
  have hdescent : baseEnd_7583285 < baseStart_7583285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583292 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_7583292 : Nat := 118140960795 + 7583292 * 2 ^ 59
def prefixEnd_7583292 : Nat := 4983230072969 + 3 ^ 40 * 7583292 * 2
def baseEnd_7583292 : Nat := 1297957913131683189625027

theorem tailTrace_7583292 : CollatzResearch.WordTrace tailWord_7583292 prefixEnd_7583292 1297957913131683189625027 := by
  unfold tailWord_7583292
  simp only [CollatzResearch.WordTrace]
  refine ⟨138292690821517841004344065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184390254428690454672458753 138292690821517841004344065)
  ·
    refine ⟨103719518116138380753258049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138292690821517841004344065 103719518116138380753258049)
    ·
      refine ⟨77789638587103785564943537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103719518116138380753258049 77789638587103785564943537)
      ·
        refine ⟨58342228940327839173707653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77789638587103785564943537 58342228940327839173707653)
        ·
          refine ⟨10939167926311469845070185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58342228940327839173707653 10939167926311469845070185)
          ·
            refine ⟨8204375944733602383802639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10939167926311469845070185 8204375944733602383802639)
            ·
              refine ⟨12306563917100403575703959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204375944733602383802639 12306563917100403575703959)
              ·
                refine ⟨18459845875650605363555939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306563917100403575703959 18459845875650605363555939)
                ·
                  refine ⟨27689768813475908045333909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18459845875650605363555939 27689768813475908045333909)
                  ·
                    refine ⟨1297957913131683189625027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27689768813475908045333909 1297957913131683189625027)
                    ·
                      rfl

theorem cell23_7583292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_7583292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583292 prefixEnd_7583292 := by exact prefixLift 7583292
  have htrace : WordTrace (prefixWord ++ tailWord_7583292) baseStart_7583292 baseEnd_7583292 := by
    simpa [prefixWord, tailWord_7583292, baseEnd_7583292] using wordTrace_append hprefix tailTrace_7583292
  have hstable : (prefixWord ++ tailWord_7583292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583292).length < 2 ^ (prefixWord ++ tailWord_7583292).sum := by decide
  have hdescent : baseEnd_7583292 < baseStart_7583292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7583295 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_7583295 : Nat := 118140960795 + 7583295 * 2 ^ 59
def prefixEnd_7583295 : Nat := 4983230072969 + 3 ^ 40 * 7583295 * 2
def baseEnd_7583295 : Nat := 3893875279837013057137567

theorem tailTrace_7583295 : CollatzResearch.WordTrace tailWord_7583295 prefixEnd_7583295 3893875279837013057137567 := by
  unfold tailWord_7583295
  simp only [CollatzResearch.WordTrace]
  refine ⟨276585491062024813521047339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184390327374683209014031559 276585491062024813521047339)
  ·
    refine ⟨414878236593037220281571009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276585491062024813521047339 414878236593037220281571009)
    ·
      refine ⟨311158677444777915211178257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414878236593037220281571009 311158677444777915211178257)
      ·
        refine ⟨233369008083583436408383693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311158677444777915211178257 233369008083583436408383693)
        ·
          refine ⟨87513378031343788653143885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233369008083583436408383693 87513378031343788653143885)
          ·
            refine ⟨32817516761753920744928957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87513378031343788653143885 32817516761753920744928957)
            ·
              refine ⟨12306568785657720279348359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32817516761753920744928957 12306568785657720279348359)
              ·
                refine ⟨18459853178486580419022539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306568785657720279348359 18459853178486580419022539)
                ·
                  refine ⟨27689779767729870628533809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18459853178486580419022539 27689779767729870628533809)
                  ·
                    refine ⟨20767334825797402971400357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27689779767729870628533809 20767334825797402971400357)
                    ·
                      refine ⟨3893875279837013057137567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20767334825797402971400357 3893875279837013057137567)
                      ·
                        rfl

theorem cell23_7583295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_7583295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7583295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7583295 prefixEnd_7583295 := by exact prefixLift 7583295
  have htrace : WordTrace (prefixWord ++ tailWord_7583295) baseStart_7583295 baseEnd_7583295 := by
    simpa [prefixWord, tailWord_7583295, baseEnd_7583295] using wordTrace_append hprefix tailTrace_7583295
  have hstable : (prefixWord ++ tailWord_7583295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7583295).length < 2 ^ (prefixWord ++ tailWord_7583295).sum := by decide
  have hdescent : baseEnd_7583295 < baseStart_7583295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7583295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
