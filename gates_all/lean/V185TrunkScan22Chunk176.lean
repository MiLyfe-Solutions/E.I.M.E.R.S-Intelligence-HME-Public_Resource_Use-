import V185TrunkScan22Chunk175

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1570558 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1570558 : Nat := 118140960795 + 1570558 * 2 ^ 59
def prefixEnd_1570558 : Nat := 4983230072969 + 3 ^ 40 * 1570558 * 2
def baseEnd_1570558 : Nat := 537634099842780945534761

theorem tailTrace_1570558 : CollatzResearch.WordTrace tailWord_1570558 prefixEnd_1570558 537634099842780945534761 := by
  unfold tailWord_1570558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160369530518008849579041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38188637496096047197754885 7160369530518008849579041)
  ·
    refine ⟨5370277147888506637184281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7160369530518008849579041 5370277147888506637184281)
    ·
      refine ⟨4027707860916379977888211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5370277147888506637184281 4027707860916379977888211)
      ·
        refine ⟨6041561791374569966832317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027707860916379977888211 6041561791374569966832317)
        ·
          refine ⟨2265585671765463737562119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6041561791374569966832317 2265585671765463737562119)
          ·
            refine ⟨3398378507648195606343179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265585671765463737562119 3398378507648195606343179)
            ·
              refine ⟨5097567761472293409514769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398378507648195606343179 5097567761472293409514769)
              ·
                refine ⟨3823175821104220057136077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097567761472293409514769 3823175821104220057136077)
                ·
                  refine ⟨1433690932914082521426029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3823175821104220057136077 1433690932914082521426029)
                  ·
                    refine ⟨537634099842780945534761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433690932914082521426029 537634099842780945534761)
                    ·
                      rfl

theorem cell22_1570558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1570558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570558 prefixEnd_1570558 := by exact prefixLift 1570558
  have htrace : WordTrace (prefixWord ++ tailWord_1570558) baseStart_1570558 baseEnd_1570558 := by
    simpa [prefixWord, tailWord_1570558, baseEnd_1570558] using wordTrace_append hprefix tailTrace_1570558
  have hstable : (prefixWord ++ tailWord_1570558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570558).length < 2 ^ (prefixWord ++ tailWord_1570558).sum := by decide
  have hdescent : baseEnd_1570558 < baseStart_1570558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570629 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_1570629 : Nat := 118140960795 + 1570629 * 2 ^ 59
def prefixEnd_1570629 : Nat := 4983230072969 + 3 ^ 40 * 1570629 * 2
def baseEnd_1570629 : Nat := 537658404593760427009543

theorem tailTrace_1570629 : CollatzResearch.WordTrace tailWord_1570629 prefixEnd_1570629 537658404593760427009543 := by
  unfold tailWord_1570629
  simp only [CollatzResearch.WordTrace]
  refine ⟨57285545826886849922466941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38190363884591233281644627 57285545826886849922466941)
  ·
    refine ⟨21482079685082568720925103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57285545826886849922466941 21482079685082568720925103)
    ·
      refine ⟨32223119527623853081387655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21482079685082568720925103 32223119527623853081387655)
      ·
        refine ⟨48334679291435779622081483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32223119527623853081387655 48334679291435779622081483)
        ·
          refine ⟨72502018937153669433122225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48334679291435779622081483 72502018937153669433122225)
          ·
            refine ⟨54376514202865252074841669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72502018937153669433122225 54376514202865252074841669)
            ·
              refine ⟨10195596413037234764032813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54376514202865252074841669 10195596413037234764032813)
              ·
                refine ⟨3823348654888963036512305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10195596413037234764032813 3823348654888963036512305)
                ·
                  refine ⟨2867511491166722277384229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823348654888963036512305 2867511491166722277384229)
                  ·
                    refine ⟨537658404593760427009543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2867511491166722277384229 537658404593760427009543)
                    ·
                      rfl

theorem cell22_1570629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_1570629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570629 prefixEnd_1570629 := by exact prefixLift 1570629
  have htrace : WordTrace (prefixWord ++ tailWord_1570629) baseStart_1570629 baseEnd_1570629 := by
    simpa [prefixWord, tailWord_1570629, baseEnd_1570629] using wordTrace_append hprefix tailTrace_1570629
  have hstable : (prefixWord ++ tailWord_1570629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570629).length < 2 ^ (prefixWord ++ tailWord_1570629).sum := by decide
  have hdescent : baseEnd_1570629 < baseStart_1570629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570644 : List Nat := [2, 4, 1, 1, 3, 1, 10]
def baseStart_1570644 : Nat := 118140960795 + 1570644 * 2 ^ 59
def prefixEnd_1570644 : Nat := 4983230072969 + 3 ^ 40 * 1570644 * 2
def baseEnd_1570644 : Nat := 19913464422233532884611

theorem tailTrace_1570644 : CollatzResearch.WordTrace tailWord_1570644 prefixEnd_1570644 19913464422233532884611 := by
  unfold tailWord_1570644
  simp only [CollatzResearch.WordTrace]
  refine ⟨28643046460916253742131493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38190728614555004989508657 28643046460916253742131493)
  ·
    refine ⟨5370571211421797576649655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28643046460916253742131493 5370571211421797576649655)
    ·
      refine ⟨8055856817132696364974483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5370571211421797576649655 8055856817132696364974483)
      ·
        refine ⟨12083785225699044547461725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055856817132696364974483 12083785225699044547461725)
        ·
          refine ⟨4531419459637141705298147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12083785225699044547461725 4531419459637141705298147)
          ·
            refine ⟨6797129189455712557947221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531419459637141705298147 6797129189455712557947221)
            ·
              refine ⟨19913464422233532884611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6797129189455712557947221 19913464422233532884611)
              ·
                rfl

theorem cell22_1570644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 10].length) (baseStart_1570644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570644 prefixEnd_1570644 := by exact prefixLift 1570644
  have htrace : WordTrace (prefixWord ++ tailWord_1570644) baseStart_1570644 baseEnd_1570644 := by
    simpa [prefixWord, tailWord_1570644, baseEnd_1570644] using wordTrace_append hprefix tailTrace_1570644
  have hstable : (prefixWord ++ tailWord_1570644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570644).length < 2 ^ (prefixWord ++ tailWord_1570644).sum := by decide
  have hdescent : baseEnd_1570644 < baseStart_1570644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570693 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_1570693 : Nat := 118140960795 + 1570693 * 2 ^ 59
def prefixEnd_1570693 : Nat := 4983230072969 + 3 ^ 40 * 1570693 * 2
def baseEnd_1570693 : Nat := 537680313101685593409347

theorem tailTrace_1570693 : CollatzResearch.WordTrace tailWord_1570693 prefixEnd_1570693 537680313101685593409347 := by
  unfold tailWord_1570693
  simp only [CollatzResearch.WordTrace]
  refine ⟨57287880098654988852796733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38191920065769992568531155 57287880098654988852796733)
  ·
    refine ⟨21482955036995620819798775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57287880098654988852796733 21482955036995620819798775)
    ·
      refine ⟨32224432555493431229698163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21482955036995620819798775 32224432555493431229698163)
      ·
        refine ⟨48336648833240146844547245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32224432555493431229698163 48336648833240146844547245)
        ·
          refine ⟨18126243312465055066705217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48336648833240146844547245 18126243312465055066705217)
          ·
            refine ⟨13594682484348791300028913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18126243312465055066705217 13594682484348791300028913)
            ·
              refine ⟨10196011863261593475021685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13594682484348791300028913 10196011863261593475021685)
              ·
                refine ⟨955876112180774388283283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10196011863261593475021685 955876112180774388283283)
                ·
                  refine ⟨1433814168271161582424925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955876112180774388283283 1433814168271161582424925)
                  ·
                    refine ⟨537680313101685593409347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433814168271161582424925 537680313101685593409347)
                    ·
                      rfl

theorem cell22_1570693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_1570693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570693 prefixEnd_1570693 := by exact prefixLift 1570693
  have htrace : WordTrace (prefixWord ++ tailWord_1570693) baseStart_1570693 baseEnd_1570693 := by
    simpa [prefixWord, tailWord_1570693, baseEnd_1570693] using wordTrace_append hprefix tailTrace_1570693
  have hstable : (prefixWord ++ tailWord_1570693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570693).length < 2 ^ (prefixWord ++ tailWord_1570693).sum := by decide
  have hdescent : baseEnd_1570693 < baseStart_1570693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570783 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 1, 5]
def baseStart_1570783 : Nat := 118140960795 + 1570783 * 2 ^ 59
def prefixEnd_1570783 : Nat := 4983230072969 + 3 ^ 40 * 1570783 * 2
def baseEnd_1570783 : Nat := 537711121940955358659071

theorem tailTrace_1570783 : CollatzResearch.WordTrace tailWord_1570783 prefixEnd_1570783 537711121940955358659071 := by
  unfold tailWord_1570783
  simp only [CollatzResearch.WordTrace]
  refine ⟨57291162668328934223573003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38194108445552622815715335 57291162668328934223573003)
  ·
    refine ⟨85936744002493401335359505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57291162668328934223573003 85936744002493401335359505)
    ·
      refine ⟨64452558001870051001519629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85936744002493401335359505 64452558001870051001519629)
      ·
        refine ⟨24169709250701269125569861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64452558001870051001519629 24169709250701269125569861)
        ·
          refine ⟨4531820484506487961044349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24169709250701269125569861 4531820484506487961044349)
          ·
            refine ⟨1699432681689932985391631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4531820484506487961044349 1699432681689932985391631)
            ·
              refine ⟨2549149022534899478087447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699432681689932985391631 2549149022534899478087447)
              ·
                refine ⟨3823723533802349217131171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549149022534899478087447 3823723533802349217131171)
                ·
                  refine ⟨5735585300703523825696757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823723533802349217131171 5735585300703523825696757)
                  ·
                    refine ⟨537711121940955358659071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5735585300703523825696757 537711121940955358659071)
                    ·
                      rfl

theorem cell22_1570783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_1570783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570783 prefixEnd_1570783 := by exact prefixLift 1570783
  have htrace : WordTrace (prefixWord ++ tailWord_1570783) baseStart_1570783 baseEnd_1570783 := by
    simpa [prefixWord, tailWord_1570783, baseEnd_1570783] using wordTrace_append hprefix tailTrace_1570783
  have hstable : (prefixWord ++ tailWord_1570783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570783).length < 2 ^ (prefixWord ++ tailWord_1570783).sum := by decide
  have hdescent : baseEnd_1570783 < baseStart_1570783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570811 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 5, 3]
def baseStart_1570811 : Nat := 118140960795 + 1570811 * 2 ^ 59
def prefixEnd_1570811 : Nat := 4983230072969 + 3 ^ 40 * 1570811 * 2
def baseEnd_1570811 : Nat := 537720706913172618958985

theorem tailTrace_1570811 : CollatzResearch.WordTrace tailWord_1570811 prefixEnd_1570811 537720706913172618958985 := by
  unfold tailWord_1570811
  simp only [CollatzResearch.WordTrace]
  refine ⟨57292183912227495005592287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38194789274818330003728191 57292183912227495005592287)
  ·
    refine ⟨85938275868341242508388431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57292183912227495005592287 85938275868341242508388431)
    ·
      refine ⟨128907413802511863762582647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85938275868341242508388431 128907413802511863762582647)
      ·
        refine ⟨193361120703767795643873971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128907413802511863762582647 193361120703767795643873971)
        ·
          refine ⟨290041681055651693465810957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193361120703767795643873971 290041681055651693465810957)
          ·
            refine ⟨108765630395869385049679109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290041681055651693465810957 108765630395869385049679109)
            ·
              refine ⟨20393555699225509696814833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108765630395869385049679109 20393555699225509696814833)
              ·
                refine ⟨15295166774419132272611125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20393555699225509696814833 15295166774419132272611125)
                ·
                  refine ⟨1433921885101793650557293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15295166774419132272611125 1433921885101793650557293)
                  ·
                    refine ⟨537720706913172618958985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1433921885101793650557293 537720706913172618958985)
                    ·
                      rfl

theorem cell22_1570811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 3].length) (baseStart_1570811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570811 prefixEnd_1570811 := by exact prefixLift 1570811
  have htrace : WordTrace (prefixWord ++ tailWord_1570811) baseStart_1570811 baseEnd_1570811 := by
    simpa [prefixWord, tailWord_1570811, baseEnd_1570811] using wordTrace_append hprefix tailTrace_1570811
  have hstable : (prefixWord ++ tailWord_1570811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570811).length < 2 ^ (prefixWord ++ tailWord_1570811).sum := by decide
  have hdescent : baseEnd_1570811 < baseStart_1570811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570935 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 2, 3]
def baseStart_1570935 : Nat := 118140960795 + 1570935 * 2 ^ 59
def prefixEnd_1570935 : Nat := 4983230072969 + 3 ^ 40 * 1570935 * 2
def baseEnd_1570935 : Nat := 537763154647277628858605

theorem tailTrace_1570935 : CollatzResearch.WordTrace tailWord_1570935 prefixEnd_1570935 537763154647277628858605 := by
  unfold tailWord_1570935
  simp only [CollatzResearch.WordTrace]
  refine ⟨57296706563778264183106259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38197804375852176122070839 57296706563778264183106259)
  ·
    refine ⟨85945059845667396274659389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57296706563778264183106259 85945059845667396274659389)
    ·
      refine ⟨32229397442125273602997271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85945059845667396274659389 32229397442125273602997271)
      ·
        refine ⟨48344096163187910404495907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32229397442125273602997271 48344096163187910404495907)
        ·
          refine ⟨72516144244781865606743861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48344096163187910404495907 72516144244781865606743861)
          ·
            refine ⟨6798388522948299900632237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72516144244781865606743861 6798388522948299900632237)
            ·
              refine ⟨2549395696105612462737089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6798388522948299900632237 2549395696105612462737089)
              ·
                refine ⟨1912046772079209347052817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549395696105612462737089 1912046772079209347052817)
                ·
                  refine ⟨1434035079059407010289613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1912046772079209347052817 1434035079059407010289613)
                  ·
                    refine ⟨537763154647277628858605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434035079059407010289613 537763154647277628858605)
                    ·
                      rfl

theorem cell22_1570935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_1570935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1570935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1570935 prefixEnd_1570935 := by exact prefixLift 1570935
  have htrace : WordTrace (prefixWord ++ tailWord_1570935) baseStart_1570935 baseEnd_1570935 := by
    simpa [prefixWord, tailWord_1570935, baseEnd_1570935] using wordTrace_append hprefix tailTrace_1570935
  have hstable : (prefixWord ++ tailWord_1570935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570935).length < 2 ^ (prefixWord ++ tailWord_1570935).sum := by decide
  have hdescent : baseEnd_1570935 < baseStart_1570935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571023 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 3, 4]
def baseStart_1571023 : Nat := 118140960795 + 1571023 * 2 ^ 59
def prefixEnd_1571023 : Nat := 4983230072969 + 3 ^ 40 * 1571023 * 2
def baseEnd_1571023 : Nat := 537793278845674732658335

theorem tailTrace_1571023 : CollatzResearch.WordTrace tailWord_1571023 prefixEnd_1571023 537793278845674732658335 := by
  unfold tailWord_1571023
  simp only [CollatzResearch.WordTrace]
  refine ⟨57299916187459455212309723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38199944124972970141539815 57299916187459455212309723)
  ·
    refine ⟨85949874281189182818464585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57299916187459455212309723 85949874281189182818464585)
    ·
      refine ⟨64462405710891887113848439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85949874281189182818464585 64462405710891887113848439)
      ·
        refine ⟨96693608566337830670772659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64462405710891887113848439 96693608566337830670772659)
        ·
          refine ⟨145040412849506746006158989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96693608566337830670772659 145040412849506746006158989)
          ·
            refine ⟨54390154818565029752309621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145040412849506746006158989 54390154818565029752309621)
            ·
              refine ⟨5099077014240471539279027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54390154818565029752309621 5099077014240471539279027)
              ·
                refine ⟨7648615521360707308918541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099077014240471539279027 7648615521360707308918541)
                ·
                  refine ⟨2868230820510265240844453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7648615521360707308918541 2868230820510265240844453)
                  ·
                    refine ⟨537793278845674732658335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868230820510265240844453 537793278845674732658335)
                    ·
                      rfl

theorem cell22_1571023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_1571023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571023 prefixEnd_1571023 := by exact prefixLift 1571023
  have htrace : WordTrace (prefixWord ++ tailWord_1571023) baseStart_1571023 baseEnd_1571023 := by
    simpa [prefixWord, tailWord_1571023, baseEnd_1571023] using wordTrace_append hprefix tailTrace_1571023
  have hstable : (prefixWord ++ tailWord_1571023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571023).length < 2 ^ (prefixWord ++ tailWord_1571023).sum := by decide
  have hdescent : baseEnd_1571023 < baseStart_1571023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571104 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_1571104 : Nat := 118140960795 + 1571104 * 2 ^ 59
def prefixEnd_1571104 : Nat := 4983230072969 + 3 ^ 40 * 1571104 * 2
def baseEnd_1571104 : Nat := 537821006801017521383087

theorem tailTrace_1571104 : CollatzResearch.WordTrace tailWord_1571104 prefixEnd_1571104 537821006801017521383087 := by
  unfold tailWord_1571104
  simp only [CollatzResearch.WordTrace]
  refine ⟨28651435250083003023004183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38201913666777337364005577 28651435250083003023004183)
  ·
    refine ⟨42977152875124504534506275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28651435250083003023004183 42977152875124504534506275)
    ·
      refine ⟨64465729312686756801759413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42977152875124504534506275 64465729312686756801759413)
      ·
        refine ⟨6043662123064383450164945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64465729312686756801759413 6043662123064383450164945)
        ·
          refine ⟨4532746592298287587623709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6043662123064383450164945 4532746592298287587623709)
          ·
            refine ⟨1699779972111857845358891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4532746592298287587623709 1699779972111857845358891)
            ·
              refine ⟨2549669958167786768038337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699779972111857845358891 2549669958167786768038337)
              ·
                refine ⟨1912252468625840076028753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549669958167786768038337 1912252468625840076028753)
                ·
                  refine ⟨1434189351469380057021565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1912252468625840076028753 1434189351469380057021565)
                  ·
                    refine ⟨537821006801017521383087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434189351469380057021565 537821006801017521383087)
                    ·
                      rfl

theorem cell22_1571104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_1571104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571104 prefixEnd_1571104 := by exact prefixLift 1571104
  have htrace : WordTrace (prefixWord ++ tailWord_1571104) baseStart_1571104 baseEnd_1571104 := by
    simpa [prefixWord, tailWord_1571104, baseEnd_1571104] using wordTrace_append hprefix tailTrace_1571104
  have hstable : (prefixWord ++ tailWord_1571104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571104).length < 2 ^ (prefixWord ++ tailWord_1571104).sum := by decide
  have hdescent : baseEnd_1571104 < baseStart_1571104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571207 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 4]
def baseStart_1571207 : Nat := 118140960795 + 1571207 * 2 ^ 59
def prefixEnd_1571207 : Nat := 4983230072969 + 3 ^ 40 * 1571207 * 2
def baseEnd_1571207 : Nat := 179285421935319862019257

theorem tailTrace_1571207 : CollatzResearch.WordTrace tailWord_1571207 prefixEnd_1571207 179285421935319862019257 := by
  unfold tailWord_1571207
  simp only [CollatzResearch.WordTrace]
  refine ⟨57306627218792854637007875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38204418145861903091338583 57306627218792854637007875)
  ·
    refine ⟨85959940828189281955511813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57306627218792854637007875 85959940828189281955511813)
    ·
      refine ⟨16117488905285490366658465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85959940828189281955511813 16117488905285490366658465)
      ·
        refine ⟨12088116678964117774993849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16117488905285490366658465 12088116678964117774993849)
        ·
          refine ⟨9066087509223088331245387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12088116678964117774993849 9066087509223088331245387)
          ·
            refine ⟨13599131263834632496868081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066087509223088331245387 13599131263834632496868081)
            ·
              refine ⟨10199348447875974372651061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13599131263834632496868081 10199348447875974372651061)
              ·
                refine ⟨956188916988372597436037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10199348447875974372651061 956188916988372597436037)
                ·
                  refine ⟨179285421935319862019257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 956188916988372597436037 179285421935319862019257)
                  ·
                    rfl

theorem cell22_1571207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 4].length) (baseStart_1571207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571207 prefixEnd_1571207 := by exact prefixLift 1571207
  have htrace : WordTrace (prefixWord ++ tailWord_1571207) baseStart_1571207 baseEnd_1571207 := by
    simpa [prefixWord, tailWord_1571207, baseEnd_1571207] using wordTrace_append hprefix tailTrace_1571207
  have hstable : (prefixWord ++ tailWord_1571207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571207).length < 2 ^ (prefixWord ++ tailWord_1571207).sum := by decide
  have hdescent : baseEnd_1571207 < baseStart_1571207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571209 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 1, 4]
def baseStart_1571209 : Nat := 118140960795 + 1571209 * 2 ^ 59
def prefixEnd_1571209 : Nat := 4983230072969 + 3 ^ 40 * 1571209 * 2
def baseEnd_1571209 : Nat := 537856950446832247507765

theorem tailTrace_1571209 : CollatzResearch.WordTrace tailWord_1571209 prefixEnd_1571209 537856950446832247507765 := by
  unfold tailWord_1571209
  simp only [CollatzResearch.WordTrace]
  refine ⟨57306700164785608978580681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38204466776523739319053787 57306700164785608978580681)
  ·
    refine ⟨42980025123589206733935511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57306700164785608978580681 42980025123589206733935511)
    ·
      refine ⟨64470037685383810100903267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42980025123589206733935511 64470037685383810100903267)
      ·
        refine ⟨96705056528075715151354901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64470037685383810100903267 96705056528075715151354901)
        ·
          refine ⟨4533049524753549147719761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96705056528075715151354901 4533049524753549147719761)
          ·
            refine ⟨3399787143565161860789821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4533049524753549147719761 3399787143565161860789821)
            ·
              refine ⟨1274920178836935697796183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3399787143565161860789821 1274920178836935697796183)
              ·
                refine ⟨1912380268255403546694275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274920178836935697796183 1912380268255403546694275)
                ·
                  refine ⟨2868570402383105320041413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912380268255403546694275 2868570402383105320041413)
                  ·
                    refine ⟨537856950446832247507765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868570402383105320041413 537856950446832247507765)
                    ·
                      rfl

theorem cell22_1571209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_1571209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571209 prefixEnd_1571209 := by exact prefixLift 1571209
  have htrace : WordTrace (prefixWord ++ tailWord_1571209) baseStart_1571209 baseEnd_1571209 := by
    simpa [prefixWord, tailWord_1571209, baseEnd_1571209] using wordTrace_append hprefix tailTrace_1571209
  have hstable : (prefixWord ++ tailWord_1571209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571209).length < 2 ^ (prefixWord ++ tailWord_1571209).sum := by decide
  have hdescent : baseEnd_1571209 < baseStart_1571209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571224 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 4]
def baseStart_1571224 : Nat := 118140960795 + 1571224 * 2 ^ 59
def prefixEnd_1571224 : Nat := 4983230072969 + 3 ^ 40 * 1571224 * 2
def baseEnd_1571224 : Nat := 179287361751125736127573

theorem tailTrace_1571224 : CollatzResearch.WordTrace tailWord_1571224 prefixEnd_1571224 179287361751125736127573 := by
  unfold tailWord_1571224
  simp only [CollatzResearch.WordTrace]
  refine ⟨28653623629865633270188363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38204831506487511026917817 28653623629865633270188363)
  ·
    refine ⟨42980435444798449905282545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28653623629865633270188363 42980435444798449905282545)
    ·
      refine ⟨32235326583598837428961909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42980435444798449905282545 32235326583598837428961909)
      ·
        refine ⟨3022061867212391008965179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32235326583598837428961909 3022061867212391008965179)
        ·
          refine ⟨4533092800818586513447769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022061867212391008965179 4533092800818586513447769)
          ·
            refine ⟨3399819600613939885085827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4533092800818586513447769 3399819600613939885085827)
            ·
              refine ⟨5099729400920909827628741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399819600613939885085827 5099729400920909827628741)
              ·
                refine ⟨956199262672670592680389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5099729400920909827628741 956199262672670592680389)
                ·
                  refine ⟨179287361751125736127573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 956199262672670592680389 179287361751125736127573)
                  ·
                    rfl

theorem cell22_1571224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_1571224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571224 prefixEnd_1571224 := by exact prefixLift 1571224
  have htrace : WordTrace (prefixWord ++ tailWord_1571224) baseStart_1571224 baseEnd_1571224 := by
    simpa [prefixWord, tailWord_1571224, baseEnd_1571224] using wordTrace_append hprefix tailTrace_1571224
  have hstable : (prefixWord ++ tailWord_1571224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571224).length < 2 ^ (prefixWord ++ tailWord_1571224).sum := by decide
  have hdescent : baseEnd_1571224 < baseStart_1571224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571235 : List Nat := [1, 1, 1, 4, 1, 4, 3, 7]
def baseStart_1571235 : Nat := 118140960795 + 1571235 * 2 ^ 59
def prefixEnd_1571235 : Nat := 4983230072969 + 3 ^ 40 * 1571235 * 2
def baseEnd_1571235 : Nat := 59762872308686316261965

theorem tailTrace_1571235 : CollatzResearch.WordTrace tailWord_1571235 prefixEnd_1571235 59762872308686316261965 := by
  unfold tailWord_1571235
  simp only [CollatzResearch.WordTrace]
  refine ⟨57307648462691415419027159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38205098975127610279351439 57307648462691415419027159)
  ·
    refine ⟨85961472694037123128540739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57307648462691415419027159 85961472694037123128540739)
    ·
      refine ⟨128942209041055684692811109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85961472694037123128540739 128942209041055684692811109)
      ·
        refine ⟨24176664195197940879902083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128942209041055684692811109 24176664195197940879902083)
        ·
          refine ⟨36264996292796911319853125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24176664195197940879902083 36264996292796911319853125)
          ·
            refine ⟨6799686804899420872472461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36264996292796911319853125 6799686804899420872472461)
            ·
              refine ⟨2549882551837282827177173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6799686804899420872472461 2549882551837282827177173)
              ·
                refine ⟨59762872308686316261965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2549882551837282827177173 59762872308686316261965)
                ·
                  rfl

theorem cell22_1571235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 7].length) (baseStart_1571235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571235 prefixEnd_1571235 := by exact prefixLift 1571235
  have htrace : WordTrace (prefixWord ++ tailWord_1571235) baseStart_1571235 baseEnd_1571235 := by
    simpa [prefixWord, tailWord_1571235, baseEnd_1571235] using wordTrace_append hprefix tailTrace_1571235
  have hstable : (prefixWord ++ tailWord_1571235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571235).length < 2 ^ (prefixWord ++ tailWord_1571235).sum := by decide
  have hdescent : baseEnd_1571235 < baseStart_1571235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571239 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1571239 : Nat := 118140960795 + 1571239 * 2 ^ 59
def prefixEnd_1571239 : Nat := 4983230072969 + 3 ^ 40 * 1571239 * 2
def baseEnd_1571239 : Nat := 537867220059922169257673

theorem tailTrace_1571239 : CollatzResearch.WordTrace tailWord_1571239 prefixEnd_1571239 537867220059922169257673 := by
  unfold tailWord_1571239
  simp only [CollatzResearch.WordTrace]
  refine ⟨57307794354676924102172771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38205196236451282734781847 57307794354676924102172771)
  ·
    refine ⟨85961691532015386153259157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57307794354676924102172771 85961691532015386153259157)
    ·
      refine ⟨4029454290563221225934023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85961691532015386153259157 4029454290563221225934023)
      ·
        refine ⟨6044181435844831838901035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029454290563221225934023 6044181435844831838901035)
        ·
          refine ⟨9066272153767247758351553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044181435844831838901035 9066272153767247758351553)
          ·
            refine ⟨6799704115325435818763665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9066272153767247758351553 6799704115325435818763665)
            ·
              refine ⟨5099778086494076864072749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799704115325435818763665 5099778086494076864072749)
              ·
                refine ⟨1912416782435278824027281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5099778086494076864072749 1912416782435278824027281)
                ·
                  refine ⟨1434312586826459118020461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1912416782435278824027281 1434312586826459118020461)
                  ·
                    refine ⟨537867220059922169257673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434312586826459118020461 537867220059922169257673)
                    ·
                      rfl

theorem cell22_1571239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1571239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571239 prefixEnd_1571239 := by exact prefixLift 1571239
  have htrace : WordTrace (prefixWord ++ tailWord_1571239) baseStart_1571239 baseEnd_1571239 := by
    simpa [prefixWord, tailWord_1571239, baseEnd_1571239] using wordTrace_append hprefix tailTrace_1571239
  have hstable : (prefixWord ++ tailWord_1571239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571239).length < 2 ^ (prefixWord ++ tailWord_1571239).sum := by decide
  have hdescent : baseEnd_1571239 < baseStart_1571239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571284 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1571284 : Nat := 118140960795 + 1571284 * 2 ^ 59
def prefixEnd_1571284 : Nat := 4983230072969 + 3 ^ 40 * 1571284 * 2
def baseEnd_1571284 : Nat := 537882624479557051882535

theorem tailTrace_1571284 : CollatzResearch.WordTrace tailWord_1571284 prefixEnd_1571284 537882624479557051882535 := by
  unfold tailWord_1571284
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654717819756948393780453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38206290426342597858373937 28654717819756948393780453)
  ·
    refine ⟨5372759591204427823833835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28654717819756948393780453 5372759591204427823833835)
    ·
      refine ⟨8059139386806641735750753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372759591204427823833835 8059139386806641735750753)
      ·
        refine ⟨6044354540104981301813065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8059139386806641735750753 6044354540104981301813065)
        ·
          refine ⟨4533265905078735976359799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6044354540104981301813065 4533265905078735976359799)
          ·
            refine ⟨6799898857618103964539699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533265905078735976359799 6799898857618103964539699)
            ·
              refine ⟨10199848286427155946809549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799898857618103964539699 10199848286427155946809549)
              ·
                refine ⟨3824943107410183480053581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10199848286427155946809549 3824943107410183480053581)
                ·
                  refine ⟨1434353665278818805020093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3824943107410183480053581 1434353665278818805020093)
                  ·
                    refine ⟨537882624479557051882535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434353665278818805020093 537882624479557051882535)
                    ·
                      rfl

theorem cell22_1571284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1571284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571284 prefixEnd_1571284 := by exact prefixLift 1571284
  have htrace : WordTrace (prefixWord ++ tailWord_1571284) baseStart_1571284 baseEnd_1571284 := by
    simpa [prefixWord, tailWord_1571284, baseEnd_1571284] using wordTrace_append hprefix tailTrace_1571284
  have hstable : (prefixWord ++ tailWord_1571284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571284).length < 2 ^ (prefixWord ++ tailWord_1571284).sum := by decide
  have hdescent : baseEnd_1571284 < baseStart_1571284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571327 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 1, 4]
def baseStart_1571327 : Nat := 118140960795 + 1571327 * 2 ^ 59
def prefixEnd_1571327 : Nat := 4983230072969 + 3 ^ 40 * 1571327 * 2
def baseEnd_1571327 : Nat := 537897344258319273057403

theorem tailTrace_1571327 : CollatzResearch.WordTrace tailWord_1571327 prefixEnd_1571327 537897344258319273057403 := by
  unfold tailWord_1571327
  simp only [CollatzResearch.WordTrace]
  refine ⟨57311003978358115131376235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38207335985572076754250823 57311003978358115131376235)
  ·
    refine ⟨85966505967537172697064353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57311003978358115131376235 85966505967537172697064353)
    ·
      refine ⟨64474879475652879522798265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85966505967537172697064353 64474879475652879522798265)
      ·
        refine ⟨48356159606739659642098699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64474879475652879522798265 48356159606739659642098699)
        ·
          refine ⟨72534239410109489463148049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48356159606739659642098699 72534239410109489463148049)
          ·
            refine ⟨54400679557582117097361037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72534239410109489463148049 54400679557582117097361037)
            ·
              refine ⟨20400254834093293911510389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54400679557582117097361037 20400254834093293911510389)
              ·
                refine ⟨1912523890696246304204099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20400254834093293911510389 1912523890696246304204099)
                ·
                  refine ⟨2868785836044369456306149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912523890696246304204099 2868785836044369456306149)
                  ·
                    refine ⟨537897344258319273057403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868785836044369456306149 537897344258319273057403)
                    ·
                      rfl

theorem cell22_1571327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_1571327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571327 prefixEnd_1571327 := by exact prefixLift 1571327
  have htrace : WordTrace (prefixWord ++ tailWord_1571327) baseStart_1571327 baseEnd_1571327 := by
    simpa [prefixWord, tailWord_1571327, baseEnd_1571327] using wordTrace_append hprefix tailTrace_1571327
  have hstable : (prefixWord ++ tailWord_1571327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571327).length < 2 ^ (prefixWord ++ tailWord_1571327).sum := by decide
  have hdescent : baseEnd_1571327 < baseStart_1571327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571348 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1571348 : Nat := 118140960795 + 1571348 * 2 ^ 59
def prefixEnd_1571348 : Nat := 4983230072969 + 3 ^ 40 * 1571348 * 2
def baseEnd_1571348 : Nat := 179301510995827406094113

theorem tailTrace_1571348 : CollatzResearch.WordTrace tailWord_1571348 prefixEnd_1571348 179301510995827406094113 := by
  unfold tailWord_1571348
  simp only [CollatzResearch.WordTrace]
  refine ⟨28655884955641017858945349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38207846607521357145260465 28655884955641017858945349)
  ·
    refine ⟨5372978429182690848552253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28655884955641017858945349 5372978429182690848552253)
    ·
      refine ⟨2014866910943509068207095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5372978429182690848552253 2014866910943509068207095)
      ·
        refine ⟨3022300366415263602310643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014866910943509068207095 3022300366415263602310643)
        ·
          refine ⟨4533450549622895403465965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022300366415263602310643 4533450549622895403465965)
          ·
            refine ⟨1700043956108585776299737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4533450549622895403465965 1700043956108585776299737)
            ·
              refine ⟨1275032967081439332224803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700043956108585776299737 1275032967081439332224803)
              ·
                refine ⟨1912549450622158998337205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275032967081439332224803 1912549450622158998337205)
                ·
                  refine ⟨179301510995827406094113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1912549450622158998337205 179301510995827406094113)
                  ·
                    rfl

theorem cell22_1571348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1571348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571348 prefixEnd_1571348 := by exact prefixLift 1571348
  have htrace : WordTrace (prefixWord ++ tailWord_1571348) baseStart_1571348 baseEnd_1571348 := by
    simpa [prefixWord, tailWord_1571348, baseEnd_1571348] using wordTrace_append hprefix tailTrace_1571348
  have hstable : (prefixWord ++ tailWord_1571348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571348).length < 2 ^ (prefixWord ++ tailWord_1571348).sum := by decide
  have hdescent : baseEnd_1571348 < baseStart_1571348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571389 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1571389 : Nat := 118140960795 + 1571389 * 2 ^ 59
def prefixEnd_1571389 : Nat := 4983230072969 + 3 ^ 40 * 1571389 * 2
def baseEnd_1571389 : Nat := 537918568125371778007213

theorem tailTrace_1571389 : CollatzResearch.WordTrace tailWord_1571389 prefixEnd_1571389 537918568125371778007213 := by
  unfold tailWord_1571389
  simp only [CollatzResearch.WordTrace]
  refine ⟨57313265304133499720133221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38208843536088999813422147 57313265304133499720133221)
  ·
    refine ⟨10746237244525031197524979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57313265304133499720133221 10746237244525031197524979)
    ·
      refine ⟨16119355866787546796287469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10746237244525031197524979 16119355866787546796287469)
      ·
        refine ⟨6044758450045330048607801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16119355866787546796287469 6044758450045330048607801)
        ·
          refine ⟨4533568837533997536455851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6044758450045330048607801 4533568837533997536455851)
          ·
            refine ⟨6800353256300996304683777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533568837533997536455851 6800353256300996304683777)
            ·
              refine ⟨5100264942225747228512833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800353256300996304683777 5100264942225747228512833)
              ·
                refine ⟨3825198706669310421384625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100264942225747228512833 3825198706669310421384625)
                ·
                  refine ⟨2868899030001982816038469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825198706669310421384625 2868899030001982816038469)
                  ·
                    refine ⟨537918568125371778007213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2868899030001982816038469 537918568125371778007213)
                    ·
                      rfl

theorem cell22_1571389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1571389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571389 prefixEnd_1571389 := by exact prefixLift 1571389
  have htrace : WordTrace (prefixWord ++ tailWord_1571389) baseStart_1571389 baseEnd_1571389 := by
    simpa [prefixWord, tailWord_1571389, baseEnd_1571389] using wordTrace_append hprefix tailTrace_1571389
  have hstable : (prefixWord ++ tailWord_1571389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571389).length < 2 ^ (prefixWord ++ tailWord_1571389).sum := by decide
  have hdescent : baseEnd_1571389 < baseStart_1571389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571393 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 4]
def baseStart_1571393 : Nat := 118140960795 + 1571393 * 2 ^ 59
def prefixEnd_1571393 : Nat := 4983230072969 + 3 ^ 40 * 1571393 * 2
def baseEnd_1571393 : Nat := 179306645802372366969067

theorem tailTrace_1571393 : CollatzResearch.WordTrace tailWord_1571393 prefixEnd_1571393 179306645802372366969067 := by
  unfold tailWord_1571393
  simp only [CollatzResearch.WordTrace]
  refine ⟨57313411196119008403278833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38208940797412672268852555 57313411196119008403278833)
  ·
    refine ⟨42985058397089256302459125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57313411196119008403278833 42985058397089256302459125)
    ·
      refine ⟨4029849224727117778355543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42985058397089256302459125 4029849224727117778355543)
      ·
        refine ⟨6044773837090676667533315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029849224727117778355543 6044773837090676667533315)
        ·
          refine ⟨9067160755636015001299973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044773837090676667533315 9067160755636015001299973)
          ·
            refine ⟨1700092641681752812743745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9067160755636015001299973 1700092641681752812743745)
            ·
              refine ⟨1275069481261314609557809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700092641681752812743745 1275069481261314609557809)
              ·
                refine ⟨956302110945985957168357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275069481261314609557809 956302110945985957168357)
                ·
                  refine ⟨179306645802372366969067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 956302110945985957168357 179306645802372366969067)
                  ·
                    rfl

theorem cell22_1571393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_1571393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571393 prefixEnd_1571393 := by exact prefixLift 1571393
  have htrace : WordTrace (prefixWord ++ tailWord_1571393) baseStart_1571393 baseEnd_1571393 := by
    simpa [prefixWord, tailWord_1571393, baseEnd_1571393] using wordTrace_append hprefix tailTrace_1571393
  have hstable : (prefixWord ++ tailWord_1571393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571393).length < 2 ^ (prefixWord ++ tailWord_1571393).sum := by decide
  have hdescent : baseEnd_1571393 < baseStart_1571393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571436 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_1571436 : Nat := 118140960795 + 1571436 * 2 ^ 59
def prefixEnd_1571436 : Nat := 4983230072969 + 3 ^ 40 * 1571436 * 2
def baseEnd_1571436 : Nat := 537934657185879322082069

theorem tailTrace_1571436 : CollatzResearch.WordTrace tailWord_1571436 prefixEnd_1571436 537934657185879322082069 := by
  unfold tailWord_1571436
  simp only [CollatzResearch.WordTrace]
  refine ⟨28657489767481613373547081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38209986356642151164729441 28657489767481613373547081)
  ·
    refine ⟨21493117325611210030160311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28657489767481613373547081 21493117325611210030160311)
    ·
      refine ⟨32239675988416815045240467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21493117325611210030160311 32239675988416815045240467)
      ·
        refine ⟨48359513982625222567860701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32239675988416815045240467 48359513982625222567860701)
        ·
          refine ⟨18134817743484458462947763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48359513982625222567860701 18134817743484458462947763)
          ·
            refine ⟨27202226615226687694421645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18134817743484458462947763 27202226615226687694421645)
            ·
              refine ⟨10200834980710007885408117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27202226615226687694421645 10200834980710007885408117)
              ·
                refine ⟨956328279441563239257011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10200834980710007885408117 956328279441563239257011)
                ·
                  refine ⟨1434492419162344858885517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956328279441563239257011 1434492419162344858885517)
                  ·
                    refine ⟨537934657185879322082069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434492419162344858885517 537934657185879322082069)
                    ·
                      rfl

theorem cell22_1571436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_1571436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571436 prefixEnd_1571436 := by exact prefixLift 1571436
  have htrace : WordTrace (prefixWord ++ tailWord_1571436) baseStart_1571436 baseEnd_1571436 := by
    simpa [prefixWord, tailWord_1571436, baseEnd_1571436] using wordTrace_append hprefix tailTrace_1571436
  have hstable : (prefixWord ++ tailWord_1571436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571436).length < 2 ^ (prefixWord ++ tailWord_1571436).sum := by decide
  have hdescent : baseEnd_1571436 < baseStart_1571436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571447 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1571447 : Nat := 118140960795 + 1571447 * 2 ^ 59
def prefixEnd_1571447 : Nat := 4983230072969 + 3 ^ 40 * 1571447 * 2
def baseEnd_1571447 : Nat := 537938422710678960057035

theorem tailTrace_1571447 : CollatzResearch.WordTrace tailWord_1571447 prefixEnd_1571447 537938422710678960057035 := by
  unfold tailWord_1571447
  simp only [CollatzResearch.WordTrace]
  refine ⟨57315380737923375625744595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38210253825282250417163063 57315380737923375625744595)
  ·
    refine ⟨85973071106885063438616893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57315380737923375625744595 85973071106885063438616893)
    ·
      refine ⟨32239901665081898789481335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85973071106885063438616893 32239901665081898789481335)
      ·
        refine ⟨48359852497622848184222003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32239901665081898789481335 48359852497622848184222003)
        ·
          refine ⟨72539778746434272276333005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48359852497622848184222003 72539778746434272276333005)
          ·
            refine ⟨27202417029912852103624877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72539778746434272276333005 27202417029912852103624877)
            ·
              refine ⟨10200906386217319538859329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27202417029912852103624877 10200906386217319538859329)
              ·
                refine ⟨7650679789662989654144497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10200906386217319538859329 7650679789662989654144497)
                ·
                  refine ⟨5738009842247242240608373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7650679789662989654144497 5738009842247242240608373)
                  ·
                    refine ⟨537938422710678960057035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5738009842247242240608373 537938422710678960057035)
                    ·
                      rfl

theorem cell22_1571447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1571447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571447 prefixEnd_1571447 := by exact prefixLift 1571447
  have htrace : WordTrace (prefixWord ++ tailWord_1571447) baseStart_1571447 baseEnd_1571447 := by
    simpa [prefixWord, tailWord_1571447, baseEnd_1571447] using wordTrace_append hprefix tailTrace_1571447
  have hstable : (prefixWord ++ tailWord_1571447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571447).length < 2 ^ (prefixWord ++ tailWord_1571447).sum := by decide
  have hdescent : baseEnd_1571447 < baseStart_1571447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571449 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 5]
def baseStart_1571449 : Nat := 118140960795 + 1571449 * 2 ^ 59
def prefixEnd_1571449 : Nat := 4983230072969 + 3 ^ 40 * 1571449 * 2
def baseEnd_1571449 : Nat := 179313035783850540502343

theorem tailTrace_1571449 : CollatzResearch.WordTrace tailWord_1571449 prefixEnd_1571449 179313035783850540502343 := by
  unfold tailWord_1571449
  simp only [CollatzResearch.WordTrace]
  refine ⟨57315453683916129967317401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38210302455944086644878267 57315453683916129967317401)
  ·
    refine ⟨42986590262937097475488051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57315453683916129967317401 42986590262937097475488051)
    ·
      refine ⟨64479885394405646213232077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42986590262937097475488051 64479885394405646213232077)
      ·
        refine ⟨24179957022902117329962029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64479885394405646213232077 24179957022902117329962029)
        ·
          refine ⟨9067483883588293998735761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24179957022902117329962029 9067483883588293998735761)
          ·
            refine ⟨6800612912691220499051821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9067483883588293998735761 6800612912691220499051821)
            ·
              refine ⟨2550229842259207687144433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6800612912691220499051821 2550229842259207687144433)
              ·
                refine ⟨1912672381694405765358325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550229842259207687144433 1912672381694405765358325)
                ·
                  refine ⟨179313035783850540502343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1912672381694405765358325 179313035783850540502343)
                  ·
                    rfl

theorem cell22_1571449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_1571449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571449 prefixEnd_1571449 := by exact prefixLift 1571449
  have htrace : WordTrace (prefixWord ++ tailWord_1571449) baseStart_1571449 baseEnd_1571449 := by
    simpa [prefixWord, tailWord_1571449, baseEnd_1571449] using wordTrace_append hprefix tailTrace_1571449
  have hstable : (prefixWord ++ tailWord_1571449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571449).length < 2 ^ (prefixWord ++ tailWord_1571449).sum := by decide
  have hdescent : baseEnd_1571449 < baseStart_1571449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571511 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 6]
def baseStart_1571511 : Nat := 118140960795 + 1571511 * 2 ^ 59
def prefixEnd_1571511 : Nat := 4983230072969 + 3 ^ 40 * 1571511 * 2
def baseEnd_1571511 : Nat := 179320110406201375485613

theorem tailTrace_1571511 : CollatzResearch.WordTrace tailWord_1571511 prefixEnd_1571511 179320110406201375485613 := by
  unfold tailWord_1571511
  simp only [CollatzResearch.WordTrace]
  refine ⟨57317715009691514556074387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38211810006461009704049591 57317715009691514556074387)
  ·
    refine ⟨85976572514537271834111581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57317715009691514556074387 85976572514537271834111581)
    ·
      refine ⟨32241214692951476937791843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85976572514537271834111581 32241214692951476937791843)
      ·
        refine ⟨48361822039427215406687765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32241214692951476937791843 48361822039427215406687765)
        ·
          refine ⟨2266960408098150722188489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48361822039427215406687765 2266960408098150722188489)
          ·
            refine ⟨1700220306073613041641367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2266960408098150722188489 1700220306073613041641367)
            ·
              refine ⟨2550330459110419562462051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700220306073613041641367 2550330459110419562462051)
              ·
                refine ⟨3825495688665629343693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550330459110419562462051 3825495688665629343693077)
                ·
                  refine ⟨179320110406201375485613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3825495688665629343693077 179320110406201375485613)
                  ·
                    rfl

theorem cell22_1571511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 6].length) (baseStart_1571511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571511 prefixEnd_1571511 := by exact prefixLift 1571511
  have htrace : WordTrace (prefixWord ++ tailWord_1571511) baseStart_1571511 baseEnd_1571511 := by
    simpa [prefixWord, tailWord_1571511, baseEnd_1571511] using wordTrace_append hprefix tailTrace_1571511
  have hstable : (prefixWord ++ tailWord_1571511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571511).length < 2 ^ (prefixWord ++ tailWord_1571511).sum := by decide
  have hdescent : baseEnd_1571511 < baseStart_1571511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571618 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1571618 : Nat := 118140960795 + 1571618 * 2 ^ 59
def prefixEnd_1571618 : Nat := 4983230072969 + 3 ^ 40 * 1571618 * 2
def baseEnd_1571618 : Nat := 179332319835097171343837

theorem tailTrace_1571618 : CollatzResearch.WordTrace tailWord_1571618 prefixEnd_1571618 179332319835097171343837 := by
  unfold tailWord_1571618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330404405075967957554877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38214411746869247886813005 14330404405075967957554877)
  ·
    refine ⟨5373901651903487984083079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14330404405075967957554877 5373901651903487984083079)
    ·
      refine ⟨8060852477855231976124619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5373901651903487984083079 8060852477855231976124619)
      ·
        refine ⟨12091278716782847964186929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060852477855231976124619 12091278716782847964186929)
        ·
          refine ⟨9068459037587135973140197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12091278716782847964186929 9068459037587135973140197)
          ·
            refine ⟨1700336069547587994963787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9068459037587135973140197 1700336069547587994963787)
            ·
              refine ⟨2550504104321381992445681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700336069547587994963787 2550504104321381992445681)
              ·
                refine ⟨1912878078241036494334261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550504104321381992445681 1912878078241036494334261)
                ·
                  refine ⟨179332319835097171343837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1912878078241036494334261 179332319835097171343837)
                  ·
                    rfl

theorem cell22_1571618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1571618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571618 prefixEnd_1571618 := by exact prefixLift 1571618
  have htrace : WordTrace (prefixWord ++ tailWord_1571618) baseStart_1571618 baseEnd_1571618 := by
    simpa [prefixWord, tailWord_1571618, baseEnd_1571618] using wordTrace_append hprefix tailTrace_1571618
  have hstable : (prefixWord ++ tailWord_1571618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571618).length < 2 ^ (prefixWord ++ tailWord_1571618).sum := by decide
  have hdescent : baseEnd_1571618 < baseStart_1571618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571659 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 8, 4]
def baseStart_1571659 : Nat := 118140960795 + 1571659 * 2 ^ 59
def prefixEnd_1571659 : Nat := 4983230072969 + 3 ^ 40 * 1571659 * 2
def baseEnd_1571659 : Nat := 538010994643181073756385

theorem tailTrace_1571659 : CollatzResearch.WordTrace tailWord_1571659 prefixEnd_1571659 538010994643181073756385 := by
  unfold tailWord_1571659
  simp only [CollatzResearch.WordTrace]
  refine ⟨57323113013155335832462031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38215408675436890554974687 57323113013155335832462031)
  ·
    refine ⟨85984669519733003748693047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57323113013155335832462031 85984669519733003748693047)
    ·
      refine ⟨128977004279599505623039571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85984669519733003748693047 128977004279599505623039571)
      ·
        refine ⟨193465506419399258434559357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128977004279599505623039571 193465506419399258434559357)
        ·
          refine ⟨72549564907274721912959759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193465506419399258434559357 72549564907274721912959759)
          ·
            refine ⟨108824347360912082869439639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72549564907274721912959759 108824347360912082869439639)
            ·
              refine ⟨163236521041368124304159459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108824347360912082869439639 163236521041368124304159459)
              ·
                refine ⟨244854781562052186456239189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163236521041368124304159459 244854781562052186456239189)
                ·
                  refine ⟨2869391971430299060034053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 244854781562052186456239189 2869391971430299060034053)
                  ·
                    refine ⟨538010994643181073756385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2869391971430299060034053 538010994643181073756385)
                    ·
                      rfl

theorem cell22_1571659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_1571659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571659 prefixEnd_1571659 := by exact prefixLift 1571659
  have htrace : WordTrace (prefixWord ++ tailWord_1571659) baseStart_1571659 baseEnd_1571659 := by
    simpa [prefixWord, tailWord_1571659, baseEnd_1571659] using wordTrace_append hprefix tailTrace_1571659
  have hstable : (prefixWord ++ tailWord_1571659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571659).length < 2 ^ (prefixWord ++ tailWord_1571659).sum := by decide
  have hdescent : baseEnd_1571659 < baseStart_1571659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571674 : List Nat := [3, 1, 1, 2, 1, 4, 10]
def baseStart_1571674 : Nat := 118140960795 + 1571674 * 2 ^ 59
def prefixEnd_1571674 : Nat := 4983230072969 + 3 ^ 40 * 1571674 * 2
def baseEnd_1571674 : Nat := 19926523312952816097457

theorem tailTrace_1571674 : CollatzResearch.WordTrace tailWord_1571674 prefixEnd_1571674 19926523312952816097457 := by
  unfold tailWord_1571674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330915027025248348564519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38215773405400662262838717 14330915027025248348564519)
  ·
    refine ⟨21496372540537872522846779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14330915027025248348564519 21496372540537872522846779)
    ·
      refine ⟨32244558810806808784270169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21496372540537872522846779 32244558810806808784270169)
      ·
        refine ⟨24183419108105106588202627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32244558810806808784270169 24183419108105106588202627)
        ·
          refine ⟨36275128662157659882303941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24183419108105106588202627 36275128662157659882303941)
          ·
            refine ⟨6801586624154561227931989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36275128662157659882303941 6801586624154561227931989)
            ·
              refine ⟨19926523312952816097457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6801586624154561227931989 19926523312952816097457)
              ·
                rfl

theorem cell22_1571674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 10].length) (baseStart_1571674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571674 prefixEnd_1571674 := by exact prefixLift 1571674
  have htrace : WordTrace (prefixWord ++ tailWord_1571674) baseStart_1571674 baseEnd_1571674 := by
    simpa [prefixWord, tailWord_1571674, baseEnd_1571674] using wordTrace_append hprefix tailTrace_1571674
  have hstable : (prefixWord ++ tailWord_1571674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571674).length < 2 ^ (prefixWord ++ tailWord_1571674).sum := by decide
  have hdescent : baseEnd_1571674 < baseStart_1571674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571704 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_1571704 : Nat := 118140960795 + 1571704 * 2 ^ 59
def prefixEnd_1571704 : Nat := 4983230072969 + 3 ^ 40 * 1571704 * 2
def baseEnd_1571704 : Nat := 538026399062815956381247

theorem tailTrace_1571704 : CollatzResearch.WordTrace tailWord_1571704 prefixEnd_1571704 538026399062815956381247 := by
  unfold tailWord_1571704
  simp only [CollatzResearch.WordTrace]
  refine ⟨28662377148996154258925083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38216502865328205678566777 28662377148996154258925083)
  ·
    refine ⟨42993565723494231388387625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28662377148996154258925083 42993565723494231388387625)
    ·
      refine ⟨32245174292620673541290719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42993565723494231388387625 32245174292620673541290719)
      ·
        refine ⟨48367761438931010311936079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32245174292620673541290719 48367761438931010311936079)
        ·
          refine ⟨72551642158396515467904119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48367761438931010311936079 72551642158396515467904119)
          ·
            refine ⟨108827463237594773201856179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72551642158396515467904119 108827463237594773201856179)
            ·
              refine ⟨163241194856392159802784269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108827463237594773201856179 163241194856392159802784269)
              ·
                refine ⟨61215448071147059926044101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163241194856392159802784269 61215448071147059926044101)
                ·
                  refine ⟨11477896513340073736133269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61215448071147059926044101 11477896513340073736133269)
                  ·
                    refine ⟨538026399062815956381247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11477896513340073736133269 538026399062815956381247)
                    ·
                      rfl

theorem cell22_1571704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_1571704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571704 prefixEnd_1571704 := by exact prefixLift 1571704
  have htrace : WordTrace (prefixWord ++ tailWord_1571704) baseStart_1571704 baseEnd_1571704 := by
    simpa [prefixWord, tailWord_1571704, baseEnd_1571704] using wordTrace_append hprefix tailTrace_1571704
  have hstable : (prefixWord ++ tailWord_1571704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571704).length < 2 ^ (prefixWord ++ tailWord_1571704).sum := by decide
  have hdescent : baseEnd_1571704 < baseStart_1571704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571706 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_1571706 : Nat := 118140960795 + 1571706 * 2 ^ 59
def prefixEnd_1571706 : Nat := 4983230072969 + 3 ^ 40 * 1571706 * 2
def baseEnd_1571706 : Nat := 538027083703688617831241

theorem tailTrace_1571706 : CollatzResearch.WordTrace tailWord_1571706 prefixEnd_1571706 538027083703688617831241 := by
  unfold tailWord_1571706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331206810996265714855743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38216551495990041906281981 14331206810996265714855743)
  ·
    refine ⟨21496810216494398572283615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14331206810996265714855743 21496810216494398572283615)
    ·
      refine ⟨32245215324741597858425423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21496810216494398572283615 32245215324741597858425423)
      ·
        refine ⟨48367822987112396787638135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32245215324741597858425423 48367822987112396787638135)
        ·
          refine ⟨72551734480668595181457203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48367822987112396787638135 72551734480668595181457203)
          ·
            refine ⟨108827601721002892772185805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72551734480668595181457203 108827601721002892772185805)
            ·
              refine ⟨40810350645376084789569677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108827601721002892772185805 40810350645376084789569677)
              ·
                refine ⟨15303881492016031796088629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40810350645376084789569677 15303881492016031796088629)
                ·
                  refine ⟨1434738889876502980883309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15303881492016031796088629 1434738889876502980883309)
                  ·
                    refine ⟨538027083703688617831241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434738889876502980883309 538027083703688617831241)
                    ·
                      rfl

theorem cell22_1571706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_1571706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571706 prefixEnd_1571706 := by exact prefixLift 1571706
  have htrace : WordTrace (prefixWord ++ tailWord_1571706) baseStart_1571706 baseEnd_1571706 := by
    simpa [prefixWord, tailWord_1571706, baseEnd_1571706] using wordTrace_append hprefix tailTrace_1571706
  have hstable : (prefixWord ++ tailWord_1571706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571706).length < 2 ^ (prefixWord ++ tailWord_1571706).sum := by decide
  have hdescent : baseEnd_1571706 < baseStart_1571706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571757 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1571757 : Nat := 118140960795 + 1571757 * 2 ^ 59
def prefixEnd_1571757 : Nat := 4983230072969 + 3 ^ 40 * 1571757 * 2
def baseEnd_1571757 : Nat := 538044542045941484806085

theorem tailTrace_1571757 : CollatzResearch.WordTrace tailWord_1571757 prefixEnd_1571757 538044542045941484806085 := by
  unfold tailWord_1571757
  simp only [CollatzResearch.WordTrace]
  refine ⟨57326687366800298569529525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38217791577866865713019683 57326687366800298569529525)
  ·
    refine ⟨5374376940637527990893393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57326687366800298569529525 5374376940637527990893393)
    ·
      refine ⟨4030782705478145993170045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5374376940637527990893393 4030782705478145993170045)
      ·
        refine ⟨1511543514554304747438767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4030782705478145993170045 1511543514554304747438767)
        ·
          refine ⟨2267315271831457121158151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511543514554304747438767 2267315271831457121158151)
          ·
            refine ⟨3400972907747185681737227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267315271831457121158151 3400972907747185681737227)
            ·
              refine ⟨5101459361620778522605841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400972907747185681737227 5101459361620778522605841)
              ·
                refine ⟨3826094521215583891954381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5101459361620778522605841 3826094521215583891954381)
                ·
                  refine ⟨1434785445455843959482893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3826094521215583891954381 1434785445455843959482893)
                  ·
                    refine ⟨538044542045941484806085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434785445455843959482893 538044542045941484806085)
                    ·
                      rfl

theorem cell22_1571757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1571757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571757 prefixEnd_1571757 := by exact prefixLift 1571757
  have htrace : WordTrace (prefixWord ++ tailWord_1571757) baseStart_1571757 baseEnd_1571757 := by
    simpa [prefixWord, tailWord_1571757, baseEnd_1571757] using wordTrace_append hprefix tailTrace_1571757
  have hstable : (prefixWord ++ tailWord_1571757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571757).length < 2 ^ (prefixWord ++ tailWord_1571757).sum := by decide
  have hdescent : baseEnd_1571757 < baseStart_1571757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571811 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_1571811 : Nat := 118140960795 + 1571811 * 2 ^ 59
def prefixEnd_1571811 : Nat := 4983230072969 + 3 ^ 40 * 1571811 * 2
def baseEnd_1571811 : Nat := 538063027349503343955919

theorem tailTrace_1571811 : CollatzResearch.WordTrace tailWord_1571811 prefixEnd_1571811 538063027349503343955919 := by
  unfold tailWord_1571811
  simp only [CollatzResearch.WordTrace]
  refine ⟨57328656908604665791995287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38219104605736443861330191 57328656908604665791995287)
  ·
    refine ⟨85992985362906998687992931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57328656908604665791995287 85992985362906998687992931)
    ·
      refine ⟨128989478044360498031989397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85992985362906998687992931 128989478044360498031989397)
      ·
        refine ⟨6046381783329398345249503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128989478044360498031989397 6046381783329398345249503)
        ·
          refine ⟨9069572674994097517874255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046381783329398345249503 9069572674994097517874255)
          ·
            refine ⟨13604359012491146276811383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069572674994097517874255 13604359012491146276811383)
            ·
              refine ⟨20406538518736719415217075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13604359012491146276811383 20406538518736719415217075)
              ·
                refine ⟨30609807778105079122825613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20406538518736719415217075 30609807778105079122825613)
                ·
                  refine ⟨11478677916789404671059605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30609807778105079122825613 11478677916789404671059605)
                  ·
                    refine ⟨538063027349503343955919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11478677916789404671059605 538063027349503343955919)
                    ·
                      rfl

theorem cell22_1571811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_1571811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571811 prefixEnd_1571811 := by exact prefixLift 1571811
  have htrace : WordTrace (prefixWord ++ tailWord_1571811) baseStart_1571811 baseEnd_1571811 := by
    simpa [prefixWord, tailWord_1571811, baseEnd_1571811] using wordTrace_append hprefix tailTrace_1571811
  have hstable : (prefixWord ++ tailWord_1571811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571811).length < 2 ^ (prefixWord ++ tailWord_1571811).sum := by decide
  have hdescent : baseEnd_1571811 < baseStart_1571811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571830 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1571830 : Nat := 118140960795 + 1571830 * 2 ^ 59
def prefixEnd_1571830 : Nat := 4983230072969 + 3 ^ 40 * 1571830 * 2
def baseEnd_1571830 : Nat := 538069531437793627730861

theorem tailTrace_1571830 : CollatzResearch.WordTrace tailWord_1571830 prefixEnd_1571830 538069531437793627730861 := by
  unfold tailWord_1571830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583084368470989502308559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38219566597023888024624629 3583084368470989502308559)
  ·
    refine ⟨5374626552706484253462839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583084368470989502308559 5374626552706484253462839)
    ·
      refine ⟨8061939829059726380194259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374626552706484253462839 8061939829059726380194259)
      ·
        refine ⟨12092909743589589570291389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8061939829059726380194259 12092909743589589570291389)
        ·
          refine ⟨4534841153846096088859271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12092909743589589570291389 4534841153846096088859271)
          ·
            refine ⟨6802261730769144133288907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534841153846096088859271 6802261730769144133288907)
            ·
              refine ⟨10203392596153716199933361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6802261730769144133288907 10203392596153716199933361)
              ·
                refine ⟨7652544447115287149950021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10203392596153716199933361 7652544447115287149950021)
                ·
                  refine ⟨1434852083834116340615629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7652544447115287149950021 1434852083834116340615629)
                  ·
                    refine ⟨538069531437793627730861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434852083834116340615629 538069531437793627730861)
                    ·
                      rfl

theorem cell22_1571830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1571830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571830 prefixEnd_1571830 := by exact prefixLift 1571830
  have htrace : WordTrace (prefixWord ++ tailWord_1571830) baseStart_1571830 baseEnd_1571830 := by
    simpa [prefixWord, tailWord_1571830, baseEnd_1571830] using wordTrace_append hprefix tailTrace_1571830
  have hstable : (prefixWord ++ tailWord_1571830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571830).length < 2 ^ (prefixWord ++ tailWord_1571830).sum := by decide
  have hdescent : baseEnd_1571830 < baseStart_1571830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571918 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1571918 : Nat := 118140960795 + 1571918 * 2 ^ 59
def prefixEnd_1571918 : Nat := 4983230072969 + 3 ^ 40 * 1571918 * 2
def baseEnd_1571918 : Nat := 538099655636190731530591

theorem tailTrace_1571918 : CollatzResearch.WordTrace tailWord_1571918 prefixEnd_1571918 538099655636190731530591 := by
  unfold tailWord_1571918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166569939902127883267551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38221706346144682044093605 7166569939902127883267551)
  ·
    refine ⟨10749854909853191824901327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7166569939902127883267551 10749854909853191824901327)
    ·
      refine ⟨16124782364779787737351991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10749854909853191824901327 16124782364779787737351991)
      ·
        refine ⟨24187173547169681606027987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16124782364779787737351991 24187173547169681606027987)
        ·
          refine ⟨36280760320754522409041981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24187173547169681606027987 36280760320754522409041981)
          ·
            refine ⟨13605285120282945903390743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36280760320754522409041981 13605285120282945903390743)
            ·
              refine ⟨20407927680424418855086115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13605285120282945903390743 20407927680424418855086115)
              ·
                refine ⟨30611891520636628282629173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20407927680424418855086115 30611891520636628282629173)
                ·
                  refine ⟨2869864830059683901496485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30611891520636628282629173 2869864830059683901496485)
                  ·
                    refine ⟨538099655636190731530591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2869864830059683901496485 538099655636190731530591)
                    ·
                      rfl

theorem cell22_1571918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1571918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571918 prefixEnd_1571918 := by exact prefixLift 1571918
  have htrace : WordTrace (prefixWord ++ tailWord_1571918) baseStart_1571918 baseEnd_1571918 := by
    simpa [prefixWord, tailWord_1571918, baseEnd_1571918] using wordTrace_append hprefix tailTrace_1571918
  have hstable : (prefixWord ++ tailWord_1571918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571918).length < 2 ^ (prefixWord ++ tailWord_1571918).sum := by decide
  have hdescent : baseEnd_1571918 < baseStart_1571918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571948 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_1571948 : Nat := 118140960795 + 1571948 * 2 ^ 59
def prefixEnd_1571948 : Nat := 4983230072969 + 3 ^ 40 * 1571948 * 2
def baseEnd_1571948 : Nat := 538109925249280653280499

theorem tailTrace_1571948 : CollatzResearch.WordTrace tailWord_1571948 prefixEnd_1571948 538109925249280653280499 := by
  unfold tailWord_1571948
  simp only [CollatzResearch.WordTrace]
  refine ⟨28666826854554169094866249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38222435806072225459821665 28666826854554169094866249)
  ·
    refine ⟨21500120140915626821149687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28666826854554169094866249 21500120140915626821149687)
    ·
      refine ⟨32250180211373440231724531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21500120140915626821149687 32250180211373440231724531)
      ·
        refine ⟨48375270317060160347586797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32250180211373440231724531 48375270317060160347586797)
        ·
          refine ⟨18140726368897560130345049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48375270317060160347586797 18140726368897560130345049)
          ·
            refine ⟨13605544776673170097758787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18140726368897560130345049 13605544776673170097758787)
            ·
              refine ⟨20408317165009755146638181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13605544776673170097758787 20408317165009755146638181)
              ·
                refine ⟨3826559468439329089994659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20408317165009755146638181 3826559468439329089994659)
                ·
                  refine ⟨5739839202658993634991989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826559468439329089994659 5739839202658993634991989)
                  ·
                    refine ⟨538109925249280653280499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5739839202658993634991989 538109925249280653280499)
                    ·
                      rfl

theorem cell22_1571948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_1571948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571948 prefixEnd_1571948 := by exact prefixLift 1571948
  have htrace : WordTrace (prefixWord ++ tailWord_1571948) baseStart_1571948 baseEnd_1571948 := by
    simpa [prefixWord, tailWord_1571948, baseEnd_1571948] using wordTrace_append hprefix tailTrace_1571948
  have hstable : (prefixWord ++ tailWord_1571948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571948).length < 2 ^ (prefixWord ++ tailWord_1571948).sum := by decide
  have hdescent : baseEnd_1571948 < baseStart_1571948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571963 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 2, 4]
def baseStart_1571963 : Nat := 118140960795 + 1571963 * 2 ^ 59
def prefixEnd_1571963 : Nat := 4983230072969 + 3 ^ 40 * 1571963 * 2
def baseEnd_1571963 : Nat := 538115060055825614155453

theorem tailTrace_1571963 : CollatzResearch.WordTrace tailWord_1571963 prefixEnd_1571963 538115060055825614155453 := by
  unfold tailWord_1571963
  simp only [CollatzResearch.WordTrace]
  refine ⟨57334200804053995751528543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38222800536035997167685695 57334200804053995751528543)
  ·
    refine ⟨86001301206080993627292815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57334200804053995751528543 86001301206080993627292815)
    ·
      refine ⟨129001951809121490440939223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86001301206080993627292815 129001951809121490440939223)
      ·
        refine ⟨193502927713682235661408835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129001951809121490440939223 193502927713682235661408835)
        ·
          refine ⟨290254391570523353492113253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193502927713682235661408835 290254391570523353492113253)
          ·
            refine ⟨54422698419473128779771235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290254391570523353492113253 54422698419473128779771235)
            ·
              refine ⟨81634047629209693169656853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54422698419473128779771235 81634047629209693169656853)
              ·
                refine ⟨3826595982619204367327665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81634047629209693169656853 3826595982619204367327665)
                ·
                  refine ⟨2869946986964403275495749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826595982619204367327665 2869946986964403275495749)
                  ·
                    refine ⟨538115060055825614155453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2869946986964403275495749 538115060055825614155453)
                    ·
                      rfl

theorem cell22_1571963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_1571963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571963 prefixEnd_1571963 := by exact prefixLift 1571963
  have htrace : WordTrace (prefixWord ++ tailWord_1571963) baseStart_1571963 baseEnd_1571963 := by
    simpa [prefixWord, tailWord_1571963, baseEnd_1571963] using wordTrace_append hprefix tailTrace_1571963
  have hstable : (prefixWord ++ tailWord_1571963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571963).length < 2 ^ (prefixWord ++ tailWord_1571963).sum := by decide
  have hdescent : baseEnd_1571963 < baseStart_1571963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571965 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_1571965 : Nat := 118140960795 + 1571965 * 2 ^ 59
def prefixEnd_1571965 : Nat := 4983230072969 + 3 ^ 40 * 1571965 * 2
def baseEnd_1571965 : Nat := 538115744696698275605447

theorem tailTrace_1571965 : CollatzResearch.WordTrace tailWord_1571965 prefixEnd_1571965 538115744696698275605447 := by
  unfold tailWord_1571965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57334273750046750093101349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38222849166697833395400899 57334273750046750093101349)
  ·
    refine ⟨10750176328133765642456503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57334273750046750093101349 10750176328133765642456503)
    ·
      refine ⟨16125264492200648463684755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750176328133765642456503 16125264492200648463684755)
      ·
        refine ⟨24187896738300972695527133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125264492200648463684755 24187896738300972695527133)
        ·
          refine ⟨9070461276862864760822675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24187896738300972695527133 9070461276862864760822675)
          ·
            refine ⟨13605691915294297141234013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070461276862864760822675 13605691915294297141234013)
            ·
              refine ⟨5102134468235361427962755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13605691915294297141234013 5102134468235361427962755)
              ·
                refine ⟨7653201702353042141944133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102134468235361427962755 7653201702353042141944133)
                ·
                  refine ⟨1434975319191195401614525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7653201702353042141944133 1434975319191195401614525)
                  ·
                    refine ⟨538115744696698275605447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1434975319191195401614525 538115744696698275605447)
                    ·
                      rfl

theorem cell22_1571965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_1571965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571965 prefixEnd_1571965 := by exact prefixLift 1571965
  have htrace : WordTrace (prefixWord ++ tailWord_1571965) baseStart_1571965 baseEnd_1571965 := by
    simpa [prefixWord, tailWord_1571965, baseEnd_1571965] using wordTrace_append hprefix tailTrace_1571965
  have hstable : (prefixWord ++ tailWord_1571965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571965).length < 2 ^ (prefixWord ++ tailWord_1571965).sum := by decide
  have hdescent : baseEnd_1571965 < baseStart_1571965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571978 : List Nat := [3, 1, 2, 3, 1, 1, 2, 9]
def baseStart_1571978 : Nat := 118140960795 + 1571978 * 2 ^ 59
def prefixEnd_1571978 : Nat := 4983230072969 + 3 ^ 40 * 1571978 * 2
def baseEnd_1571978 : Nat := 59791132762485619447823

theorem tailTrace_1571978 : CollatzResearch.WordTrace tailWord_1571978 prefixEnd_1571978 59791132762485619447823 := by
  unfold tailWord_1571978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14333686974749913328331147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38223165265999768875549725 14333686974749913328331147)
  ·
    refine ⟨21500530462124869992496721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14333686974749913328331147 21500530462124869992496721)
    ·
      refine ⟨16125397846593652494372541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21500530462124869992496721 16125397846593652494372541)
      ·
        refine ⟨6047024192472619685389703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16125397846593652494372541 6047024192472619685389703)
        ·
          refine ⟨9070536288708929528084555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047024192472619685389703 9070536288708929528084555)
          ·
            refine ⟨13605804433063394292126833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070536288708929528084555 13605804433063394292126833)
            ·
              refine ⟨10204353324797545719095125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13605804433063394292126833 10204353324797545719095125)
              ·
                refine ⟨59791132762485619447823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10204353324797545719095125 59791132762485619447823)
                ·
                  rfl

theorem cell22_1571978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_1571978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571978 prefixEnd_1571978 := by exact prefixLift 1571978
  have htrace : WordTrace (prefixWord ++ tailWord_1571978) baseStart_1571978 baseEnd_1571978 := by
    simpa [prefixWord, tailWord_1571978, baseEnd_1571978] using wordTrace_append hprefix tailTrace_1571978
  have hstable : (prefixWord ++ tailWord_1571978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571978).length < 2 ^ (prefixWord ++ tailWord_1571978).sum := by decide
  have hdescent : baseEnd_1571978 < baseStart_1571978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571982 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1571982 : Nat := 118140960795 + 1571982 * 2 ^ 59
def prefixEnd_1571982 : Nat := 4983230072969 + 3 ^ 40 * 1571982 * 2
def baseEnd_1571982 : Nat := 538121564144115897930395

theorem tailTrace_1571982 : CollatzResearch.WordTrace tailWord_1571982 prefixEnd_1571982 538121564144115897930395 := by
  unfold tailWord_1571982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166861723873145249558775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38223262527323441330980133 7166861723873145249558775)
  ·
    refine ⟨10750292585809717874338163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7166861723873145249558775 10750292585809717874338163)
    ·
      refine ⟨16125438878714576811507245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750292585809717874338163 16125438878714576811507245)
      ·
        refine ⟨6047039579517966304315217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16125438878714576811507245 6047039579517966304315217)
        ·
          refine ⟨4535279684638474728236413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6047039579517966304315217 4535279684638474728236413)
          ·
            refine ⟨1700729881739428023088655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4535279684638474728236413 1700729881739428023088655)
            ·
              refine ⟨2551094822609142034632983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700729881739428023088655 2551094822609142034632983)
              ·
                refine ⟨3826642233913713051949475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551094822609142034632983 3826642233913713051949475)
                ·
                  refine ⟨5739963350870569577924213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826642233913713051949475 5739963350870569577924213)
                  ·
                    refine ⟨538121564144115897930395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5739963350870569577924213 538121564144115897930395)
                    ·
                      rfl

theorem cell22_1571982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1571982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1571982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1571982 prefixEnd_1571982 := by exact prefixLift 1571982
  have htrace : WordTrace (prefixWord ++ tailWord_1571982) baseStart_1571982 baseEnd_1571982 := by
    simpa [prefixWord, tailWord_1571982, baseEnd_1571982] using wordTrace_append hprefix tailTrace_1571982
  have hstable : (prefixWord ++ tailWord_1571982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571982).length < 2 ^ (prefixWord ++ tailWord_1571982).sum := by decide
  have hdescent : baseEnd_1571982 < baseStart_1571982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572023 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 7]
def baseStart_1572023 : Nat := 118140960795 + 1572023 * 2 ^ 59
def prefixEnd_1572023 : Nat := 4983230072969 + 3 ^ 40 * 1572023 * 2
def baseEnd_1572023 : Nat := 179378533094001819218423

theorem tailTrace_1572023 : CollatzResearch.WordTrace tailWord_1572023 prefixEnd_1572023 179378533094001819218423 := by
  unfold tailWord_1572023
  simp only [CollatzResearch.WordTrace]
  refine ⟨57336389183836625998712723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38224259455891083999141815 57336389183836625998712723)
  ·
    refine ⟨86004583775754938998069085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57336389183836625998712723 86004583775754938998069085)
    ·
      refine ⟨32251718915908102124275907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86004583775754938998069085 32251718915908102124275907)
      ·
        refine ⟨48377578373862153186413861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32251718915908102124275907 48377578373862153186413861)
        ·
          refine ⟨9070795945099153722452599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48377578373862153186413861 9070795945099153722452599)
          ·
            refine ⟨13606193917648730583678899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070795945099153722452599 13606193917648730583678899)
            ·
              refine ⟨20409290876473095875518349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13606193917648730583678899 20409290876473095875518349)
              ·
                refine ⟨7653484078677410953319381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20409290876473095875518349 7653484078677410953319381)
                ·
                  refine ⟨179378533094001819218423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7653484078677410953319381 179378533094001819218423)
                  ·
                    rfl

theorem cell22_1572023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_1572023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572023 prefixEnd_1572023 := by exact prefixLift 1572023
  have htrace : WordTrace (prefixWord ++ tailWord_1572023) baseStart_1572023 baseEnd_1572023 := by
    simpa [prefixWord, tailWord_1572023, baseEnd_1572023] using wordTrace_append hprefix tailTrace_1572023
  have hstable : (prefixWord ++ tailWord_1572023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572023).length < 2 ^ (prefixWord ++ tailWord_1572023).sum := by decide
  have hdescent : baseEnd_1572023 < baseStart_1572023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572164 : List Nat := [2, 3, 4, 1, 1, 1, 4, 6]
def baseStart_1572164 : Nat := 118140960795 + 1572164 * 2 ^ 59
def prefixEnd_1572164 : Nat := 4983230072969 + 3 ^ 40 * 1572164 * 2
def baseEnd_1572164 : Nat := 59798207384836454431093

theorem tailTrace_1572164 : CollatzResearch.WordTrace tailWord_1572164 prefixEnd_1572164 59798207384836454431093 := by
  unfold tailWord_1572164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28670765938162903539797773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38227687917550538053063697 28670765938162903539797773)
  ·
    refine ⟨10751537226811088827424165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28670765938162903539797773 10751537226811088827424165)
    ·
      refine ⟨2015913230027079155142031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10751537226811088827424165 2015913230027079155142031)
      ·
        refine ⟨3023869845040618732713047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015913230027079155142031 3023869845040618732713047)
        ·
          refine ⟨4535804767560928099069571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023869845040618732713047 4535804767560928099069571)
          ·
            refine ⟨6803707151341392148604357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535804767560928099069571 6803707151341392148604357)
            ·
              refine ⟨1275695090876511027863317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6803707151341392148604357 1275695090876511027863317)
              ·
                refine ⟨59798207384836454431093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1275695090876511027863317 59798207384836454431093)
                ·
                  rfl

theorem cell22_1572164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 6].length) (baseStart_1572164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572164 prefixEnd_1572164 := by exact prefixLift 1572164
  have htrace : WordTrace (prefixWord ++ tailWord_1572164) baseStart_1572164 baseEnd_1572164 := by
    simpa [prefixWord, tailWord_1572164, baseEnd_1572164] using wordTrace_append hprefix tailTrace_1572164
  have hstable : (prefixWord ++ tailWord_1572164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572164).length < 2 ^ (prefixWord ++ tailWord_1572164).sum := by decide
  have hdescent : baseEnd_1572164 < baseStart_1572164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572220 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_1572220 : Nat := 118140960795 + 1572220 * 2 ^ 59
def prefixEnd_1572220 : Nat := 4983230072969 + 3 ^ 40 * 1572220 * 2
def baseEnd_1572220 : Nat := 179401012135987536826555

theorem tailTrace_1572220 : CollatzResearch.WordTrace tailWord_1572220 prefixEnd_1572220 179401012135987536826555 := by
  unfold tailWord_1572220
  simp only [CollatzResearch.WordTrace]
  refine ⟨28671787182061464321817057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38229049576081952429089409 28671787182061464321817057)
  ·
    refine ⟨21503840386546098241362793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28671787182061464321817057 21503840386546098241362793)
    ·
      refine ⟨16127880289909573681022095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21503840386546098241362793 16127880289909573681022095)
      ·
        refine ⟨24191820434864360521533143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16127880289909573681022095 24191820434864360521533143)
        ·
          refine ⟨36287730652296540782299715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24191820434864360521533143 36287730652296540782299715)
          ·
            refine ⟨54431595978444811173449573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36287730652296540782299715 54431595978444811173449573)
            ·
              refine ⟨10205924245958402095021795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54431595978444811173449573 10205924245958402095021795)
              ·
                refine ⟨15308886368937603142532693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10205924245958402095021795 15308886368937603142532693)
                ·
                  refine ⟨179401012135987536826555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15308886368937603142532693 179401012135987536826555)
                  ·
                    rfl

theorem cell22_1572220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_1572220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572220 prefixEnd_1572220 := by exact prefixLift 1572220
  have htrace : WordTrace (prefixWord ++ tailWord_1572220) baseStart_1572220 baseEnd_1572220 := by
    simpa [prefixWord, tailWord_1572220, baseEnd_1572220] using wordTrace_append hprefix tailTrace_1572220
  have hstable : (prefixWord ++ tailWord_1572220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572220).length < 2 ^ (prefixWord ++ tailWord_1572220).sum := by decide
  have hdescent : baseEnd_1572220 < baseStart_1572220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572269 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1572269 : Nat := 118140960795 + 1572269 * 2 ^ 59
def prefixEnd_1572269 : Nat := 4983230072969 + 3 ^ 40 * 1572269 * 2
def baseEnd_1572269 : Nat := 538219810109342816004515

theorem tailTrace_1572269 : CollatzResearch.WordTrace tailWord_1572269 prefixEnd_1572269 538219810109342816004515 := by
  unfold tailWord_1572269
  simp only [CollatzResearch.WordTrace]
  refine ⟨57345361540945410012167861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38230241027296940008111907 57345361540945410012167861)
  ·
    refine ⟨5376127644463632188640737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57345361540945410012167861 5376127644463632188640737)
    ·
      refine ⟨4032095733347724141480553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5376127644463632188640737 4032095733347724141480553)
      ·
        refine ⟨3024071800010793106110415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4032095733347724141480553 3024071800010793106110415)
        ·
          refine ⟨4536107700016189659165623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024071800010793106110415 4536107700016189659165623)
          ·
            refine ⟨6804161550024284488748435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536107700016189659165623 6804161550024284488748435)
            ·
              refine ⟨10206242325036426733122653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804161550024284488748435 10206242325036426733122653)
              ·
                refine ⟨3827340871888660024920995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10206242325036426733122653 3827340871888660024920995)
                ·
                  refine ⟨5741011307832990037381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827340871888660024920995 5741011307832990037381493)
                  ·
                    refine ⟨538219810109342816004515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5741011307832990037381493 538219810109342816004515)
                    ·
                      rfl

theorem cell22_1572269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1572269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572269 prefixEnd_1572269 := by exact prefixLift 1572269
  have htrace : WordTrace (prefixWord ++ tailWord_1572269) baseStart_1572269 baseEnd_1572269 := by
    simpa [prefixWord, tailWord_1572269, baseEnd_1572269] using wordTrace_append hprefix tailTrace_1572269
  have hstable : (prefixWord ++ tailWord_1572269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572269).length < 2 ^ (prefixWord ++ tailWord_1572269).sum := by decide
  have hdescent : baseEnd_1572269 < baseStart_1572269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572284 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_1572284 : Nat := 118140960795 + 1572284 * 2 ^ 59
def prefixEnd_1572284 : Nat := 4983230072969 + 3 ^ 40 * 1572284 * 2
def baseEnd_1572284 : Nat := 538224944915887776879469

theorem tailTrace_1572284 : CollatzResearch.WordTrace tailWord_1572284 prefixEnd_1572284 538224944915887776879469 := by
  unfold tailWord_1572284
  simp only [CollatzResearch.WordTrace]
  refine ⟨28672954317945533786981953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38230605757260711715975937 28672954317945533786981953)
  ·
    refine ⟨21504715738459150340236465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28672954317945533786981953 21504715738459150340236465)
    ·
      refine ⟨16128536803844362755177349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21504715738459150340236465 16128536803844362755177349)
      ·
        refine ⟨3024100650720818016595753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16128536803844362755177349 3024100650720818016595753)
        ·
          refine ⟨2268075488040613512446815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024100650720818016595753 2268075488040613512446815)
          ·
            refine ⟨3402113232060920268670223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268075488040613512446815 3402113232060920268670223)
            ·
              refine ⟨5103169848091380403005335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402113232060920268670223 5103169848091380403005335)
              ·
                refine ⟨7654754772137070604508003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103169848091380403005335 7654754772137070604508003)
                ·
                  refine ⟨11482132158205605906762005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7654754772137070604508003 11482132158205605906762005)
                  ·
                    refine ⟨538224944915887776879469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11482132158205605906762005 538224944915887776879469)
                    ·
                      rfl

theorem cell22_1572284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_1572284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572284 prefixEnd_1572284 := by exact prefixLift 1572284
  have htrace : WordTrace (prefixWord ++ tailWord_1572284) baseStart_1572284 baseEnd_1572284 := by
    simpa [prefixWord, tailWord_1572284, baseEnd_1572284] using wordTrace_append hprefix tailTrace_1572284
  have hstable : (prefixWord ++ tailWord_1572284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572284).length < 2 ^ (prefixWord ++ tailWord_1572284).sum := by decide
  have hdescent : baseEnd_1572284 < baseStart_1572284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572297 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_1572297 : Nat := 118140960795 + 1572297 * 2 ^ 59
def prefixEnd_1572297 : Nat := 4983230072969 + 3 ^ 40 * 1572297 * 2
def baseEnd_1572297 : Nat := 538229395081560076304429

theorem tailTrace_1572297 : CollatzResearch.WordTrace tailWord_1572297 prefixEnd_1572297 538229395081560076304429 := by
  unfold tailWord_1572297
  simp only [CollatzResearch.WordTrace]
  refine ⟨57346382784843970794187145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38230921856562647196124763 57346382784843970794187145)
  ·
    refine ⟨43009787088632978095640359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57346382784843970794187145 43009787088632978095640359)
    ·
      refine ⟨64514680632949467143460539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43009787088632978095640359 64514680632949467143460539)
      ·
        refine ⟨96772020949424200715190809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64514680632949467143460539 96772020949424200715190809)
        ·
          refine ⟨72579015712068150536393107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96772020949424200715190809 72579015712068150536393107)
          ·
            refine ⟨108868523568102225804589661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72579015712068150536393107 108868523568102225804589661)
            ·
              refine ⟨40825696338038334676721123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108868523568102225804589661 40825696338038334676721123)
              ·
                refine ⟨61238544507057502015081685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40825696338038334676721123 61238544507057502015081685)
                ·
                  refine ⟨1435278386884160203478477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 61238544507057502015081685 1435278386884160203478477)
                  ·
                    refine ⟨538229395081560076304429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435278386884160203478477 538229395081560076304429)
                    ·
                      rfl

theorem cell22_1572297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_1572297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572297 prefixEnd_1572297 := by exact prefixLift 1572297
  have htrace : WordTrace (prefixWord ++ tailWord_1572297) baseStart_1572297 baseEnd_1572297 := by
    simpa [prefixWord, tailWord_1572297, baseEnd_1572297] using wordTrace_append hprefix tailTrace_1572297
  have hstable : (prefixWord ++ tailWord_1572297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572297).length < 2 ^ (prefixWord ++ tailWord_1572297).sum := by decide
  have hdescent : baseEnd_1572297 < baseStart_1572297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572314 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_1572314 : Nat := 118140960795 + 1572314 * 2 ^ 59
def prefixEnd_1572314 : Nat := 4983230072969 + 3 ^ 40 * 1572314 * 2
def baseEnd_1572314 : Nat := 538235214528977698629377

theorem tailTrace_1572314 : CollatzResearch.WordTrace tailWord_1572314 prefixEnd_1572314 538235214528977698629377 := by
  unfold tailWord_1572314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14336750706445595674388999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38231335217188255131703997 14336750706445595674388999)
  ·
    refine ⟨21505126059668393511583499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14336750706445595674388999 21505126059668393511583499)
    ·
      refine ⟨32257689089502590267375249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21505126059668393511583499 32257689089502590267375249)
      ·
        refine ⟨24193266817126942700531437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32257689089502590267375249 24193266817126942700531437)
        ·
          refine ⟨9072475056422603512699289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24193266817126942700531437 9072475056422603512699289)
          ·
            refine ⟨6804356292316952634524467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9072475056422603512699289 6804356292316952634524467)
            ·
              refine ⟨10206534438475428951786701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804356292316952634524467 10206534438475428951786701)
              ·
                refine ⟨3827450414428285856920013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10206534438475428951786701 3827450414428285856920013)
                ·
                  refine ⟨1435293905410607196345005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3827450414428285856920013 1435293905410607196345005)
                  ·
                    refine ⟨538235214528977698629377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435293905410607196345005 538235214528977698629377)
                    ·
                      rfl

theorem cell22_1572314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_1572314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572314 prefixEnd_1572314 := by exact prefixLift 1572314
  have htrace : WordTrace (prefixWord ++ tailWord_1572314) baseStart_1572314 baseEnd_1572314 := by
    simpa [prefixWord, tailWord_1572314, baseEnd_1572314] using wordTrace_append hprefix tailTrace_1572314
  have hstable : (prefixWord ++ tailWord_1572314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572314).length < 2 ^ (prefixWord ++ tailWord_1572314).sum := by decide
  have hdescent : baseEnd_1572314 < baseStart_1572314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572333 : List Nat := [1, 5, 1, 3, 3, 1, 2, 6]
def baseStart_1572333 : Nat := 118140960795 + 1572333 * 2 ^ 59
def prefixEnd_1572333 : Nat := 4983230072969 + 3 ^ 40 * 1572333 * 2
def baseEnd_1572333 : Nat := 59804635401918664711591

theorem tailTrace_1572333 : CollatzResearch.WordTrace tailWord_1572333 prefixEnd_1572333 59804635401918664711591 := by
  unfold tailWord_1572333
  simp only [CollatzResearch.WordTrace]
  refine ⟨57347695812713548942497653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38231797208475699294998435 57347695812713548942497653)
  ·
    refine ⟨5376346482441895213359155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57347695812713548942497653 5376346482441895213359155)
    ·
      refine ⟨8064519723662842820038733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376346482441895213359155 8064519723662842820038733)
      ·
        refine ⟨3024194896373566057514525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8064519723662842820038733 3024194896373566057514525)
        ·
          refine ⟨1134073086140087271567947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3024194896373566057514525 1134073086140087271567947)
          ·
            refine ⟨1701109629210130907351921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134073086140087271567947 1701109629210130907351921)
            ·
              refine ⟨1275832221907598180513941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701109629210130907351921 1275832221907598180513941)
              ·
                refine ⟨59804635401918664711591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1275832221907598180513941 59804635401918664711591)
                ·
                  rfl

theorem cell22_1572333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 6].length) (baseStart_1572333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572333 prefixEnd_1572333 := by exact prefixLift 1572333
  have htrace : WordTrace (prefixWord ++ tailWord_1572333) baseStart_1572333 baseEnd_1572333 := by
    simpa [prefixWord, tailWord_1572333, baseEnd_1572333] using wordTrace_append hprefix tailTrace_1572333
  have hstable : (prefixWord ++ tailWord_1572333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572333).length < 2 ^ (prefixWord ++ tailWord_1572333).sum := by decide
  have hdescent : baseEnd_1572333 < baseStart_1572333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572357 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_1572357 : Nat := 118140960795 + 1572357 * 2 ^ 59
def prefixEnd_1572357 : Nat := 4983230072969 + 3 ^ 40 * 1572357 * 2
def baseEnd_1572357 : Nat := 538249934307739919804245

theorem tailTrace_1572357 : CollatzResearch.WordTrace tailWord_1572357 prefixEnd_1572357 538249934307739919804245 := by
  unfold tailWord_1572357
  simp only [CollatzResearch.WordTrace]
  refine ⟨57348571164626601041371325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38232380776417734027580883 57348571164626601041371325)
  ·
    refine ⟨21505714186734975390514247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57348571164626601041371325 21505714186734975390514247)
    ·
      refine ⟨32258571280102463085771371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21505714186734975390514247 32258571280102463085771371)
      ·
        refine ⟨48387856920153694628657057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32258571280102463085771371 48387856920153694628657057)
        ·
          refine ⟨36290892690115270971492793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48387856920153694628657057 36290892690115270971492793)
          ·
            refine ⟨27218169517586453228619595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36290892690115270971492793 27218169517586453228619595)
            ·
              refine ⟨40827254276379679842929393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27218169517586453228619595 40827254276379679842929393)
              ·
                refine ⟨30620440707284759882197045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40827254276379679842929393 30620440707284759882197045)
                ·
                  refine ⟨2870666316307946238955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30620440707284759882197045 2870666316307946238955973)
                  ·
                    refine ⟨538249934307739919804245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2870666316307946238955973 538249934307739919804245)
                    ·
                      rfl

theorem cell22_1572357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_1572357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572357 prefixEnd_1572357 := by exact prefixLift 1572357
  have htrace : WordTrace (prefixWord ++ tailWord_1572357) baseStart_1572357 baseEnd_1572357 := by
    simpa [prefixWord, tailWord_1572357, baseEnd_1572357] using wordTrace_append hprefix tailTrace_1572357
  have hstable : (prefixWord ++ tailWord_1572357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572357).length < 2 ^ (prefixWord ++ tailWord_1572357).sum := by decide
  have hdescent : baseEnd_1572357 < baseStart_1572357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572421 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_1572421 : Nat := 118140960795 + 1572421 * 2 ^ 59
def prefixEnd_1572421 : Nat := 4983230072969 + 3 ^ 40 * 1572421 * 2
def baseEnd_1572421 : Nat := 538271842815665086204049

theorem tailTrace_1572421 : CollatzResearch.WordTrace tailWord_1572421 prefixEnd_1572421 538271842815665086204049 := by
  unfold tailWord_1572421
  simp only [CollatzResearch.WordTrace]
  refine ⟨57350905436394739971701117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38233936957596493314467411 57350905436394739971701117)
  ·
    refine ⟨21506589538648027489387919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57350905436394739971701117 21506589538648027489387919)
    ·
      refine ⟨32259884307972041234081879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21506589538648027489387919 32259884307972041234081879)
      ·
        refine ⟨48389826461958061851122819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32259884307972041234081879 48389826461958061851122819)
        ·
          refine ⟨72584739692937092776684229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48389826461958061851122819 72584739692937092776684229)
          ·
            refine ⟨13609638692425704895628293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72584739692937092776684229 13609638692425704895628293)
            ·
              refine ⟨2551807254829819667930305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13609638692425704895628293 2551807254829819667930305)
              ·
                refine ⟨1913855441122364750947729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2551807254829819667930305 1913855441122364750947729)
                ·
                  refine ⟨1435391580841773563210797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1913855441122364750947729 1435391580841773563210797)
                  ·
                    refine ⟨538271842815665086204049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435391580841773563210797 538271842815665086204049)
                    ·
                      rfl

theorem cell22_1572421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_1572421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572421 prefixEnd_1572421 := by exact prefixLift 1572421
  have htrace : WordTrace (prefixWord ++ tailWord_1572421) baseStart_1572421 baseEnd_1572421 := by
    simpa [prefixWord, tailWord_1572421, baseEnd_1572421] using wordTrace_append hprefix tailTrace_1572421
  have hstable : (prefixWord ++ tailWord_1572421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572421).length < 2 ^ (prefixWord ++ tailWord_1572421).sum := by decide
  have hdescent : baseEnd_1572421 < baseStart_1572421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572434 : List Nat := [3, 2, 2, 1, 2, 2, 3, 7]
def baseStart_1572434 : Nat := 118140960795 + 1572434 * 2 ^ 59
def prefixEnd_1572434 : Nat := 4983230072969 + 3 ^ 40 * 1572434 * 2
def baseEnd_1572434 : Nat := 59808476997926376181001

theorem tailTrace_1572434 : CollatzResearch.WordTrace tailWord_1572434 prefixEnd_1572434 59808476997926376181001 := by
  unfold tailWord_1572434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337844896336910797981089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38234253056898428794616237 14337844896336910797981089)
  ·
    refine ⟨10753383672252683098485817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14337844896336910797981089 10753383672252683098485817)
    ·
      refine ⟨8065037754189512323864363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10753383672252683098485817 8065037754189512323864363)
      ·
        refine ⟨12097556631284268485796545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8065037754189512323864363 12097556631284268485796545)
        ·
          refine ⟨9073167473463201364347409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12097556631284268485796545 9073167473463201364347409)
          ·
            refine ⟨6804875605097401023260557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9073167473463201364347409 6804875605097401023260557)
            ·
              refine ⟨2551828351911525383722709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6804875605097401023260557 2551828351911525383722709)
              ·
                refine ⟨59808476997926376181001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2551828351911525383722709 59808476997926376181001)
                ·
                  rfl

theorem cell22_1572434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_1572434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572434 prefixEnd_1572434 := by exact prefixLift 1572434
  have htrace : WordTrace (prefixWord ++ tailWord_1572434) baseStart_1572434 baseEnd_1572434 := by
    simpa [prefixWord, tailWord_1572434, baseEnd_1572434] using wordTrace_append hprefix tailTrace_1572434
  have hstable : (prefixWord ++ tailWord_1572434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572434).length < 2 ^ (prefixWord ++ tailWord_1572434).sum := by decide
  have hdescent : baseEnd_1572434 < baseStart_1572434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572534 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1572534 : Nat := 118140960795 + 1572534 * 2 ^ 59
def prefixEnd_1572534 : Nat := 4983230072969 + 3 ^ 40 * 1572534 * 2
def baseEnd_1572534 : Nat := 538310525024970458128703

theorem tailTrace_1572534 : CollatzResearch.WordTrace tailWord_1572534 prefixEnd_1572534 538310525024970458128703 := by
  unfold tailWord_1572534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3584689180311585016910291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38236684589990240180376437 3584689180311585016910291)
  ·
    refine ⟨5377033770467377525365437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3584689180311585016910291 5377033770467377525365437)
    ·
      refine ⟨2016387663925266572012039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5377033770467377525365437 2016387663925266572012039)
      ·
        refine ⟨3024581495887899858018059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016387663925266572012039 3024581495887899858018059)
        ·
          refine ⟨4536872243831849787027089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024581495887899858018059 4536872243831849787027089)
          ·
            refine ⟨3402654182873887340270317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4536872243831849787027089 3402654182873887340270317)
            ·
              refine ⟨1275995318577707752601369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3402654182873887340270317 1275995318577707752601369)
              ·
                refine ⟨956996488933280814451027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275995318577707752601369 956996488933280814451027)
                ·
                  refine ⟨1435494733399921221676541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956996488933280814451027 1435494733399921221676541)
                  ·
                    refine ⟨538310525024970458128703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435494733399921221676541 538310525024970458128703)
                    ·
                      rfl

theorem cell22_1572534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1572534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572534 prefixEnd_1572534 := by exact prefixLift 1572534
  have htrace : WordTrace (prefixWord ++ tailWord_1572534) baseStart_1572534 baseEnd_1572534 := by
    simpa [prefixWord, tailWord_1572534, baseEnd_1572534] using wordTrace_append hprefix tailTrace_1572534
  have hstable : (prefixWord ++ tailWord_1572534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572534).length < 2 ^ (prefixWord ++ tailWord_1572534).sum := by decide
  have hdescent : baseEnd_1572534 < baseStart_1572534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572569 : List Nat := [1, 2, 1, 2, 3, 3, 2, 8]
def baseStart_1572569 : Nat := 118140960795 + 1572569 * 2 ^ 59
def prefixEnd_1572569 : Nat := 4983230072969 + 3 ^ 40 * 1572569 * 2
def baseEnd_1572569 : Nat := 59813611804471337055955

theorem tailTrace_1572569 : CollatzResearch.WordTrace tailWord_1572569 prefixEnd_1572569 59813611804471337055955 := by
  unfold tailWord_1572569
  simp only [CollatzResearch.WordTrace]
  refine ⟨57356303439858561248088761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38237535626572374165392507 57356303439858561248088761)
  ·
    refine ⟨43017227579893920936066571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57356303439858561248088761 43017227579893920936066571)
    ·
      refine ⟨64525841369840881404099857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43017227579893920936066571 64525841369840881404099857)
      ·
        refine ⟨48394381027380661053074893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64525841369840881404099857 48394381027380661053074893)
        ·
          refine ⟨18147892885267747894903085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48394381027380661053074893 18147892885267747894903085)
          ·
            refine ⟨6805459831975405460588657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18147892885267747894903085 6805459831975405460588657)
            ·
              refine ⟨5104094873981554095441493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6805459831975405460588657 5104094873981554095441493)
              ·
                refine ⟨59813611804471337055955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5104094873981554095441493 59813611804471337055955)
                ·
                  rfl

theorem cell22_1572569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 8].length) (baseStart_1572569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572569 prefixEnd_1572569 := by exact prefixLift 1572569
  have htrace : WordTrace (prefixWord ++ tailWord_1572569) baseStart_1572569 baseEnd_1572569 := by
    simpa [prefixWord, tailWord_1572569, baseEnd_1572569] using wordTrace_append hprefix tailTrace_1572569
  have hstable : (prefixWord ++ tailWord_1572569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572569).length < 2 ^ (prefixWord ++ tailWord_1572569).sum := by decide
  have hdescent : baseEnd_1572569 < baseStart_1572569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572599 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1572599 : Nat := 118140960795 + 1572599 * 2 ^ 59
def prefixEnd_1572599 : Nat := 4983230072969 + 3 ^ 40 * 1572599 * 2
def baseEnd_1572599 : Nat := 538332775853331955253503

theorem tailTrace_1572599 : CollatzResearch.WordTrace tailWord_1572599 prefixEnd_1572599 538332775853331955253503 := by
  unfold tailWord_1572599
  simp only [CollatzResearch.WordTrace]
  refine ⟨57357397629749876371680851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38238265086499917581120567 57357397629749876371680851)
  ·
    refine ⟨86036096444624814557521277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57357397629749876371680851 86036096444624814557521277)
    ·
      refine ⟨32263536166734305459070479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86036096444624814557521277 32263536166734305459070479)
      ·
        refine ⟨48395304250101458188605719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32263536166734305459070479 48395304250101458188605719)
        ·
          refine ⟨72592956375152187282908579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48395304250101458188605719 72592956375152187282908579)
          ·
            refine ⟨108889434562728280924362869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72592956375152187282908579 108889434562728280924362869)
            ·
              refine ⟨10208384490255776336659019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108889434562728280924362869 10208384490255776336659019)
              ·
                refine ⟨15312576735383664504988529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10208384490255776336659019 15312576735383664504988529)
                ·
                  refine ⟨11484432551537748378741397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15312576735383664504988529 11484432551537748378741397)
                  ·
                    refine ⟨538332775853331955253503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11484432551537748378741397 538332775853331955253503)
                    ·
                      rfl

theorem cell22_1572599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1572599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572599 prefixEnd_1572599 := by exact prefixLift 1572599
  have htrace : WordTrace (prefixWord ++ tailWord_1572599) baseStart_1572599 baseEnd_1572599 := by
    simpa [prefixWord, tailWord_1572599, baseEnd_1572599] using wordTrace_append hprefix tailTrace_1572599
  have hstable : (prefixWord ++ tailWord_1572599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572599).length < 2 ^ (prefixWord ++ tailWord_1572599).sum := by decide
  have hdescent : baseEnd_1572599 < baseStart_1572599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572618 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1572618 : Nat := 118140960795 + 1572618 * 2 ^ 59
def prefixEnd_1572618 : Nat := 4983230072969 + 3 ^ 40 * 1572618 * 2
def baseEnd_1572618 : Nat := 538339279941622239028445

theorem tailTrace_1572618 : CollatzResearch.WordTrace tailWord_1572618 prefixEnd_1572618 538339279941622239028445 := by
  unfold tailWord_1572618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339522654170260654155627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38238727077787361744415005 14339522654170260654155627)
  ·
    refine ⟨21509283981255390981233441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14339522654170260654155627 21509283981255390981233441)
    ·
      refine ⟨16131962985941543235925081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21509283981255390981233441 16131962985941543235925081)
      ·
        refine ⟨12098972239456157426943811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16131962985941543235925081 12098972239456157426943811)
        ·
          refine ⟨18148458359184236140415717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12098972239456157426943811 18148458359184236140415717)
          ·
            refine ⟨3402835942347044276327947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18148458359184236140415717 3402835942347044276327947)
            ·
              refine ⟨5104253913520566414491921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402835942347044276327947 5104253913520566414491921)
              ·
                refine ⟨3828190435140424810868941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104253913520566414491921 3828190435140424810868941)
                ·
                  refine ⟨1435571413177659304075853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3828190435140424810868941 1435571413177659304075853)
                  ·
                    refine ⟨538339279941622239028445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435571413177659304075853 538339279941622239028445)
                    ·
                      rfl

theorem cell22_1572618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1572618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572618 prefixEnd_1572618 := by exact prefixLift 1572618
  have htrace : WordTrace (prefixWord ++ tailWord_1572618) baseStart_1572618 baseEnd_1572618 := by
    simpa [prefixWord, tailWord_1572618, baseEnd_1572618] using wordTrace_append hprefix tailTrace_1572618
  have hstable : (prefixWord ++ tailWord_1572618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572618).length < 2 ^ (prefixWord ++ tailWord_1572618).sum := by decide
  have hdescent : baseEnd_1572618 < baseStart_1572618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572648 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_1572648 : Nat := 118140960795 + 1572648 * 2 ^ 59
def prefixEnd_1572648 : Nat := 4983230072969 + 3 ^ 40 * 1572648 * 2
def baseEnd_1572648 : Nat := 179449849851570720259451

theorem tailTrace_1572648 : CollatzResearch.WordTrace tailWord_1572648 prefixEnd_1572648 179449849851570720259451 := by
  unfold tailWord_1572648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679592403286178870107299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38239456537714905160143065 28679592403286178870107299)
  ·
    refine ⟨43019388604929268305160949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28679592403286178870107299 43019388604929268305160949)
    ·
      refine ⟨4033067681712118903608839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43019388604929268305160949 4033067681712118903608839)
      ·
        refine ⟨6049601522568178355413259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033067681712118903608839 6049601522568178355413259)
        ·
          refine ⟨9074402283852267533119889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049601522568178355413259 9074402283852267533119889)
          ·
            refine ⟨6805801712889200649839917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9074402283852267533119889 6805801712889200649839917)
            ·
              refine ⟨2552175642333450243689969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6805801712889200649839917 2552175642333450243689969)
              ·
                refine ⟨1914131731750087682767477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552175642333450243689969 1914131731750087682767477)
                ·
                  refine ⟨179449849851570720259451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1914131731750087682767477 179449849851570720259451)
                  ·
                    rfl

theorem cell22_1572648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_1572648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572648 prefixEnd_1572648 := by exact prefixLift 1572648
  have htrace : WordTrace (prefixWord ++ tailWord_1572648) baseStart_1572648 baseEnd_1572648 := by
    simpa [prefixWord, tailWord_1572648, baseEnd_1572648] using wordTrace_append hprefix tailTrace_1572648
  have hstable : (prefixWord ++ tailWord_1572648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572648).length < 2 ^ (prefixWord ++ tailWord_1572648).sum := by decide
  have hdescent : baseEnd_1572648 < baseStart_1572648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572721 : List Nat := [1, 2, 2, 2, 1, 3, 4, 7]
def baseStart_1572721 : Nat := 118140960795 + 1572721 * 2 ^ 59
def prefixEnd_1572721 : Nat := 4983230072969 + 3 ^ 40 * 1572721 * 2
def baseEnd_1572721 : Nat := 59819393216284922633681

theorem tailTrace_1572721 : CollatzResearch.WordTrace tailWord_1572721 prefixEnd_1572721 59819393216284922633681 := by
  unfold tailWord_1572721
  simp only [CollatzResearch.WordTrace]
  refine ⟨57361847335307891207622017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38241231556871927471748011 57361847335307891207622017)
  ·
    refine ⟨43021385501480918405716513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57361847335307891207622017 43021385501480918405716513)
    ·
      refine ⟨32266039126110688804287385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43021385501480918405716513 32266039126110688804287385)
      ·
        refine ⟨24199529344583016603215539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32266039126110688804287385 24199529344583016603215539)
        ·
          refine ⟨36299294016874524904823309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24199529344583016603215539 36299294016874524904823309)
          ·
            refine ⟨13612235256327946839308741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36299294016874524904823309 13612235256327946839308741)
            ·
              refine ⟨2552294110561490032370389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13612235256327946839308741 2552294110561490032370389)
              ·
                refine ⟨59819393216284922633681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2552294110561490032370389 59819393216284922633681)
                ·
                  rfl

theorem cell22_1572721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 7].length) (baseStart_1572721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572721 prefixEnd_1572721 := by exact prefixLift 1572721
  have htrace : WordTrace (prefixWord ++ tailWord_1572721) baseStart_1572721 baseEnd_1572721 := by
    simpa [prefixWord, tailWord_1572721, baseEnd_1572721] using wordTrace_append hprefix tailTrace_1572721
  have hstable : (prefixWord ++ tailWord_1572721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572721).length < 2 ^ (prefixWord ++ tailWord_1572721).sum := by decide
  have hdescent : baseEnd_1572721 < baseStart_1572721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572725 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1572725 : Nat := 118140960795 + 1572725 * 2 ^ 59
def prefixEnd_1572725 : Nat := 4983230072969 + 3 ^ 40 * 1572725 * 2
def baseEnd_1572725 : Nat := 538375908228309626603117

theorem tailTrace_1572725 : CollatzResearch.WordTrace tailWord_1572725 prefixEnd_1572725 538375908228309626603117 := by
  unfold tailWord_1572725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57361993227293399890767629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38241328818195599927178419 57361993227293399890767629)
  ·
    refine ⟨21510747460235024959037861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57361993227293399890767629 21510747460235024959037861)
    ·
      refine ⟨4033265148794067179819599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21510747460235024959037861 4033265148794067179819599)
      ·
        refine ⟨6049897723191100769729399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033265148794067179819599 6049897723191100769729399)
        ·
          refine ⟨9074846584786651154594099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049897723191100769729399 9074846584786651154594099)
          ·
            refine ⟨13612269877179976731891149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074846584786651154594099 13612269877179976731891149)
            ·
              refine ⟨5104601203942491274459181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13612269877179976731891149 5104601203942491274459181)
              ·
                refine ⟨1914225451478434227922193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5104601203942491274459181 1914225451478434227922193)
                ·
                  refine ⟨1435669088608825670941645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1914225451478434227922193 1435669088608825670941645)
                  ·
                    refine ⟨538375908228309626603117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435669088608825670941645 538375908228309626603117)
                    ·
                      rfl

theorem cell22_1572725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1572725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572725 prefixEnd_1572725 := by exact prefixLift 1572725
  have htrace : WordTrace (prefixWord ++ tailWord_1572725) baseStart_1572725 baseEnd_1572725 := by
    simpa [prefixWord, tailWord_1572725, baseEnd_1572725] using wordTrace_append hprefix tailTrace_1572725
  have hstable : (prefixWord ++ tailWord_1572725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572725).length < 2 ^ (prefixWord ++ tailWord_1572725).sum := by decide
  have hdescent : baseEnd_1572725 < baseStart_1572725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572811 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 8]
def baseStart_1572811 : Nat := 118140960795 + 1572811 * 2 ^ 59
def prefixEnd_1572811 : Nat := 4983230072969 + 3 ^ 40 * 1572811 * 2
def baseEnd_1572811 : Nat := 179468449261944689650951

theorem tailTrace_1572811 : CollatzResearch.WordTrace tailWord_1572811 prefixEnd_1572811 179468449261944689650951 := by
  unfold tailWord_1572811
  simp only [CollatzResearch.WordTrace]
  refine ⟨57365129904981836578398287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38243419936654557718932191 57365129904981836578398287)
  ·
    refine ⟨86047694857472754867597431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57365129904981836578398287 86047694857472754867597431)
    ·
      refine ⟨129071542286209132301396147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86047694857472754867597431 129071542286209132301396147)
      ·
        refine ⟨193607313429313698452094221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129071542286209132301396147 193607313429313698452094221)
        ·
          refine ⟨72602742535992636919535333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193607313429313698452094221 72602742535992636919535333)
          ·
            refine ⟨13613014225498619422412875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72602742535992636919535333 13613014225498619422412875)
            ·
              refine ⟨20419521338247929133619313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13613014225498619422412875 20419521338247929133619313)
              ·
                refine ⟨15314641003685946850214485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20419521338247929133619313 15314641003685946850214485)
                ·
                  refine ⟨179468449261944689650951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15314641003685946850214485 179468449261944689650951)
                  ·
                    rfl

theorem cell22_1572811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_1572811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572811 prefixEnd_1572811 := by exact prefixLift 1572811
  have htrace : WordTrace (prefixWord ++ tailWord_1572811) baseStart_1572811 baseEnd_1572811 := by
    simpa [prefixWord, tailWord_1572811, baseEnd_1572811] using wordTrace_append hprefix tailTrace_1572811
  have hstable : (prefixWord ++ tailWord_1572811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572811).length < 2 ^ (prefixWord ++ tailWord_1572811).sum := by decide
  have hdescent : baseEnd_1572811 < baseStart_1572811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572834 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1572834 : Nat := 118140960795 + 1572834 * 2 ^ 59
def prefixEnd_1572834 : Nat := 4983230072969 + 3 ^ 40 * 1572834 * 2
def baseEnd_1572834 : Nat := 179471073718623225209261

theorem tailTrace_1572834 : CollatzResearch.WordTrace tailWord_1572834 prefixEnd_1572834 179471073718623225209261 := by
  unfold tailWord_1572834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14341492195974627876621389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38243979189265674337657037 14341492195974627876621389)
  ·
    refine ⟨5378059573490485453733021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14341492195974627876621389 5378059573490485453733021)
    ·
      refine ⟨2016772340058932045149883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5378059573490485453733021 2016772340058932045149883)
      ·
        refine ⟨3025158510088398067724825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016772340058932045149883 3025158510088398067724825)
        ·
          refine ⟨2268868882566298550793619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3025158510088398067724825 2268868882566298550793619)
          ·
            refine ⟨3403303323849447826190429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268868882566298550793619 3403303323849447826190429)
            ·
              refine ⟨1276238746443542934821411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3403303323849447826190429 1276238746443542934821411)
              ·
                refine ⟨1914358119665314402232117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276238746443542934821411 1914358119665314402232117)
                ·
                  refine ⟨179471073718623225209261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1914358119665314402232117 179471073718623225209261)
                  ·
                    rfl

theorem cell22_1572834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1572834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572834 prefixEnd_1572834 := by exact prefixLift 1572834
  have htrace : WordTrace (prefixWord ++ tailWord_1572834) baseStart_1572834 baseEnd_1572834 := by
    simpa [prefixWord, tailWord_1572834, baseEnd_1572834] using wordTrace_append hprefix tailTrace_1572834
  have hstable : (prefixWord ++ tailWord_1572834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572834).length < 2 ^ (prefixWord ++ tailWord_1572834).sum := by decide
  have hdescent : baseEnd_1572834 < baseStart_1572834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572922 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_1572922 : Nat := 118140960795 + 1572922 * 2 ^ 59
def prefixEnd_1572922 : Nat := 4983230072969 + 3 ^ 40 * 1572922 * 2
def baseEnd_1572922 : Nat := 538443345354266779427513

theorem tailTrace_1572922 : CollatzResearch.WordTrace tailWord_1572922 prefixEnd_1572922 538443345354266779427513 := by
  unfold tailWord_1572922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14342294601894925633922255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38246118938386468357126013 14342294601894925633922255)
  ·
    refine ⟨21513441902842388450883383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14342294601894925633922255 21513441902842388450883383)
    ·
      refine ⟨32270162854263582676325075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21513441902842388450883383 32270162854263582676325075)
      ·
        refine ⟨48405244281395374014487613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32270162854263582676325075 48405244281395374014487613)
        ·
          refine ⟨18151966605523265255432855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48405244281395374014487613 18151966605523265255432855)
          ·
            refine ⟨27227949908284897883149283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18151966605523265255432855 27227949908284897883149283)
            ·
              refine ⟨40841924862427346824723925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27227949908284897883149283 40841924862427346824723925)
              ·
                refine ⟨957232613963140941204467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40841924862427346824723925 957232613963140941204467)
                ·
                  refine ⟨1435848920944711411806701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957232613963140941204467 1435848920944711411806701)
                  ·
                    refine ⟨538443345354266779427513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1435848920944711411806701 538443345354266779427513)
                    ·
                      rfl

theorem cell22_1572922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_1572922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572922 prefixEnd_1572922 := by exact prefixLift 1572922
  have htrace : WordTrace (prefixWord ++ tailWord_1572922) baseStart_1572922 baseEnd_1572922 := by
    simpa [prefixWord, tailWord_1572922, baseEnd_1572922] using wordTrace_append hprefix tailTrace_1572922
  have hstable : (prefixWord ++ tailWord_1572922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572922).length < 2 ^ (prefixWord ++ tailWord_1572922).sum := by decide
  have hdescent : baseEnd_1572922 < baseStart_1572922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572933 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_1572933 : Nat := 118140960795 + 1572933 * 2 ^ 59
def prefixEnd_1572933 : Nat := 4983230072969 + 3 ^ 40 * 1572933 * 2
def baseEnd_1572933 : Nat := 538447110879066417402479

theorem tailTrace_1572933 : CollatzResearch.WordTrace tailWord_1572933 prefixEnd_1572933 538447110879066417402479 := by
  unfold tailWord_1572933
  simp only [CollatzResearch.WordTrace]
  refine ⟨57369579610539851414339453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38246386407026567609559635 57369579610539851414339453)
  ·
    refine ⟨21513592353952444280377295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57369579610539851414339453 21513592353952444280377295)
    ·
      refine ⟨32270388530928666420565943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21513592353952444280377295 32270388530928666420565943)
      ·
        refine ⟨48405582796392999630848915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32270388530928666420565943 48405582796392999630848915)
        ·
          refine ⟨72608374194589499446273373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48405582796392999630848915 72608374194589499446273373)
          ·
            refine ⟨27228140322971062292352515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72608374194589499446273373 27228140322971062292352515)
            ·
              refine ⟨40842210484456593438528773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27228140322971062292352515 40842210484456593438528773)
              ·
                refine ⟨7657914465835611269724145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40842210484456593438528773 7657914465835611269724145)
                ·
                  refine ⟨5743435849376708452293109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657914465835611269724145 5743435849376708452293109)
                  ·
                    refine ⟨538447110879066417402479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5743435849376708452293109 538447110879066417402479)
                    ·
                      rfl

theorem cell22_1572933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_1572933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572933 prefixEnd_1572933 := by exact prefixLift 1572933
  have htrace : WordTrace (prefixWord ++ tailWord_1572933) baseStart_1572933 baseEnd_1572933 := by
    simpa [prefixWord, tailWord_1572933, baseEnd_1572933] using wordTrace_append hprefix tailTrace_1572933
  have hstable : (prefixWord ++ tailWord_1572933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572933).length < 2 ^ (prefixWord ++ tailWord_1572933).sum := by decide
  have hdescent : baseEnd_1572933 < baseStart_1572933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572935 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 5]
def baseStart_1572935 : Nat := 118140960795 + 1572935 * 2 ^ 59
def prefixEnd_1572935 : Nat := 4983230072969 + 3 ^ 40 * 1572935 * 2
def baseEnd_1572935 : Nat := 179482598506646359617491

theorem tailTrace_1572935 : CollatzResearch.WordTrace tailWord_1572935 prefixEnd_1572935 179482598506646359617491 := by
  unfold tailWord_1572935
  simp only [CollatzResearch.WordTrace]
  refine ⟨57369652556532605755912259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38246435037688403837274839 57369652556532605755912259)
  ·
    refine ⟨86054478834798908633868389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57369652556532605755912259 86054478834798908633868389)
    ·
      refine ⟨16135214781524795368850323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86054478834798908633868389 16135214781524795368850323)
      ·
        refine ⟨24202822172287193053275485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16135214781524795368850323 24202822172287193053275485)
        ·
          refine ⟨9076058314607697394978307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24202822172287193053275485 9076058314607697394978307)
          ·
            refine ⟨13614087471911546092467461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076058314607697394978307 13614087471911546092467461)
            ·
              refine ⟨2552641400983414892337649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13614087471911546092467461 2552641400983414892337649)
              ·
                refine ⟨1914481050737561169253237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552641400983414892337649 1914481050737561169253237)
                ·
                  refine ⟨179482598506646359617491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1914481050737561169253237 179482598506646359617491)
                  ·
                    rfl

theorem cell22_1572935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 5].length) (baseStart_1572935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572935 prefixEnd_1572935 := by exact prefixLift 1572935
  have htrace : WordTrace (prefixWord ++ tailWord_1572935) baseStart_1572935 baseEnd_1572935 := by
    simpa [prefixWord, tailWord_1572935, baseEnd_1572935] using wordTrace_append hprefix tailTrace_1572935
  have hstable : (prefixWord ++ tailWord_1572935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572935).length < 2 ^ (prefixWord ++ tailWord_1572935).sum := by decide
  have hdescent : baseEnd_1572935 < baseStart_1572935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572963 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 8]
def baseStart_1572963 : Nat := 118140960795 + 1572963 * 2 ^ 59
def prefixEnd_1572963 : Nat := 4983230072969 + 3 ^ 40 * 1572963 * 2
def baseEnd_1572963 : Nat := 179485793497385446384129

theorem tailTrace_1572963 : CollatzResearch.WordTrace tailWord_1572963 prefixEnd_1572963 179485793497385446384129 := by
  unfold tailWord_1572963
  simp only [CollatzResearch.WordTrace]
  refine ⟨57370673800431166537931543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38247115866954111025287695 57370673800431166537931543)
  ·
    refine ⟨86056010700646749806897315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57370673800431166537931543 86056010700646749806897315)
    ·
      refine ⟨129084016050970124710345973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86056010700646749806897315 129084016050970124710345973)
      ·
        refine ⟨12101626504778449191594935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129084016050970124710345973 12101626504778449191594935)
        ·
          refine ⟨18152439757167673787392403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12101626504778449191594935 18152439757167673787392403)
          ·
            refine ⟨27228659635751510681088605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152439757167673787392403 27228659635751510681088605)
            ·
              refine ⟨10210747363406816505408227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27228659635751510681088605 10210747363406816505408227)
              ·
                refine ⟨15316121045110224758112341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210747363406816505408227 15316121045110224758112341)
                ·
                  refine ⟨179485793497385446384129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15316121045110224758112341 179485793497385446384129)
                  ·
                    rfl

theorem cell22_1572963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_1572963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572963 prefixEnd_1572963 := by exact prefixLift 1572963
  have htrace : WordTrace (prefixWord ++ tailWord_1572963) baseStart_1572963 baseEnd_1572963 := by
    simpa [prefixWord, tailWord_1572963, baseEnd_1572963] using wordTrace_append hprefix tailTrace_1572963
  have hstable : (prefixWord ++ tailWord_1572963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572963).length < 2 ^ (prefixWord ++ tailWord_1572963).sum := by decide
  have hdescent : baseEnd_1572963 < baseStart_1572963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572965 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_1572965 : Nat := 118140960795 + 1572965 * 2 ^ 59
def prefixEnd_1572965 : Nat := 4983230072969 + 3 ^ 40 * 1572965 * 2
def baseEnd_1572965 : Nat := 538458065133029000602381

theorem tailTrace_1572965 : CollatzResearch.WordTrace tailWord_1572965 prefixEnd_1572965 538458065133029000602381 := by
  unfold tailWord_1572965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57370746746423920879504349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38247164497615947253002899 57370746746423920879504349)
  ·
    refine ⟨21514030029908970329814131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57370746746423920879504349 21514030029908970329814131)
    ·
      refine ⟨32271045044863455494721197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21514030029908970329814131 32271045044863455494721197)
      ·
        refine ⟨12101641891823795810520449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32271045044863455494721197 12101641891823795810520449)
        ·
          refine ⟨9076231418867846857890337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12101641891823795810520449 9076231418867846857890337)
          ·
            refine ⟨6807173564150885143417753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9076231418867846857890337 6807173564150885143417753)
            ·
              refine ⟨5105380173113163857563315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807173564150885143417753 5105380173113163857563315)
              ·
                refine ⟨7658070259669745786344973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105380173113163857563315 7658070259669745786344973)
                ·
                  refine ⟨2871776347376154669879365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7658070259669745786344973 2871776347376154669879365)
                  ·
                    refine ⟨538458065133029000602381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2871776347376154669879365 538458065133029000602381)
                    ·
                      rfl

theorem cell22_1572965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_1572965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572965 prefixEnd_1572965 := by exact prefixLift 1572965
  have htrace : WordTrace (prefixWord ++ tailWord_1572965) baseStart_1572965 baseEnd_1572965 := by
    simpa [prefixWord, tailWord_1572965, baseEnd_1572965] using wordTrace_append hprefix tailTrace_1572965
  have hstable : (prefixWord ++ tailWord_1572965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572965).length < 2 ^ (prefixWord ++ tailWord_1572965).sum := by decide
  have hdescent : baseEnd_1572965 < baseStart_1572965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572997 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 4]
def baseStart_1572997 : Nat := 118140960795 + 1572997 * 2 ^ 59
def prefixEnd_1572997 : Nat := 4983230072969 + 3 ^ 40 * 1572997 * 2
def baseEnd_1572997 : Nat := 179489673128997194600761

theorem tailTrace_1572997 : CollatzResearch.WordTrace tailWord_1572997 prefixEnd_1572997 179489673128997194600761 := by
  unfold tailWord_1572997
  simp only [CollatzResearch.WordTrace]
  refine ⟨57371913882307990344669245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38247942588205326896446163 57371913882307990344669245)
  ·
    refine ⟨21514467705865496379250967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57371913882307990344669245 21514467705865496379250967)
    ·
      refine ⟨32271701558798244568876451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21514467705865496379250967 32271701558798244568876451)
      ·
        refine ⟨48407552338197366853314677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32271701558798244568876451 48407552338197366853314677)
        ·
          refine ⟨4538208031706003142498251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48407552338197366853314677 4538208031706003142498251)
          ·
            refine ⟨6807312047559004713747377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538208031706003142498251 6807312047559004713747377)
            ·
              refine ⟨5105484035669253535310533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807312047559004713747377 5105484035669253535310533)
              ·
                refine ⟨957278256687985037870725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5105484035669253535310533 957278256687985037870725)
                ·
                  refine ⟨179489673128997194600761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957278256687985037870725 179489673128997194600761)
                  ·
                    rfl

theorem cell22_1572997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_1572997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1572997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1572997 prefixEnd_1572997 := by exact prefixLift 1572997
  have htrace : WordTrace (prefixWord ++ tailWord_1572997) baseStart_1572997 baseEnd_1572997 := by
    simpa [prefixWord, tailWord_1572997, baseEnd_1572997] using wordTrace_append hprefix tailTrace_1572997
  have hstable : (prefixWord ++ tailWord_1572997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572997).length < 2 ^ (prefixWord ++ tailWord_1572997).sum := by decide
  have hdescent : baseEnd_1572997 < baseStart_1572997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573008 : List Nat := [2, 1, 1, 1, 1, 1, 6, 9]
def baseStart_1573008 : Nat := 118140960795 + 1573008 * 2 ^ 59
def prefixEnd_1573008 : Nat := 4983230072969 + 3 ^ 40 * 1573008 * 2
def baseEnd_1573008 : Nat := 59830309434643469086361

theorem tailTrace_1573008 : CollatzResearch.WordTrace tailWord_1573008 prefixEnd_1573008 59830309434643469086361 := by
  unfold tailWord_1573008
  simp only [CollatzResearch.WordTrace]
  refine ⟨28686157542634069611659839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38248210056845426148879785 28686157542634069611659839)
  ·
    refine ⟨43029236313951104417489759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28686157542634069611659839 43029236313951104417489759)
    ·
      refine ⟨64543854470926656626234639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43029236313951104417489759 64543854470926656626234639)
      ·
        refine ⟨96815781706389984939351959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64543854470926656626234639 96815781706389984939351959)
        ·
          refine ⟨145223672559584977409027939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96815781706389984939351959 145223672559584977409027939)
          ·
            refine ⟨217835508839377466113541909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145223672559584977409027939 217835508839377466113541909)
            ·
              refine ⟨10211039476845818724072277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217835508839377466113541909 10211039476845818724072277)
              ·
                refine ⟨59830309434643469086361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10211039476845818724072277 59830309434643469086361)
                ·
                  rfl

theorem cell22_1573008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_1573008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573008 prefixEnd_1573008 := by exact prefixLift 1573008
  have htrace : WordTrace (prefixWord ++ tailWord_1573008) baseStart_1573008 baseEnd_1573008 := by
    simpa [prefixWord, tailWord_1573008, baseEnd_1573008] using wordTrace_append hprefix tailTrace_1573008
  have hstable : (prefixWord ++ tailWord_1573008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573008).length < 2 ^ (prefixWord ++ tailWord_1573008).sum := by decide
  have hdescent : baseEnd_1573008 < baseStart_1573008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573010 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1573010 : Nat := 118140960795 + 1573010 * 2 ^ 59
def prefixEnd_1573010 : Nat := 4983230072969 + 3 ^ 40 * 1573010 * 2
def baseEnd_1573010 : Nat := 538473469552663883227243

theorem tailTrace_1573010 : CollatzResearch.WordTrace tailWord_1573010 prefixEnd_1573010 538473469552663883227243 := by
  unfold tailWord_1573010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14343097007815223391223121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38248258687507262376594989 14343097007815223391223121)
  ·
    refine ⟨10757322755861417543417341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14343097007815223391223121 10757322755861417543417341)
    ·
      refine ⟨4033996033448031578781503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10757322755861417543417341 4033996033448031578781503)
      ·
        refine ⟨6050994050172047368172255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033996033448031578781503 6050994050172047368172255)
        ·
          refine ⟨9076491075258071052258383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050994050172047368172255 9076491075258071052258383)
          ·
            refine ⟨13614736612887106578387575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076491075258071052258383 13614736612887106578387575)
            ·
              refine ⟨20422104919330659867581363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13614736612887106578387575 20422104919330659867581363)
              ·
                refine ⟨30633157378995989801372045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20422104919330659867581363 30633157378995989801372045)
                ·
                  refine ⟨11487434017123496175514517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30633157378995989801372045 11487434017123496175514517)
                  ·
                    refine ⟨538473469552663883227243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11487434017123496175514517 538473469552663883227243)
                    ·
                      rfl

theorem cell22_1573010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1573010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573010 prefixEnd_1573010 := by exact prefixLift 1573010
  have htrace : WordTrace (prefixWord ++ tailWord_1573010) baseStart_1573010 baseEnd_1573010 := by
    simpa [prefixWord, tailWord_1573010, baseEnd_1573010] using wordTrace_append hprefix tailTrace_1573010
  have hstable : (prefixWord ++ tailWord_1573010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573010).length < 2 ^ (prefixWord ++ tailWord_1573010).sum := by decide
  have hdescent : baseEnd_1573010 < baseStart_1573010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573025 : List Nat := [1, 2, 3, 3, 1, 3, 1, 8]
def baseStart_1573025 : Nat := 118140960795 + 1573025 * 2 ^ 59
def prefixEnd_1573025 : Nat := 4983230072969 + 3 ^ 40 * 1573025 * 2
def baseEnd_1573025 : Nat := 59830956039912093789133

theorem tailTrace_1573025 : CollatzResearch.WordTrace tailWord_1573025 prefixEnd_1573025 59830956039912093789133 := by
  unfold tailWord_1573025
  simp only [CollatzResearch.WordTrace]
  refine ⟨57372935126206551126688529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38248623417471034084459019 57372935126206551126688529)
  ·
    refine ⟨43029701344654913345016397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57372935126206551126688529 43029701344654913345016397)
    ·
      refine ⟨16136138004245592504381149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43029701344654913345016397 16136138004245592504381149)
      ·
        refine ⟨6051051751592097189142931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16136138004245592504381149 6051051751592097189142931)
        ·
          refine ⟨9076577627388145783714397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6051051751592097189142931 9076577627388145783714397)
          ·
            refine ⟨3403716610270554668892899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9076577627388145783714397 3403716610270554668892899)
            ·
              refine ⟨5105574915405832003339349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403716610270554668892899 5105574915405832003339349)
              ·
                refine ⟨59830956039912093789133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5105574915405832003339349 59830956039912093789133)
                ·
                  rfl

theorem cell22_1573025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 8].length) (baseStart_1573025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573025 prefixEnd_1573025 := by exact prefixLift 1573025
  have htrace : WordTrace (prefixWord ++ tailWord_1573025) baseStart_1573025 baseEnd_1573025 := by
    simpa [prefixWord, tailWord_1573025, baseEnd_1573025] using wordTrace_append hprefix tailTrace_1573025
  have hstable : (prefixWord ++ tailWord_1573025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573025).length < 2 ^ (prefixWord ++ tailWord_1573025).sum := by decide
  have hdescent : baseEnd_1573025 < baseStart_1573025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573031 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 4]
def baseStart_1573031 : Nat := 118140960795 + 1573031 * 2 ^ 59
def prefixEnd_1573031 : Nat := 4983230072969 + 3 ^ 40 * 1573031 * 2
def baseEnd_1573031 : Nat := 179493552760608942817393

theorem tailTrace_1573031 : CollatzResearch.WordTrace tailWord_1573031 prefixEnd_1573031 179493552760608942817393 := by
  unfold tailWord_1573031
  simp only [CollatzResearch.WordTrace]
  refine ⟨57373153964184814151406947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38248769309456542767604631 57373153964184814151406947)
  ·
    refine ⟨86059730946277221227110421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57373153964184814151406947 86059730946277221227110421)
    ·
      refine ⟨4034049888106744745020801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86059730946277221227110421 4034049888106744745020801)
      ·
        refine ⟨3025537416080058558765601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4034049888106744745020801 3025537416080058558765601)
        ·
          refine ⟨2269153062060043919074201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3025537416080058558765601 2269153062060043919074201)
          ·
            refine ⟨1701864796545032939305651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2269153062060043919074201 1701864796545032939305651)
            ·
              refine ⟨2552797194817549408958477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701864796545032939305651 2552797194817549408958477)
              ·
                refine ⟨957298948056581028359429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2552797194817549408958477 957298948056581028359429)
                ·
                  refine ⟨179493552760608942817393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957298948056581028359429 179493552760608942817393)
                  ·
                    rfl

theorem cell22_1573031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 4].length) (baseStart_1573031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573031 prefixEnd_1573031 := by exact prefixLift 1573031
  have htrace : WordTrace (prefixWord ++ tailWord_1573031) baseStart_1573031 baseEnd_1573031 := by
    simpa [prefixWord, tailWord_1573031, baseEnd_1573031] using wordTrace_append hprefix tailTrace_1573031
  have hstable : (prefixWord ++ tailWord_1573031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573031).length < 2 ^ (prefixWord ++ tailWord_1573031).sum := by decide
  have hdescent : baseEnd_1573031 < baseStart_1573031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573151 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 1, 4]
def baseStart_1573151 : Nat := 118140960795 + 1573151 * 2 ^ 59
def prefixEnd_1573151 : Nat := 4983230072969 + 3 ^ 40 * 1573151 * 2
def baseEnd_1573151 : Nat := 538521736734186515451811

theorem tailTrace_1573151 : CollatzResearch.WordTrace tailWord_1573151 prefixEnd_1573151 538521736734186515451811 := by
  unfold tailWord_1573151
  simp only [CollatzResearch.WordTrace]
  refine ⟨57377530723750074645775307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38251687149166716430516871 57377530723750074645775307)
  ·
    refine ⟨86066296085625111968662961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57377530723750074645775307 86066296085625111968662961)
    ·
      refine ⟨64549722064218833976497221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86066296085625111968662961 64549722064218833976497221)
      ·
        refine ⟨12103072887041031370593229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64549722064218833976497221 12103072887041031370593229)
        ·
          refine ⟨4538652332640386763972461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12103072887041031370593229 4538652332640386763972461)
          ·
            refine ⟨1701994624740145036489673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4538652332640386763972461 1701994624740145036489673)
            ·
              refine ⟨1276495968555108777367255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701994624740145036489673 1276495968555108777367255)
              ·
                refine ⟨1914743952832663166050883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276495968555108777367255 1914743952832663166050883)
                ·
                  refine ⟨2872115929248994749076325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914743952832663166050883 2872115929248994749076325)
                  ·
                    refine ⟨538521736734186515451811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2872115929248994749076325 538521736734186515451811)
                    ·
                      rfl

theorem cell22_1573151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_1573151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573151 prefixEnd_1573151 := by exact prefixLift 1573151
  have htrace : WordTrace (prefixWord ++ tailWord_1573151) baseStart_1573151 baseEnd_1573151 := by
    simpa [prefixWord, tailWord_1573151, baseEnd_1573151] using wordTrace_append hprefix tailTrace_1573151
  have hstable : (prefixWord ++ tailWord_1573151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573151).length < 2 ^ (prefixWord ++ tailWord_1573151).sum := by decide
  have hdescent : baseEnd_1573151 < baseStart_1573151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573164 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1573164 : Nat := 118140960795 + 1573164 * 2 ^ 59
def prefixEnd_1573164 : Nat := 4983230072969 + 3 ^ 40 * 1573164 * 2
def baseEnd_1573164 : Nat := 538526186899858814876771

theorem tailTrace_1573164 : CollatzResearch.WordTrace tailWord_1573164 prefixEnd_1573164 538526186899858814876771 := by
  unfold tailWord_1573164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28689002436351488932999273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38252003248468651910665697 28689002436351488932999273)
  ·
    refine ⟨21516751827263616699749455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28689002436351488932999273 21516751827263616699749455)
    ·
      refine ⟨32275127740895425049624183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21516751827263616699749455 32275127740895425049624183)
      ·
        refine ⟨48412691611343137574436275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32275127740895425049624183 48412691611343137574436275)
        ·
          refine ⟨72619037417014706361654413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48412691611343137574436275 72619037417014706361654413)
          ·
            refine ⟨27232139031380514885620405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72619037417014706361654413 27232139031380514885620405)
            ·
              refine ⟨2553013034191923270526913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27232139031380514885620405 2553013034191923270526913)
              ·
                refine ⟨1914759775643942452895185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2553013034191923270526913 1914759775643942452895185)
                ·
                  refine ⟨1436069831732956839671389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1914759775643942452895185 1436069831732956839671389)
                  ·
                    refine ⟨538526186899858814876771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436069831732956839671389 538526186899858814876771)
                    ·
                      rfl

theorem cell22_1573164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1573164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573164 prefixEnd_1573164 := by exact prefixLift 1573164
  have htrace : WordTrace (prefixWord ++ tailWord_1573164) baseStart_1573164 baseEnd_1573164 := by
    simpa [prefixWord, tailWord_1573164, baseEnd_1573164] using wordTrace_append hprefix tailTrace_1573164
  have hstable : (prefixWord ++ tailWord_1573164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573164).length < 2 ^ (prefixWord ++ tailWord_1573164).sum := by decide
  have hdescent : baseEnd_1573164 < baseStart_1573164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573166 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_1573166 : Nat := 118140960795 + 1573166 * 2 ^ 59
def prefixEnd_1573166 : Nat := 4983230072969 + 3 ^ 40 * 1573166 * 2
def baseEnd_1573166 : Nat := 179508957180243825442255

theorem tailTrace_1573166 : CollatzResearch.WordTrace tailWord_1573166 prefixEnd_1573166 179508957180243825442255 := by
  unfold tailWord_1573166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7172259727336966525946419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38252051879130488138380901 7172259727336966525946419)
  ·
    refine ⟨10758389591005449788919629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7172259727336966525946419 10758389591005449788919629)
    ·
      refine ⟨4034396096627043670844861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10758389591005449788919629 4034396096627043670844861)
      ·
        refine ⟨1512898536235141376566823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4034396096627043670844861 1512898536235141376566823)
        ·
          refine ⟨2269347804352712064850235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512898536235141376566823 2269347804352712064850235)
          ·
            refine ⟨3404021706529068097275353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269347804352712064850235 3404021706529068097275353)
            ·
              refine ⟨2553016279896801072956515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3404021706529068097275353 2553016279896801072956515)
              ·
                refine ⟨3829524419845201609434773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553016279896801072956515 3829524419845201609434773)
                ·
                  refine ⟨179508957180243825442255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3829524419845201609434773 179508957180243825442255)
                  ·
                    rfl

theorem cell22_1573166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_1573166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573166 prefixEnd_1573166 := by exact prefixLift 1573166
  have htrace : WordTrace (prefixWord ++ tailWord_1573166) baseStart_1573166 baseEnd_1573166 := by
    simpa [prefixWord, tailWord_1573166, baseEnd_1573166] using wordTrace_append hprefix tailTrace_1573166
  have hstable : (prefixWord ++ tailWord_1573166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573166).length < 2 ^ (prefixWord ++ tailWord_1573166).sum := by decide
  have hdescent : baseEnd_1573166 < baseStart_1573166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573226 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1573226 : Nat := 118140960795 + 1573226 * 2 ^ 59
def prefixEnd_1573226 : Nat := 4983230072969 + 3 ^ 40 * 1573226 * 2
def baseEnd_1573226 : Nat := 538547410766911319826581

theorem tailTrace_1573226 : CollatzResearch.WordTrace tailWord_1573226 prefixEnd_1573226 538547410766911319826581 := by
  unfold tailWord_1573226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345066549619590613688883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38253510798985574969837021 14345066549619590613688883)
  ·
    refine ⟨21517599824429385920533325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14345066549619590613688883 21517599824429385920533325)
    ·
      refine ⟨8069099934161019720199997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21517599824429385920533325 8069099934161019720199997)
      ·
        refine ⟨3025912475310382395074999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8069099934161019720199997 3025912475310382395074999)
        ·
          refine ⟨4538868712965573592612499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025912475310382395074999 4538868712965573592612499)
          ·
            refine ⟨6808303069448360388918749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538868712965573592612499 6808303069448360388918749)
            ·
              refine ⟨2553113651043135145844531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6808303069448360388918749 2553113651043135145844531)
              ·
                refine ⟨3829670476564702718766797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553113651043135145844531 3829670476564702718766797)
                ·
                  refine ⟨1436126428711763519537549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3829670476564702718766797 1436126428711763519537549)
                  ·
                    refine ⟨538547410766911319826581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436126428711763519537549 538547410766911319826581)
                    ·
                      rfl

theorem cell22_1573226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1573226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573226 prefixEnd_1573226 := by exact prefixLift 1573226
  have htrace : WordTrace (prefixWord ++ tailWord_1573226) baseStart_1573226 baseEnd_1573226 := by
    simpa [prefixWord, tailWord_1573226, baseEnd_1573226] using wordTrace_append hprefix tailTrace_1573226
  have hstable : (prefixWord ++ tailWord_1573226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573226).length < 2 ^ (prefixWord ++ tailWord_1573226).sum := by decide
  have hdescent : baseEnd_1573226 < baseStart_1573226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573277 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_1573277 : Nat := 118140960795 + 1573277 * 2 ^ 59
def prefixEnd_1573277 : Nat := 4983230072969 + 3 ^ 40 * 1573277 * 2
def baseEnd_1573277 : Nat := 538564869109164186801425

theorem tailTrace_1573277 : CollatzResearch.WordTrace tailWord_1573277 prefixEnd_1573277 538564869109164186801425 := by
  unfold tailWord_1573277
  simp only [CollatzResearch.WordTrace]
  refine ⟨57382126321293598164862085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38254750880862398776574723 57382126321293598164862085)
  ·
    refine ⟨10759148685242549655911641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57382126321293598164862085 10759148685242549655911641)
    ·
      refine ⟨8069361513931912241933731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10759148685242549655911641 8069361513931912241933731)
      ·
        refine ⟨12104042270897868362900597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069361513931912241933731 12104042270897868362900597)
        ·
          refine ⟨1134753962896675159021931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12104042270897868362900597 1134753962896675159021931)
          ·
            refine ⟨1702130944345012738532897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134753962896675159021931 1702130944345012738532897)
            ·
              refine ⟨1276598208258759553899673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702130944345012738532897 1276598208258759553899673)
              ·
                refine ⟨957448656194069665424755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276598208258759553899673 957448656194069665424755)
                ·
                  refine ⟨1436172984291104498137133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957448656194069665424755 1436172984291104498137133)
                  ·
                    refine ⟨538564869109164186801425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436172984291104498137133 538564869109164186801425)
                    ·
                      rfl

theorem cell22_1573277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_1573277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573277 prefixEnd_1573277 := by exact prefixLift 1573277
  have htrace : WordTrace (prefixWord ++ tailWord_1573277) baseStart_1573277 baseEnd_1573277 := by
    simpa [prefixWord, tailWord_1573277, baseEnd_1573277] using wordTrace_append hprefix tailTrace_1573277
  have hstable : (prefixWord ++ tailWord_1573277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573277).length < 2 ^ (prefixWord ++ tailWord_1573277).sum := by decide
  have hdescent : baseEnd_1573277 < baseStart_1573277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573333 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1573333 : Nat := 118140960795 + 1573333 * 2 ^ 59
def prefixEnd_1573333 : Nat := 4983230072969 + 3 ^ 40 * 1573333 * 2
def baseEnd_1573333 : Nat := 538584039053598707401253

theorem tailTrace_1573333 : CollatzResearch.WordTrace tailWord_1573333 prefixEnd_1573333 538584039053598707401253 := by
  unfold tailWord_1573333
  simp only [CollatzResearch.WordTrace]
  refine ⟨57384168809090719728900653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38256112539393813152600435 57384168809090719728900653)
  ·
    refine ⟨21519063303409019898337745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57384168809090719728900653 21519063303409019898337745)
    ·
      refine ⟨16139297477556764923753309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21519063303409019898337745 16139297477556764923753309)
      ·
        refine ⟨6052236554083786846407491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16139297477556764923753309 6052236554083786846407491)
        ·
          refine ⟨9078354831125680269611237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6052236554083786846407491 9078354831125680269611237)
          ·
            refine ⟨1702191530836065050552107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9078354831125680269611237 1702191530836065050552107)
            ·
              refine ⟨2553287296254097575828161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702191530836065050552107 2553287296254097575828161)
              ·
                refine ⟨1914965472190573181871121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2553287296254097575828161 1914965472190573181871121)
                ·
                  refine ⟨1436224104142929886403341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1914965472190573181871121 1436224104142929886403341)
                  ·
                    refine ⟨538584039053598707401253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436224104142929886403341 538584039053598707401253)
                    ·
                      rfl

theorem cell22_1573333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1573333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573333 prefixEnd_1573333 := by exact prefixLift 1573333
  have htrace : WordTrace (prefixWord ++ tailWord_1573333) baseStart_1573333 baseEnd_1573333 := by
    simpa [prefixWord, tailWord_1573333, baseEnd_1573333] using wordTrace_append hprefix tailTrace_1573333
  have hstable : (prefixWord ++ tailWord_1573333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573333).length < 2 ^ (prefixWord ++ tailWord_1573333).sum := by decide
  have hdescent : baseEnd_1573333 < baseStart_1573333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573434 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1573434 : Nat := 118140960795 + 1573434 * 2 ^ 59
def prefixEnd_1573434 : Nat := 4983230072969 + 3 ^ 40 * 1573434 * 2
def baseEnd_1573434 : Nat := 538618613417668110625943

theorem tailTrace_1573434 : CollatzResearch.WordTrace tailWord_1573434 prefixEnd_1573434 538618613417668110625943 := by
  unfold tailWord_1573434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14346963145431203494581839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38258568387816542652218237 14346963145431203494581839)
  ·
    refine ⟨21520444718146805241872759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14346963145431203494581839 21520444718146805241872759)
    ·
      refine ⟨32280667077220207862809139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21520444718146805241872759 32280667077220207862809139)
      ·
        refine ⟨48421000615830311794213709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32280667077220207862809139 48421000615830311794213709)
        ·
          refine ⟨18157875230936366922830141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48421000615830311794213709 18157875230936366922830141)
          ·
            refine ⟨6809203211601137596061303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18157875230936366922830141 6809203211601137596061303)
            ·
              refine ⟨10213804817401706394091955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809203211601137596061303 10213804817401706394091955)
              ·
                refine ⟨15320707226102559591137933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10213804817401706394091955 15320707226102559591137933)
                ·
                  refine ⟨5745265209788459846676725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15320707226102559591137933 5745265209788459846676725)
                  ·
                    refine ⟨538618613417668110625943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5745265209788459846676725 538618613417668110625943)
                    ·
                      rfl

theorem cell22_1573434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1573434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573434 prefixEnd_1573434 := by exact prefixLift 1573434
  have htrace : WordTrace (prefixWord ++ tailWord_1573434) baseStart_1573434 baseEnd_1573434 := by
    simpa [prefixWord, tailWord_1573434, baseEnd_1573434] using wordTrace_append hprefix tailTrace_1573434
  have hstable : (prefixWord ++ tailWord_1573434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573434).length < 2 ^ (prefixWord ++ tailWord_1573434).sum := by decide
  have hdescent : baseEnd_1573434 < baseStart_1573434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573451 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 2, 3]
def baseStart_1573451 : Nat := 118140960795 + 1573451 * 2 ^ 59
def prefixEnd_1573451 : Nat := 4983230072969 + 3 ^ 40 * 1573451 * 2
def baseEnd_1573451 : Nat := 538624432865085732950891

theorem tailTrace_1573451 : CollatzResearch.WordTrace tailWord_1573451 prefixEnd_1573451 538624432865085732950891 := by
  unfold tailWord_1573451
  simp only [CollatzResearch.WordTrace]
  refine ⟨57388472622663225881696207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38258981748442150587797471 57388472622663225881696207)
  ·
    refine ⟨86082708933994838822544311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57388472622663225881696207 86082708933994838822544311)
    ·
      refine ⟨129124063400992258233816467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86082708933994838822544311 129124063400992258233816467)
      ·
        refine ⟨193686095101488387350724701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129124063400992258233816467 193686095101488387350724701)
        ·
          refine ⟨72632285663058145256521763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193686095101488387350724701 72632285663058145256521763)
          ·
            refine ⟨108948428494587217884782645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72632285663058145256521763 108948428494587217884782645)
            ·
              refine ⟨10213915171367551676698373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108948428494587217884782645 10213915171367551676698373)
              ·
                refine ⟨1915109094631415939380945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10213915171367551676698373 1915109094631415939380945)
                ·
                  refine ⟨1436331820973561954535709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1915109094631415939380945 1436331820973561954535709)
                  ·
                    refine ⟨538624432865085732950891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436331820973561954535709 538624432865085732950891)
                    ·
                      rfl

theorem cell22_1573451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 3].length) (baseStart_1573451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573451 prefixEnd_1573451 := by exact prefixLift 1573451
  have htrace : WordTrace (prefixWord ++ tailWord_1573451) baseStart_1573451 baseEnd_1573451 := by
    simpa [prefixWord, tailWord_1573451, baseEnd_1573451] using wordTrace_append hprefix tailTrace_1573451
  have hstable : (prefixWord ++ tailWord_1573451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573451).length < 2 ^ (prefixWord ++ tailWord_1573451).sum := by decide
  have hdescent : baseEnd_1573451 < baseStart_1573451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573464 : List Nat := [2, 1, 2, 2, 1, 2, 5, 7]
def baseStart_1573464 : Nat := 118140960795 + 1573464 * 2 ^ 59
def prefixEnd_1573464 : Nat := 4983230072969 + 3 ^ 40 * 1573464 * 2
def baseEnd_1573464 : Nat := 59847653670084225819539

theorem tailTrace_1573464 : CollatzResearch.WordTrace tailWord_1573464 prefixEnd_1573464 59847653670084225819539 := by
  unfold tailWord_1573464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28694473385808064550959723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38259297847744086067946297 28694473385808064550959723)
  ·
    refine ⟨43041710078712096826439585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28694473385808064550959723 43041710078712096826439585)
    ·
      refine ⟨32281282559034072619829689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43041710078712096826439585 32281282559034072619829689)
      ·
        refine ⟨24210961919275554464872267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32281282559034072619829689 24210961919275554464872267)
        ·
          refine ⟨36316442878913331697308401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24210961919275554464872267 36316442878913331697308401)
          ·
            refine ⟨27237332159184998772981301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36316442878913331697308401 27237332159184998772981301)
            ·
              refine ⟨2553499889923593634966997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27237332159184998772981301 2553499889923593634966997)
              ·
                refine ⟨59847653670084225819539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2553499889923593634966997 59847653670084225819539)
                ·
                  rfl

theorem cell22_1573464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_1573464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573464 prefixEnd_1573464 := by exact prefixLift 1573464
  have htrace : WordTrace (prefixWord ++ tailWord_1573464) baseStart_1573464 baseEnd_1573464 := by
    simpa [prefixWord, tailWord_1573464, baseEnd_1573464] using wordTrace_append hprefix tailTrace_1573464
  have hstable : (prefixWord ++ tailWord_1573464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573464).length < 2 ^ (prefixWord ++ tailWord_1573464).sum := by decide
  have hdescent : baseEnd_1573464 < baseStart_1573464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573468 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1573468 : Nat := 118140960795 + 1573468 * 2 ^ 59
def prefixEnd_1573468 : Nat := 4983230072969 + 3 ^ 40 * 1573468 * 2
def baseEnd_1573468 : Nat := 538630252312503355275839

theorem tailTrace_1573468 : CollatzResearch.WordTrace tailWord_1573468 prefixEnd_1573468 538630252312503355275839 := by
  unfold tailWord_1573468
  simp only [CollatzResearch.WordTrace]
  refine ⟨28694546331800818892532529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38259395109067758523376705 28694546331800818892532529)
  ·
    refine ⟨21520909748850614169399397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28694546331800818892532529 21520909748850614169399397)
    ·
      refine ⟨4035170577909490156762387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21520909748850614169399397 4035170577909490156762387)
      ·
        refine ⟨6052755866864235235143581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035170577909490156762387 6052755866864235235143581)
        ·
          refine ⟨2269783450074088213178843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6052755866864235235143581 2269783450074088213178843)
          ·
            refine ⟨3404675175111132319768265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269783450074088213178843 3404675175111132319768265)
            ·
              refine ⟨2553506381333349239826199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3404675175111132319768265 2553506381333349239826199)
              ·
                refine ⟨3830259572000023859739299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553506381333349239826199 3830259572000023859739299)
                ·
                  refine ⟨5745389358000035789608949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830259572000023859739299 5745389358000035789608949)
                  ·
                    refine ⟨538630252312503355275839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5745389358000035789608949 538630252312503355275839)
                    ·
                      rfl

theorem cell22_1573468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1573468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573468 prefixEnd_1573468 := by exact prefixLift 1573468
  have htrace : WordTrace (prefixWord ++ tailWord_1573468) baseStart_1573468 baseEnd_1573468 := by
    simpa [prefixWord, tailWord_1573468, baseEnd_1573468] using wordTrace_append hprefix tailTrace_1573468
  have hstable : (prefixWord ++ tailWord_1573468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573468).length < 2 ^ (prefixWord ++ tailWord_1573468).sum := by decide
  have hdescent : baseEnd_1573468 < baseStart_1573468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573603 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 1, 5]
def baseStart_1573603 : Nat := 118140960795 + 1573603 * 2 ^ 59
def prefixEnd_1573603 : Nat := 4983230072969 + 3 ^ 40 * 1573603 * 2
def baseEnd_1573603 : Nat := 538676465571408003150425

theorem tailTrace_1573603 : CollatzResearch.WordTrace tailWord_1573603 prefixEnd_1573603 538676465571408003150425 := by
  unfold tailWord_1573603
  simp only [CollatzResearch.WordTrace]
  refine ⟨57394016518112555841229463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38262677678741703894152975 57394016518112555841229463)
  ·
    refine ⟨86091024777168833761844195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57394016518112555841229463 86091024777168833761844195)
    ·
      refine ⟨129136537165753250642766293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86091024777168833761844195 129136537165753250642766293)
      ·
        refine ⟨3026637589822341811939835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 129136537165753250642766293 3026637589822341811939835)
        ·
          refine ⟨4539956384733512717909753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026637589822341811939835 4539956384733512717909753)
          ·
            refine ⟨3404967288550134538432315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539956384733512717909753 3404967288550134538432315)
            ·
              refine ⟨5107450932825201807648473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404967288550134538432315 5107450932825201807648473)
              ·
                refine ⟨3830588199618901355736355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107450932825201807648473 3830588199618901355736355)
                ·
                  refine ⟨5745882299428352033604533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830588199618901355736355 5745882299428352033604533)
                  ·
                    refine ⟨538676465571408003150425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5745882299428352033604533 538676465571408003150425)
                    ·
                      rfl

theorem cell22_1573603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_1573603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573603 prefixEnd_1573603 := by exact prefixLift 1573603
  have htrace : WordTrace (prefixWord ++ tailWord_1573603) baseStart_1573603 baseEnd_1573603 := by
    simpa [prefixWord, tailWord_1573603, baseEnd_1573603] using wordTrace_append hprefix tailTrace_1573603
  have hstable : (prefixWord ++ tailWord_1573603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573603).length < 2 ^ (prefixWord ++ tailWord_1573603).sum := by decide
  have hdescent : baseEnd_1573603 < baseStart_1573603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573618 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1573618 : Nat := 118140960795 + 1573618 * 2 ^ 59
def prefixEnd_1573618 : Nat := 4983230072969 + 3 ^ 40 * 1573618 * 2
def baseEnd_1573618 : Nat := 538681600377952964025379

theorem tailTrace_1573618 : CollatzResearch.WordTrace tailWord_1573618 prefixEnd_1573618 538681600377952964025379 := by
  unfold tailWord_1573618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348640903264553350756377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38263042408705475602017005 14348640903264553350756377)
  ·
    refine ⟨10761480677448415013067283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14348640903264553350756377 10761480677448415013067283)
    ·
      refine ⟨16142221016172622519600925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10761480677448415013067283 16142221016172622519600925)
      ·
        refine ⟨6053332881064733444850347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16142221016172622519600925 6053332881064733444850347)
        ·
          refine ⟨9079999321597100167275521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053332881064733444850347 9079999321597100167275521)
          ·
            refine ⟨6809999491197825125456641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9079999321597100167275521 6809999491197825125456641)
            ·
              refine ⟨5107499618398368844092481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6809999491197825125456641 5107499618398368844092481)
              ·
                refine ⟨3830624713798776633069361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107499618398368844092481 3830624713798776633069361)
                ·
                  refine ⟨2872968535349082474802021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830624713798776633069361 2872968535349082474802021)
                  ·
                    refine ⟨538681600377952964025379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2872968535349082474802021 538681600377952964025379)
                    ·
                      rfl

theorem cell22_1573618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1573618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573618 prefixEnd_1573618 := by exact prefixLift 1573618
  have htrace : WordTrace (prefixWord ++ tailWord_1573618) baseStart_1573618 baseEnd_1573618 := by
    simpa [prefixWord, tailWord_1573618, baseEnd_1573618] using wordTrace_append hprefix tailTrace_1573618
  have hstable : (prefixWord ++ tailWord_1573618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573618).length < 2 ^ (prefixWord ++ tailWord_1573618).sum := by decide
  have hdescent : baseEnd_1573618 < baseStart_1573618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573646 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1573646 : Nat := 118140960795 + 1573646 * 2 ^ 59
def prefixEnd_1573646 : Nat := 4983230072969 + 3 ^ 40 * 1573646 * 2
def baseEnd_1573646 : Nat := 538691185350170224325293

theorem tailTrace_1573646 : CollatzResearch.WordTrace tailWord_1573646 prefixEnd_1573646 538691185350170224325293 := by
  unfold tailWord_1573646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174448107119596773130599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38263723237971182790029861 7174448107119596773130599)
  ·
    refine ⟨10761672160679395159695899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7174448107119596773130599 10761672160679395159695899)
    ·
      refine ⟨16142508241019092739543849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10761672160679395159695899 16142508241019092739543849)
      ·
        refine ⟨12106881180764319554657887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16142508241019092739543849 12106881180764319554657887)
        ·
          refine ⟨18160321771146479331986831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12106881180764319554657887 18160321771146479331986831)
          ·
            refine ⟨27240482656719718997980247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18160321771146479331986831 27240482656719718997980247)
            ·
              refine ⟨40860723985079578496970371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27240482656719718997980247 40860723985079578496970371)
              ·
                refine ⟨61291085977619367745455557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40860723985079578496970371 61291085977619367745455557)
                ·
                  refine ⟨11492078620803631452272917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61291085977619367745455557 11492078620803631452272917)
                  ·
                    refine ⟨538691185350170224325293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11492078620803631452272917 538691185350170224325293)
                    ·
                      rfl

theorem cell22_1573646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1573646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573646 prefixEnd_1573646 := by exact prefixLift 1573646
  have htrace : WordTrace (prefixWord ++ tailWord_1573646) baseStart_1573646 baseEnd_1573646 := by
    simpa [prefixWord, tailWord_1573646, baseEnd_1573646] using wordTrace_append hprefix tailTrace_1573646
  have hstable : (prefixWord ++ tailWord_1573646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573646).length < 2 ^ (prefixWord ++ tailWord_1573646).sum := by decide
  have hdescent : baseEnd_1573646 < baseStart_1573646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573676 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_1573676 : Nat := 118140960795 + 1573676 * 2 ^ 59
def prefixEnd_1573676 : Nat := 4983230072969 + 3 ^ 40 * 1573676 * 2
def baseEnd_1573676 : Nat := 538701454963260146075201

theorem tailTrace_1573676 : CollatzResearch.WordTrace tailWord_1573676 prefixEnd_1573676 538701454963260146075201 := by
  unfold tailWord_1573676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28698339523424044654318441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38264452697898726205757921 28698339523424044654318441)
  ·
    refine ⟨21523754642568033490738831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28698339523424044654318441 21523754642568033490738831)
    ·
      refine ⟨32285631963852050236108247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21523754642568033490738831 32285631963852050236108247)
      ·
        refine ⟨48428447945778075354162371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32285631963852050236108247 48428447945778075354162371)
        ·
          refine ⟨72642671918667113031243557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48428447945778075354162371 72642671918667113031243557)
          ·
            refine ⟨13620500984750083693358167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72642671918667113031243557 13620500984750083693358167)
            ·
              refine ⟨20430751477125125540037251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13620500984750083693358167 20430751477125125540037251)
              ·
                refine ⟨30646127215687688310055877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20430751477125125540037251 30646127215687688310055877)
                ·
                  refine ⟨5746148852941441558135477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30646127215687688310055877 5746148852941441558135477)
                  ·
                    refine ⟨538701454963260146075201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5746148852941441558135477 538701454963260146075201)
                    ·
                      rfl

theorem cell22_1573676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_1573676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573676 prefixEnd_1573676 := by exact prefixLift 1573676
  have htrace : WordTrace (prefixWord ++ tailWord_1573676) baseStart_1573676 baseEnd_1573676 := by
    simpa [prefixWord, tailWord_1573676, baseEnd_1573676] using wordTrace_append hprefix tailTrace_1573676
  have hstable : (prefixWord ++ tailWord_1573676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573676).length < 2 ^ (prefixWord ++ tailWord_1573676).sum := by decide
  have hdescent : baseEnd_1573676 < baseStart_1573676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573695 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 5]
def baseStart_1573695 : Nat := 118140960795 + 1573695 * 2 ^ 59
def prefixEnd_1573695 : Nat := 4983230072969 + 3 ^ 40 * 1573695 * 2
def baseEnd_1573695 : Nat := 179569319683850143283381

theorem tailTrace_1573695 : CollatzResearch.WordTrace tailWord_1573695 prefixEnd_1573695 179569319683850143283381 := by
  unfold tailWord_1573695
  simp only [CollatzResearch.WordTrace]
  refine ⟨57397372033779255553578539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38264914689186170369052359 57397372033779255553578539)
  ·
    refine ⟨86096058050668883330367809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57397372033779255553578539 86096058050668883330367809)
    ·
      refine ⟨64572043538001662497775857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86096058050668883330367809 64572043538001662497775857)
      ·
        refine ⟨48429032653501246873331893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64572043538001662497775857 48429032653501246873331893)
        ·
          refine ⟨4540221811265741894374865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48429032653501246873331893 4540221811265741894374865)
          ·
            refine ⟨3405166358449306420781149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4540221811265741894374865 3405166358449306420781149)
            ·
              refine ⟨1276937384418489907792931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3405166358449306420781149 1276937384418489907792931)
              ·
                refine ⟨1915406076627734861689397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276937384418489907792931 1915406076627734861689397)
                ·
                  refine ⟨179569319683850143283381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1915406076627734861689397 179569319683850143283381)
                  ·
                    rfl

theorem cell22_1573695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 5].length) (baseStart_1573695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573695 prefixEnd_1573695 := by exact prefixLift 1573695
  have htrace : WordTrace (prefixWord ++ tailWord_1573695) baseStart_1573695 baseEnd_1573695 := by
    simpa [prefixWord, tailWord_1573695, baseEnd_1573695] using wordTrace_append hprefix tailTrace_1573695
  have hstable : (prefixWord ++ tailWord_1573695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573695).length < 2 ^ (prefixWord ++ tailWord_1573695).sum := by decide
  have hdescent : baseEnd_1573695 < baseStart_1573695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573706 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_1573706 : Nat := 118140960795 + 1573706 * 2 ^ 59
def prefixEnd_1573706 : Nat := 4983230072969 + 3 ^ 40 * 1573706 * 2
def baseEnd_1573706 : Nat := 179570574858783355941703

theorem tailTrace_1573706 : CollatzResearch.WordTrace tailWord_1573706 prefixEnd_1573706 179570574858783355941703 := by
  unfold tailWord_1573706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14349443309184851108057243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38265182157826269621485981 14349443309184851108057243)
  ·
    refine ⟨21524164963777276662085865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14349443309184851108057243 21524164963777276662085865)
    ·
      refine ⟨16143123722832957496564399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21524164963777276662085865 16143123722832957496564399)
      ·
        refine ⟨24214685584249436244846599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16143123722832957496564399 24214685584249436244846599)
        ·
          refine ⟨36322028376374154367269899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24214685584249436244846599 36322028376374154367269899)
          ·
            refine ⟨54483042564561231550904849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36322028376374154367269899 54483042564561231550904849)
            ·
              refine ⟨40862281923420923663178637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54483042564561231550904849 40862281923420923663178637)
              ·
                refine ⟨15323355721282846373691989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40862281923420923663178637 15323355721282846373691989)
                ·
                  refine ⟨179570574858783355941703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15323355721282846373691989 179570574858783355941703)
                  ·
                    rfl

theorem cell22_1573706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_1573706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573706 prefixEnd_1573706 := by exact prefixLift 1573706
  have htrace : WordTrace (prefixWord ++ tailWord_1573706) baseStart_1573706 baseEnd_1573706 := by
    simpa [prefixWord, tailWord_1573706, baseEnd_1573706] using wordTrace_append hprefix tailTrace_1573706
  have hstable : (prefixWord ++ tailWord_1573706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573706).length < 2 ^ (prefixWord ++ tailWord_1573706).sum := by decide
  have hdescent : baseEnd_1573706 < baseStart_1573706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573716 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1573716 : Nat := 118140960795 + 1573716 * 2 ^ 59
def prefixEnd_1573716 : Nat := 4983230072969 + 3 ^ 40 * 1573716 * 2
def baseEnd_1573716 : Nat := 538715147780713375075079

theorem tailTrace_1573716 : CollatzResearch.WordTrace tailWord_1573716 prefixEnd_1573716 538715147780713375075079 := by
  unfold tailWord_1573716
  simp only [CollatzResearch.WordTrace]
  refine ⟨28699068983351588070046501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38265425311135450760062001 28699068983351588070046501)
  ·
    refine ⟨5381075434378422763133719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28699068983351588070046501 5381075434378422763133719)
    ·
      refine ⟨8071613151567634144700579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381075434378422763133719 8071613151567634144700579)
      ·
        refine ⟨12107419727351451217050869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8071613151567634144700579 12107419727351451217050869)
        ·
          refine ⟨1135070599439198551598519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12107419727351451217050869 1135070599439198551598519)
          ·
            refine ⟨1702605899158797827397779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135070599439198551598519 1702605899158797827397779)
            ·
              refine ⟨2553908848738196741096669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702605899158797827397779 2553908848738196741096669)
              ·
                refine ⟨957715818276823777911251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2553908848738196741096669 957715818276823777911251)
                ·
                  refine ⟨1436573727415235666866877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957715818276823777911251 1436573727415235666866877)
                  ·
                    refine ⟨538715147780713375075079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436573727415235666866877 538715147780713375075079)
                    ·
                      rfl

theorem cell22_1573716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1573716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573716 prefixEnd_1573716 := by exact prefixLift 1573716
  have htrace : WordTrace (prefixWord ++ tailWord_1573716) baseStart_1573716 baseEnd_1573716 := by
    simpa [prefixWord, tailWord_1573716, baseEnd_1573716] using wordTrace_append hprefix tailTrace_1573716
  have hstable : (prefixWord ++ tailWord_1573716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573716).length < 2 ^ (prefixWord ++ tailWord_1573716).sum := by decide
  have hdescent : baseEnd_1573716 < baseStart_1573716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573768 : List Nat := [2, 1, 3, 3, 2, 1, 2, 8]
def baseStart_1573768 : Nat := 118140960795 + 1573768 * 2 ^ 59
def prefixEnd_1573768 : Nat := 4983230072969 + 3 ^ 40 * 1573768 * 2
def baseEnd_1573768 : Nat := 59859216493711396974991

theorem tailTrace_1573768 : CollatzResearch.WordTrace tailWord_1573768 prefixEnd_1573768 59859216493711396974991 := by
  unfold tailWord_1573768
  simp only [CollatzResearch.WordTrace]
  refine ⟨28700017281257394510492979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38266689708343192680657305 28700017281257394510492979)
  ·
    refine ⟨43050025921886091765739469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28700017281257394510492979 43050025921886091765739469)
    ·
      refine ⟨16143759720707284412152301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43050025921886091765739469 16143759720707284412152301)
      ·
        refine ⟨6053909895265231654557113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16143759720707284412152301 6053909895265231654557113)
        ·
          refine ⟨4540432421448923740917835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6053909895265231654557113 4540432421448923740917835)
          ·
            refine ⟨6810648632173385611376753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540432421448923740917835 6810648632173385611376753)
            ·
              refine ⟨5107986474130039208532565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810648632173385611376753 5107986474130039208532565)
              ·
                refine ⟨59859216493711396974991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5107986474130039208532565 59859216493711396974991)
                ·
                  rfl

theorem cell22_1573768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_1573768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573768 prefixEnd_1573768 := by exact prefixLift 1573768
  have htrace : WordTrace (prefixWord ++ tailWord_1573768) baseStart_1573768 baseEnd_1573768 := by
    simpa [prefixWord, tailWord_1573768, baseEnd_1573768] using wordTrace_append hprefix tailTrace_1573768
  have hstable : (prefixWord ++ tailWord_1573768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573768).length < 2 ^ (prefixWord ++ tailWord_1573768).sum := by decide
  have hdescent : baseEnd_1573768 < baseStart_1573768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573770 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1573770 : Nat := 118140960795 + 1573770 * 2 ^ 59
def prefixEnd_1573770 : Nat := 4983230072969 + 3 ^ 40 * 1573770 * 2
def baseEnd_1573770 : Nat := 538733633084275234224913

theorem tailTrace_1573770 : CollatzResearch.WordTrace tailWord_1573770 prefixEnd_1573770 538733633084275234224913 := by
  unfold tailWord_1573770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14350026877126885840639691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38266738339005028908372509 14350026877126885840639691)
  ·
    refine ⟨21525040315690328760959537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14350026877126885840639691 21525040315690328760959537)
    ·
      refine ⟨16143780236767746570719653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21525040315690328760959537 16143780236767746570719653)
      ·
        refine ⟨3026958794393952482009935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16143780236767746570719653 3026958794393952482009935)
        ·
          refine ⟨4540438191590928723014903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026958794393952482009935 4540438191590928723014903)
          ·
            refine ⟨6810657287386393084522355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540438191590928723014903 6810657287386393084522355)
            ·
              refine ⟨10215985931079589626783533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810657287386393084522355 10215985931079589626783533)
              ·
                refine ⟨3830994724154846110043825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10215985931079589626783533 3830994724154846110043825)
                ·
                  refine ⟨2873246043116134582532869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830994724154846110043825 2873246043116134582532869)
                  ·
                    refine ⟨538733633084275234224913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873246043116134582532869 538733633084275234224913)
                    ·
                      rfl

theorem cell22_1573770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1573770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573770 prefixEnd_1573770 := by exact prefixLift 1573770
  have htrace : WordTrace (prefixWord ++ tailWord_1573770) baseStart_1573770 baseEnd_1573770 := by
    simpa [prefixWord, tailWord_1573770, baseEnd_1573770] using wordTrace_append hprefix tailTrace_1573770
  have hstable : (prefixWord ++ tailWord_1573770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573770).length < 2 ^ (prefixWord ++ tailWord_1573770).sum := by decide
  have hdescent : baseEnd_1573770 < baseStart_1573770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573909 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 4]
def baseStart_1573909 : Nat := 118140960795 + 1573909 * 2 ^ 59
def prefixEnd_1573909 : Nat := 4983230072969 + 3 ^ 40 * 1573909 * 2
def baseEnd_1573909 : Nat := 179593738541641734999829

theorem tailTrace_1573909 : CollatzResearch.WordTrace tailWord_1573909 prefixEnd_1573909 179593738541641734999829 := by
  unfold tailWord_1573909
  simp only [CollatzResearch.WordTrace]
  refine ⟨57405177255003970101868781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38270118170002646734579187 57405177255003970101868781)
  ·
    refine ⟨21526941470626488788200793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57405177255003970101868781 21526941470626488788200793)
    ·
      refine ⟨16145206102969866591150595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21526941470626488788200793 16145206102969866591150595)
      ·
        refine ⟨24217809154454799886725893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16145206102969866591150595 24217809154454799886725893)
        ·
          refine ⟨4540839216460274978761105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24217809154454799886725893 4540839216460274978761105)
          ·
            refine ⟨3405629412345206234070829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4540839216460274978761105 3405629412345206234070829)
            ·
              refine ⟨1277111029629452337776561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3405629412345206234070829 1277111029629452337776561)
              ·
                refine ⟨957833272222089253332421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277111029629452337776561 957833272222089253332421)
                ·
                  refine ⟨179593738541641734999829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957833272222089253332421 179593738541641734999829)
                  ·
                    rfl

theorem cell22_1573909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_1573909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573909 prefixEnd_1573909 := by exact prefixLift 1573909
  have htrace : WordTrace (prefixWord ++ tailWord_1573909) baseStart_1573909 baseEnd_1573909 := by
    simpa [prefixWord, tailWord_1573909, baseEnd_1573909] using wordTrace_append hprefix tailTrace_1573909
  have hstable : (prefixWord ++ tailWord_1573909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573909).length < 2 ^ (prefixWord ++ tailWord_1573909).sum := by decide
  have hdescent : baseEnd_1573909 < baseStart_1573909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573924 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_1573924 : Nat := 118140960795 + 1573924 * 2 ^ 59
def prefixEnd_1573924 : Nat := 4983230072969 + 3 ^ 40 * 1573924 * 2
def baseEnd_1573924 : Nat := 538786350431470165874441

theorem tailTrace_1573924 : CollatzResearch.WordTrace tailWord_1573924 prefixEnd_1573924 538786350431470165874441 := by
  unfold tailWord_1573924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28702862174974813831832413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38270482899966418442443217 28702862174974813831832413)
  ·
    refine ⟨10763573315615555186937155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28702862174974813831832413 10763573315615555186937155)
    ·
      refine ⟨16145359973423332780405733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10763573315615555186937155 16145359973423332780405733)
      ·
        refine ⟨3027254995016874896326075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16145359973423332780405733 3027254995016874896326075)
        ·
          refine ⟨4540882492525312344489113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027254995016874896326075 4540882492525312344489113)
          ·
            refine ⟨3405661869393984258366835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4540882492525312344489113 3405661869393984258366835)
            ·
              refine ⟨5108492804090976387550253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405661869393984258366835 5108492804090976387550253)
              ·
                refine ⟨1915684801534116145331345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5108492804090976387550253 1915684801534116145331345)
                ·
                  refine ⟨1436763601150587108998509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1915684801534116145331345 1436763601150587108998509)
                  ·
                    refine ⟨538786350431470165874441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1436763601150587108998509 538786350431470165874441)
                    ·
                      rfl

theorem cell22_1573924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_1573924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1573924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1573924 prefixEnd_1573924 := by exact prefixLift 1573924
  have htrace : WordTrace (prefixWord ++ tailWord_1573924) baseStart_1573924 baseEnd_1573924 := by
    simpa [prefixWord, tailWord_1573924, baseEnd_1573924] using wordTrace_append hprefix tailTrace_1573924
  have hstable : (prefixWord ++ tailWord_1573924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573924).length < 2 ^ (prefixWord ++ tailWord_1573924).sum := by decide
  have hdescent : baseEnd_1573924 < baseStart_1573924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574012 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_1574012 : Nat := 118140960795 + 1574012 * 2 ^ 59
def prefixEnd_1574012 : Nat := 4983230072969 + 3 ^ 40 * 1574012 * 2
def baseEnd_1574012 : Nat := 538816474629867269674171

theorem tailTrace_1574012 : CollatzResearch.WordTrace tailWord_1574012 prefixEnd_1574012 538816474629867269674171 := by
  unfold tailWord_1574012
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704466986815409346434145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38272622649087212461912193 28704466986815409346434145)
  ·
    refine ⟨21528350240111557009825609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28704466986815409346434145 21528350240111557009825609)
    ·
      refine ⟨16146262680083667757369207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21528350240111557009825609 16146262680083667757369207)
      ·
        refine ⟨24219394020125501636053811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16146262680083667757369207 24219394020125501636053811)
        ·
          refine ⟨36329091030188252454080717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24219394020125501636053811 36329091030188252454080717)
          ·
            refine ⟨13623409136320594670280269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36329091030188252454080717 13623409136320594670280269)
            ·
              refine ⟨5108778426120223001355101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13623409136320594670280269 5108778426120223001355101)
              ·
                refine ⟨1915791909795083625508163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5108778426120223001355101 1915791909795083625508163)
                ·
                  refine ⟨2873687864692625438262245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915791909795083625508163 2873687864692625438262245)
                  ·
                    refine ⟨538816474629867269674171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873687864692625438262245 538816474629867269674171)
                    ·
                      rfl

theorem cell22_1574012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_1574012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574012 prefixEnd_1574012 := by exact prefixLift 1574012
  have htrace : WordTrace (prefixWord ++ tailWord_1574012) baseStart_1574012 baseEnd_1574012 := by
    simpa [prefixWord, tailWord_1574012, baseEnd_1574012] using wordTrace_append hprefix tailTrace_1574012
  have hstable : (prefixWord ++ tailWord_1574012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574012).length < 2 ^ (prefixWord ++ tailWord_1574012).sum := by decide
  have hdescent : baseEnd_1574012 < baseStart_1574012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574046 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1574046 : Nat := 118140960795 + 1574046 * 2 ^ 59
def prefixEnd_1574046 : Nat := 4983230072969 + 3 ^ 40 * 1574046 * 2
def baseEnd_1574046 : Nat := 538828113524702514324067

theorem tailTrace_1574046 : CollatzResearch.WordTrace tailWord_1574046 prefixEnd_1574046 538828113524702514324067 := by
  unfold tailWord_1574046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176271756938455312450749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38273449370338428333070661 7176271756938455312450749)
  ·
    refine ⟨2691101908851920742169031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7176271756938455312450749 2691101908851920742169031)
    ·
      refine ⟨4036652863277881113253547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691101908851920742169031 4036652863277881113253547)
      ·
        refine ⟨6054979294916821669880321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036652863277881113253547 6054979294916821669880321)
        ·
          refine ⟨4541234471187616252410241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6054979294916821669880321 4541234471187616252410241)
          ·
            refine ⟨3405925853390712189307681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4541234471187616252410241 3405925853390712189307681)
            ·
              refine ⟨2554444390043034141980761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3405925853390712189307681 2554444390043034141980761)
              ·
                refine ⟨1915833292532275606485571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554444390043034141980761 1915833292532275606485571)
                ·
                  refine ⟨2873749938798413409728357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915833292532275606485571 2873749938798413409728357)
                  ·
                    refine ⟨538828113524702514324067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873749938798413409728357 538828113524702514324067)
                    ·
                      rfl

theorem cell22_1574046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1574046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574046 prefixEnd_1574046 := by exact prefixLift 1574046
  have htrace : WordTrace (prefixWord ++ tailWord_1574046) baseStart_1574046 baseEnd_1574046 := by
    simpa [prefixWord, tailWord_1574046, baseEnd_1574046] using wordTrace_append hprefix tailTrace_1574046
  have hstable : (prefixWord ++ tailWord_1574046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574046).length < 2 ^ (prefixWord ++ tailWord_1574046).sum := by decide
  have hdescent : baseEnd_1574046 < baseStart_1574046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574085 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_1574085 : Nat := 118140960795 + 1574085 * 2 ^ 59
def prefixEnd_1574085 : Nat := 4983230072969 + 3 ^ 40 * 1574085 * 2
def baseEnd_1574085 : Nat := 538841464021719412598947

theorem tailTrace_1574085 : CollatzResearch.WordTrace tailWord_1574085 prefixEnd_1574085 538841464021719412598947 := by
  unfold tailWord_1574085
  simp only [CollatzResearch.WordTrace]
  refine ⟨57411596502366352160275709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38274397668244234773517139 57411596502366352160275709)
  ·
    refine ⟨21529348688387382060103391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57411596502366352160275709 21529348688387382060103391)
    ·
      refine ⟨32294023032581073090155087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21529348688387382060103391 32294023032581073090155087)
      ·
        refine ⟨48441034548871609635232631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32294023032581073090155087 48441034548871609635232631)
        ·
          refine ⟨72661551823307414452848947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48441034548871609635232631 72661551823307414452848947)
          ·
            refine ⟨108992327734961121679273421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72661551823307414452848947 108992327734961121679273421)
            ·
              refine ⟨40872122900610420629727533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108992327734961121679273421 40872122900610420629727533)
              ·
                refine ⟨15327046087728907736147825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40872122900610420629727533 15327046087728907736147825)
                ·
                  refine ⟨11495284565796680802110869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15327046087728907736147825 11495284565796680802110869)
                  ·
                    refine ⟨538841464021719412598947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11495284565796680802110869 538841464021719412598947)
                    ·
                      rfl

theorem cell22_1574085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_1574085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574085 prefixEnd_1574085 := by exact prefixLift 1574085
  have htrace : WordTrace (prefixWord ++ tailWord_1574085) baseStart_1574085 baseEnd_1574085 := by
    simpa [prefixWord, tailWord_1574085, baseEnd_1574085] using wordTrace_append hprefix tailTrace_1574085
  have hstable : (prefixWord ++ tailWord_1574085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574085).length < 2 ^ (prefixWord ++ tailWord_1574085).sum := by decide
  have hdescent : baseEnd_1574085 < baseStart_1574085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574147 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 3, 4]
def baseStart_1574147 : Nat := 118140960795 + 1574147 * 2 ^ 59
def prefixEnd_1574147 : Nat := 4983230072969 + 3 ^ 40 * 1574147 * 2
def baseEnd_1574147 : Nat := 538862687888771917548757

theorem tailTrace_1574147 : CollatzResearch.WordTrace tailWord_1574147 prefixEnd_1574147 538862687888771917548757 := by
  unfold tailWord_1574147
  simp only [CollatzResearch.WordTrace]
  refine ⟨57413857828141736749032695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38275905218761157832688463 57413857828141736749032695)
  ·
    refine ⟨86120786742212605123549043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57413857828141736749032695 86120786742212605123549043)
    ·
      refine ⟨129181180113318907685323565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86120786742212605123549043 129181180113318907685323565)
      ·
        refine ⟨48442942542494590381996337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129181180113318907685323565 48442942542494590381996337)
        ·
          refine ⟨36332206906870942786497253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48442942542494590381996337 36332206906870942786497253)
          ·
            refine ⟨6812288795038301772468235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36332206906870942786497253 6812288795038301772468235)
            ·
              refine ⟨10218433192557452658702353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812288795038301772468235 10218433192557452658702353)
              ·
                refine ⟨7663824894418089494026765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10218433192557452658702353 7663824894418089494026765)
                ·
                  refine ⟨2873934335406783560260037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7663824894418089494026765 2873934335406783560260037)
                  ·
                    refine ⟨538862687888771917548757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873934335406783560260037 538862687888771917548757)
                    ·
                      rfl

theorem cell22_1574147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_1574147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574147 prefixEnd_1574147 := by exact prefixLift 1574147
  have htrace : WordTrace (prefixWord ++ tailWord_1574147) baseStart_1574147 baseEnd_1574147 := by
    simpa [prefixWord, tailWord_1574147, baseEnd_1574147] using wordTrace_append hprefix tailTrace_1574147
  have hstable : (prefixWord ++ tailWord_1574147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574147).length < 2 ^ (prefixWord ++ tailWord_1574147).sum := by decide
  have hdescent : baseEnd_1574147 < baseStart_1574147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574179 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 4]
def baseStart_1574179 : Nat := 118140960795 + 1574179 * 2 ^ 59
def prefixEnd_1574179 : Nat := 4983230072969 + 3 ^ 40 * 1574179 * 2
def baseEnd_1574179 : Nat := 179624547380911500249553

theorem tailTrace_1574179 : CollatzResearch.WordTrace tailWord_1574179 prefixEnd_1574179 179624547380911500249553 := by
  unfold tailWord_1574179
  simp only [CollatzResearch.WordTrace]
  refine ⟨57415024964025806214197591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38276683309350537476131727 57415024964025806214197591)
  ·
    refine ⟨86122537446038709321296387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57415024964025806214197591 86122537446038709321296387)
    ·
      refine ⟨129183806169058063981944581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86122537446038709321296387 129183806169058063981944581)
      ·
        refine ⟨24221963656698386996614609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129183806169058063981944581 24221963656698386996614609)
        ·
          refine ⟨18166472742523790247460957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24221963656698386996614609 18166472742523790247460957)
          ·
            refine ⟨6812427278446421342797859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18166472742523790247460957 6812427278446421342797859)
            ·
              refine ⟨10218640917669632014196789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812427278446421342797859 10218640917669632014196789)
              ·
                refine ⟨957997586031528001330949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10218640917669632014196789 957997586031528001330949)
                ·
                  refine ⟨179624547380911500249553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957997586031528001330949 179624547380911500249553)
                  ·
                    rfl

theorem cell22_1574179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 4].length) (baseStart_1574179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574179 prefixEnd_1574179 := by exact prefixLift 1574179
  have htrace : WordTrace (prefixWord ++ tailWord_1574179) baseStart_1574179 baseEnd_1574179 := by
    simpa [prefixWord, tailWord_1574179, baseEnd_1574179] using wordTrace_append hprefix tailTrace_1574179
  have hstable : (prefixWord ++ tailWord_1574179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574179).length < 2 ^ (prefixWord ++ tailWord_1574179).sum := by decide
  have hdescent : baseEnd_1574179 < baseStart_1574179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574181 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_1574181 : Nat := 118140960795 + 1574181 * 2 ^ 59
def prefixEnd_1574181 : Nat := 4983230072969 + 3 ^ 40 * 1574181 * 2
def baseEnd_1574181 : Nat := 538874326783607162198653

theorem tailTrace_1574181 : CollatzResearch.WordTrace tailWord_1574181 prefixEnd_1574181 538874326783607162198653 := by
  unfold tailWord_1574181
  simp only [CollatzResearch.WordTrace]
  refine ⟨57415097910018560555770397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38276731940012373703846931 57415097910018560555770397)
  ·
    refine ⟨21530661716256960208413899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57415097910018560555770397 21530661716256960208413899)
    ·
      refine ⟨32295992574385440312620849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21530661716256960208413899 32295992574385440312620849)
      ·
        refine ⟨24221994430789080234465637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32295992574385440312620849 24221994430789080234465637)
        ·
          refine ⟨4541623955772952543962307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24221994430789080234465637 4541623955772952543962307)
          ·
            refine ⟨6812435933659428815943461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541623955772952543962307 6812435933659428815943461)
            ·
              refine ⟨1277331737561142902989399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6812435933659428815943461 1277331737561142902989399)
              ·
                refine ⟨1915997606341714354484099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277331737561142902989399 1915997606341714354484099)
                ·
                  refine ⟨2873996409512571531726149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915997606341714354484099 2873996409512571531726149)
                  ·
                    refine ⟨538874326783607162198653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873996409512571531726149 538874326783607162198653)
                    ·
                      rfl

theorem cell22_1574181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_1574181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574181 prefixEnd_1574181 := by exact prefixLift 1574181
  have htrace : WordTrace (prefixWord ++ tailWord_1574181) baseStart_1574181 baseEnd_1574181 := by
    simpa [prefixWord, tailWord_1574181, baseEnd_1574181] using wordTrace_append hprefix tailTrace_1574181
  have hstable : (prefixWord ++ tailWord_1574181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574181).length < 2 ^ (prefixWord ++ tailWord_1574181).sum := by decide
  have hdescent : baseEnd_1574181 < baseStart_1574181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574192 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_1574192 : Nat := 118140960795 + 1574192 * 2 ^ 59
def prefixEnd_1574192 : Nat := 4983230072969 + 3 ^ 40 * 1574192 * 2
def baseEnd_1574192 : Nat := 538878092308406800173619

theorem tailTrace_1574192 : CollatzResearch.WordTrace tailWord_1574192 prefixEnd_1574192 538878092308406800173619 := by
  unfold tailWord_1574192
  simp only [CollatzResearch.WordTrace]
  refine ⟨28707749556489354717210415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38276999408652472956280553 28707749556489354717210415)
  ·
    refine ⟨43061624334734032075815623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28707749556489354717210415 43061624334734032075815623)
    ·
      refine ⟨64592436502101048113723435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43061624334734032075815623 64592436502101048113723435)
      ·
        refine ⟨96888654753151572170585153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64592436502101048113723435 96888654753151572170585153)
        ·
          refine ⟨72666491064863679127938865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96888654753151572170585153 72666491064863679127938865)
          ·
            refine ⟨54499868298647759345954149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72666491064863679127938865 54499868298647759345954149)
            ·
              refine ⟨10218725305996454877366403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54499868298647759345954149 10218725305996454877366403)
              ·
                refine ⟨15328087958994682316049605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10218725305996454877366403 15328087958994682316049605)
                ·
                  refine ⟨2874016492311502934259301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15328087958994682316049605 2874016492311502934259301)
                  ·
                    refine ⟨538878092308406800173619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874016492311502934259301 538878092308406800173619)
                    ·
                      rfl

theorem cell22_1574192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_1574192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574192 prefixEnd_1574192 := by exact prefixLift 1574192
  have htrace : WordTrace (prefixWord ++ tailWord_1574192) baseStart_1574192 baseEnd_1574192 := by
    simpa [prefixWord, tailWord_1574192, baseEnd_1574192] using wordTrace_append hprefix tailTrace_1574192
  have hstable : (prefixWord ++ tailWord_1574192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574192).length < 2 ^ (prefixWord ++ tailWord_1574192).sum := by decide
  have hdescent : baseEnd_1574192 < baseStart_1574192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574196 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1574196 : Nat := 118140960795 + 1574196 * 2 ^ 59
def prefixEnd_1574196 : Nat := 4983230072969 + 3 ^ 40 * 1574196 * 2
def baseEnd_1574196 : Nat := 179626487196717374357869

theorem tailTrace_1574196 : CollatzResearch.WordTrace tailWord_1574196 prefixEnd_1574196 179626487196717374357869 := by
  unfold tailWord_1574196
  simp only [CollatzResearch.WordTrace]
  refine ⟨28707822502482109058783221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38277096669976145411710961 28707822502482109058783221)
  ·
    refine ⟨2691358359607697724260927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28707822502482109058783221 2691358359607697724260927)
    ·
      refine ⟨4037037539411546586391391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691358359607697724260927 4037037539411546586391391)
      ·
        refine ⟨6055556309117319879587087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037037539411546586391391 6055556309117319879587087)
        ·
          refine ⟨9083334463675979819380631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6055556309117319879587087 9083334463675979819380631)
          ·
            refine ⟨13625001695513969729070947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083334463675979819380631 13625001695513969729070947)
            ·
              refine ⟨20437502543270954593606421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13625001695513969729070947 20437502543270954593606421)
              ·
                refine ⟨958007931715825996575301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20437502543270954593606421 958007931715825996575301)
                ·
                  refine ⟨179626487196717374357869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958007931715825996575301 179626487196717374357869)
                  ·
                    rfl

theorem cell22_1574196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1574196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574196 prefixEnd_1574196 := by exact prefixLift 1574196
  have htrace : WordTrace (prefixWord ++ tailWord_1574196) baseStart_1574196 baseEnd_1574196 := by
    simpa [prefixWord, tailWord_1574196, baseEnd_1574196] using wordTrace_append hprefix tailTrace_1574196
  have hstable : (prefixWord ++ tailWord_1574196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574196).length < 2 ^ (prefixWord ++ tailWord_1574196).sum := by decide
  have hdescent : baseEnd_1574196 < baseStart_1574196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574209 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1574209 : Nat := 118140960795 + 1574209 * 2 ^ 59
def prefixEnd_1574209 : Nat := 4983230072969 + 3 ^ 40 * 1574209 * 2
def baseEnd_1574209 : Nat := 538883911755824422498567

theorem tailTrace_1574209 : CollatzResearch.WordTrace tailWord_1574209 prefixEnd_1574209 538883911755824422498567 := by
  unfold tailWord_1574209
  simp only [CollatzResearch.WordTrace]
  refine ⟨57416119153917121337789681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38277412769278080891859787 57416119153917121337789681)
  ·
    refine ⟨43062089365437841003342261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57416119153917121337789681 43062089365437841003342261)
    ·
      refine ⟨4037070878009797594063337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43062089365437841003342261 4037070878009797594063337)
      ·
        refine ⟨3027803158507348195547503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4037070878009797594063337 3027803158507348195547503)
        ·
          refine ⟨4541704737761022293321255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027803158507348195547503 4541704737761022293321255)
          ·
            refine ⟨6812557106641533439981883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541704737761022293321255 6812557106641533439981883)
            ·
              refine ⟨10218835659962300159972825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812557106641533439981883 10218835659962300159972825)
              ·
                refine ⟨7664126744971725119979619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10218835659962300159972825 7664126744971725119979619)
                ·
                  refine ⟨11496190117457587679969429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7664126744971725119979619 11496190117457587679969429)
                  ·
                    refine ⟨538883911755824422498567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11496190117457587679969429 538883911755824422498567)
                    ·
                      rfl

theorem cell22_1574209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1574209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574209 prefixEnd_1574209 := by exact prefixLift 1574209
  have htrace : WordTrace (prefixWord ++ tailWord_1574209) baseStart_1574209 baseEnd_1574209 := by
    simpa [prefixWord, tailWord_1574209, baseEnd_1574209] using wordTrace_append hprefix tailTrace_1574209
  have hstable : (prefixWord ++ tailWord_1574209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574209).length < 2 ^ (prefixWord ++ tailWord_1574209).sum := by decide
  have hdescent : baseEnd_1574209 < baseStart_1574209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574222 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1574222 : Nat := 118140960795 + 1574222 * 2 ^ 59
def prefixEnd_1574222 : Nat := 4983230072969 + 3 ^ 40 * 1574222 * 2
def baseEnd_1574222 : Nat := 538888361921496721923527

theorem tailTrace_1574222 : CollatzResearch.WordTrace tailWord_1574222 prefixEnd_1574222 538888361921496721923527 := by
  unfold tailWord_1574222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177074162858753069751615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38277728868580016372008613 7177074162858753069751615)
  ·
    refine ⟨10765611244288129604627423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177074162858753069751615 10765611244288129604627423)
    ·
      refine ⟨16148416866432194406941135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10765611244288129604627423 16148416866432194406941135)
      ·
        refine ⟨24222625299648291610411703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16148416866432194406941135 24222625299648291610411703)
        ·
          refine ⟨36333937949472437415617555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24222625299648291610411703 36333937949472437415617555)
          ·
            refine ⟨54500906924208656123426333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36333937949472437415617555 54500906924208656123426333)
            ·
              refine ⟨20437840096578246046284875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54500906924208656123426333 20437840096578246046284875)
              ·
                refine ⟨30656760144867369069427313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20437840096578246046284875 30656760144867369069427313)
                ·
                  refine ⟨22992570108650526802070485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30656760144867369069427313 22992570108650526802070485)
                  ·
                    refine ⟨538888361921496721923527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22992570108650526802070485 538888361921496721923527)
                    ·
                      rfl

theorem cell22_1574222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1574222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574222 prefixEnd_1574222 := by exact prefixLift 1574222
  have htrace : WordTrace (prefixWord ++ tailWord_1574222) baseStart_1574222 baseEnd_1574222 := by
    simpa [prefixWord, tailWord_1574222, baseEnd_1574222] using wordTrace_append hprefix tailTrace_1574222
  have hstable : (prefixWord ++ tailWord_1574222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574222).length < 2 ^ (prefixWord ++ tailWord_1574222).sum := by decide
  have hdescent : baseEnd_1574222 < baseStart_1574222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574267 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_1574267 : Nat := 118140960795 + 1574267 * 2 ^ 59
def prefixEnd_1574267 : Nat := 4983230072969 + 3 ^ 40 * 1574267 * 2
def baseEnd_1574267 : Nat := 538903766341131604548389

theorem tailTrace_1574267 : CollatzResearch.WordTrace tailWord_1574267 prefixEnd_1574267 538903766341131604548389 := by
  unfold tailWord_1574267
  simp only [CollatzResearch.WordTrace]
  refine ⟨57418234587706997243401055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38278823058471331495600703 57418234587706997243401055)
  ·
    refine ⟨86127351881560495865101583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57418234587706997243401055 86127351881560495865101583)
    ·
      refine ⟨129191027822340743797652375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86127351881560495865101583 129191027822340743797652375)
      ·
        refine ⟨193786541733511115696478563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129191027822340743797652375 193786541733511115696478563)
        ·
          refine ⟨290679812600266673544717845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193786541733511115696478563 290679812600266673544717845)
          ·
            refine ⟨13625616215637500322408649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290679812600266673544717845 13625616215637500322408649)
            ·
              refine ⟨10219212161728125241806487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13625616215637500322408649 10219212161728125241806487)
              ·
                refine ⟨15328818242592187862709731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219212161728125241806487 15328818242592187862709731)
                ·
                  refine ⟨22993227363888281794064597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15328818242592187862709731 22993227363888281794064597)
                  ·
                    refine ⟨538903766341131604548389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22993227363888281794064597 538903766341131604548389)
                    ·
                      rfl

theorem cell22_1574267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_1574267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574267 prefixEnd_1574267 := by exact prefixLift 1574267
  have htrace : WordTrace (prefixWord ++ tailWord_1574267) baseStart_1574267 baseEnd_1574267 := by
    simpa [prefixWord, tailWord_1574267, baseEnd_1574267] using wordTrace_append hprefix tailTrace_1574267
  have hstable : (prefixWord ++ tailWord_1574267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574267).length < 2 ^ (prefixWord ++ tailWord_1574267).sum := by decide
  have hdescent : baseEnd_1574267 < baseStart_1574267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574269 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1574269 : Nat := 118140960795 + 1574269 * 2 ^ 59
def prefixEnd_1574269 : Nat := 4983230072969 + 3 ^ 40 * 1574269 * 2
def baseEnd_1574269 : Nat := 179634816994001421999461

theorem tailTrace_1574269 : CollatzResearch.WordTrace tailWord_1574269 prefixEnd_1574269 179634816994001421999461 := by
  unfold tailWord_1574269
  simp only [CollatzResearch.WordTrace]
  refine ⟨57418307533699751584973861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38278871689133167723315907 57418307533699751584973861)
  ·
    refine ⟨10765932662568703422182599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57418307533699751584973861 10765932662568703422182599)
    ·
      refine ⟨16148898993853055133273899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10765932662568703422182599 16148898993853055133273899)
      ·
        refine ⟨24223348490779582699910849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16148898993853055133273899 24223348490779582699910849)
        ·
          refine ⟨18167511368084687024933137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24223348490779582699910849 18167511368084687024933137)
          ·
            refine ⟨13625633526063515268699853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18167511368084687024933137 13625633526063515268699853)
            ·
              refine ⟨5109612572273818225762445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13625633526063515268699853 5109612572273818225762445)
              ·
                refine ⟨1916104714602681834660917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5109612572273818225762445 1916104714602681834660917)
                ·
                  refine ⟨179634816994001421999461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1916104714602681834660917 179634816994001421999461)
                  ·
                    rfl

theorem cell22_1574269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1574269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574269 prefixEnd_1574269 := by exact prefixLift 1574269
  have htrace : WordTrace (prefixWord ++ tailWord_1574269) baseStart_1574269 baseEnd_1574269 := by
    simpa [prefixWord, tailWord_1574269, baseEnd_1574269] using wordTrace_append hprefix tailTrace_1574269
  have hstable : (prefixWord ++ tailWord_1574269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574269).length < 2 ^ (prefixWord ++ tailWord_1574269).sum := by decide
  have hdescent : baseEnd_1574269 < baseStart_1574269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574344 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_1574344 : Nat := 118140960795 + 1574344 * 2 ^ 59
def prefixEnd_1574344 : Nat := 4983230072969 + 3 ^ 40 * 1574344 * 2
def baseEnd_1574344 : Nat := 538930125014729070373153

theorem tailTrace_1574344 : CollatzResearch.WordTrace tailWord_1574344 prefixEnd_1574344 538930125014729070373153 := by
  unfold tailWord_1574344
  simp only [CollatzResearch.WordTrace]
  refine ⟨28710521504214019696977043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38280695338952026262636057 28710521504214019696977043)
  ·
    refine ⟨43065782256321029545465565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28710521504214019696977043 43065782256321029545465565)
    ·
      refine ⟨16149668346120386079549587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43065782256321029545465565 16149668346120386079549587)
      ·
        refine ⟨24224502519180579119324381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16149668346120386079549587 24224502519180579119324381)
        ·
          refine ⟨9084188444692717169746643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24224502519180579119324381 9084188444692717169746643)
          ·
            refine ⟨13626282667039075754619965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084188444692717169746643 13626282667039075754619965)
            ·
              refine ⟨5109856000139653407982487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13626282667039075754619965 5109856000139653407982487)
              ·
                refine ⟨7664784000209480111973731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5109856000139653407982487 7664784000209480111973731)
                ·
                  refine ⟨11497176000314220167960597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7664784000209480111973731 11497176000314220167960597)
                  ·
                    refine ⟨538930125014729070373153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11497176000314220167960597 538930125014729070373153)
                    ·
                      rfl

theorem cell22_1574344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_1574344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574344 prefixEnd_1574344 := by exact prefixLift 1574344
  have htrace : WordTrace (prefixWord ++ tailWord_1574344) baseStart_1574344 baseEnd_1574344 := by
    simpa [prefixWord, tailWord_1574344, baseEnd_1574344] using wordTrace_append hprefix tailTrace_1574344
  have hstable : (prefixWord ++ tailWord_1574344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574344).length < 2 ^ (prefixWord ++ tailWord_1574344).sum := by decide
  have hdescent : baseEnd_1574344 < baseStart_1574344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574348 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 4]
def baseStart_1574348 : Nat := 118140960795 + 1574348 * 2 ^ 59
def prefixEnd_1574348 : Nat := 4983230072969 + 3 ^ 40 * 1574348 * 2
def baseEnd_1574348 : Nat := 179643831432158131091047

theorem tailTrace_1574348 : CollatzResearch.WordTrace tailWord_1574348 prefixEnd_1574348 179643831432158131091047 := by
  unfold tailWord_1574348
  simp only [CollatzResearch.WordTrace]
  refine ⟨28710594450206774038549849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38280792600275698718066465 28710594450206774038549849)
  ·
    refine ⟨21532945837655080528912387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28710594450206774038549849 21532945837655080528912387)
    ·
      refine ⟨32299418756482620793368581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21532945837655080528912387 32299418756482620793368581)
      ·
        refine ⟨6056141016840491398756609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32299418756482620793368581 6056141016840491398756609)
        ·
          refine ⟨4542105762630368549067457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6056141016840491398756609 4542105762630368549067457)
          ·
            refine ⟨3406579321972776411800593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4542105762630368549067457 3406579321972776411800593)
            ·
              refine ⟨2554934491479582308850445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406579321972776411800593 2554934491479582308850445)
              ·
                refine ⟨958100434304843365818917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2554934491479582308850445 958100434304843365818917)
                ·
                  refine ⟨179643831432158131091047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958100434304843365818917 179643831432158131091047)
                  ·
                    rfl

theorem cell22_1574348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_1574348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574348 prefixEnd_1574348 := by exact prefixLift 1574348
  have htrace : WordTrace (prefixWord ++ tailWord_1574348) baseStart_1574348 baseEnd_1574348 := by
    simpa [prefixWord, tailWord_1574348, baseEnd_1574348] using wordTrace_append hprefix tailTrace_1574348
  have hstable : (prefixWord ++ tailWord_1574348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574348).length < 2 ^ (prefixWord ++ tailWord_1574348).sum := by decide
  have hdescent : baseEnd_1574348 < baseStart_1574348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574449 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 8]
def baseStart_1574449 : Nat := 118140960795 + 1574449 * 2 ^ 59
def prefixEnd_1574449 : Nat := 4983230072969 + 3 ^ 40 * 1574449 * 2
def baseEnd_1574449 : Nat := 179655356220181265499277

theorem tailTrace_1574449 : CollatzResearch.WordTrace tailWord_1574449 prefixEnd_1574449 179655356220181265499277 := by
  unfold tailWord_1574449
  simp only [CollatzResearch.WordTrace]
  refine ⟨57424872673047642326526401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38283248448698428217684267 57424872673047642326526401)
  ·
    refine ⟨43068654504785731744894801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57424872673047642326526401 43068654504785731744894801)
    ·
      refine ⟨32301490878589298808671101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43068654504785731744894801 32301490878589298808671101)
      ·
        refine ⟨12113059079470987053251663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32301490878589298808671101 12113059079470987053251663)
        ·
          refine ⟨18169588619206480579877495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12113059079470987053251663 18169588619206480579877495)
          ·
            refine ⟨27254382928809720869816243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18169588619206480579877495 27254382928809720869816243)
            ·
              refine ⟨40881574393214581304724365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27254382928809720869816243 40881574393214581304724365)
              ·
                refine ⟨15330590397455467989271637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40881574393214581304724365 15330590397455467989271637)
                ·
                  refine ⟨179655356220181265499277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15330590397455467989271637 179655356220181265499277)
                  ·
                    rfl

theorem cell22_1574449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_1574449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574449 prefixEnd_1574449 := by exact prefixLift 1574449
  have htrace : WordTrace (prefixWord ++ tailWord_1574449) baseStart_1574449 baseEnd_1574449 := by
    simpa [prefixWord, tailWord_1574449, baseEnd_1574449] using wordTrace_append hprefix tailTrace_1574449
  have hstable : (prefixWord ++ tailWord_1574449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574449).length < 2 ^ (prefixWord ++ tailWord_1574449).sum := by decide
  have hdescent : baseEnd_1574449 < baseStart_1574449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574451 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 3, 4]
def baseStart_1574451 : Nat := 118140960795 + 1574451 * 2 ^ 59
def prefixEnd_1574451 : Nat := 4983230072969 + 3 ^ 40 * 1574451 * 2
def baseEnd_1574451 : Nat := 538966753301416457947825

theorem tailTrace_1574451 : CollatzResearch.WordTrace tailWord_1574451 prefixEnd_1574451 538966753301416457947825 := by
  unfold tailWord_1574451
  simp only [CollatzResearch.WordTrace]
  refine ⟨57424945619040396668099207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38283297079360264445399471 57424945619040396668099207)
  ·
    refine ⟨86137418428560595002148811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57424945619040396668099207 86137418428560595002148811)
    ·
      refine ⟨129206127642840892503223217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86137418428560595002148811 129206127642840892503223217)
      ·
        refine ⟨96904595732130669377417413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129206127642840892503223217 96904595732130669377417413)
        ·
          refine ⟨18169611699774500508265765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96904595732130669377417413 18169611699774500508265765)
          ·
            refine ⟨3406802193707718845299831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18169611699774500508265765 3406802193707718845299831)
            ·
              refine ⟨5110203290561578267949747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406802193707718845299831 5110203290561578267949747)
              ·
                refine ⟨7665304935842367401924621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110203290561578267949747 7665304935842367401924621)
                ·
                  refine ⟨2874489350940887775721733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7665304935842367401924621 2874489350940887775721733)
                  ·
                    refine ⟨538966753301416457947825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874489350940887775721733 538966753301416457947825)
                    ·
                      rfl

theorem cell22_1574451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_1574451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574451 prefixEnd_1574451 := by exact prefixLift 1574451
  have htrace : WordTrace (prefixWord ++ tailWord_1574451) baseStart_1574451 baseEnd_1574451 := by
    simpa [prefixWord, tailWord_1574451, baseEnd_1574451] using wordTrace_append hprefix tailTrace_1574451
  have hstable : (prefixWord ++ tailWord_1574451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574451).length < 2 ^ (prefixWord ++ tailWord_1574451).sum := by decide
  have hdescent : baseEnd_1574451 < baseStart_1574451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574479 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_1574479 : Nat := 118140960795 + 1574479 * 2 ^ 59
def prefixEnd_1574479 : Nat := 4983230072969 + 3 ^ 40 * 1574479 * 2
def baseEnd_1574479 : Nat := 538976338273633718247739

theorem tailTrace_1574479 : CollatzResearch.WordTrace tailWord_1574479 prefixEnd_1574479 538976338273633718247739 := by
  unfold tailWord_1574479
  simp only [CollatzResearch.WordTrace]
  refine ⟨57425966862938957450118491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38283977908625971633412327 57425966862938957450118491)
  ·
    refine ⟨86138950294408436175177737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57425966862938957450118491 86138950294408436175177737)
    ·
      refine ⟨64604212720806327131383303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86138950294408436175177737 64604212720806327131383303)
      ·
        refine ⟨96906319081209490697074955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64604212720806327131383303 96906319081209490697074955)
        ·
          refine ⟨145359478621814236045612433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96906319081209490697074955 145359478621814236045612433)
          ·
            refine ⟨109019608966360677034209325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145359478621814236045612433 109019608966360677034209325)
            ·
              refine ⟨40882353362385253887828497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109019608966360677034209325 40882353362385253887828497)
              ·
                refine ⟨30661765021788940415871373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40882353362385253887828497 30661765021788940415871373)
                ·
                  refine ⟨11498161883170852655951765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30661765021788940415871373 11498161883170852655951765)
                  ·
                    refine ⟨538976338273633718247739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11498161883170852655951765 538976338273633718247739)
                    ·
                      rfl

theorem cell22_1574479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_1574479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574479 prefixEnd_1574479 := by exact prefixLift 1574479
  have htrace : WordTrace (prefixWord ++ tailWord_1574479) baseStart_1574479 baseEnd_1574479 := by
    simpa [prefixWord, tailWord_1574479, baseEnd_1574479] using wordTrace_append hprefix tailTrace_1574479
  have hstable : (prefixWord ++ tailWord_1574479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574479).length < 2 ^ (prefixWord ++ tailWord_1574479).sum := by decide
  have hdescent : baseEnd_1574479 < baseStart_1574479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574532 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1574532 : Nat := 118140960795 + 1574532 * 2 ^ 59
def prefixEnd_1574532 : Nat := 4983230072969 + 3 ^ 40 * 1574532 * 2
def baseEnd_1574532 : Nat := 538994481256759246672577

theorem tailTrace_1574532 : CollatzResearch.WordTrace tailWord_1574532 prefixEnd_1574532 538994481256759246672577 := by
  unfold tailWord_1574532
  simp only [CollatzResearch.WordTrace]
  refine ⟨28713949965873473750898925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38285266621164631667865233 28713949965873473750898925)
  ·
    refine ⟨10767731237202552656587097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28713949965873473750898925 10767731237202552656587097)
    ·
      refine ⟨8075798427901914492440323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10767731237202552656587097 8075798427901914492440323)
      ·
        refine ⟨12113697641852871738660485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8075798427901914492440323 12113697641852871738660485)
        ·
          refine ⟨2271318307847413450998841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12113697641852871738660485 2271318307847413450998841)
          ·
            refine ⟨1703488730885560088249131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271318307847413450998841 1703488730885560088249131)
            ·
              refine ⟨2555233096328340132373697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703488730885560088249131 2555233096328340132373697)
              ·
                refine ⟨1916424822246255099280273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555233096328340132373697 1916424822246255099280273)
                ·
                  refine ⟨1437318616684691324460205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1916424822246255099280273 1437318616684691324460205)
                  ·
                    refine ⟨538994481256759246672577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1437318616684691324460205 538994481256759246672577)
                    ·
                      rfl

theorem cell22_1574532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1574532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574532 prefixEnd_1574532 := by exact prefixLift 1574532
  have htrace : WordTrace (prefixWord ++ tailWord_1574532) baseStart_1574532 baseEnd_1574532 := by
    simpa [prefixWord, tailWord_1574532, baseEnd_1574532] using wordTrace_append hprefix tailTrace_1574532
  have hstable : (prefixWord ++ tailWord_1574532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574532).length < 2 ^ (prefixWord ++ tailWord_1574532).sum := by decide
  have hdescent : baseEnd_1574532 < baseStart_1574532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574562 : List Nat := [3, 3, 1, 4, 1, 2, 2, 6]
def baseStart_1574562 : Nat := 118140960795 + 1574562 * 2 ^ 59
def prefixEnd_1574562 : Nat := 4983230072969 + 3 ^ 40 * 1574562 * 2
def baseEnd_1574562 : Nat := 59889416763316574269165

theorem tailTrace_1574562 : CollatzResearch.WordTrace tailWord_1574562 prefixEnd_1574562 59889416763316574269165 := by
  unfold tailWord_1574562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357248530409565656347485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38285996081092175083593293 14357248530409565656347485)
  ·
    refine ⟨5383968198903587121130307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14357248530409565656347485 5383968198903587121130307)
    ·
      refine ⟨8075952298355380681695461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5383968198903587121130307 8075952298355380681695461)
      ·
        refine ⟨1514241055941633877817899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8075952298355380681695461 1514241055941633877817899)
        ·
          refine ⟨2271361583912450816726849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514241055941633877817899 2271361583912450816726849)
          ·
            refine ⟨1703521187934338112545137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271361583912450816726849 1703521187934338112545137)
            ·
              refine ⟨1277640890950753584408853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703521187934338112545137 1277640890950753584408853)
              ·
                refine ⟨59889416763316574269165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1277640890950753584408853 59889416763316574269165)
                ·
                  rfl

theorem cell22_1574562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_1574562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574562 prefixEnd_1574562 := by exact prefixLift 1574562
  have htrace : WordTrace (prefixWord ++ tailWord_1574562) baseStart_1574562 baseEnd_1574562 := by
    simpa [prefixWord, tailWord_1574562, baseEnd_1574562] using wordTrace_append hprefix tailTrace_1574562
  have hstable : (prefixWord ++ tailWord_1574562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574562).length < 2 ^ (prefixWord ++ tailWord_1574562).sum := by decide
  have hdescent : baseEnd_1574562 < baseStart_1574562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574637 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_1574637 : Nat := 118140960795 + 1574637 * 2 ^ 59
def prefixEnd_1574637 : Nat := 4983230072969 + 3 ^ 40 * 1574637 * 2
def baseEnd_1574637 : Nat := 539030424902573972797255

theorem tailTrace_1574637 : CollatzResearch.WordTrace tailWord_1574637 prefixEnd_1574637 539030424902573972797255 := by
  unfold tailWord_1574637
  simp only [CollatzResearch.WordTrace]
  refine ⟨57431729596366550434370165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38287819730911033622913443 57431729596366550434370165)
  ·
    refine ⟨5384224649659364103222203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57431729596366550434370165 5384224649659364103222203)
    ·
      refine ⟨8076336974489046154833305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5384224649659364103222203 8076336974489046154833305)
      ·
        refine ⟨6057252730866784616124979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8076336974489046154833305 6057252730866784616124979)
        ·
          refine ⟨9085879096300176924187469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6057252730866784616124979 9085879096300176924187469)
          ·
            refine ⟨3407204661112566346570301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9085879096300176924187469 3407204661112566346570301)
            ·
              refine ⟨1277701747917212379963863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3407204661112566346570301 1277701747917212379963863)
              ·
                refine ⟨1916552621875818569945795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277701747917212379963863 1916552621875818569945795)
                ·
                  refine ⟨2874828932813727854918693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916552621875818569945795 2874828932813727854918693)
                  ·
                    refine ⟨539030424902573972797255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874828932813727854918693 539030424902573972797255)
                    ·
                      rfl

theorem cell22_1574637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_1574637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574637 prefixEnd_1574637 := by exact prefixLift 1574637
  have htrace : WordTrace (prefixWord ++ tailWord_1574637) baseStart_1574637 baseEnd_1574637 := by
    simpa [prefixWord, tailWord_1574637, baseEnd_1574637] using wordTrace_append hprefix tailTrace_1574637
  have hstable : (prefixWord ++ tailWord_1574637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574637).length < 2 ^ (prefixWord ++ tailWord_1574637).sum := by decide
  have hdescent : baseEnd_1574637 < baseStart_1574637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574661 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_1574661 : Nat := 118140960795 + 1574661 * 2 ^ 59
def prefixEnd_1574661 : Nat := 4983230072969 + 3 ^ 40 * 1574661 * 2
def baseEnd_1574661 : Nat := 539038640593045910197181

theorem tailTrace_1574661 : CollatzResearch.WordTrace tailWord_1574661 prefixEnd_1574661 539038640593045910197181 := by
  unfold tailWord_1574661
  simp only [CollatzResearch.WordTrace]
  refine ⟨57432604948279602533243837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38288403298853068355495891 57432604948279602533243837)
  ·
    refine ⟨21537226855604850949966439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57432604948279602533243837 21537226855604850949966439)
    ·
      refine ⟨32305840283407276424949659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21537226855604850949966439 32305840283407276424949659)
      ·
        refine ⟨48458760425110914637424489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32305840283407276424949659 48458760425110914637424489)
        ·
          refine ⟨36344070318833185978068367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48458760425110914637424489 36344070318833185978068367)
          ·
            refine ⟨54516105478249778967102551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36344070318833185978068367 54516105478249778967102551)
            ·
              refine ⟨81774158217374668450653827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54516105478249778967102551 81774158217374668450653827)
              ·
                refine ⟨122661237326062002675980741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81774158217374668450653827 122661237326062002675980741)
                ·
                  refine ⟨22998981998636625501746389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122661237326062002675980741 22998981998636625501746389)
                  ·
                    refine ⟨539038640593045910197181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22998981998636625501746389 539038640593045910197181)
                    ·
                      rfl

theorem cell22_1574661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_1574661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574661 prefixEnd_1574661 := by exact prefixLift 1574661
  have htrace : WordTrace (prefixWord ++ tailWord_1574661) baseStart_1574661 baseEnd_1574661 := by
    simpa [prefixWord, tailWord_1574661, baseEnd_1574661] using wordTrace_append hprefix tailTrace_1574661
  have hstable : (prefixWord ++ tailWord_1574661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574661).length < 2 ^ (prefixWord ++ tailWord_1574661).sum := by decide
  have hdescent : baseEnd_1574661 < baseStart_1574661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574686 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1574686 : Nat := 118140960795 + 1574686 * 2 ^ 59
def prefixEnd_1574686 : Nat := 4983230072969 + 3 ^ 40 * 1574686 * 2
def baseEnd_1574686 : Nat := 179682399534651392774035

theorem tailTrace_1574686 : CollatzResearch.WordTrace tailWord_1574686 prefixEnd_1574686 179682399534651392774035 := by
  unfold tailWord_1574686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179189596648628975362989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38289011182126021201935941 7179189596648628975362989)
  ·
    refine ⟨2692196098743235865761121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7179189596648628975362989 2692196098743235865761121)
    ·
      refine ⟨2019147074057426899320841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2692196098743235865761121 2019147074057426899320841)
      ·
        refine ⟨1514360305543070174490631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2019147074057426899320841 1514360305543070174490631)
        ·
          refine ⟨2271540458314605261735947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514360305543070174490631 2271540458314605261735947)
          ·
            refine ⟨3407310687471907892603921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271540458314605261735947 3407310687471907892603921)
            ·
              refine ⟨2555483015603930919452941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407310687471907892603921 2555483015603930919452941)
              ·
                refine ⟨958306130851474094794853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2555483015603930919452941 958306130851474094794853)
                ·
                  refine ⟨179682399534651392774035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958306130851474094794853 179682399534651392774035)
                  ·
                    rfl

theorem cell22_1574686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1574686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574686 prefixEnd_1574686 := by exact prefixLift 1574686
  have htrace : WordTrace (prefixWord ++ tailWord_1574686) baseStart_1574686 baseEnd_1574686 := by
    simpa [prefixWord, tailWord_1574686, baseEnd_1574686] using wordTrace_append hprefix tailTrace_1574686
  have hstable : (prefixWord ++ tailWord_1574686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574686).length < 2 ^ (prefixWord ++ tailWord_1574686).sum := by decide
  have hdescent : baseEnd_1574686 < baseStart_1574686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574712 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 1, 3]
def baseStart_1574712 : Nat := 118140960795 + 1574712 * 2 ^ 59
def prefixEnd_1574712 : Nat := 4983230072969 + 3 ^ 40 * 1574712 * 2
def baseEnd_1574712 : Nat := 539056098935298777172025

theorem tailTrace_1574712 : CollatzResearch.WordTrace tailWord_1574712 prefixEnd_1574712 539056098935298777172025 := by
  unfold tailWord_1574712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28717232535547419121675195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38289643380729892162233593 28717232535547419121675195)
  ·
    refine ⟨43075848803321128682512793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28717232535547419121675195 43075848803321128682512793)
    ·
      refine ⟨32306886602490846511884595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43075848803321128682512793 32306886602490846511884595)
      ·
        refine ⟨48460329903736269767826893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32306886602490846511884595 48460329903736269767826893)
        ·
          refine ⟨18172623713901101162935085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48460329903736269767826893 18172623713901101162935085)
          ·
            refine ⟨6814733892712912936100657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18172623713901101162935085 6814733892712912936100657)
            ·
              refine ⟨5111050419534684702075493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814733892712912936100657 5111050419534684702075493)
              ·
                refine ⟨958321953662753381639155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5111050419534684702075493 958321953662753381639155)
                ·
                  refine ⟨1437482930494130072458733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958321953662753381639155 1437482930494130072458733)
                  ·
                    refine ⟨539056098935298777172025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1437482930494130072458733 539056098935298777172025)
                    ·
                      rfl

theorem cell22_1574712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_1574712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574712 prefixEnd_1574712 := by exact prefixLift 1574712
  have htrace : WordTrace (prefixWord ++ tailWord_1574712) baseStart_1574712 baseEnd_1574712 := by
    simpa [prefixWord, tailWord_1574712, baseEnd_1574712] using wordTrace_append hprefix tailTrace_1574712
  have hstable : (prefixWord ++ tailWord_1574712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574712).length < 2 ^ (prefixWord ++ tailWord_1574712).sum := by decide
  have hdescent : baseEnd_1574712 < baseStart_1574712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574723 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 2, 5]
def baseStart_1574723 : Nat := 118140960795 + 1574723 * 2 ^ 59
def prefixEnd_1574723 : Nat := 4983230072969 + 3 ^ 40 * 1574723 * 2
def baseEnd_1574723 : Nat := 539059864460098415146991

theorem tailTrace_1574723 : CollatzResearch.WordTrace tailWord_1574723 prefixEnd_1574723 539059864460098415146991 := by
  unfold tailWord_1574723
  simp only [CollatzResearch.WordTrace]
  refine ⟨57434866274054987122000823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38289910849369991414667215 57434866274054987122000823)
  ·
    refine ⟨86152299411082480683001235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57434866274054987122000823 86152299411082480683001235)
    ·
      refine ⟨129228449116623721024501853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86152299411082480683001235 129228449116623721024501853)
      ·
        refine ⟨48460668418733895384188195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129228449116623721024501853 48460668418733895384188195)
        ·
          refine ⟨72691002628100843076282293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48460668418733895384188195 72691002628100843076282293)
          ·
            refine ⟨6814781496384454038401465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72691002628100843076282293 6814781496384454038401465)
            ·
              refine ⟨5111086122288340528801099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814781496384454038401465 5111086122288340528801099)
              ·
                refine ⟨7666629183432510793201649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111086122288340528801099 7666629183432510793201649)
                ·
                  refine ⟨5749971887574383094901237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7666629183432510793201649 5749971887574383094901237)
                  ·
                    refine ⟨539059864460098415146991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5749971887574383094901237 539059864460098415146991)
                    ·
                      rfl

theorem cell22_1574723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_1574723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574723 prefixEnd_1574723 := by exact prefixLift 1574723
  have htrace : WordTrace (prefixWord ++ tailWord_1574723) baseStart_1574723 baseEnd_1574723 := by
    simpa [prefixWord, tailWord_1574723, baseEnd_1574723] using wordTrace_append hprefix tailTrace_1574723
  have hstable : (prefixWord ++ tailWord_1574723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574723).length < 2 ^ (prefixWord ++ tailWord_1574723).sum := by decide
  have hdescent : baseEnd_1574723 < baseStart_1574723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574725 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 5]
def baseStart_1574725 : Nat := 118140960795 + 1574725 * 2 ^ 59
def prefixEnd_1574725 : Nat := 4983230072969 + 3 ^ 40 * 1574725 * 2
def baseEnd_1574725 : Nat := 179686849700323692198995

theorem tailTrace_1574725 : CollatzResearch.WordTrace tailWord_1574725 prefixEnd_1574725 179686849700323692198995 := by
  unfold tailWord_1574725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57434939220047741463573629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38289959480031827642382419 57434939220047741463573629)
  ·
    refine ⟨21538102207517903048840111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57434939220047741463573629 21538102207517903048840111)
    ·
      refine ⟨32307153311276854573260167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21538102207517903048840111 32307153311276854573260167)
      ·
        refine ⟨48460729966915281859890251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32307153311276854573260167 48460729966915281859890251)
        ·
          refine ⟨72691094950372922789835377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48460729966915281859890251 72691094950372922789835377)
          ·
            refine ⟨54518321212779692092376533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72691094950372922789835377 54518321212779692092376533)
            ·
              refine ⟨1277773153424524033415075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54518321212779692092376533 1277773153424524033415075)
              ·
                refine ⟨1916659730136786050122613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277773153424524033415075 1916659730136786050122613)
                ·
                  refine ⟨179686849700323692198995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1916659730136786050122613 179686849700323692198995)
                  ·
                    rfl

theorem cell22_1574725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_1574725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574725 prefixEnd_1574725 := by exact prefixLift 1574725
  have htrace : WordTrace (prefixWord ++ tailWord_1574725) baseStart_1574725 baseEnd_1574725 := by
    simpa [prefixWord, tailWord_1574725, baseEnd_1574725] using wordTrace_append hprefix tailTrace_1574725
  have hstable : (prefixWord ++ tailWord_1574725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574725).length < 2 ^ (prefixWord ++ tailWord_1574725).sum := by decide
  have hdescent : baseEnd_1574725 < baseStart_1574725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574783 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 6, 4]
def baseStart_1574783 : Nat := 118140960795 + 1574783 * 2 ^ 59
def prefixEnd_1574783 : Nat := 4983230072969 + 3 ^ 40 * 1574783 * 2
def baseEnd_1574783 : Nat := 539080403686278258646807

theorem tailTrace_1574783 : CollatzResearch.WordTrace tailWord_1574783 prefixEnd_1574783 539080403686278258646807 := by
  unfold tailWord_1574783
  simp only [CollatzResearch.WordTrace]
  refine ⟨57437054653837617369185003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38291369769225078246123335 57437054653837617369185003)
  ·
    refine ⟨86155581980756426053777505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57437054653837617369185003 86155581980756426053777505)
    ·
      refine ⟨64616686485567319540333129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86155581980756426053777505 64616686485567319540333129)
      ·
        refine ⟨48462514864175489655249847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64616686485567319540333129 48462514864175489655249847)
        ·
          refine ⟨72693772296263234482874771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48462514864175489655249847 72693772296263234482874771)
          ·
            refine ⟨109040658444394851724312157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72693772296263234482874771 109040658444394851724312157)
            ·
              refine ⟨40890246916648069396617059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109040658444394851724312157 40890246916648069396617059)
              ·
                refine ⟨61335370374972104094925589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40890246916648069396617059 61335370374972104094925589)
                ·
                  refine ⟨2875095486326817379449637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61335370374972104094925589 2875095486326817379449637)
                  ·
                    refine ⟨539080403686278258646807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875095486326817379449637 539080403686278258646807)
                    ·
                      rfl

theorem cell22_1574783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_1574783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574783 prefixEnd_1574783 := by exact prefixLift 1574783
  have htrace : WordTrace (prefixWord ++ tailWord_1574783) baseStart_1574783 baseEnd_1574783 := by
    simpa [prefixWord, tailWord_1574783, baseEnd_1574783] using wordTrace_append hprefix tailTrace_1574783
  have hstable : (prefixWord ++ tailWord_1574783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574783).length < 2 ^ (prefixWord ++ tailWord_1574783).sum := by decide
  have hdescent : baseEnd_1574783 < baseStart_1574783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574802 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1574802 : Nat := 118140960795 + 1574802 * 2 ^ 59
def prefixEnd_1574802 : Nat := 4983230072969 + 3 ^ 40 * 1574802 * 2
def baseEnd_1574802 : Nat := 539086907774568542421749

theorem tailTrace_1574802 : CollatzResearch.WordTrace tailWord_1574802 prefixEnd_1574802 539086907774568542421749 := by
  unfold tailWord_1574802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14359436910192195903531665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38291831760512522409417773 14359436910192195903531665)
  ·
    refine ⟨10769577682644146927648749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14359436910192195903531665 10769577682644146927648749)
    ·
      refine ⟨4038591630991555097868281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10769577682644146927648749 4038591630991555097868281)
      ·
        refine ⟨3028943723243666323401211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038591630991555097868281 3028943723243666323401211)
        ·
          refine ⟨4543415584865499485101817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028943723243666323401211 4543415584865499485101817)
          ·
            refine ⟨3407561688649124613826363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4543415584865499485101817 3407561688649124613826363)
            ·
              refine ⟨5111342532973686920739545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407561688649124613826363 5111342532973686920739545)
              ·
                refine ⟨3833506899730265190554659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5111342532973686920739545 3833506899730265190554659)
                ·
                  refine ⟨5750260349595397785831989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833506899730265190554659 5750260349595397785831989)
                  ·
                    refine ⟨539086907774568542421749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5750260349595397785831989 539086907774568542421749)
                    ·
                      rfl

theorem cell22_1574802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1574802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574802 prefixEnd_1574802 := by exact prefixLift 1574802
  have htrace : WordTrace (prefixWord ++ tailWord_1574802) baseStart_1574802 baseEnd_1574802 := by
    simpa [prefixWord, tailWord_1574802, baseEnd_1574802] using wordTrace_append hprefix tailTrace_1574802
  have hstable : (prefixWord ++ tailWord_1574802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574802).length < 2 ^ (prefixWord ++ tailWord_1574802).sum := by decide
  have hdescent : baseEnd_1574802 < baseStart_1574802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574815 : List Nat := [1, 1, 2, 5, 4, 9]
def baseStart_1574815 : Nat := 118140960795 + 1574815 * 2 ^ 59
def prefixEnd_1574815 : Nat := 4983230072969 + 3 ^ 40 * 1574815 * 2
def baseEnd_1574815 : Nat := 6655448863459763479589

theorem tailTrace_1574815 : CollatzResearch.WordTrace tailWord_1574815 prefixEnd_1574815 6655448863459763479589 := by
  unfold tailWord_1574815
  simp only [CollatzResearch.WordTrace]
  refine ⟨57438221789721686834349899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38292147859814457889566599 57438221789721686834349899)
  ·
    refine ⟨86157332684582530251524849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57438221789721686834349899 86157332684582530251524849)
    ·
      refine ⟨64617999513436897688643637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86157332684582530251524849 64617999513436897688643637)
      ·
        refine ⟨6057937454384709158310341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64617999513436897688643637 6057937454384709158310341)
        ·
          refine ⟨1135863272697132967183189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6057937454384709158310341 1135863272697132967183189)
          ·
            refine ⟨6655448863459763479589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1135863272697132967183189 6655448863459763479589)
            ·
              rfl

theorem cell22_1574815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 9].length) (baseStart_1574815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574815 prefixEnd_1574815 := by exact prefixLift 1574815
  have htrace : WordTrace (prefixWord ++ tailWord_1574815) baseStart_1574815 baseEnd_1574815 := by
    simpa [prefixWord, tailWord_1574815, baseEnd_1574815] using wordTrace_append hprefix tailTrace_1574815
  have hstable : (prefixWord ++ tailWord_1574815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574815).length < 2 ^ (prefixWord ++ tailWord_1574815).sum := by decide
  have hdescent : baseEnd_1574815 < baseStart_1574815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574877 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 7]
def baseStart_1574877 : Nat := 118140960795 + 1574877 * 2 ^ 59
def prefixEnd_1574877 : Nat := 4983230072969 + 3 ^ 40 * 1574877 * 2
def baseEnd_1574877 : Nat := 179704193935764448932173

theorem tailTrace_1574877 : CollatzResearch.WordTrace tailWord_1574877 prefixEnd_1574877 179704193935764448932173 := by
  unfold tailWord_1574877
  simp only [CollatzResearch.WordTrace]
  refine ⟨57440483115497071423106885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38293655410331380948737923 57440483115497071423106885)
  ·
    refine ⟨10770090584155700891832541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57440483115497071423106885 10770090584155700891832541)
    ·
      refine ⟨4038783969058387834437203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10770090584155700891832541 4038783969058387834437203)
      ·
        refine ⟨6058175953587581751655805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038783969058387834437203 6058175953587581751655805)
        ·
          refine ⟨2271815982595343156870927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6058175953587581751655805 2271815982595343156870927)
          ·
            refine ⟨3407723973893014735306391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271815982595343156870927 3407723973893014735306391)
            ·
              refine ⟨5111585960839522102959587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407723973893014735306391 5111585960839522102959587)
              ·
                refine ⟨7667378941259283154439381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111585960839522102959587 7667378941259283154439381)
                ·
                  refine ⟨179704193935764448932173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7667378941259283154439381 179704193935764448932173)
                  ·
                    rfl

theorem cell22_1574877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_1574877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574877 prefixEnd_1574877 := by exact prefixLift 1574877
  have htrace : WordTrace (prefixWord ++ tailWord_1574877) baseStart_1574877 baseEnd_1574877 := by
    simpa [prefixWord, tailWord_1574877, baseEnd_1574877] using wordTrace_append hprefix tailTrace_1574877
  have hstable : (prefixWord ++ tailWord_1574877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574877).length < 2 ^ (prefixWord ++ tailWord_1574877).sum := by decide
  have hdescent : baseEnd_1574877 < baseStart_1574877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574894 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_1574894 : Nat := 118140960795 + 1574894 * 2 ^ 59
def prefixEnd_1574894 : Nat := 4983230072969 + 3 ^ 40 * 1574894 * 2
def baseEnd_1574894 : Nat := 179706133751570323040489

theorem tailTrace_1574894 : CollatzResearch.WordTrace tailWord_1574894 prefixEnd_1574894 179706133751570323040489 := by
  unfold tailWord_1574894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180137894554435415809467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38294068770956988884317157 7180137894554435415809467)
  ·
    refine ⟨10770206841831653123714201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7180137894554435415809467 10770206841831653123714201)
    ·
      refine ⟨8077655131373739842785651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10770206841831653123714201 8077655131373739842785651)
      ·
        refine ⟨12116482697060609764178477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8077655131373739842785651 12116482697060609764178477)
        ·
          refine ⟨4543681011397728661566929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12116482697060609764178477 4543681011397728661566929)
          ·
            refine ⟨3407760758548296496175197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4543681011397728661566929 3407760758548296496175197)
            ·
              refine ⟨1277910284455611186065699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3407760758548296496175197 1277910284455611186065699)
              ·
                refine ⟨1916865426683416779098549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277910284455611186065699 1916865426683416779098549)
                ·
                  refine ⟨179706133751570323040489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1916865426683416779098549 179706133751570323040489)
                  ·
                    rfl

theorem cell22_1574894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_1574894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574894 prefixEnd_1574894 := by exact prefixLift 1574894
  have htrace : WordTrace (prefixWord ++ tailWord_1574894) baseStart_1574894 baseEnd_1574894 := by
    simpa [prefixWord, tailWord_1574894, baseEnd_1574894] using wordTrace_append hprefix tailTrace_1574894
  have hstable : (prefixWord ++ tailWord_1574894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574894).length < 2 ^ (prefixWord ++ tailWord_1574894).sum := by decide
  have hdescent : baseEnd_1574894 < baseStart_1574894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574905 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 6]
def baseStart_1574905 : Nat := 118140960795 + 1574905 * 2 ^ 59
def prefixEnd_1574905 : Nat := 4983230072969 + 3 ^ 40 * 1574905 * 2
def baseEnd_1574905 : Nat := 179707388926503535698811

theorem tailTrace_1574905 : CollatzResearch.WordTrace tailWord_1574905 prefixEnd_1574905 179707388926503535698811 := by
  unfold tailWord_1574905
  simp only [CollatzResearch.WordTrace]
  refine ⟨57441504359395632205126169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38294336239597088136750779 57441504359395632205126169)
  ·
    refine ⟨43081128269546724153844627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57441504359395632205126169 43081128269546724153844627)
    ·
      refine ⟨64621692404320086230766941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43081128269546724153844627 64621692404320086230766941)
      ·
        refine ⟨24233134651620032336537603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64621692404320086230766941 24233134651620032336537603)
        ·
          refine ⟨36349701977430048504806405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24233134651620032336537603 36349701977430048504806405)
          ·
            refine ⟨6815569120768134094651201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36349701977430048504806405 6815569120768134094651201)
            ·
              refine ⟨5111676840576100570988401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6815569120768134094651201 5111676840576100570988401)
              ·
                refine ⟨3833757630432075428241301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5111676840576100570988401 3833757630432075428241301)
                ·
                  refine ⟨179707388926503535698811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3833757630432075428241301 179707388926503535698811)
                  ·
                    rfl

theorem cell22_1574905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_1574905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574905 prefixEnd_1574905 := by exact prefixLift 1574905
  have htrace : WordTrace (prefixWord ++ tailWord_1574905) baseStart_1574905 baseEnd_1574905 := by
    simpa [prefixWord, tailWord_1574905, baseEnd_1574905] using wordTrace_append hprefix tailTrace_1574905
  have hstable : (prefixWord ++ tailWord_1574905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574905).length < 2 ^ (prefixWord ++ tailWord_1574905).sum := by decide
  have hdescent : baseEnd_1574905 < baseStart_1574905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574920 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1574920 : Nat := 118140960795 + 1574920 * 2 ^ 59
def prefixEnd_1574920 : Nat := 4983230072969 + 3 ^ 40 * 1574920 * 2
def baseEnd_1574920 : Nat := 539127301586055567971387

theorem tailTrace_1574920 : CollatzResearch.WordTrace tailWord_1574920 prefixEnd_1574920 539127301586055567971387 := by
  unfold tailWord_1574920
  simp only [CollatzResearch.WordTrace]
  refine ⟨28721025727170644883461107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38294700969560859844614809 28721025727170644883461107)
  ·
    refine ⟨43081538590755967325191661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28721025727170644883461107 43081538590755967325191661)
    ·
      refine ⟨16155576971533487746946873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43081538590755967325191661 16155576971533487746946873)
      ·
        refine ⟨12116682728650115810210155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16155576971533487746946873 12116682728650115810210155)
        ·
          refine ⟨18175024092975173715315233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12116682728650115810210155 18175024092975173715315233)
          ·
            refine ⟨13631268069731380286486425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18175024092975173715315233 13631268069731380286486425)
            ·
              refine ⟨10223451052298535214864819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13631268069731380286486425 10223451052298535214864819)
              ·
                refine ⟨15335176578447802822297229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10223451052298535214864819 15335176578447802822297229)
                ·
                  refine ⟨5750691216917926058361461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15335176578447802822297229 5750691216917926058361461)
                  ·
                    refine ⟨539127301586055567971387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5750691216917926058361461 539127301586055567971387)
                    ·
                      rfl

theorem cell22_1574920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1574920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574920 prefixEnd_1574920 := by exact prefixLift 1574920
  have htrace : WordTrace (prefixWord ++ tailWord_1574920) baseStart_1574920 baseEnd_1574920 := by
    simpa [prefixWord, tailWord_1574920, baseEnd_1574920] using wordTrace_append hprefix tailTrace_1574920
  have hstable : (prefixWord ++ tailWord_1574920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574920).length < 2 ^ (prefixWord ++ tailWord_1574920).sum := by decide
  have hdescent : baseEnd_1574920 < baseStart_1574920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574937 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_1574937 : Nat := 118140960795 + 1574937 * 2 ^ 59
def prefixEnd_1574937 : Nat := 4983230072969 + 3 ^ 40 * 1574937 * 2
def baseEnd_1574937 : Nat := 539133121033473190296335

theorem tailTrace_1574937 : CollatzResearch.WordTrace tailWord_1574937 prefixEnd_1574937 539133121033473190296335 := by
  unfold tailWord_1574937
  simp only [CollatzResearch.WordTrace]
  refine ⟨57442671495279701670291065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38295114330186467780194043 57442671495279701670291065)
  ·
    refine ⟨43082003621459776252718299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57442671495279701670291065 43082003621459776252718299)
    ·
      refine ⟨64623005432189664379077449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43082003621459776252718299 64623005432189664379077449)
      ·
        refine ⟨48467254074142248284308087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64623005432189664379077449 48467254074142248284308087)
        ·
          refine ⟨72700881111213372426462131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48467254074142248284308087 72700881111213372426462131)
          ·
            refine ⟨109051321666820058639693197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72700881111213372426462131 109051321666820058639693197)
            ·
              refine ⟨40894245625057521989884949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109051321666820058639693197 40894245625057521989884949)
              ·
                refine ⟨1916917763674571343275857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40894245625057521989884949 1916917763674571343275857)
                ·
                  refine ⟨1437688322755928507456893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1916917763674571343275857 1437688322755928507456893)
                  ·
                    refine ⟨539133121033473190296335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1437688322755928507456893 539133121033473190296335)
                    ·
                      rfl

theorem cell22_1574937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_1574937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574937 prefixEnd_1574937 := by exact prefixLift 1574937
  have htrace : WordTrace (prefixWord ++ tailWord_1574937) baseStart_1574937 baseEnd_1574937 := by
    simpa [prefixWord, tailWord_1574937, baseEnd_1574937] using wordTrace_append hprefix tailTrace_1574937
  have hstable : (prefixWord ++ tailWord_1574937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574937).length < 2 ^ (prefixWord ++ tailWord_1574937).sum := by decide
  have hdescent : baseEnd_1574937 < baseStart_1574937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574965 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1574965 : Nat := 118140960795 + 1574965 * 2 ^ 59
def prefixEnd_1574965 : Nat := 4983230072969 + 3 ^ 40 * 1574965 * 2
def baseEnd_1574965 : Nat := 539142706005690450596249

theorem tailTrace_1574965 : CollatzResearch.WordTrace tailWord_1574965 prefixEnd_1574965 539142706005690450596249 := by
  unfold tailWord_1574965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57443692739178262452310349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38295795159452174968206899 57443692739178262452310349)
  ·
    refine ⟨21541384777191848419616381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57443692739178262452310349 21541384777191848419616381)
    ·
      refine ⟨8078019291446943157356143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21541384777191848419616381 8078019291446943157356143)
      ·
        refine ⟨12117028937170414736034215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8078019291446943157356143 12117028937170414736034215)
        ·
          refine ⟨18175543405755622104051323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12117028937170414736034215 18175543405755622104051323)
          ·
            refine ⟨27263315108633433156076985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18175543405755622104051323 27263315108633433156076985)
            ·
              refine ⟨20447486331475074867057739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27263315108633433156076985 20447486331475074867057739)
              ·
                refine ⟨30671229497212612300586609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20447486331475074867057739 30671229497212612300586609)
                ·
                  refine ⟨23003422122909459225439957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30671229497212612300586609 23003422122909459225439957)
                  ·
                    refine ⟨539142706005690450596249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23003422122909459225439957 539142706005690450596249)
                    ·
                      rfl

theorem cell22_1574965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1574965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574965 prefixEnd_1574965 := by exact prefixLift 1574965
  have htrace : WordTrace (prefixWord ++ tailWord_1574965) baseStart_1574965 baseEnd_1574965 := by
    simpa [prefixWord, tailWord_1574965, baseEnd_1574965] using wordTrace_append hprefix tailTrace_1574965
  have hstable : (prefixWord ++ tailWord_1574965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574965).length < 2 ^ (prefixWord ++ tailWord_1574965).sum := by decide
  have hdescent : baseEnd_1574965 < baseStart_1574965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574969 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_1574969 : Nat := 118140960795 + 1574969 * 2 ^ 59
def prefixEnd_1574969 : Nat := 4983230072969 + 3 ^ 40 * 1574969 * 2
def baseEnd_1574969 : Nat := 539144075287435773496237

theorem tailTrace_1574969 : CollatzResearch.WordTrace tailWord_1574969 prefixEnd_1574969 539144075287435773496237 := by
  unfold tailWord_1574969
  simp only [CollatzResearch.WordTrace]
  refine ⟨57443838631163771135455961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38295892420775847423637307 57443838631163771135455961)
  ·
    refine ⟨43082878973372828351591971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57443838631163771135455961 43082878973372828351591971)
    ·
      refine ⟨64624318460059242527387957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43082878973372828351591971 64624318460059242527387957)
      ·
        refine ⟨6058529855630553986942621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64624318460059242527387957 6058529855630553986942621)
        ·
          refine ⟨2271948695861457745103483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6058529855630553986942621 2271948695861457745103483)
          ·
            refine ⟨3407923043792186617655225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271948695861457745103483 3407923043792186617655225)
            ·
              refine ⟨2555942282844139963241419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407923043792186617655225 2555942282844139963241419)
              ·
                refine ⟨3833913424266209944862129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555942282844139963241419 3833913424266209944862129)
                ·
                  refine ⟨2875435068199657458646597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833913424266209944862129 2875435068199657458646597)
                  ·
                    refine ⟨539144075287435773496237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875435068199657458646597 539144075287435773496237)
                    ·
                      rfl

theorem cell22_1574969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_1574969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1574969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1574969 prefixEnd_1574969 := by exact prefixLift 1574969
  have htrace : WordTrace (prefixWord ++ tailWord_1574969) baseStart_1574969 baseEnd_1574969 := by
    simpa [prefixWord, tailWord_1574969, baseEnd_1574969] using wordTrace_append hprefix tailTrace_1574969
  have hstable : (prefixWord ++ tailWord_1574969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574969).length < 2 ^ (prefixWord ++ tailWord_1574969).sum := by decide
  have hdescent : baseEnd_1574969 < baseStart_1574969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575012 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_1575012 : Nat := 118140960795 + 1575012 * 2 ^ 59
def prefixEnd_1575012 : Nat := 4983230072969 + 3 ^ 40 * 1575012 * 2
def baseEnd_1575012 : Nat := 179719598355399331557035

theorem tailTrace_1575012 : CollatzResearch.WordTrace tailWord_1575012 prefixEnd_1575012 179719598355399331557035 := by
  unfold tailWord_1575012
  simp only [CollatzResearch.WordTrace]
  refine ⟨28722703485003994739635645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38296937980005326319514193 28722703485003994739635645)
  ·
    refine ⟨10771013806876498027363367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28722703485003994739635645 10771013806876498027363367)
    ·
      refine ⟨16156520710314747041045051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771013806876498027363367 16156520710314747041045051)
      ·
        refine ⟨24234781065472120561567577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16156520710314747041045051 24234781065472120561567577)
        ·
          refine ⟨18176085799104090421175683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24234781065472120561567577 18176085799104090421175683)
          ·
            refine ⟨27264128698656135631763525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18176085799104090421175683 27264128698656135631763525)
            ·
              refine ⟨5112024130998025430955661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27264128698656135631763525 5112024130998025430955661)
              ·
                refine ⟨1917009049124259536608373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5112024130998025430955661 1917009049124259536608373)
                ·
                  refine ⟨179719598355399331557035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1917009049124259536608373 179719598355399331557035)
                  ·
                    rfl

theorem cell22_1575012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_1575012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575012 prefixEnd_1575012 := by exact prefixLift 1575012
  have htrace : WordTrace (prefixWord ++ tailWord_1575012) baseStart_1575012 baseEnd_1575012 := by
    simpa [prefixWord, tailWord_1575012, baseEnd_1575012] using wordTrace_append hprefix tailTrace_1575012
  have hstable : (prefixWord ++ tailWord_1575012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575012).length < 2 ^ (prefixWord ++ tailWord_1575012).sum := by decide
  have hdescent : baseEnd_1575012 < baseStart_1575012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575040 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_1575040 : Nat := 118140960795 + 1575040 * 2 ^ 59
def prefixEnd_1575040 : Nat := 4983230072969 + 3 ^ 40 * 1575040 * 2
def baseEnd_1575040 : Nat := 179722793346138418323673

theorem tailTrace_1575040 : CollatzResearch.WordTrace tailWord_1575040 prefixEnd_1575040 179722793346138418323673 := by
  unfold tailWord_1575040
  simp only [CollatzResearch.WordTrace]
  refine ⟨28723214106953275130645287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38297618809271033507527049 28723214106953275130645287)
  ·
    refine ⟨43084821160429912695967931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28723214106953275130645287 43084821160429912695967931)
    ·
      refine ⟨64627231740644869043951897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43084821160429912695967931 64627231740644869043951897)
      ·
        refine ⟨48470423805483651782963923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64627231740644869043951897 48470423805483651782963923)
        ·
          refine ⟨72705635708225477674445885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48470423805483651782963923 72705635708225477674445885)
          ·
            refine ⟨27264613390584554127917207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72705635708225477674445885 27264613390584554127917207)
            ·
              refine ⟨40896920085876831191875811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27264613390584554127917207 40896920085876831191875811)
              ·
                refine ⟨61345380128815246787813717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40896920085876831191875811 61345380128815246787813717)
                ·
                  refine ⟨179722793346138418323673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 61345380128815246787813717 179722793346138418323673)
                  ·
                    rfl

theorem cell22_1575040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_1575040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575040 prefixEnd_1575040 := by exact prefixLift 1575040
  have htrace : WordTrace (prefixWord ++ tailWord_1575040) baseStart_1575040 baseEnd_1575040 := by
    simpa [prefixWord, tailWord_1575040, baseEnd_1575040] using wordTrace_append hprefix tailTrace_1575040
  have hstable : (prefixWord ++ tailWord_1575040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575040).length < 2 ^ (prefixWord ++ tailWord_1575040).sum := by decide
  have hdescent : baseEnd_1575040 < baseStart_1575040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575074 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1575074 : Nat := 118140960795 + 1575074 * 2 ^ 59
def prefixEnd_1575074 : Nat := 4983230072969 + 3 ^ 40 * 1575074 * 2
def baseEnd_1575074 : Nat := 179726672977750166540305

theorem tailTrace_1575074 : CollatzResearch.WordTrace tailWord_1575074 prefixEnd_1575074 179726672977750166540305 := by
  unfold tailWord_1575074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361917073945843517007069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38298445530522249378685517 14361917073945843517007069)
  ·
    refine ⟨5385718902729691318877651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14361917073945843517007069 5385718902729691318877651)
    ·
      refine ⟨8078578354094536978316477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5385718902729691318877651 8078578354094536978316477)
      ·
        refine ⟨3029466882785451366868679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8078578354094536978316477 3029466882785451366868679)
        ·
          refine ⟨4544200324178177050303019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029466882785451366868679 4544200324178177050303019)
          ·
            refine ⟨6816300486267265575454529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544200324178177050303019 6816300486267265575454529)
            ·
              refine ⟨5112225364700449181590897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6816300486267265575454529 5112225364700449181590897)
              ·
                refine ⟨3834169023525336886193173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112225364700449181590897 3834169023525336886193173)
                ·
                  refine ⟨179726672977750166540305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3834169023525336886193173 179726672977750166540305)
                  ·
                    rfl

theorem cell22_1575074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1575074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575074 prefixEnd_1575074 := by exact prefixLift 1575074
  have htrace : WordTrace (prefixWord ++ tailWord_1575074) baseStart_1575074 baseEnd_1575074 := by
    simpa [prefixWord, tailWord_1575074, baseEnd_1575074] using wordTrace_append hprefix tailTrace_1575074
  have hstable : (prefixWord ++ tailWord_1575074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575074).length < 2 ^ (prefixWord ++ tailWord_1575074).sum := by decide
  have hdescent : baseEnd_1575074 < baseStart_1575074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575076 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1575076 : Nat := 118140960795 + 1575076 * 2 ^ 59
def prefixEnd_1575076 : Nat := 4983230072969 + 3 ^ 40 * 1575076 * 2
def baseEnd_1575076 : Nat := 539180703574123161070909

theorem tailTrace_1575076 : CollatzResearch.WordTrace tailWord_1575076 prefixEnd_1575076 539180703574123161070909 := by
  unfold tailWord_1575076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28723870620888064204800541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38298494161184085606400721 28723870620888064204800541)
  ·
    refine ⟨10771451482833024076800203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28723870620888064204800541 10771451482833024076800203)
    ·
      refine ⟨16157177224249536115200305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771451482833024076800203 16157177224249536115200305)
      ·
        refine ⟨12117882918187152086400229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16157177224249536115200305 12117882918187152086400229)
        ·
          refine ⟨2272103047160091016200043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12117882918187152086400229 2272103047160091016200043)
          ·
            refine ⟨3408154570740136524300065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272103047160091016200043 3408154570740136524300065)
            ·
              refine ⟨2556115928055102393225049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408154570740136524300065 2556115928055102393225049)
              ·
                refine ⟨1917086946041326794918787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556115928055102393225049 1917086946041326794918787)
                ·
                  refine ⟨2875630419061990192378181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917086946041326794918787 2875630419061990192378181)
                  ·
                    refine ⟨539180703574123161070909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875630419061990192378181 539180703574123161070909)
                    ·
                      rfl

theorem cell22_1575076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1575076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575076 prefixEnd_1575076 := by exact prefixLift 1575076
  have htrace : WordTrace (prefixWord ++ tailWord_1575076) baseStart_1575076 baseEnd_1575076 := by
    simpa [prefixWord, tailWord_1575076, baseEnd_1575076] using wordTrace_append hprefix tailTrace_1575076
  have hstable : (prefixWord ++ tailWord_1575076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575076).length < 2 ^ (prefixWord ++ tailWord_1575076).sum := by decide
  have hdescent : baseEnd_1575076 < baseStart_1575076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575087 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 2, 4]
def baseStart_1575087 : Nat := 118140960795 + 1575087 * 2 ^ 59
def prefixEnd_1575087 : Nat := 4983230072969 + 3 ^ 40 * 1575087 * 2
def baseEnd_1575087 : Nat := 539184469098922799045875

theorem tailTrace_1575087 : CollatzResearch.WordTrace tailWord_1575087 prefixEnd_1575087 539184469098922799045875 := by
  unfold tailWord_1575087
  simp only [CollatzResearch.WordTrace]
  refine ⟨57448142444736277288251515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38298761629824184858834343 57448142444736277288251515)
  ·
    refine ⟨86172213667104415932377273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57448142444736277288251515 86172213667104415932377273)
    ·
      refine ⟨64629160250328311949282955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86172213667104415932377273 64629160250328311949282955)
      ·
        refine ⟨96943740375492467923924433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64629160250328311949282955 96943740375492467923924433)
        ·
          refine ⟨72707805281619350942943325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96943740375492467923924433 72707805281619350942943325)
          ·
            refine ⟨27265426980607256603603747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72707805281619350942943325 27265426980607256603603747)
            ·
              refine ⟨40898140470910884905405621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27265426980607256603603747 40898140470910884905405621)
              ·
                refine ⟨3834200669147895459881777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40898140470910884905405621 3834200669147895459881777)
                ·
                  refine ⟨2875650501860921594911333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3834200669147895459881777 2875650501860921594911333)
                  ·
                    refine ⟨539184469098922799045875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875650501860921594911333 539184469098922799045875)
                    ·
                      rfl

theorem cell22_1575087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_1575087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575087 prefixEnd_1575087 := by exact prefixLift 1575087
  have htrace : WordTrace (prefixWord ++ tailWord_1575087) baseStart_1575087 baseEnd_1575087 := by
    simpa [prefixWord, tailWord_1575087, baseEnd_1575087] using wordTrace_append hprefix tailTrace_1575087
  have hstable : (prefixWord ++ tailWord_1575087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575087).length < 2 ^ (prefixWord ++ tailWord_1575087).sum := by decide
  have hdescent : baseEnd_1575087 < baseStart_1575087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575104 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_1575104 : Nat := 118140960795 + 1575104 * 2 ^ 59
def prefixEnd_1575104 : Nat := 4983230072969 + 3 ^ 40 * 1575104 * 2
def baseEnd_1575104 : Nat := 539190288546340421370823

theorem tailTrace_1575104 : CollatzResearch.WordTrace tailWord_1575104 prefixEnd_1575104 539190288546340421370823 := by
  unfold tailWord_1575104
  simp only [CollatzResearch.WordTrace]
  refine ⟨28724381242837344595810183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38299174990449792794413577 28724381242837344595810183)
  ·
    refine ⟨43086571864256016893715275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28724381242837344595810183 43086571864256016893715275)
    ·
      refine ⟨64629857796384025340572913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43086571864256016893715275 64629857796384025340572913)
      ·
        refine ⟨48472393347288019005429685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64629857796384025340572913 48472393347288019005429685)
        ·
          refine ⟨4544286876308251781759033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48472393347288019005429685 4544286876308251781759033)
          ·
            refine ⟨3408215157231188836319275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544286876308251781759033 3408215157231188836319275)
            ·
              refine ⟨5112322735846783254478913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408215157231188836319275 5112322735846783254478913)
              ·
                refine ⟨3834242051885087440859185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112322735846783254478913 3834242051885087440859185)
                ·
                  refine ⟨2875681538913815580644389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3834242051885087440859185 2875681538913815580644389)
                  ·
                    refine ⟨539190288546340421370823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875681538913815580644389 539190288546340421370823)
                    ·
                      rfl

theorem cell22_1575104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_1575104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575104 prefixEnd_1575104 := by exact prefixLift 1575104
  have htrace : WordTrace (prefixWord ++ tailWord_1575104) baseStart_1575104 baseEnd_1575104 := by
    simpa [prefixWord, tailWord_1575104, baseEnd_1575104] using wordTrace_append hprefix tailTrace_1575104
  have hstable : (prefixWord ++ tailWord_1575104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575104).length < 2 ^ (prefixWord ++ tailWord_1575104).sum := by decide
  have hdescent : baseEnd_1575104 < baseStart_1575104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575108 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1575108 : Nat := 118140960795 + 1575108 * 2 ^ 59
def prefixEnd_1575108 : Nat := 4983230072969 + 3 ^ 40 * 1575108 * 2
def baseEnd_1575108 : Nat := 179730552609361914756937

theorem tailTrace_1575108 : CollatzResearch.WordTrace tailWord_1575108 prefixEnd_1575108 179730552609361914756937 := by
  unfold tailWord_1575108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28724454188830098937382989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38299272251773465249843985 28724454188830098937382989)
  ·
    refine ⟨10771670320811287101518621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28724454188830098937382989 10771670320811287101518621)
    ·
      refine ⟨4039376370304232663069483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10771670320811287101518621 4039376370304232663069483)
      ·
        refine ⟨6059064555456348994604225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039376370304232663069483 6059064555456348994604225)
        ·
          refine ⟨4544298416592261745953169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6059064555456348994604225 4544298416592261745953169)
          ·
            refine ⟨3408223812444196309464877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544298416592261745953169 3408223812444196309464877)
            ·
              refine ⟨1278083929666573616049329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3408223812444196309464877 1278083929666573616049329)
              ·
                refine ⟨958562947249930212036997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278083929666573616049329 958562947249930212036997)
                ·
                  refine ⟨179730552609361914756937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958562947249930212036997 179730552609361914756937)
                  ·
                    rfl

theorem cell22_1575108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1575108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575108 prefixEnd_1575108 := by exact prefixLift 1575108
  have htrace : WordTrace (prefixWord ++ tailWord_1575108) baseStart_1575108 baseEnd_1575108 := by
    simpa [prefixWord, tailWord_1575108, baseEnd_1575108] using wordTrace_append hprefix tailTrace_1575108
  have hstable : (prefixWord ++ tailWord_1575108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575108).length < 2 ^ (prefixWord ++ tailWord_1575108).sum := by decide
  have hdescent : baseEnd_1575108 < baseStart_1575108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575164 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_1575164 : Nat := 118140960795 + 1575164 * 2 ^ 59
def prefixEnd_1575164 : Nat := 4983230072969 + 3 ^ 40 * 1575164 * 2
def baseEnd_1575164 : Nat := 179736942590840088290213

theorem tailTrace_1575164 : CollatzResearch.WordTrace tailWord_1575164 prefixEnd_1575164 179736942590840088290213 := by
  unfold tailWord_1575164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725475432728659719402273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38300633910304879625869697 28725475432728659719402273)
  ·
    refine ⟨21544106574546494789551705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28725475432728659719402273 21544106574546494789551705)
    ·
      refine ⟨16158079930909871092163779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21544106574546494789551705 16158079930909871092163779)
      ·
        refine ⟨24237119896364806638245669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16158079930909871092163779 24237119896364806638245669)
        ·
          refine ⟨4544459980568401244671063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24237119896364806638245669 4544459980568401244671063)
          ·
            refine ⟨6816689970852601867006595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544459980568401244671063 6816689970852601867006595)
            ·
              refine ⟨10225034956278902800509893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816689970852601867006595 10225034956278902800509893)
              ·
                refine ⟨1917194054302294275095605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10225034956278902800509893 1917194054302294275095605)
                ·
                  refine ⟨179736942590840088290213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1917194054302294275095605 179736942590840088290213)
                  ·
                    rfl

theorem cell22_1575164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_1575164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575164 prefixEnd_1575164 := by exact prefixLift 1575164
  have htrace : WordTrace (prefixWord ++ tailWord_1575164) baseStart_1575164 baseEnd_1575164 := by
    simpa [prefixWord, tailWord_1575164, baseEnd_1575164] using wordTrace_append hprefix tailTrace_1575164
  have hstable : (prefixWord ++ tailWord_1575164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575164).length < 2 ^ (prefixWord ++ tailWord_1575164).sum := by decide
  have hdescent : baseEnd_1575164 < baseStart_1575164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575168 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 1, 3]
def baseStart_1575168 : Nat := 118140960795 + 1575168 * 2 ^ 59
def prefixEnd_1575168 : Nat := 4983230072969 + 3 ^ 40 * 1575168 * 2
def baseEnd_1575168 : Nat := 539212197054265587770627

theorem tailTrace_1575168 : CollatzResearch.WordTrace tailWord_1575168 prefixEnd_1575168 539212197054265587770627 := by
  unfold tailWord_1575168
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725548378721414060975079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38300731171628552081300105 28725548378721414060975079)
  ·
    refine ⟨43088322568082121091462619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28725548378721414060975079 43088322568082121091462619)
    ·
      refine ⟨64632483852123181637193929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43088322568082121091462619 64632483852123181637193929)
      ·
        refine ⟨48474362889092386227895447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64632483852123181637193929 48474362889092386227895447)
        ·
          refine ⟨72711544333638579341843171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48474362889092386227895447 72711544333638579341843171)
          ·
            refine ⟨109067316500457869012764757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72711544333638579341843171 109067316500457869012764757)
            ·
              refine ⟨1278132615239740652493337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 109067316500457869012764757 1278132615239740652493337)
              ·
                refine ⟨958599461429805489370003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278132615239740652493337 958599461429805489370003)
                ·
                  refine ⟨1437899192144708234055005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958599461429805489370003 1437899192144708234055005)
                  ·
                    refine ⟨539212197054265587770627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1437899192144708234055005 539212197054265587770627)
                    ·
                      rfl

theorem cell22_1575168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_1575168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575168 prefixEnd_1575168 := by exact prefixLift 1575168
  have htrace : WordTrace (prefixWord ++ tailWord_1575168) baseStart_1575168 baseEnd_1575168 := by
    simpa [prefixWord, tailWord_1575168, baseEnd_1575168] using wordTrace_append hprefix tailTrace_1575168
  have hstable : (prefixWord ++ tailWord_1575168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575168).length < 2 ^ (prefixWord ++ tailWord_1575168).sum := by decide
  have hdescent : baseEnd_1575168 < baseStart_1575168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575226 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_1575226 : Nat := 118140960795 + 1575226 * 2 ^ 59
def prefixEnd_1575226 : Nat := 4983230072969 + 3 ^ 40 * 1575226 * 2
def baseEnd_1575226 : Nat := 179744017213190923273483

theorem tailTrace_1575226 : CollatzResearch.WordTrace tailWord_1575226 prefixEnd_1575226 179744017213190923273483 := by
  unfold tailWord_1575226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14363303047808176006890383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38302141460821802685041021 14363303047808176006890383)
  ·
    refine ⟨21544954571712264010335575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14363303047808176006890383 21544954571712264010335575)
    ·
      refine ⟨32317431857568396015503363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21544954571712264010335575 32317431857568396015503363)
      ·
        refine ⟨48476147786352594023255045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32317431857568396015503363 48476147786352594023255045)
        ·
          refine ⟨9089277709941111379360321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48476147786352594023255045 9089277709941111379360321)
          ·
            refine ⟨6816958282455833534520241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9089277709941111379360321 6816958282455833534520241)
            ·
              refine ⟨5112718711841875150890181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6816958282455833534520241 5112718711841875150890181)
              ·
                refine ⟨958634758470351590791909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5112718711841875150890181 958634758470351590791909)
                ·
                  refine ⟨179744017213190923273483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958634758470351590791909 179744017213190923273483)
                  ·
                    rfl

theorem cell22_1575226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_1575226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575226 prefixEnd_1575226 := by exact prefixLift 1575226
  have htrace : WordTrace (prefixWord ++ tailWord_1575226) baseStart_1575226 baseEnd_1575226 := by
    simpa [prefixWord, tailWord_1575226, baseEnd_1575226] using wordTrace_append hprefix tailTrace_1575226
  have hstable : (prefixWord ++ tailWord_1575226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575226).length < 2 ^ (prefixWord ++ tailWord_1575226).sum := by decide
  have hdescent : baseEnd_1575226 < baseStart_1575226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575380 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1575380 : Nat := 118140960795 + 1575380 * 2 ^ 59
def prefixEnd_1575380 : Nat := 4983230072969 + 3 ^ 40 * 1575380 * 2
def baseEnd_1575380 : Nat := 539284768986767701469977

theorem tailTrace_1575380 : CollatzResearch.WordTrace tailWord_1575380 prefixEnd_1575380 539284768986767701469977 := by
  unfold tailWord_1575380
  simp only [CollatzResearch.WordTrace]
  refine ⟨28729414516337394164333797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38305886021783192219111729 28729414516337394164333797)
  ·
    refine ⟨5386765221813261405812587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28729414516337394164333797 5386765221813261405812587)
    ·
      refine ⟨8080147832719892108718881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5386765221813261405812587 8080147832719892108718881)
      ·
        refine ⟨6060110874539919081539161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8080147832719892108718881 6060110874539919081539161)
        ·
          refine ⟨4545083155904939311154371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6060110874539919081539161 4545083155904939311154371)
          ·
            refine ⟨6817624733857408966731557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545083155904939311154371 6817624733857408966731557)
            ·
              refine ⟨1278304637598264181262167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6817624733857408966731557 1278304637598264181262167)
              ·
                refine ⟨1917456956397396271893251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278304637598264181262167 1917456956397396271893251)
                ·
                  refine ⟨2876185434596094407839877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917456956397396271893251 2876185434596094407839877)
                  ·
                    refine ⟨539284768986767701469977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876185434596094407839877 539284768986767701469977)
                    ·
                      rfl

theorem cell22_1575380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1575380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575380 prefixEnd_1575380 := by exact prefixLift 1575380
  have htrace : WordTrace (prefixWord ++ tailWord_1575380) baseStart_1575380 baseEnd_1575380 := by
    simpa [prefixWord, tailWord_1575380, baseEnd_1575380] using wordTrace_append hprefix tailTrace_1575380
  have hstable : (prefixWord ++ tailWord_1575380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575380).length < 2 ^ (prefixWord ++ tailWord_1575380).sum := by decide
  have hdescent : baseEnd_1575380 < baseStart_1575380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575410 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_1575410 : Nat := 118140960795 + 1575410 * 2 ^ 59
def prefixEnd_1575410 : Nat := 4983230072969 + 3 ^ 40 * 1575410 * 2
def baseEnd_1575410 : Nat := 539295038599857623219885

theorem tailTrace_1575410 : CollatzResearch.WordTrace tailWord_1575410 prefixEnd_1575410 539295038599857623219885 := by
  unfold tailWord_1575410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14364980805641525863064921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38306615481710735634839789 14364980805641525863064921)
  ·
    refine ⟨10773735604231144397298691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14364980805641525863064921 10773735604231144397298691)
    ·
      refine ⟨16160603406346716595948037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773735604231144397298691 16160603406346716595948037)
      ·
        refine ⟨3030113138690009361740257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16160603406346716595948037 3030113138690009361740257)
        ·
          refine ⟨2272584854017507021305193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3030113138690009361740257 2272584854017507021305193)
          ·
            refine ⟨1704438640513130265978895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2272584854017507021305193 1704438640513130265978895)
            ·
              refine ⟨2556657960769695398968343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704438640513130265978895 2556657960769695398968343)
              ·
                refine ⟨3834986941154543098452515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556657960769695398968343 3834986941154543098452515)
                ·
                  refine ⟨5752480411731814647678773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834986941154543098452515 5752480411731814647678773)
                  ·
                    refine ⟨539295038599857623219885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5752480411731814647678773 539295038599857623219885)
                    ·
                      rfl

theorem cell22_1575410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_1575410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575410 prefixEnd_1575410 := by exact prefixLift 1575410
  have htrace : WordTrace (prefixWord ++ tailWord_1575410) baseStart_1575410 baseEnd_1575410 := by
    simpa [prefixWord, tailWord_1575410, baseEnd_1575410] using wordTrace_append hprefix tailTrace_1575410
  have hstable : (prefixWord ++ tailWord_1575410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575410).length < 2 ^ (prefixWord ++ tailWord_1575410).sum := by decide
  have hdescent : baseEnd_1575410 < baseStart_1575410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575511 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1575511 : Nat := 118140960795 + 1575511 * 2 ^ 59
def prefixEnd_1575511 : Nat := 4983230072969 + 3 ^ 40 * 1575511 * 2
def baseEnd_1575511 : Nat := 539329612963927026444575

theorem tailTrace_1575511 : CollatzResearch.WordTrace tailWord_1575511 prefixEnd_1575511 539329612963927026444575 := by
  unfold tailWord_1575511
  simp only [CollatzResearch.WordTrace]
  refine ⟨57463606995200197701686387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38309071330133465134457591 57463606995200197701686387)
  ·
    refine ⟨86195410492800296552529581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57463606995200197701686387 86195410492800296552529581)
    ·
      refine ⟨32323278934800111207198593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86195410492800296552529581 32323278934800111207198593)
      ·
        refine ⟨24242459201100083405398945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32323278934800111207198593 24242459201100083405398945)
        ·
          refine ⟨18181844400825062554049209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24242459201100083405398945 18181844400825062554049209)
          ·
            refine ⟨13636383300618796915536907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18181844400825062554049209 13636383300618796915536907)
            ·
              refine ⟨20454574950928195373305361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13636383300618796915536907 20454574950928195373305361)
              ·
                refine ⟨15340931213196146529979021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20454574950928195373305361 15340931213196146529979021)
                ·
                  refine ⟨5752849204948554948742133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15340931213196146529979021 5752849204948554948742133)
                  ·
                    refine ⟨539329612963927026444575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5752849204948554948742133 539329612963927026444575)
                    ·
                      rfl

theorem cell22_1575511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1575511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575511 prefixEnd_1575511 := by exact prefixLift 1575511
  have htrace : WordTrace (prefixWord ++ tailWord_1575511) baseStart_1575511 baseEnd_1575511 := by
    simpa [prefixWord, tailWord_1575511, baseEnd_1575511] using wordTrace_append hprefix tailTrace_1575511
  have hstable : (prefixWord ++ tailWord_1575511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575511).length < 2 ^ (prefixWord ++ tailWord_1575511).sum := by decide
  have hdescent : baseEnd_1575511 < baseStart_1575511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575543 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 2, 4]
def baseStart_1575543 : Nat := 118140960795 + 1575543 * 2 ^ 59
def prefixEnd_1575543 : Nat := 4983230072969 + 3 ^ 40 * 1575543 * 2
def baseEnd_1575543 : Nat := 539340567217889609644477

theorem tailTrace_1575543 : CollatzResearch.WordTrace tailWord_1575543 prefixEnd_1575543 539340567217889609644477 := by
  unfold tailWord_1575543
  simp only [CollatzResearch.WordTrace]
  refine ⟨57464774131084267166851283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38309849420722844777900855 57464774131084267166851283)
  ·
    refine ⟨86197161196626400750276925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57464774131084267166851283 86197161196626400750276925)
    ·
      refine ⟨32323935448734900281353847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86197161196626400750276925 32323935448734900281353847)
      ·
        refine ⟨48485903173102350422030771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32323935448734900281353847 48485903173102350422030771)
        ·
          refine ⟨72728854759653525633046157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48485903173102350422030771 72728854759653525633046157)
          ·
            refine ⟨27273320534870072112392309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72728854759653525633046157 27273320534870072112392309)
            ·
              refine ⟨2556873800144069260536779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27273320534870072112392309 2556873800144069260536779)
              ·
                refine ⟨3835310700216103890805169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556873800144069260536779 3835310700216103890805169)
                ·
                  refine ⟨2876483025162077918103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3835310700216103890805169 2876483025162077918103877)
                  ·
                    refine ⟨539340567217889609644477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876483025162077918103877 539340567217889609644477)
                    ·
                      rfl

theorem cell22_1575543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_1575543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575543 prefixEnd_1575543 := by exact prefixLift 1575543
  have htrace : WordTrace (prefixWord ++ tailWord_1575543) baseStart_1575543 baseEnd_1575543 := by
    simpa [prefixWord, tailWord_1575543, baseEnd_1575543] using wordTrace_append hprefix tailTrace_1575543
  have hstable : (prefixWord ++ tailWord_1575543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575543).length < 2 ^ (prefixWord ++ tailWord_1575543).sum := by decide
  have hdescent : baseEnd_1575543 < baseStart_1575543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575549 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_1575549 : Nat := 118140960795 + 1575549 * 2 ^ 59
def prefixEnd_1575549 : Nat := 4983230072969 + 3 ^ 40 * 1575549 * 2
def baseEnd_1575549 : Nat := 539342621140507593994459

theorem tailTrace_1575549 : CollatzResearch.WordTrace tailWord_1575549 prefixEnd_1575549 539342621140507593994459 := by
  unfold tailWord_1575549
  simp only [CollatzResearch.WordTrace]
  refine ⟨57464992969062530191569701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38309995312708353461046467 57464992969062530191569701)
  ·
    refine ⟨10774686181699224410919319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57464992969062530191569701 10774686181699224410919319)
    ·
      refine ⟨16162029272548836616378979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10774686181699224410919319 16162029272548836616378979)
      ·
        refine ⟨24243043908823254924568469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16162029272548836616378979 24243043908823254924568469)
        ·
          refine ⟨1136392683226090074589147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24243043908823254924568469 1136392683226090074589147)
          ·
            refine ⟨1704589024839135111883721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136392683226090074589147 1704589024839135111883721)
            ·
              refine ⟨1278441768629351333912791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704589024839135111883721 1278441768629351333912791)
              ·
                refine ⟨1917662652944027000869187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278441768629351333912791 1917662652944027000869187)
                ·
                  refine ⟨2876493979416040501303781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917662652944027000869187 2876493979416040501303781)
                  ·
                    refine ⟨539342621140507593994459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876493979416040501303781 539342621140507593994459)
                    ·
                      rfl

theorem cell22_1575549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_1575549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575549 prefixEnd_1575549 := by exact prefixLift 1575549
  have htrace : WordTrace (prefixWord ++ tailWord_1575549) baseStart_1575549 baseEnd_1575549 := by
    simpa [prefixWord, tailWord_1575549, baseEnd_1575549] using wordTrace_append hprefix tailTrace_1575549
  have hstable : (prefixWord ++ tailWord_1575549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575549).length < 2 ^ (prefixWord ++ tailWord_1575549).sum := by decide
  have hdescent : baseEnd_1575549 < baseStart_1575549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575624 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 1, 3]
def baseStart_1575624 : Nat := 118140960795 + 1575624 * 2 ^ 59
def prefixEnd_1575624 : Nat := 4983230072969 + 3 ^ 40 * 1575624 * 2
def baseEnd_1575624 : Nat := 539368295173232398369229

theorem tailTrace_1575624 : CollatzResearch.WordTrace tailWord_1575624 prefixEnd_1575624 539368295173232398369229 := by
  unfold tailWord_1575624
  simp only [CollatzResearch.WordTrace]
  refine ⟨28733864221895409000274963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38311818962527212000366617 28733864221895409000274963)
  ·
    refine ⟨43100796332843113500412445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28733864221895409000274963 43100796332843113500412445)
    ·
      refine ⟨16162798624816167562654667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43100796332843113500412445 16162798624816167562654667)
      ·
        refine ⟨24244197937224251343982001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16162798624816167562654667 24244197937224251343982001)
        ·
          refine ⟨18183148452918188507986501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24244197937224251343982001 18183148452918188507986501)
          ·
            refine ⟨3409340334922160345247469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18183148452918188507986501 3409340334922160345247469)
            ·
              refine ⟨1278502625595810129467801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409340334922160345247469 1278502625595810129467801)
              ·
                refine ⟨958876969196857597100851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278502625595810129467801 958876969196857597100851)
                ·
                  refine ⟨1438315453795286395651277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958876969196857597100851 1438315453795286395651277)
                  ·
                    refine ⟨539368295173232398369229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438315453795286395651277 539368295173232398369229)
                    ·
                      rfl

theorem cell22_1575624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_1575624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575624 prefixEnd_1575624 := by exact prefixLift 1575624
  have htrace : WordTrace (prefixWord ++ tailWord_1575624) baseStart_1575624 baseEnd_1575624 := by
    simpa [prefixWord, tailWord_1575624, baseEnd_1575624] using wordTrace_append hprefix tailTrace_1575624
  have hstable : (prefixWord ++ tailWord_1575624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575624).length < 2 ^ (prefixWord ++ tailWord_1575624).sum := by decide
  have hdescent : baseEnd_1575624 < baseStart_1575624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575633 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1575633 : Nat := 118140960795 + 1575633 * 2 ^ 59
def prefixEnd_1575633 : Nat := 4983230072969 + 3 ^ 40 * 1575633 * 2
def baseEnd_1575633 : Nat := 539371376057159374894201

theorem tailTrace_1575633 : CollatzResearch.WordTrace tailWord_1575633 prefixEnd_1575633 539371376057159374894201 := by
  unfold tailWord_1575633
  simp only [CollatzResearch.WordTrace]
  refine ⟨57468056700758212537627553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38312037800505475025085035 57468056700758212537627553)
  ·
    refine ⟨43101042525568659403220665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57468056700758212537627553 43101042525568659403220665)
    ·
      refine ⟨32325781894176494552415499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43101042525568659403220665 32325781894176494552415499)
      ·
        refine ⟨48488672841264741828623249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32325781894176494552415499 48488672841264741828623249)
        ·
          refine ⟨36366504630948556371467437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48488672841264741828623249 36366504630948556371467437)
          ·
            refine ⟨13637439236605708639300289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36366504630948556371467437 13637439236605708639300289)
            ·
              refine ⟨10228079427454281479475217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13637439236605708639300289 10228079427454281479475217)
              ·
                refine ⟨7671059570590711109606413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10228079427454281479475217 7671059570590711109606413)
                ·
                  refine ⟨2876647338971516666102405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7671059570590711109606413 2876647338971516666102405)
                  ·
                    refine ⟨539371376057159374894201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876647338971516666102405 539371376057159374894201)
                    ·
                      rfl

theorem cell22_1575633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1575633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575633 prefixEnd_1575633 := by exact prefixLift 1575633
  have htrace : WordTrace (prefixWord ++ tailWord_1575633) baseStart_1575633 baseEnd_1575633 := by
    simpa [prefixWord, tailWord_1575633, baseEnd_1575633] using wordTrace_append hprefix tailTrace_1575633
  have hstable : (prefixWord ++ tailWord_1575633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575633).length < 2 ^ (prefixWord ++ tailWord_1575633).sum := by decide
  have hdescent : baseEnd_1575633 < baseStart_1575633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575637 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 5]
def baseStart_1575637 : Nat := 118140960795 + 1575637 * 2 ^ 59
def prefixEnd_1575637 : Nat := 4983230072969 + 3 ^ 40 * 1575637 * 2
def baseEnd_1575637 : Nat := 179790915112968232598063

theorem tailTrace_1575637 : CollatzResearch.WordTrace tailWord_1575637 prefixEnd_1575637 179790915112968232598063 := by
  unfold tailWord_1575637
  simp only [CollatzResearch.WordTrace]
  refine ⟨57468202592743721220773165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38312135061829147480515443 57468202592743721220773165)
  ·
    refine ⟨21550575972278895457789937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57468202592743721220773165 21550575972278895457789937)
    ·
      refine ⟨16162931979209171593342453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21550575972278895457789937 16162931979209171593342453)
      ·
        refine ⟨1515274873050859836875855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16162931979209171593342453 1515274873050859836875855)
        ·
          refine ⟨2272912309576289755313783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515274873050859836875855 2272912309576289755313783)
          ·
            refine ⟨3409368464364434632970675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272912309576289755313783 3409368464364434632970675)
            ·
              refine ⟨5114052696546651949456013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409368464364434632970675 5114052696546651949456013)
              ·
                refine ⟨1917769761204994481046005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114052696546651949456013 1917769761204994481046005)
                ·
                  refine ⟨179790915112968232598063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1917769761204994481046005 179790915112968232598063)
                  ·
                    rfl

theorem cell22_1575637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_1575637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575637 prefixEnd_1575637 := by exact prefixLift 1575637
  have htrace : WordTrace (prefixWord ++ tailWord_1575637) baseStart_1575637 baseEnd_1575637 := by
    simpa [prefixWord, tailWord_1575637, baseEnd_1575637] using wordTrace_append hprefix tailTrace_1575637
  have hstable : (prefixWord ++ tailWord_1575637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575637).length < 2 ^ (prefixWord ++ tailWord_1575637).sum := by decide
  have hdescent : baseEnd_1575637 < baseStart_1575637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575663 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_1575663 : Nat := 118140960795 + 1575663 * 2 ^ 59
def prefixEnd_1575663 : Nat := 4983230072969 + 3 ^ 40 * 1575663 * 2
def baseEnd_1575663 : Nat := 539381645670249296644109

theorem tailTrace_1575663 : CollatzResearch.WordTrace tailWord_1575663 prefixEnd_1575663 539381645670249296644109 := by
  unfold tailWord_1575663
  simp only [CollatzResearch.WordTrace]
  refine ⟨57469150890649527661219643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38312767260433018440813095 57469150890649527661219643)
  ·
    refine ⟨86203726335974291491829465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57469150890649527661219643 86203726335974291491829465)
    ·
      refine ⟨64652794751980718618872099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86203726335974291491829465 64652794751980718618872099)
      ·
        refine ⟨96979192127971077928308149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64652794751980718618872099 96979192127971077928308149)
        ·
          refine ⟨9091799261997288555778889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96979192127971077928308149 9091799261997288555778889)
          ·
            refine ⟨6818849446497966416834167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9091799261997288555778889 6818849446497966416834167)
            ·
              refine ⟨10228274169746949625251251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6818849446497966416834167 10228274169746949625251251)
              ·
                refine ⟨15342411254620424437876877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228274169746949625251251 15342411254620424437876877)
                ·
                  refine ⟨5753404220482659164203829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15342411254620424437876877 5753404220482659164203829)
                  ·
                    refine ⟨539381645670249296644109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5753404220482659164203829 539381645670249296644109)
                    ·
                      rfl

theorem cell22_1575663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_1575663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575663 prefixEnd_1575663 := by exact prefixLift 1575663
  have htrace : WordTrace (prefixWord ++ tailWord_1575663) baseStart_1575663 baseEnd_1575663 := by
    simpa [prefixWord, tailWord_1575663, baseEnd_1575663] using wordTrace_append hprefix tailTrace_1575663
  have hstable : (prefixWord ++ tailWord_1575663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575663).length < 2 ^ (prefixWord ++ tailWord_1575663).sum := by decide
  have hdescent : baseEnd_1575663 < baseStart_1575663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575665 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 4]
def baseStart_1575665 : Nat := 118140960795 + 1575665 * 2 ^ 59
def prefixEnd_1575665 : Nat := 4983230072969 + 3 ^ 40 * 1575665 * 2
def baseEnd_1575665 : Nat := 179794110103707319364701

theorem tailTrace_1575665 : CollatzResearch.WordTrace tailWord_1575665 prefixEnd_1575665 179794110103707319364701 := by
  unfold tailWord_1575665
  simp only [CollatzResearch.WordTrace]
  refine ⟨57469223836642282002792449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38312815891094854668528299 57469223836642282002792449)
  ·
    refine ⟨43101917877481711502094337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57469223836642282002792449 43101917877481711502094337)
    ·
      refine ⟨32326438408111283626570753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43101917877481711502094337 32326438408111283626570753)
      ·
        refine ⟨24244828806083462719928065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32326438408111283626570753 24244828806083462719928065)
        ·
          refine ⟨18183621604562597039946049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24244828806083462719928065 18183621604562597039946049)
          ·
            refine ⟨13637716203421947779959537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18183621604562597039946049 13637716203421947779959537)
            ·
              refine ⟨10228287152566460834969653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13637716203421947779959537 10228287152566460834969653)
              ·
                refine ⟨958901920553105703278405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10228287152566460834969653 958901920553105703278405)
                ·
                  refine ⟨179794110103707319364701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958901920553105703278405 179794110103707319364701)
                  ·
                    rfl

theorem cell22_1575665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_1575665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575665 prefixEnd_1575665 := by exact prefixLift 1575665
  have htrace : WordTrace (prefixWord ++ tailWord_1575665) baseStart_1575665 baseEnd_1575665 := by
    simpa [prefixWord, tailWord_1575665, baseEnd_1575665] using wordTrace_append hprefix tailTrace_1575665
  have hstable : (prefixWord ++ tailWord_1575665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575665).length < 2 ^ (prefixWord ++ tailWord_1575665).sum := by decide
  have hdescent : baseEnd_1575665 < baseStart_1575665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575712 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_1575712 : Nat := 118140960795 + 1575712 * 2 ^ 59
def prefixEnd_1575712 : Nat := 4983230072969 + 3 ^ 40 * 1575712 * 2
def baseEnd_1575712 : Nat := 539398419371629502168959

theorem tailTrace_1575712 : CollatzResearch.WordTrace tailWord_1575712 prefixEnd_1575712 539398419371629502168959 := by
  unfold tailWord_1575712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28735469033736004514876695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38313958711648006019835593 28735469033736004514876695)
  ·
    refine ⟨43103203550604006772315043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28735469033736004514876695 43103203550604006772315043)
    ·
      refine ⟨64654805325906010158472565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43103203550604006772315043 64654805325906010158472565)
      ·
        refine ⟨6061387999303688452356803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64654805325906010158472565 6061387999303688452356803)
        ·
          refine ⟨9092081998955532678535205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061387999303688452356803 9092081998955532678535205)
          ·
            refine ⟨1704765374804162377225351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9092081998955532678535205 1704765374804162377225351)
            ·
              refine ⟨2557148062206243565838027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704765374804162377225351 2557148062206243565838027)
              ·
                refine ⟨3835722093309365348757041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2557148062206243565838027 3835722093309365348757041)
                ·
                  refine ⟨2876791569982024011567781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3835722093309365348757041 2876791569982024011567781)
                  ·
                    refine ⟨539398419371629502168959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876791569982024011567781 539398419371629502168959)
                    ·
                      rfl

theorem cell22_1575712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_1575712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575712 prefixEnd_1575712 := by exact prefixLift 1575712
  have htrace : WordTrace (prefixWord ++ tailWord_1575712) baseStart_1575712 baseEnd_1575712 := by
    simpa [prefixWord, tailWord_1575712, baseEnd_1575712] using wordTrace_append hprefix tailTrace_1575712
  have hstable : (prefixWord ++ tailWord_1575712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575712).length < 2 ^ (prefixWord ++ tailWord_1575712).sum := by decide
  have hdescent : baseEnd_1575712 < baseStart_1575712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575748 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1575748 : Nat := 118140960795 + 1575748 * 2 ^ 59
def prefixEnd_1575748 : Nat := 4983230072969 + 3 ^ 40 * 1575748 * 2
def baseEnd_1575748 : Nat := 539410742907337408268849

theorem tailTrace_1575748 : CollatzResearch.WordTrace tailWord_1575748 prefixEnd_1575748 539410742907337408268849 := by
  unfold tailWord_1575748
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736125547670793589031949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38314834063561058118709265 28736125547670793589031949)
  ·
    refine ⟨10776047080376547595886981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28736125547670793589031949 10776047080376547595886981)
    ·
      refine ⟨2020508827570602674228809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10776047080376547595886981 2020508827570602674228809)
      ·
        refine ⟨1515381620677952005671607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2020508827570602674228809 1515381620677952005671607)
        ·
          refine ⟨2273072431016928008507411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515381620677952005671607 2273072431016928008507411)
          ·
            refine ⟨3409608646525392012761117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273072431016928008507411 3409608646525392012761117)
            ·
              refine ⟨1278603242447022004785419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409608646525392012761117 1278603242447022004785419)
              ·
                refine ⟨1917904863670533007178129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278603242447022004785419 1917904863670533007178129)
                ·
                  refine ⟨1438428647752899755383597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1917904863670533007178129 1438428647752899755383597)
                  ·
                    refine ⟨539410742907337408268849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438428647752899755383597 539410742907337408268849)
                    ·
                      rfl

theorem cell22_1575748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1575748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575748 prefixEnd_1575748 := by exact prefixLift 1575748
  have htrace : WordTrace (prefixWord ++ tailWord_1575748) baseStart_1575748 baseEnd_1575748 := by
    simpa [prefixWord, tailWord_1575748, baseEnd_1575748] using wordTrace_append hprefix tailTrace_1575748
  have hstable : (prefixWord ++ tailWord_1575748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575748).length < 2 ^ (prefixWord ++ tailWord_1575748).sum := by decide
  have hdescent : baseEnd_1575748 < baseStart_1575748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575768 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_1575768 : Nat := 118140960795 + 1575768 * 2 ^ 59
def prefixEnd_1575768 : Nat := 4983230072969 + 3 ^ 40 * 1575768 * 2
def baseEnd_1575768 : Nat := 539417589316064022768787

theorem tailTrace_1575768 : CollatzResearch.WordTrace tailWord_1575768 prefixEnd_1575768 539417589316064022768787 := by
  unfold tailWord_1575768
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736490277634565296895979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38315320370179420395861305 28736490277634565296895979)
  ·
    refine ⟨43104735416451847945343969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28736490277634565296895979 43104735416451847945343969)
    ·
      refine ⟨32328551562338885959007977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43104735416451847945343969 32328551562338885959007977)
      ·
        refine ⟨24246413671754164469255983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32328551562338885959007977 24246413671754164469255983)
        ·
          refine ⟨36369620507631246703883975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24246413671754164469255983 36369620507631246703883975)
          ·
            refine ⟨54554430761446870055825963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36369620507631246703883975 54554430761446870055825963)
            ·
              refine ⟨81831646142170305083738945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54554430761446870055825963 81831646142170305083738945)
              ·
                refine ⟨61373734606627728812804209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81831646142170305083738945 61373734606627728812804209)
                ·
                  refine ⟨46030300954970796609603157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61373734606627728812804209 46030300954970796609603157)
                  ·
                    refine ⟨539417589316064022768787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46030300954970796609603157 539417589316064022768787)
                    ·
                      rfl

theorem cell22_1575768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_1575768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575768 prefixEnd_1575768 := by exact prefixLift 1575768
  have htrace : WordTrace (prefixWord ++ tailWord_1575768) baseStart_1575768 baseEnd_1575768 := by
    simpa [prefixWord, tailWord_1575768, baseEnd_1575768] using wordTrace_append hprefix tailTrace_1575768
  have hstable : (prefixWord ++ tailWord_1575768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575768).length < 2 ^ (prefixWord ++ tailWord_1575768).sum := by decide
  have hdescent : baseEnd_1575768 < baseStart_1575768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575836 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1575836 : Nat := 118140960795 + 1575836 * 2 ^ 59
def prefixEnd_1575836 : Nat := 4983230072969 + 3 ^ 40 * 1575836 * 2
def baseEnd_1575836 : Nat := 539440867105734512068579

theorem tailTrace_1575836 : CollatzResearch.WordTrace tailWord_1575836 prefixEnd_1575836 539440867105734512068579 := by
  unfold tailWord_1575836
  simp only [CollatzResearch.WordTrace]
  refine ⟨28737730359511389103633681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38316973812681852138178241 28737730359511389103633681)
  ·
    refine ⟨21553297769633541827725261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28737730359511389103633681 21553297769633541827725261)
    ·
      refine ⟨8082486663612578185396973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21553297769633541827725261 8082486663612578185396973)
      ·
        refine ⟨3030932498854716819523865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8082486663612578185396973 3030932498854716819523865)
        ·
          refine ⟨2273199374141037614642899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3030932498854716819523865 2273199374141037614642899)
          ·
            refine ⟨3409799061211556421964349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273199374141037614642899 3409799061211556421964349)
            ·
              refine ⟨1278674647954333658236631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409799061211556421964349 1278674647954333658236631)
              ·
                refine ⟨1918011971931500487354947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278674647954333658236631 1918011971931500487354947)
                ·
                  refine ⟨2877017957897250731032421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918011971931500487354947 2877017957897250731032421)
                  ·
                    refine ⟨539440867105734512068579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2877017957897250731032421 539440867105734512068579)
                    ·
                      rfl

theorem cell22_1575836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1575836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575836 prefixEnd_1575836 := by exact prefixLift 1575836
  have htrace : WordTrace (prefixWord ++ tailWord_1575836) baseStart_1575836 baseEnd_1575836 := by
    simpa [prefixWord, tailWord_1575836, baseEnd_1575836] using wordTrace_append hprefix tailTrace_1575836
  have hstable : (prefixWord ++ tailWord_1575836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575836).length < 2 ^ (prefixWord ++ tailWord_1575836).sum := by decide
  have hdescent : baseEnd_1575836 < baseStart_1575836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575885 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1575885 : Nat := 118140960795 + 1575885 * 2 ^ 59
def prefixEnd_1575885 : Nat := 4983230072969 + 3 ^ 40 * 1575885 * 2
def baseEnd_1575885 : Nat := 179819213602371572531143

theorem tailTrace_1575885 : CollatzResearch.WordTrace tailWord_1575885 prefixEnd_1575885 179819213602371572531143 := by
  unfold tailWord_1575885
  simp only [CollatzResearch.WordTrace]
  refine ⟨57477247895845259575801109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38318165263896839717200739 57477247895845259575801109)
  ·
    refine ⟨2694245995117746542615677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57477247895845259575801109 2694245995117746542615677)
    ·
      refine ⟨1010342248169154953480879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2694245995117746542615677 1010342248169154953480879)
      ·
        refine ⟨1515513372253732430221319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010342248169154953480879 1515513372253732430221319)
        ·
          refine ⟨2273270058380598645331979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515513372253732430221319 2273270058380598645331979)
          ·
            refine ⟨3409905087570897967997969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273270058380598645331979 3409905087570897967997969)
            ·
              refine ⟨2557428815678173475998477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3409905087570897967997969 2557428815678173475998477)
              ·
                refine ⟨959035805879315053499429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2557428815678173475998477 959035805879315053499429)
                ·
                  refine ⟨179819213602371572531143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959035805879315053499429 179819213602371572531143)
                  ·
                    rfl

theorem cell22_1575885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1575885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575885 prefixEnd_1575885 := by exact prefixLift 1575885
  have htrace : WordTrace (prefixWord ++ tailWord_1575885) baseStart_1575885 baseEnd_1575885 := by
    simpa [prefixWord, tailWord_1575885, baseEnd_1575885] using wordTrace_append hprefix tailTrace_1575885
  have hstable : (prefixWord ++ tailWord_1575885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575885).length < 2 ^ (prefixWord ++ tailWord_1575885).sum := by decide
  have hdescent : baseEnd_1575885 < baseStart_1575885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575911 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1575911 : Nat := 118140960795 + 1575911 * 2 ^ 59
def prefixEnd_1575911 : Nat := 4983230072969 + 3 ^ 40 * 1575911 * 2
def baseEnd_1575911 : Nat := 539466541138459316443349

theorem tailTrace_1575911 : CollatzResearch.WordTrace tailWord_1575911 prefixEnd_1575911 539466541138459316443349 := by
  unfold tailWord_1575911
  simp only [CollatzResearch.WordTrace]
  refine ⟨57478196193751066016247587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38318797462500710677498391 57478196193751066016247587)
  ·
    refine ⟨86217294290626599024371381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57478196193751066016247587 86217294290626599024371381)
    ·
      refine ⟨8082871339746243658534817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86217294290626599024371381 8082871339746243658534817)
      ·
        refine ⟨6062153504809682743901113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8082871339746243658534817 6062153504809682743901113)
        ·
          refine ⟨4546615128607262057925835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6062153504809682743901113 4546615128607262057925835)
          ·
            refine ⟨6819922692910893086888753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546615128607262057925835 6819922692910893086888753)
            ·
              refine ⟨5114942019683169815166565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6819922692910893086888753 5114942019683169815166565)
              ·
                refine ⟨959051628690594340343731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5114942019683169815166565 959051628690594340343731)
                ·
                  refine ⟨1438577443035891510515597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959051628690594340343731 1438577443035891510515597)
                  ·
                    refine ⟨539466541138459316443349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438577443035891510515597 539466541138459316443349)
                    ·
                      rfl

theorem cell22_1575911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1575911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575911 prefixEnd_1575911 := by exact prefixLift 1575911
  have htrace : WordTrace (prefixWord ++ tailWord_1575911) baseStart_1575911 baseEnd_1575911 := by
    simpa [prefixWord, tailWord_1575911, baseEnd_1575911] using wordTrace_append hprefix tailTrace_1575911
  have hstable : (prefixWord ++ tailWord_1575911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575911).length < 2 ^ (prefixWord ++ tailWord_1575911).sum := by decide
  have hdescent : baseEnd_1575911 < baseStart_1575911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575969 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 6]
def baseStart_1575969 : Nat := 118140960795 + 1575969 * 2 ^ 59
def prefixEnd_1575969 : Nat := 4983230072969 + 3 ^ 40 * 1575969 * 2
def baseEnd_1575969 : Nat := 179828798574588832831057

theorem tailTrace_1575969 : CollatzResearch.WordTrace tailWord_1575969 prefixEnd_1575969 179828798574588832831057 := by
  unfold tailWord_1575969
  simp only [CollatzResearch.WordTrace]
  refine ⟨57480311627540941921858961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38320207751693961281239307 57480311627540941921858961)
  ·
    refine ⟨43110233720655706441394221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57480311627540941921858961 43110233720655706441394221)
    ·
      refine ⟨16166337645245889915522833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43110233720655706441394221 16166337645245889915522833)
      ·
        refine ⟨12124753233934417436642125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16166337645245889915522833 12124753233934417436642125)
        ·
          refine ⟨4546782462725406538740797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12124753233934417436642125 4546782462725406538740797)
          ·
            refine ⟨1705043423522027452027799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4546782462725406538740797 1705043423522027452027799)
            ·
              refine ⟨2557565135283041178041699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705043423522027452027799 2557565135283041178041699)
              ·
                refine ⟨3836347702924561767062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2557565135283041178041699 3836347702924561767062549)
                ·
                  refine ⟨179828798574588832831057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3836347702924561767062549 179828798574588832831057)
                  ·
                    rfl

theorem cell22_1575969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_1575969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575969 prefixEnd_1575969 := by exact prefixLift 1575969
  have htrace : WordTrace (prefixWord ++ tailWord_1575969) baseStart_1575969 baseEnd_1575969 := by
    simpa [prefixWord, tailWord_1575969, baseEnd_1575969] using wordTrace_append hprefix tailTrace_1575969
  have hstable : (prefixWord ++ tailWord_1575969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575969).length < 2 ^ (prefixWord ++ tailWord_1575969).sum := by decide
  have hdescent : baseEnd_1575969 < baseStart_1575969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575984 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_1575984 : Nat := 118140960795 + 1575984 * 2 ^ 59
def prefixEnd_1575984 : Nat := 4983230072969 + 3 ^ 40 * 1575984 * 2
def baseEnd_1575984 : Nat := 539491530530311459368125

theorem tailTrace_1575984 : CollatzResearch.WordTrace tailWord_1575984 prefixEnd_1575984 539491530530311459368125 := by
  unfold tailWord_1575984
  simp only [CollatzResearch.WordTrace]
  refine ⟨28740429361243299741827503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38320572481657732989103337 28740429361243299741827503)
  ·
    refine ⟨43110644041864949612741255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28740429361243299741827503 43110644041864949612741255)
    ·
      refine ⟨64665966062797424419111883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43110644041864949612741255 64665966062797424419111883)
      ·
        refine ⟨96998949094196136628667825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64665966062797424419111883 96998949094196136628667825)
        ·
          refine ⟨72749211820647102471500869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96998949094196136628667825 72749211820647102471500869)
          ·
            refine ⟨13640477216371331713406413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72749211820647102471500869 13640477216371331713406413)
            ·
              refine ⟨5115178956139249392527405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13640477216371331713406413 5115178956139249392527405)
              ·
                refine ⟨1918192108552218522197777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5115178956139249392527405 1918192108552218522197777)
                ·
                  refine ⟨1438644081414163891648333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918192108552218522197777 1438644081414163891648333)
                  ·
                    refine ⟨539491530530311459368125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438644081414163891648333 539491530530311459368125)
                    ·
                      rfl

theorem cell22_1575984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_1575984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575984 prefixEnd_1575984 := by exact prefixLift 1575984
  have htrace : WordTrace (prefixWord ++ tailWord_1575984) baseStart_1575984 baseEnd_1575984 := by
    simpa [prefixWord, tailWord_1575984, baseEnd_1575984] using wordTrace_append hprefix tailTrace_1575984
  have hstable : (prefixWord ++ tailWord_1575984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575984).length < 2 ^ (prefixWord ++ tailWord_1575984).sum := by decide
  have hdescent : baseEnd_1575984 < baseStart_1575984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575988 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1575988 : Nat := 118140960795 + 1575988 * 2 ^ 59
def prefixEnd_1575988 : Nat := 4983230072969 + 3 ^ 40 * 1575988 * 2
def baseEnd_1575988 : Nat := 539492899812056782268113

theorem tailTrace_1575988 : CollatzResearch.WordTrace tailWord_1575988 prefixEnd_1575988 539492899812056782268113 := by
  unfold tailWord_1575988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28740502307236054083400309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38320669742981405444533745 28740502307236054083400309)
  ·
    refine ⟨2694422091303380070318779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28740502307236054083400309 2694422091303380070318779)
    ·
      refine ⟨4041633136955070105478169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694422091303380070318779 4041633136955070105478169)
      ·
        refine ⟨3031224852716302579108627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4041633136955070105478169 3031224852716302579108627)
        ·
          refine ⟨4546837279074453868662941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031224852716302579108627 4546837279074453868662941)
          ·
            refine ⟨1705063979652920200748603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4546837279074453868662941 1705063979652920200748603)
            ·
              refine ⟨2557595969479380301122905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705063979652920200748603 2557595969479380301122905)
              ·
                refine ⟨1918196977109535225842179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557595969479380301122905 1918196977109535225842179)
                ·
                  refine ⟨2877295465664302838763269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918196977109535225842179 2877295465664302838763269)
                  ·
                    refine ⟨539492899812056782268113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2877295465664302838763269 539492899812056782268113)
                    ·
                      rfl

theorem cell22_1575988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1575988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575988 prefixEnd_1575988 := by exact prefixLift 1575988
  have htrace : WordTrace (prefixWord ++ tailWord_1575988) baseStart_1575988 baseEnd_1575988 := by
    simpa [prefixWord, tailWord_1575988, baseEnd_1575988] using wordTrace_append hprefix tailTrace_1575988
  have hstable : (prefixWord ++ tailWord_1575988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575988).length < 2 ^ (prefixWord ++ tailWord_1575988).sum := by decide
  have hdescent : baseEnd_1575988 < baseStart_1575988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575997 : List Nat := [1, 4, 1, 3, 1, 2, 2, 8]
def baseStart_1575997 : Nat := 118140960795 + 1575997 * 2 ^ 59
def prefixEnd_1575997 : Nat := 4983230072969 + 3 ^ 40 * 1575997 * 2
def baseEnd_1575997 : Nat := 59943997855109306532565

theorem tailTrace_1575997 : CollatzResearch.WordTrace tailWord_1575997 prefixEnd_1575997 59943997855109306532565 := by
  unfold tailWord_1575997
  simp only [CollatzResearch.WordTrace]
  refine ⟨57481332871439502703878245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38320888580959668469252163 57481332871439502703878245)
  ·
    refine ⟨10777749913394906756977171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57481332871439502703878245 10777749913394906756977171)
    ·
      refine ⟨16166624870092360135465757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10777749913394906756977171 16166624870092360135465757)
      ·
        refine ⟨6062484326284635050799659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16166624870092360135465757 6062484326284635050799659)
        ·
          refine ⟨9093726489426952576199489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6062484326284635050799659 9093726489426952576199489)
          ·
            refine ⟨6820294867070214432149617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9093726489426952576199489 6820294867070214432149617)
            ·
              refine ⟨5115221150302660824112213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6820294867070214432149617 5115221150302660824112213)
              ·
                refine ⟨59943997855109306532565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5115221150302660824112213 59943997855109306532565)
                ·
                  rfl

theorem cell22_1575997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 8].length) (baseStart_1575997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1575997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1575997 prefixEnd_1575997 := by exact prefixLift 1575997
  have htrace : WordTrace (prefixWord ++ tailWord_1575997) baseStart_1575997 baseEnd_1575997 := by
    simpa [prefixWord, tailWord_1575997, baseEnd_1575997] using wordTrace_append hprefix tailTrace_1575997
  have hstable : (prefixWord ++ tailWord_1575997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575997).length < 2 ^ (prefixWord ++ tailWord_1575997).sum := by decide
  have hdescent : baseEnd_1575997 < baseStart_1575997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576046 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1576046 : Nat := 118140960795 + 1576046 * 2 ^ 59
def prefixEnd_1576046 : Nat := 4983230072969 + 3 ^ 40 * 1576046 * 2
def baseEnd_1576046 : Nat := 539512754397363964317935

theorem tailTrace_1576046 : CollatzResearch.WordTrace tailWord_1576046 prefixEnd_1576046 539512754397363964317935 := by
  unfold tailWord_1576046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185390006032748009051499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38322080032174656048274661 7185390006032748009051499)
  ·
    refine ⟨10778085009049122013577249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7185390006032748009051499 10778085009049122013577249)
    ·
      refine ⟨8083563756786841510182937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10778085009049122013577249 8083563756786841510182937)
      ·
        refine ⟨6062672817590131132637203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8083563756786841510182937 6062672817590131132637203)
        ·
          refine ⟨9094009226385196698955805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6062672817590131132637203 9094009226385196698955805)
          ·
            refine ⟨3410253459894448762108427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9094009226385196698955805 3410253459894448762108427)
            ·
              refine ⟨5115380189841673143162641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410253459894448762108427 5115380189841673143162641)
              ·
                refine ⟨3836535142381254857371981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115380189841673143162641 3836535142381254857371981)
                ·
                  refine ⟨1438700678392970571514493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3836535142381254857371981 1438700678392970571514493)
                  ·
                    refine ⟨539512754397363964317935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438700678392970571514493 539512754397363964317935)
                    ·
                      rfl

theorem cell22_1576046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1576046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576046 prefixEnd_1576046 := by exact prefixLift 1576046
  have htrace : WordTrace (prefixWord ++ tailWord_1576046) baseStart_1576046 baseEnd_1576046 := by
    simpa [prefixWord, tailWord_1576046, baseEnd_1576046] using wordTrace_append hprefix tailTrace_1576046
  have hstable : (prefixWord ++ tailWord_1576046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576046).length < 2 ^ (prefixWord ++ tailWord_1576046).sum := by decide
  have hdescent : baseEnd_1576046 < baseStart_1576046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576119 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 6, 3]
def baseStart_1576119 : Nat := 118140960795 + 1576119 * 2 ^ 59
def prefixEnd_1576119 : Nat := 4983230072969 + 3 ^ 40 * 1576119 * 2
def baseEnd_1576119 : Nat := 539537743789216107242711

theorem tailTrace_1576119 : CollatzResearch.WordTrace tailWord_1576119 prefixEnd_1576119 539537743789216107242711 := by
  unfold tailWord_1576119
  simp only [CollatzResearch.WordTrace]
  refine ⟨57485782576997517539819411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38323855051331678359879607 57485782576997517539819411)
  ·
    refine ⟨86228673865496276309729117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57485782576997517539819411 86228673865496276309729117)
    ·
      refine ⟨32335752699561103616148419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86228673865496276309729117 32335752699561103616148419)
      ·
        refine ⟨48503629049341655424222629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32335752699561103616148419 48503629049341655424222629)
        ·
          refine ⟨9094430446751560392041743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48503629049341655424222629 9094430446751560392041743)
          ·
            refine ⟨13641645670127340588062615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9094430446751560392041743 13641645670127340588062615)
            ·
              refine ⟨20462468505191010882093923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13641645670127340588062615 20462468505191010882093923)
              ·
                refine ⟨30693702757786516323140885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20462468505191010882093923 30693702757786516323140885)
                ·
                  refine ⟨1438767316771242952647229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30693702757786516323140885 1438767316771242952647229)
                  ·
                    refine ⟨539537743789216107242711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438767316771242952647229 539537743789216107242711)
                    ·
                      rfl

theorem cell22_1576119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_1576119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576119 prefixEnd_1576119 := by exact prefixLift 1576119
  have htrace : WordTrace (prefixWord ++ tailWord_1576119) baseStart_1576119 baseEnd_1576119 := by
    simpa [prefixWord, tailWord_1576119, baseEnd_1576119] using wordTrace_append hprefix tailTrace_1576119
  have hstable : (prefixWord ++ tailWord_1576119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576119).length < 2 ^ (prefixWord ++ tailWord_1576119).sum := by decide
  have hdescent : baseEnd_1576119 < baseStart_1576119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576121 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 4]
def baseStart_1576121 : Nat := 118140960795 + 1576121 * 2 ^ 59
def prefixEnd_1576121 : Nat := 4983230072969 + 3 ^ 40 * 1576121 * 2
def baseEnd_1576121 : Nat := 179846142810029589564235

theorem tailTrace_1576121 : CollatzResearch.WordTrace tailWord_1576121 prefixEnd_1576121 179846142810029589564235 := by
  unfold tailWord_1576121
  simp only [CollatzResearch.WordTrace]
  refine ⟨57485855522990271881392217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38323903681993514587594811 57485855522990271881392217)
  ·
    refine ⟨43114391642242703911044163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57485855522990271881392217 43114391642242703911044163)
    ·
      refine ⟨64671587463364055866566245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43114391642242703911044163 64671587463364055866566245)
      ·
        refine ⟨12125922649380760474981171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64671587463364055866566245 12125922649380760474981171)
        ·
          refine ⟨18188883974071140712471757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12125922649380760474981171 18188883974071140712471757)
          ·
            refine ⟨6820831490276677767176909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18188883974071140712471757 6820831490276677767176909)
            ·
              refine ⟨2557811808853754162691341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6820831490276677767176909 2557811808853754162691341)
              ·
                refine ⟨959179428320157811009253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2557811808853754162691341 959179428320157811009253)
                ·
                  refine ⟨179846142810029589564235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959179428320157811009253 179846142810029589564235)
                  ·
                    rfl

theorem cell22_1576121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_1576121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576121 prefixEnd_1576121 := by exact prefixLift 1576121
  have htrace : WordTrace (prefixWord ++ tailWord_1576121) baseStart_1576121 baseEnd_1576121 := by
    simpa [prefixWord, tailWord_1576121, baseEnd_1576121] using wordTrace_append hprefix tailTrace_1576121
  have hstable : (prefixWord ++ tailWord_1576121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576121).length < 2 ^ (prefixWord ++ tailWord_1576121).sum := by decide
  have hdescent : baseEnd_1576121 < baseStart_1576121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576138 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_1576138 : Nat := 118140960795 + 1576138 * 2 ^ 59
def prefixEnd_1576138 : Nat := 4983230072969 + 3 ^ 40 * 1576138 * 2
def baseEnd_1576138 : Nat := 179848082625835463672551

theorem tailTrace_1576138 : CollatzResearch.WordTrace tailWord_1576138 prefixEnd_1576138 179848082625835463672551 := by
  unfold tailWord_1576138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14371618890982170946190267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38324317042619122523174045 14371618890982170946190267)
  ·
    refine ⟨21557428336473256419285401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14371618890982170946190267 21557428336473256419285401)
    ·
      refine ⟨16168071252354942314464051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21557428336473256419285401 16168071252354942314464051)
      ·
        refine ⟨24252106878532413471696077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16168071252354942314464051 24252106878532413471696077)
        ·
          refine ⟨9094540079449655051886029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24252106878532413471696077 9094540079449655051886029)
          ·
            refine ⟨3410452529793620644457261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9094540079449655051886029 3410452529793620644457261)
            ·
              refine ⟨1278919698672607741671473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3410452529793620644457261 1278919698672607741671473)
              ·
                refine ⟨959189774004455806253605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278919698672607741671473 959189774004455806253605)
                ·
                  refine ⟨179848082625835463672551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959189774004455806253605 179848082625835463672551)
                  ·
                    rfl

theorem cell22_1576138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_1576138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576138 prefixEnd_1576138 := by exact prefixLift 1576138
  have htrace : WordTrace (prefixWord ++ tailWord_1576138) baseStart_1576138 baseEnd_1576138 := by
    simpa [prefixWord, tailWord_1576138, baseEnd_1576138] using wordTrace_append hprefix tailTrace_1576138
  have hstable : (prefixWord ++ tailWord_1576138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576138).length < 2 ^ (prefixWord ++ tailWord_1576138).sum := by decide
  have hdescent : baseEnd_1576138 < baseStart_1576138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576149 : List Nat := [1, 3, 2, 4, 1, 1, 1, 9]
def baseStart_1576149 : Nat := 118140960795 + 1576149 * 2 ^ 59
def prefixEnd_1576149 : Nat := 4983230072969 + 3 ^ 40 * 1576149 * 2
def baseEnd_1576149 : Nat := 59949779266922892110291

theorem tailTrace_1576149 : CollatzResearch.WordTrace tailWord_1576149 prefixEnd_1576149 59949779266922892110291 := by
  unfold tailWord_1576149
  simp only [CollatzResearch.WordTrace]
  refine ⟨57486876766888832663411501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38324584511259221775607667 57486876766888832663411501)
  ·
    refine ⟨21557578787583312248779313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57486876766888832663411501 21557578787583312248779313)
    ·
      refine ⟨16168184090687484186584485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21557578787583312248779313 16168184090687484186584485)
      ·
        refine ⟨3031534517003903284984591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16168184090687484186584485 3031534517003903284984591)
        ·
          refine ⟨4547301775505854927476887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031534517003903284984591 4547301775505854927476887)
          ·
            refine ⟨6820952663258782391215331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4547301775505854927476887 6820952663258782391215331)
            ·
              refine ⟨10231428994888173586822997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820952663258782391215331 10231428994888173586822997)
              ·
                refine ⟨59949779266922892110291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10231428994888173586822997 59949779266922892110291)
                ·
                  rfl

theorem cell22_1576149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 9].length) (baseStart_1576149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576149 prefixEnd_1576149 := by exact prefixLift 1576149
  have htrace : WordTrace (prefixWord ++ tailWord_1576149) baseStart_1576149 baseEnd_1576149 := by
    simpa [prefixWord, tailWord_1576149, baseEnd_1576149] using wordTrace_append hprefix tailTrace_1576149
  have hstable : (prefixWord ++ tailWord_1576149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576149).length < 2 ^ (prefixWord ++ tailWord_1576149).sum := by decide
  have hdescent : baseEnd_1576149 < baseStart_1576149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576209 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1576209 : Nat := 118140960795 + 1576209 * 2 ^ 59
def prefixEnd_1576209 : Nat := 4983230072969 + 3 ^ 40 * 1576209 * 2
def baseEnd_1576209 : Nat := 539568552628485872492435

theorem tailTrace_1576209 : CollatzResearch.WordTrace tailWord_1576209 prefixEnd_1576209 539568552628485872492435 := by
  unfold tailWord_1576209
  simp only [CollatzResearch.WordTrace]
  refine ⟨57489065146671462910595681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38326043431114308607063787 57489065146671462910595681)
  ·
    refine ⟨43116798860003597182946761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57489065146671462910595681 43116798860003597182946761)
    ·
      refine ⟨32337599145002697887210071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43116798860003597182946761 32337599145002697887210071)
      ·
        refine ⟨48506398717504046830815107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32337599145002697887210071 48506398717504046830815107)
        ·
          refine ⟨72759598076256070246222661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48506398717504046830815107 72759598076256070246222661)
          ·
            refine ⟨13642424639298013171166749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72759598076256070246222661 13642424639298013171166749)
            ·
              refine ⟨5115909239736754939187531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13642424639298013171166749 5115909239736754939187531)
              ·
                refine ⟨7673863859605132408781297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115909239736754939187531 7673863859605132408781297)
                ·
                  refine ⟨5755397894703849306585973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673863859605132408781297 5755397894703849306585973)
                  ·
                    refine ⟨539568552628485872492435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5755397894703849306585973 539568552628485872492435)
                    ·
                      rfl

theorem cell22_1576209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1576209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576209 prefixEnd_1576209 := by exact prefixLift 1576209
  have htrace : WordTrace (prefixWord ++ tailWord_1576209) baseStart_1576209 baseEnd_1576209 := by
    simpa [prefixWord, tailWord_1576209, baseEnd_1576209] using wordTrace_append hprefix tailTrace_1576209
  have hstable : (prefixWord ++ tailWord_1576209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576209).length < 2 ^ (prefixWord ++ tailWord_1576209).sum := by decide
  have hdescent : baseEnd_1576209 < baseStart_1576209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576256 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 4]
def baseStart_1576256 : Nat := 118140960795 + 1576256 * 2 ^ 59
def prefixEnd_1576256 : Nat := 4983230072969 + 3 ^ 40 * 1576256 * 2
def baseEnd_1576256 : Nat := 179861547229664472189097

theorem tailTrace_1576256 : CollatzResearch.WordTrace tailWord_1576256 prefixEnd_1576256 179861547229664472189097 := by
  unfold tailWord_1576256
  simp only [CollatzResearch.WordTrace]
  refine ⟨28745389688750594968778311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38327186251667459958371081 28745389688750594968778311)
  ·
    refine ⟨43118084533125892453167467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28745389688750594968778311 43118084533125892453167467)
    ·
      refine ⟨64677126799688838679751201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43118084533125892453167467 64677126799688838679751201)
      ·
        refine ⟨48507845099766629009813401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64677126799688838679751201 48507845099766629009813401)
        ·
          refine ⟨36380883824824971757360051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48507845099766629009813401 36380883824824971757360051)
          ·
            refine ⟨54571325737237457636040077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36380883824824971757360051 54571325737237457636040077)
            ·
              refine ⟨20464247151464046613515029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54571325737237457636040077 20464247151464046613515029)
              ·
                refine ⟨959261585224877185008517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20464247151464046613515029 959261585224877185008517)
                ·
                  refine ⟨179861547229664472189097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959261585224877185008517 179861547229664472189097)
                  ·
                    rfl

theorem cell22_1576256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_1576256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576256 prefixEnd_1576256 := by exact prefixLift 1576256
  have htrace : WordTrace (prefixWord ++ tailWord_1576256) baseStart_1576256 baseEnd_1576256 := by
    simpa [prefixWord, tailWord_1576256, baseEnd_1576256] using wordTrace_append hprefix tailTrace_1576256
  have hstable : (prefixWord ++ tailWord_1576256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576256).length < 2 ^ (prefixWord ++ tailWord_1576256).sum := by decide
  have hdescent : baseEnd_1576256 < baseStart_1576256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576301 : List Nat := [1, 5, 1, 1, 1, 5, 8]
def baseStart_1576301 : Nat := 118140960795 + 1576301 * 2 ^ 59
def prefixEnd_1576301 : Nat := 4983230072969 + 3 ^ 40 * 1576301 * 2
def baseEnd_1576301 : Nat := 19985186892912159229339

theorem tailTrace_1576301 : CollatzResearch.WordTrace tailWord_1576301 prefixEnd_1576301 19985186892912159229339 := by
  unfold tailWord_1576301
  simp only [CollatzResearch.WordTrace]
  refine ⟨57492420662338162622944757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38328280441558775081963171 57492420662338162622944757)
  ·
    refine ⟨5389914437094202745901071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57492420662338162622944757 5389914437094202745901071)
    ·
      refine ⟨8084871655641304118851607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389914437094202745901071 8084871655641304118851607)
      ·
        refine ⟨12127307483461956178277411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8084871655641304118851607 12127307483461956178277411)
        ·
          refine ⟨18190961225192934267416117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12127307483461956178277411 18190961225192934267416117)
          ·
            refine ⟨1705402614861837587570261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18190961225192934267416117 1705402614861837587570261)
            ·
              refine ⟨19985186892912159229339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1705402614861837587570261 19985186892912159229339)
              ·
                rfl

theorem cell22_1576301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 8].length) (baseStart_1576301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576301 prefixEnd_1576301 := by exact prefixLift 1576301
  have htrace : WordTrace (prefixWord ++ tailWord_1576301) baseStart_1576301 baseEnd_1576301 := by
    simpa [prefixWord, tailWord_1576301, baseEnd_1576301] using wordTrace_append hprefix tailTrace_1576301
  have hstable : (prefixWord ++ tailWord_1576301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576301).length < 2 ^ (prefixWord ++ tailWord_1576301).sum := by decide
  have hdescent : baseEnd_1576301 < baseStart_1576301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576314 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1576314 : Nat := 118140960795 + 1576314 * 2 ^ 59
def prefixEnd_1576314 : Nat := 4983230072969 + 3 ^ 40 * 1576314 * 2
def baseEnd_1576314 : Nat := 539604496274300598617113

theorem tailTrace_1576314 : CollatzResearch.WordTrace tailWord_1576314 prefixEnd_1576314 539604496274300598617113 := by
  unfold tailWord_1576314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14373223702822766460791999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38328596540860710562111997 14373223702822766460791999)
  ·
    refine ⟨21559835554234149691187999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14373223702822766460791999 21559835554234149691187999)
    ·
      refine ⟨32339753331351224536781999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21559835554234149691187999 32339753331351224536781999)
      ·
        refine ⟨48509629997026836805172999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32339753331351224536781999 48509629997026836805172999)
        ·
          refine ⟨72764444995540255207759499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48509629997026836805172999 72764444995540255207759499)
          ·
            refine ⟨109146667493310382811639249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72764444995540255207759499 109146667493310382811639249)
            ·
              refine ⟨81860000619982787108729437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109146667493310382811639249 81860000619982787108729437)
              ·
                refine ⟨30697500232493545165773539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81860000619982787108729437 30697500232493545165773539)
                ·
                  refine ⟨46046250348740317748660309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30697500232493545165773539 46046250348740317748660309)
                  ·
                    refine ⟨539604496274300598617113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46046250348740317748660309 539604496274300598617113)
                    ·
                      rfl

theorem cell22_1576314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1576314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576314 prefixEnd_1576314 := by exact prefixLift 1576314
  have htrace : WordTrace (prefixWord ++ tailWord_1576314) baseStart_1576314 baseEnd_1576314 := by
    simpa [prefixWord, tailWord_1576314, baseEnd_1576314] using wordTrace_append hprefix tailTrace_1576314
  have hstable : (prefixWord ++ tailWord_1576314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576314).length < 2 ^ (prefixWord ++ tailWord_1576314).sum := by decide
  have hdescent : baseEnd_1576314 < baseStart_1576314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576322 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1576322 : Nat := 118140960795 + 1576322 * 2 ^ 59
def prefixEnd_1576322 : Nat := 4983230072969 + 3 ^ 40 * 1576322 * 2
def baseEnd_1576322 : Nat := 539607234837791244417089

theorem tailTrace_1576322 : CollatzResearch.WordTrace tailWord_1576322 prefixEnd_1576322 539607234837791244417089 := by
  unfold tailWord_1576322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14373296648815520802364805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38328791063508055472972813 14373296648815520802364805)
  ·
    refine ⟨2694993121652910150443401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14373296648815520802364805 2694993121652910150443401)
    ·
      refine ⟨2021244841239682612832551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2694993121652910150443401 2021244841239682612832551)
      ·
        refine ⟨3031867261859523919248827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021244841239682612832551 3031867261859523919248827)
        ·
          refine ⟨4547800892789285878873241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031867261859523919248827 4547800892789285878873241)
          ·
            refine ⟨3410850669591964409154931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547800892789285878873241 3410850669591964409154931)
            ·
              refine ⟨5116276004387946613732397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410850669591964409154931 5116276004387946613732397)
              ·
                refine ⟨1918603501645479980149649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5116276004387946613732397 1918603501645479980149649)
                ·
                  refine ⟨1438952626234109985112237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918603501645479980149649 1438952626234109985112237)
                  ·
                    refine ⟨539607234837791244417089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438952626234109985112237 539607234837791244417089)
                    ·
                      rfl

theorem cell22_1576322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1576322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576322 prefixEnd_1576322 := by exact prefixLift 1576322
  have htrace : WordTrace (prefixWord ++ tailWord_1576322) baseStart_1576322 baseEnd_1576322 := by
    simpa [prefixWord, tailWord_1576322, baseEnd_1576322] using wordTrace_append hprefix tailTrace_1576322
  have hstable : (prefixWord ++ tailWord_1576322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576322).length < 2 ^ (prefixWord ++ tailWord_1576322).sum := by decide
  have hdescent : baseEnd_1576322 < baseStart_1576322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576376 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_1576376 : Nat := 118140960795 + 1576376 * 2 ^ 59
def prefixEnd_1576376 : Nat := 4983230072969 + 3 ^ 40 * 1576376 * 2
def baseEnd_1576376 : Nat := 539625720141353103566923

theorem tailTrace_1576376 : CollatzResearch.WordTrace tailWord_1576376 prefixEnd_1576376 539625720141353103566923 := by
  unfold tailWord_1576376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28747578068533225215962491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38330104091377633621283321 28747578068533225215962491)
  ·
    refine ⟨43121367102799837823943737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28747578068533225215962491 43121367102799837823943737)
    ·
      refine ⟨32341025327099878367957803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43121367102799837823943737 32341025327099878367957803)
      ·
        refine ⟨48511537990649817551936705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32341025327099878367957803 48511537990649817551936705)
        ·
          refine ⟨36383653492987363163952529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48511537990649817551936705 36383653492987363163952529)
          ·
            refine ⟨27287740119740522372964397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36383653492987363163952529 27287740119740522372964397)
            ·
              refine ⟨10232902544902695889861649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27287740119740522372964397 10232902544902695889861649)
              ·
                refine ⟨7674676908677021917396237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10232902544902695889861649 7674676908677021917396237)
                ·
                  refine ⟨2878003840753883219023589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7674676908677021917396237 2878003840753883219023589)
                  ·
                    refine ⟨539625720141353103566923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2878003840753883219023589 539625720141353103566923)
                    ·
                      rfl

theorem cell22_1576376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_1576376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576376 prefixEnd_1576376 := by exact prefixLift 1576376
  have htrace : WordTrace (prefixWord ++ tailWord_1576376) baseStart_1576376 baseEnd_1576376 := by
    simpa [prefixWord, tailWord_1576376, baseEnd_1576376] using wordTrace_append hprefix tailTrace_1576376
  have hstable : (prefixWord ++ tailWord_1576376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576376).length < 2 ^ (prefixWord ++ tailWord_1576376).sum := by decide
  have hdescent : baseEnd_1576376 < baseStart_1576376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576391 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 6]
def baseStart_1576391 : Nat := 118140960795 + 1576391 * 2 ^ 59
def prefixEnd_1576391 : Nat := 4983230072969 + 3 ^ 40 * 1576391 * 2
def baseEnd_1576391 : Nat := 179876951649299354813959

theorem tailTrace_1576391 : CollatzResearch.WordTrace tailWord_1576391 prefixEnd_1576391 179876951649299354813959 := by
  unfold tailWord_1576391
  simp only [CollatzResearch.WordTrace]
  refine ⟨57495703232012107993721027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38330468821341405329147351 57495703232012107993721027)
  ·
    refine ⟨86243554848018161990581541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57495703232012107993721027 86243554848018161990581541)
    ·
      refine ⟨16170666534003405373234039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86243554848018161990581541 16170666534003405373234039)
      ·
        refine ⟨24255999801005108059851059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16170666534003405373234039 24255999801005108059851059)
        ·
          refine ⟨36383999701507662089776589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24255999801005108059851059 36383999701507662089776589)
          ·
            refine ⟨13643999888065373283666221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36383999701507662089776589 13643999888065373283666221)
            ·
              refine ⟨5116499958024514981374833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13643999888065373283666221 5116499958024514981374833)
              ·
                refine ⟨3837374968518386236031125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116499958024514981374833 3837374968518386236031125)
                ·
                  refine ⟨179876951649299354813959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3837374968518386236031125 179876951649299354813959)
                  ·
                    rfl

theorem cell22_1576391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 6].length) (baseStart_1576391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576391 prefixEnd_1576391 := by exact prefixLift 1576391
  have htrace : WordTrace (prefixWord ++ tailWord_1576391) baseStart_1576391 baseEnd_1576391 := by
    simpa [prefixWord, tailWord_1576391, baseEnd_1576391] using wordTrace_append hprefix tailTrace_1576391
  have hstable : (prefixWord ++ tailWord_1576391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576391).length < 2 ^ (prefixWord ++ tailWord_1576391).sum := by decide
  have hdescent : baseEnd_1576391 < baseStart_1576391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576408 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 4]
def baseStart_1576408 : Nat := 118140960795 + 1576408 * 2 ^ 59
def prefixEnd_1576408 : Nat := 4983230072969 + 3 ^ 40 * 1576408 * 2
def baseEnd_1576408 : Nat := 179878891465105228922275

theorem tailTrace_1576408 : CollatzResearch.WordTrace tailWord_1576408 prefixEnd_1576408 179878891465105228922275 := by
  unfold tailWord_1576408
  simp only [CollatzResearch.WordTrace]
  refine ⟨28748161636475259948544939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38330882181967013264726585 28748161636475259948544939)
  ·
    refine ⟨43122242454712889922817409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28748161636475259948544939 43122242454712889922817409)
    ·
      refine ⟨32341681841034667442113057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43122242454712889922817409 32341681841034667442113057)
      ·
        refine ⟨24256261380776000581584793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32341681841034667442113057 24256261380776000581584793)
        ·
          refine ⟨18192196035582000436188595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24256261380776000581584793 18192196035582000436188595)
          ·
            refine ⟨27288294053373000654282893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18192196035582000436188595 27288294053373000654282893)
            ·
              refine ⟨10233110270014875245356085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27288294053373000654282893 10233110270014875245356085)
              ·
                refine ⟨959354087813894554252133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10233110270014875245356085 959354087813894554252133)
                ·
                  refine ⟨179878891465105228922275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959354087813894554252133 179878891465105228922275)
                  ·
                    rfl

theorem cell22_1576408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_1576408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576408 prefixEnd_1576408 := by exact prefixLift 1576408
  have htrace : WordTrace (prefixWord ++ tailWord_1576408) baseStart_1576408 baseEnd_1576408 := by
    simpa [prefixWord, tailWord_1576408, baseEnd_1576408] using wordTrace_append hprefix tailTrace_1576408
  have hstable : (prefixWord ++ tailWord_1576408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576408).length < 2 ^ (prefixWord ++ tailWord_1576408).sum := by decide
  have hdescent : baseEnd_1576408 < baseStart_1576408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576410 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_1576410 : Nat := 118140960795 + 1576410 * 2 ^ 59
def prefixEnd_1576410 : Nat := 4983230072969 + 3 ^ 40 * 1576410 * 2
def baseEnd_1576410 : Nat := 539637359036188348216819

theorem tailTrace_1576410 : CollatzResearch.WordTrace tailWord_1576410 prefixEnd_1576410 539637359036188348216819 := by
  unfold tailWord_1576410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374099054735818559665671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38330930812628849492441789 14374099054735818559665671)
  ·
    refine ⟨21561148582103727839498507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14374099054735818559665671 21561148582103727839498507)
    ·
      refine ⟨32341722873155591759247761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21561148582103727839498507 32341722873155591759247761)
      ·
        refine ⟨24256292154866693819435821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32341722873155591759247761 24256292154866693819435821)
        ·
          refine ⟨9096109558075010182288433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24256292154866693819435821 9096109558075010182288433)
          ·
            refine ⟨6822082168556257636716325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9096109558075010182288433 6822082168556257636716325)
            ·
              refine ⟨1279140406604298306884311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6822082168556257636716325 1279140406604298306884311)
              ·
                refine ⟨1918710609906447460326467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279140406604298306884311 1918710609906447460326467)
                ·
                  refine ⟨2878065914859671190489701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918710609906447460326467 2878065914859671190489701)
                  ·
                    refine ⟨539637359036188348216819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2878065914859671190489701 539637359036188348216819)
                    ·
                      rfl

theorem cell22_1576410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_1576410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576410 prefixEnd_1576410 := by exact prefixLift 1576410
  have htrace : WordTrace (prefixWord ++ tailWord_1576410) baseStart_1576410 baseEnd_1576410 := by
    simpa [prefixWord, tailWord_1576410, baseEnd_1576410] using wordTrace_append hprefix tailTrace_1576410
  have hstable : (prefixWord ++ tailWord_1576410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576410).length < 2 ^ (prefixWord ++ tailWord_1576410).sum := by decide
  have hdescent : baseEnd_1576410 < baseStart_1576410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576438 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1576438 : Nat := 118140960795 + 1576438 * 2 ^ 59
def prefixEnd_1576438 : Nat := 4983230072969 + 3 ^ 40 * 1576438 * 2
def baseEnd_1576438 : Nat := 539646944008405608516733

theorem tailTrace_1576438 : CollatzResearch.WordTrace tailWord_1576438 prefixEnd_1576438 539646944008405608516733 := by
  unfold tailWord_1576438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593588591427614688792623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38331611641894556680454645 3593588591427614688792623)
  ·
    refine ⟨5390382887141422033188935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593588591427614688792623 5390382887141422033188935)
    ·
      refine ⟨8085574330712133049783403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390382887141422033188935 8085574330712133049783403)
      ·
        refine ⟨12128361496068199574675105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085574330712133049783403 12128361496068199574675105)
        ·
          refine ⟨9096271122051149681006329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12128361496068199574675105 9096271122051149681006329)
          ·
            refine ⟨6822203341538362260754747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9096271122051149681006329 6822203341538362260754747)
            ·
              refine ⟨10233305012307543391132121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6822203341538362260754747 10233305012307543391132121)
              ·
                refine ⟨7674978759230657543349091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10233305012307543391132121 7674978759230657543349091)
                ·
                  refine ⟨11512468138845986315023637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7674978759230657543349091 11512468138845986315023637)
                  ·
                    refine ⟨539646944008405608516733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11512468138845986315023637 539646944008405608516733)
                    ·
                      rfl

theorem cell22_1576438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1576438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576438 prefixEnd_1576438 := by exact prefixLift 1576438
  have htrace : WordTrace (prefixWord ++ tailWord_1576438) baseStart_1576438 baseEnd_1576438 := by
    simpa [prefixWord, tailWord_1576438, baseEnd_1576438] using wordTrace_append hprefix tailTrace_1576438
  have hstable : (prefixWord ++ tailWord_1576438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576438).length < 2 ^ (prefixWord ++ tailWord_1576438).sum := by decide
  have hdescent : baseEnd_1576438 < baseStart_1576438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576496 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_1576496 : Nat := 118140960795 + 1576496 * 2 ^ 59
def prefixEnd_1576496 : Nat := 4983230072969 + 3 ^ 40 * 1576496 * 2
def baseEnd_1576496 : Nat := 539666798593712790566555

theorem tailTrace_1576496 : CollatzResearch.WordTrace tailWord_1576496 prefixEnd_1576496 539666798593712790566555 := by
  unfold tailWord_1576496
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749766448315855463146671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38333021931087807284195561 28749766448315855463146671)
  ·
    refine ⟨43124649672473783194720007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28749766448315855463146671 43124649672473783194720007)
    ·
      refine ⟨64686974508710674792080011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43124649672473783194720007 64686974508710674792080011)
      ·
        refine ⟨97030461763066012188120017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64686974508710674792080011 97030461763066012188120017)
        ·
          refine ⟨72772846322299509141090013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97030461763066012188120017 72772846322299509141090013)
          ·
            refine ⟨27289817370862315927908755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72772846322299509141090013 27289817370862315927908755)
            ·
              refine ⟨40934726056293473891863133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27289817370862315927908755 40934726056293473891863133)
              ·
                refine ⟨15350522271110052709448675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40934726056293473891863133 15350522271110052709448675)
                ·
                  refine ⟨23025783406665079064173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15350522271110052709448675 23025783406665079064173013)
                  ·
                    refine ⟨539666798593712790566555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23025783406665079064173013 539666798593712790566555)
                    ·
                      rfl

theorem cell22_1576496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_1576496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576496 prefixEnd_1576496 := by exact prefixLift 1576496
  have htrace : WordTrace (prefixWord ++ tailWord_1576496) baseStart_1576496 baseEnd_1576496 := by
    simpa [prefixWord, tailWord_1576496, baseEnd_1576496] using wordTrace_append hprefix tailTrace_1576496
  have hstable : (prefixWord ++ tailWord_1576496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576496).length < 2 ^ (prefixWord ++ tailWord_1576496).sum := by decide
  have hdescent : baseEnd_1576496 < baseStart_1576496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576577 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 4]
def baseStart_1576577 : Nat := 118140960795 + 1576577 * 2 ^ 59
def prefixEnd_1576577 : Nat := 4983230072969 + 3 ^ 40 * 1576577 * 2
def baseEnd_1576577 : Nat := 179898175516351859763769

theorem tailTrace_1576577 : CollatzResearch.WordTrace tailWord_1576577 prefixEnd_1576577 179898175516351859763769 := by
  unfold tailWord_1576577
  simp only [CollatzResearch.WordTrace]
  refine ⟨57502487209338261759991985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38334991472892174506661323 57502487209338261759991985)
  ·
    refine ⟨43126865407003696319993989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57502487209338261759991985 43126865407003696319993989)
    ·
      refine ⟨8086287263813193059998873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43126865407003696319993989 8086287263813193059998873)
      ·
        refine ⟨6064715447859894794999155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8086287263813193059998873 6064715447859894794999155)
        ·
          refine ⟨9097073171789842192498733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064715447859894794999155 9097073171789842192498733)
          ·
            refine ⟨3411402439421190822187025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9097073171789842192498733 3411402439421190822187025)
            ·
              refine ⟨2558551829565893116640269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411402439421190822187025 2558551829565893116640269)
              ·
                refine ⟨959456936087209918740101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2558551829565893116640269 959456936087209918740101)
                ·
                  refine ⟨179898175516351859763769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959456936087209918740101 179898175516351859763769)
                  ·
                    rfl

theorem cell22_1576577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_1576577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576577 prefixEnd_1576577 := by exact prefixLift 1576577
  have htrace : WordTrace (prefixWord ++ tailWord_1576577) baseStart_1576577 baseEnd_1576577 := by
    simpa [prefixWord, tailWord_1576577, baseEnd_1576577] using wordTrace_append hprefix tailTrace_1576577
  have hstable : (prefixWord ++ tailWord_1576577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576577).length < 2 ^ (prefixWord ++ tailWord_1576577).sum := by decide
  have hdescent : baseEnd_1576577 < baseStart_1576577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576609 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 2, 3]
def baseStart_1576609 : Nat := 118140960795 + 1576609 * 2 ^ 59
def prefixEnd_1576609 : Nat := 4983230072969 + 3 ^ 40 * 1576609 * 2
def baseEnd_1576609 : Nat := 539705480803018162491209

theorem tailTrace_1576609 : CollatzResearch.WordTrace tailWord_1576609 prefixEnd_1576609 539705480803018162491209 := by
  unfold tailWord_1576609
  simp only [CollatzResearch.WordTrace]
  refine ⟨57503654345222331225156881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38335769563481554150104587 57503654345222331225156881)
  ·
    refine ⟨43127740758916748418867661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57503654345222331225156881 43127740758916748418867661)
    ·
      refine ⟨16172902784593780657075373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43127740758916748418867661 16172902784593780657075373)
      ·
        refine ⟨6064838544222667746403265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16172902784593780657075373 6064838544222667746403265)
        ·
          refine ⟨4548628908167000809802449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6064838544222667746403265 4548628908167000809802449)
          ·
            refine ⟨3411471681125250607351837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4548628908167000809802449 3411471681125250607351837)
            ·
              refine ⟨1279301880421968977756939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3411471681125250607351837 1279301880421968977756939)
              ·
                refine ⟨1918952820632953466635409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279301880421968977756939 1918952820632953466635409)
                ·
                  refine ⟨1439214615474715099976557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918952820632953466635409 1439214615474715099976557)
                  ·
                    refine ⟨539705480803018162491209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439214615474715099976557 539705480803018162491209)
                    ·
                      rfl

theorem cell22_1576609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_1576609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576609 prefixEnd_1576609 := by exact prefixLift 1576609
  have htrace : WordTrace (prefixWord ++ tailWord_1576609) baseStart_1576609 baseEnd_1576609 := by
    simpa [prefixWord, tailWord_1576609, baseEnd_1576609] using wordTrace_append hprefix tailTrace_1576609
  have hstable : (prefixWord ++ tailWord_1576609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576609).length < 2 ^ (prefixWord ++ tailWord_1576609).sum := by decide
  have hdescent : baseEnd_1576609 < baseStart_1576609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576622 : List Nat := [4, 1, 4, 1, 2, 1, 1, 8]
def baseStart_1576622 : Nat := 118140960795 + 1576622 * 2 ^ 59
def prefixEnd_1576622 : Nat := 4983230072969 + 3 ^ 40 * 1576622 * 2
def baseEnd_1576622 : Nat := 59967770107632273546241

theorem tailTrace_1576622 : CollatzResearch.WordTrace tailWord_1576622 prefixEnd_1576622 59967770107632273546241 := by
  unfold tailWord_1576622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188016061771904305672515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38336085662783489630253413 7188016061771904305672515)
  ·
    refine ⟨10782024092657856458508773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7188016061771904305672515 10782024092657856458508773)
    ·
      refine ⟨2021629517373348085970395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10782024092657856458508773 2021629517373348085970395)
      ·
        refine ⟨3032444276060022128955593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021629517373348085970395 3032444276060022128955593)
        ·
          refine ⟨2274333207045016596716695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3032444276060022128955593 2274333207045016596716695)
          ·
            refine ⟨3411499810567524895075043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274333207045016596716695 3411499810567524895075043)
            ·
              refine ⟨5117249715851287342612565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411499810567524895075043 5117249715851287342612565)
              ·
                refine ⟨59967770107632273546241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5117249715851287342612565 59967770107632273546241)
                ·
                  rfl

theorem cell22_1576622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_1576622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576622 prefixEnd_1576622 := by exact prefixLift 1576622
  have htrace : WordTrace (prefixWord ++ tailWord_1576622) baseStart_1576622 baseEnd_1576622 := by
    simpa [prefixWord, tailWord_1576622, baseEnd_1576622] using wordTrace_append hprefix tailTrace_1576622
  have hstable : (prefixWord ++ tailWord_1576622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576622).length < 2 ^ (prefixWord ++ tailWord_1576622).sum := by decide
  have hdescent : baseEnd_1576622 < baseStart_1576622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576633 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 7]
def baseStart_1576633 : Nat := 118140960795 + 1576633 * 2 ^ 59
def prefixEnd_1576633 : Nat := 4983230072969 + 3 ^ 40 * 1576633 * 2
def baseEnd_1576633 : Nat := 179904565497830033297045

theorem tailTrace_1576633 : CollatzResearch.WordTrace tailWord_1576633 prefixEnd_1576633 179904565497830033297045 := by
  unfold tailWord_1576633
  simp only [CollatzResearch.WordTrace]
  refine ⟨57504529697135383324030553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38336353131423588882687035 57504529697135383324030553)
  ·
    refine ⟨43128397272851537493022915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57504529697135383324030553 43128397272851537493022915)
    ·
      refine ⟨64692595909277306239534373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43128397272851537493022915 64692595909277306239534373)
      ·
        refine ⟨12129861732989494919912695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64692595909277306239534373 12129861732989494919912695)
        ·
          refine ⟨18194792599484242379869043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12129861732989494919912695 18194792599484242379869043)
          ·
            refine ⟨27292188899226363569803565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18194792599484242379869043 27292188899226363569803565)
            ·
              refine ⟨10234570837209886338676337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27292188899226363569803565 10234570837209886338676337)
              ·
                refine ⟨7675928127907414754007253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10234570837209886338676337 7675928127907414754007253)
                ·
                  refine ⟨179904565497830033297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7675928127907414754007253 179904565497830033297045)
                  ·
                    rfl

theorem cell22_1576633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_1576633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576633 prefixEnd_1576633 := by exact prefixLift 1576633
  have htrace : WordTrace (prefixWord ++ tailWord_1576633) baseStart_1576633 baseEnd_1576633 := by
    simpa [prefixWord, tailWord_1576633, baseEnd_1576633] using wordTrace_append hprefix tailTrace_1576633
  have hstable : (prefixWord ++ tailWord_1576633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576633).length < 2 ^ (prefixWord ++ tailWord_1576633).sum := by decide
  have hdescent : baseEnd_1576633 < baseStart_1576633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576712 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 4]
def baseStart_1576712 : Nat := 118140960795 + 1576712 * 2 ^ 59
def prefixEnd_1576712 : Nat := 4983230072969 + 3 ^ 40 * 1576712 * 2
def baseEnd_1576712 : Nat := 179913579935986742388631

theorem tailTrace_1576712 : CollatzResearch.WordTrace tailWord_1576712 prefixEnd_1576712 179913579935986742388631 := by
  unfold tailWord_1576712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28753705531924589908078195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38338274042566119877437593 28753705531924589908078195)
  ·
    refine ⟨43130558297886884862117293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28753705531924589908078195 43130558297886884862117293)
    ·
      refine ⟨16173959361707581823293985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43130558297886884862117293 16173959361707581823293985)
      ·
        refine ⟨12130469521280686367470489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16173959361707581823293985 12130469521280686367470489)
        ·
          refine ⟨9097852140960514775602867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12130469521280686367470489 9097852140960514775602867)
          ·
            refine ⟨13646778211440772163404301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097852140960514775602867 13646778211440772163404301)
            ·
              refine ⟨5117541829290289561276613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13646778211440772163404301 5117541829290289561276613)
              ·
                refine ⟨959539092991929292739365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5117541829290289561276613 959539092991929292739365)
                ·
                  refine ⟨179913579935986742388631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959539092991929292739365 179913579935986742388631)
                  ·
                    rfl

theorem cell22_1576712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_1576712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576712 prefixEnd_1576712 := by exact prefixLift 1576712
  have htrace : WordTrace (prefixWord ++ tailWord_1576712) baseStart_1576712 baseEnd_1576712 := by
    simpa [prefixWord, tailWord_1576712, baseEnd_1576712] using wordTrace_append hprefix tailTrace_1576712
  have hstable : (prefixWord ++ tailWord_1576712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576712).length < 2 ^ (prefixWord ++ tailWord_1576712).sum := by decide
  have hdescent : baseEnd_1576712 < baseStart_1576712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576723 : List Nat := [1, 1, 1, 2, 1, 3, 2, 11]
def baseStart_1576723 : Nat := 118140960795 + 1576723 * 2 ^ 59
def prefixEnd_1576723 : Nat := 4983230072969 + 3 ^ 40 * 1576723 * 2
def baseEnd_1576723 : Nat := 59971611703639985015651

theorem tailTrace_1576723 : CollatzResearch.WordTrace tailWord_1576723 prefixEnd_1576723 59971611703639985015651 := by
  unfold tailWord_1576723
  simp only [CollatzResearch.WordTrace]
  refine ⟨57507812266809328694806823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38338541511206219129871215 57507812266809328694806823)
  ·
    refine ⟨86261718400213993042210235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57507812266809328694806823 86261718400213993042210235)
    ·
      refine ⟨129392577600320989563315353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86261718400213993042210235 129392577600320989563315353)
      ·
        refine ⟨97044433200240742172486515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129392577600320989563315353 97044433200240742172486515)
        ·
          refine ⟨145566649800361113258729773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97044433200240742172486515 145566649800361113258729773)
          ·
            refine ⟨54587493675135417472023665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145566649800361113258729773 54587493675135417472023665)
            ·
              refine ⟨40940620256351563104017749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54587493675135417472023665 40940620256351563104017749)
              ·
                refine ⟨59971611703639985015651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40940620256351563104017749 59971611703639985015651)
                ·
                  rfl

theorem cell22_1576723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 11].length) (baseStart_1576723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576723 prefixEnd_1576723 := by exact prefixLift 1576723
  have htrace : WordTrace (prefixWord ++ tailWord_1576723) baseStart_1576723 baseEnd_1576723 := by
    simpa [prefixWord, tailWord_1576723, baseEnd_1576723] using wordTrace_append hprefix tailTrace_1576723
  have hstable : (prefixWord ++ tailWord_1576723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576723).length < 2 ^ (prefixWord ++ tailWord_1576723).sum := by decide
  have hdescent : baseEnd_1576723 < baseStart_1576723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576727 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 1, 5]
def baseStart_1576727 : Nat := 118140960795 + 1576727 * 2 ^ 59
def prefixEnd_1576727 : Nat := 4983230072969 + 3 ^ 40 * 1576727 * 2
def baseEnd_1576727 : Nat := 539745874614505188040847

theorem tailTrace_1576727 : CollatzResearch.WordTrace tailWord_1576727 prefixEnd_1576727 539745874614505188040847 := by
  unfold tailWord_1576727
  simp only [CollatzResearch.WordTrace]
  refine ⟨57507958158794837377952435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38338638772529891585301623 57507958158794837377952435)
  ·
    refine ⟨86261937238192256066928653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57507958158794837377952435 86261937238192256066928653)
    ·
      refine ⟨32348226464322096025098245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86261937238192256066928653 32348226464322096025098245)
      ·
        refine ⟨6065292462060393004705921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32348226464322096025098245 6065292462060393004705921)
        ·
          refine ⟨4548969346545294753529441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065292462060393004705921 4548969346545294753529441)
          ·
            refine ⟨3411727009908971065147081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4548969346545294753529441 3411727009908971065147081)
            ·
              refine ⟨2558795257431728298860311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411727009908971065147081 2558795257431728298860311)
              ·
                refine ⟨3838192886147592448290467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558795257431728298860311 3838192886147592448290467)
                ·
                  refine ⟨5757289329221388672435701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838192886147592448290467 5757289329221388672435701)
                  ·
                    refine ⟨539745874614505188040847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5757289329221388672435701 539745874614505188040847)
                    ·
                      rfl

theorem cell22_1576727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_1576727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576727 prefixEnd_1576727 := by exact prefixLift 1576727
  have htrace : WordTrace (prefixWord ++ tailWord_1576727) baseStart_1576727 baseEnd_1576727 := by
    simpa [prefixWord, tailWord_1576727, baseEnd_1576727] using wordTrace_append hprefix tailTrace_1576727
  have hstable : (prefixWord ++ tailWord_1576727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576727).length < 2 ^ (prefixWord ++ tailWord_1576727).sum := by decide
  have hdescent : baseEnd_1576727 < baseStart_1576727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576802 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1576802 : Nat := 118140960795 + 1576802 * 2 ^ 59
def prefixEnd_1576802 : Nat := 4983230072969 + 3 ^ 40 * 1576802 * 2
def baseEnd_1576802 : Nat := 179923849549076664138539

theorem tailTrace_1576802 : CollatzResearch.WordTrace tailWord_1576802 prefixEnd_1576802 179923849549076664138539 := by
  unfold tailWord_1576802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377673408380781296733165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38340462422348750124621773 14377673408380781296733165)
  ·
    refine ⟨5391627528142792986274937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14377673408380781296733165 5391627528142792986274937)
    ·
      refine ⟨4043720646107094739706203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5391627528142792986274937 4043720646107094739706203)
      ·
        refine ⟨6065580969160642109559305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043720646107094739706203 6065580969160642109559305)
        ·
          refine ⟨4549185726870481582169479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065580969160642109559305 4549185726870481582169479)
          ·
            refine ⟨6823778590305722373254219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549185726870481582169479 6823778590305722373254219)
            ·
              refine ⟨10235667885458583559881329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823778590305722373254219 10235667885458583559881329)
              ·
                refine ⟨7676750914093937669910997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10235667885458583559881329 7676750914093937669910997)
                ·
                  refine ⟨179923849549076664138539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7676750914093937669910997 179923849549076664138539)
                  ·
                    rfl

theorem cell22_1576802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1576802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576802 prefixEnd_1576802 := by exact prefixLift 1576802
  have htrace : WordTrace (prefixWord ++ tailWord_1576802) baseStart_1576802 baseEnd_1576802 := by
    simpa [prefixWord, tailWord_1576802, baseEnd_1576802] using wordTrace_append hprefix tailTrace_1576802
  have hstable : (prefixWord ++ tailWord_1576802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576802).length < 2 ^ (prefixWord ++ tailWord_1576802).sum := by decide
  have hdescent : baseEnd_1576802 < baseStart_1576802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576815 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 7, 4]
def baseStart_1576815 : Nat := 118140960795 + 1576815 * 2 ^ 59
def prefixEnd_1576815 : Nat := 4983230072969 + 3 ^ 40 * 1576815 * 2
def baseEnd_1576815 : Nat := 539775998812902291840577

theorem tailTrace_1576815 : CollatzResearch.WordTrace tailWord_1576815 prefixEnd_1576815 539775998812902291840577 := by
  unfold tailWord_1576815
  simp only [CollatzResearch.WordTrace]
  refine ⟨57511167782476028407155899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38340778521650685604770599 57511167782476028407155899)
  ·
    refine ⟨86266751673714042610733849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57511167782476028407155899 86266751673714042610733849)
    ·
      refine ⟨64700063755285531958050387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86266751673714042610733849 64700063755285531958050387)
      ·
        refine ⟨97050095632928297937075581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64700063755285531958050387 97050095632928297937075581)
        ·
          refine ⟨36393785862348111726403343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97050095632928297937075581 36393785862348111726403343)
          ·
            refine ⟨54590678793522167589605015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36393785862348111726403343 54590678793522167589605015)
            ·
              refine ⟨81886018190283251384407523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54590678793522167589605015 81886018190283251384407523)
              ·
                refine ⟨122829027285424877076611285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81886018190283251384407523 122829027285424877076611285)
                ·
                  refine ⟨2878805327002145556483077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 122829027285424877076611285 2878805327002145556483077)
                  ·
                    refine ⟨539775998812902291840577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2878805327002145556483077 539775998812902291840577)
                    ·
                      rfl

theorem cell22_1576815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_1576815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576815 prefixEnd_1576815 := by exact prefixLift 1576815
  have htrace : WordTrace (prefixWord ++ tailWord_1576815) baseStart_1576815 baseEnd_1576815 := by
    simpa [prefixWord, tailWord_1576815, baseEnd_1576815] using wordTrace_append hprefix tailTrace_1576815
  have hstable : (prefixWord ++ tailWord_1576815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576815).length < 2 ^ (prefixWord ++ tailWord_1576815).sum := by decide
  have hdescent : baseEnd_1576815 < baseStart_1576815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576879 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 2, 3]
def baseStart_1576879 : Nat := 118140960795 + 1576879 * 2 ^ 59
def prefixEnd_1576879 : Nat := 4983230072969 + 3 ^ 40 * 1576879 * 2
def baseEnd_1576879 : Nat := 539797907320827458240381

theorem tailTrace_1576879 : CollatzResearch.WordTrace tailWord_1576879 prefixEnd_1576879 539797907320827458240381 := by
  unfold tailWord_1576879
  simp only [CollatzResearch.WordTrace]
  refine ⟨57513502054244167337485691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38342334702829444891657127 57513502054244167337485691)
  ·
    refine ⟨86270253081366251006228537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57513502054244167337485691 86270253081366251006228537)
    ·
      refine ⟨64702689811024688254671403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86270253081366251006228537 64702689811024688254671403)
      ·
        refine ⟨97054034716537032382007105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64702689811024688254671403 97054034716537032382007105)
        ·
          refine ⟨72790526037402774286505329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97054034716537032382007105 72790526037402774286505329)
          ·
            refine ⟨54592894528052080714878997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72790526037402774286505329 54592894528052080714878997)
            ·
              refine ⟨2559041931002441283509953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54592894528052080714878997 2559041931002441283509953)
              ·
                refine ⟨1919281448251830962632465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559041931002441283509953 1919281448251830962632465)
                ·
                  refine ⟨1439461086188873221974349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1919281448251830962632465 1439461086188873221974349)
                  ·
                    refine ⟨539797907320827458240381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439461086188873221974349 539797907320827458240381)
                    ·
                      rfl

theorem cell22_1576879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_1576879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576879 prefixEnd_1576879 := by exact prefixLift 1576879
  have htrace : WordTrace (prefixWord ++ tailWord_1576879) baseStart_1576879 baseEnd_1576879 := by
    simpa [prefixWord, tailWord_1576879, baseEnd_1576879] using wordTrace_append hprefix tailTrace_1576879
  have hstable : (prefixWord ++ tailWord_1576879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576879).length < 2 ^ (prefixWord ++ tailWord_1576879).sum := by decide
  have hdescent : baseEnd_1576879 < baseStart_1576879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576881 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 4]
def baseStart_1576881 : Nat := 118140960795 + 1576881 * 2 ^ 59
def prefixEnd_1576881 : Nat := 4983230072969 + 3 ^ 40 * 1576881 * 2
def baseEnd_1576881 : Nat := 179932863987233373230125

theorem tailTrace_1576881 : CollatzResearch.WordTrace tailWord_1576881 prefixEnd_1576881 179932863987233373230125 := by
  unfold tailWord_1576881
  simp only [CollatzResearch.WordTrace]
  refine ⟨57513575000236921679058497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38342383333491281119372331 57513575000236921679058497)
  ·
    refine ⟨43135181250177691259293873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57513575000236921679058497 43135181250177691259293873)
    ·
      refine ⟨32351385937633268444470405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43135181250177691259293873 32351385937633268444470405)
      ·
        refine ⟨6065884863306237833338201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32351385937633268444470405 6065884863306237833338201)
        ·
          refine ⟨4549413647479678375003651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065884863306237833338201 4549413647479678375003651)
          ·
            refine ⟨6824120471219517562505477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549413647479678375003651 6824120471219517562505477)
            ·
              refine ⟨1279522588353659542969777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6824120471219517562505477 1279522588353659542969777)
              ·
                refine ⟨959641941265244657227333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279522588353659542969777 959641941265244657227333)
                ·
                  refine ⟨179932863987233373230125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959641941265244657227333 179932863987233373230125)
                  ·
                    rfl

theorem cell22_1576881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_1576881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576881 prefixEnd_1576881 := by exact prefixLift 1576881
  have htrace : WordTrace (prefixWord ++ tailWord_1576881) baseStart_1576881 baseEnd_1576881 := by
    simpa [prefixWord, tailWord_1576881, baseEnd_1576881] using wordTrace_append hprefix tailTrace_1576881
  have hstable : (prefixWord ++ tailWord_1576881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576881).length < 2 ^ (prefixWord ++ tailWord_1576881).sum := by decide
  have hdescent : baseEnd_1576881 < baseStart_1576881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576930 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1576930 : Nat := 118140960795 + 1576930 * 2 ^ 59
def prefixEnd_1576930 : Nat := 4983230072969 + 3 ^ 40 * 1576930 * 2
def baseEnd_1576930 : Nat := 539815365663080325215225

theorem tailTrace_1576930 : CollatzResearch.WordTrace tailWord_1576930 prefixEnd_1576930 539815365663080325215225 := by
  unfold tailWord_1576930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14378840544264850761898061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38343574784706268698394829 14378840544264850761898061)
  ·
    refine ⟨5392065204099319035711773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14378840544264850761898061 5392065204099319035711773)
    ·
      refine ⟨2022024451537244638391915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5392065204099319035711773 2022024451537244638391915)
      ·
        refine ⟨3033036677305866957587873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022024451537244638391915 3033036677305866957587873)
        ·
          refine ⟨2274777507979400218190905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3033036677305866957587873 2274777507979400218190905)
          ·
            refine ⟨1706083130984550163643179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274777507979400218190905 1706083130984550163643179)
            ·
              refine ⟨2559124696476825245464769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706083130984550163643179 2559124696476825245464769)
              ·
                refine ⟨1919343522357618934098577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559124696476825245464769 1919343522357618934098577)
                ·
                  refine ⟨1439507641768214200573933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1919343522357618934098577 1439507641768214200573933)
                  ·
                    refine ⟨539815365663080325215225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439507641768214200573933 539815365663080325215225)
                    ·
                      rfl

theorem cell22_1576930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1576930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576930 prefixEnd_1576930 := by exact prefixLift 1576930
  have htrace : WordTrace (prefixWord ++ tailWord_1576930) baseStart_1576930 baseEnd_1576930 := by
    simpa [prefixWord, tailWord_1576930, baseEnd_1576930] using wordTrace_append hprefix tailTrace_1576930
  have hstable : (prefixWord ++ tailWord_1576930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576930).length < 2 ^ (prefixWord ++ tailWord_1576930).sum := by decide
  have hdescent : baseEnd_1576930 < baseStart_1576930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576952 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_1576952 : Nat := 118140960795 + 1576952 * 2 ^ 59
def prefixEnd_1576952 : Nat := 4983230072969 + 3 ^ 40 * 1576952 * 2
def baseEnd_1576952 : Nat := 539822896712679601165157

theorem tailTrace_1576952 : CollatzResearch.WordTrace tailWord_1576952 prefixEnd_1576952 539822896712679601165157 := by
  unfold tailWord_1576952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28758082291489850402446555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38344109721986467203262073 28758082291489850402446555)
  ·
    refine ⟨43137123437234775603669833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28758082291489850402446555 43137123437234775603669833)
    ·
      refine ⟨32352842577926081702752375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43137123437234775603669833 32352842577926081702752375)
      ·
        refine ⟨48529263866889122554128563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32352842577926081702752375 48529263866889122554128563)
        ·
          refine ⟨72793895800333683831192845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48529263866889122554128563 72793895800333683831192845)
          ·
            refine ⟨27297710925125131436697317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72793895800333683831192845 27297710925125131436697317)
            ·
              refine ⟨5118320798460962144380747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27297710925125131436697317 5118320798460962144380747)
              ·
                refine ⟨7677481197691443216571121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118320798460962144380747 7677481197691443216571121)
                ·
                  refine ⟨5758110898268582412428341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677481197691443216571121 5758110898268582412428341)
                  ·
                    refine ⟨539822896712679601165157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5758110898268582412428341 539822896712679601165157)
                    ·
                      rfl

theorem cell22_1576952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_1576952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576952 prefixEnd_1576952 := by exact prefixLift 1576952
  have htrace : WordTrace (prefixWord ++ tailWord_1576952) baseStart_1576952 baseEnd_1576952 := by
    simpa [prefixWord, tailWord_1576952, baseEnd_1576952] using wordTrace_append hprefix tailTrace_1576952
  have hstable : (prefixWord ++ tailWord_1576952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576952).length < 2 ^ (prefixWord ++ tailWord_1576952).sum := by decide
  have hdescent : baseEnd_1576952 < baseStart_1576952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576984 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_1576984 : Nat := 118140960795 + 1576984 * 2 ^ 59
def prefixEnd_1576984 : Nat := 4983230072969 + 3 ^ 40 * 1576984 * 2
def baseEnd_1576984 : Nat := 539833850966642184365059

theorem tailTrace_1576984 : CollatzResearch.WordTrace tailWord_1576984 prefixEnd_1576984 539833850966642184365059 := by
  unfold tailWord_1576984
  simp only [CollatzResearch.WordTrace]
  refine ⟨28758665859431885135029003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38344887812575846846705337 28758665859431885135029003)
  ·
    refine ⟨43137998789147827702543505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28758665859431885135029003 43137998789147827702543505)
    ·
      refine ⟨32353499091860870776907629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43137998789147827702543505 32353499091860870776907629)
      ·
        refine ⟨12132562159447826541340361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32353499091860870776907629 12132562159447826541340361)
        ·
          refine ⟨9099421619585869906005271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12132562159447826541340361 9099421619585869906005271)
          ·
            refine ⟨13649132429378804859007907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099421619585869906005271 13649132429378804859007907)
            ·
              refine ⟨20473698644068207288511861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13649132429378804859007907 20473698644068207288511861)
              ·
                refine ⟨1919409247881394433297987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20473698644068207288511861 1919409247881394433297987)
                ·
                  refine ⟨2879113871822091649946981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919409247881394433297987 2879113871822091649946981)
                  ·
                    refine ⟨539833850966642184365059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879113871822091649946981 539833850966642184365059)
                    ·
                      rfl

theorem cell22_1576984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_1576984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1576984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1576984 prefixEnd_1576984 := by exact prefixLift 1576984
  have htrace : WordTrace (prefixWord ++ tailWord_1576984) baseStart_1576984 baseEnd_1576984 := by
    simpa [prefixWord, tailWord_1576984, baseEnd_1576984] using wordTrace_append hprefix tailTrace_1576984
  have hstable : (prefixWord ++ tailWord_1576984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576984).length < 2 ^ (prefixWord ++ tailWord_1576984).sum := by decide
  have hdescent : baseEnd_1576984 < baseStart_1576984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577093 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_1577093 : Nat := 118140960795 + 1577093 * 2 ^ 59
def prefixEnd_1577093 : Nat := 4983230072969 + 3 ^ 40 * 1577093 * 2
def baseEnd_1577093 : Nat := 539871163894202233389725

theorem tailTrace_1577093 : CollatzResearch.WordTrace tailWord_1577093 prefixEnd_1577093 539871163894202233389725 := by
  unfold tailWord_1577093
  simp only [CollatzResearch.WordTrace]
  refine ⟨57521307275468881885775933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38347538183645921257183955 57521307275468881885775933)
  ·
    refine ⟨21570490228300830707165975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57521307275468881885775933 21570490228300830707165975)
    ·
      refine ⟨32355735342451246060748963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21570490228300830707165975 32355735342451246060748963)
      ·
        refine ⟨48533603013676869091123445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32355735342451246060748963 48533603013676869091123445)
        ·
          refine ⟨4550025282532206477292823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48533603013676869091123445 4550025282532206477292823)
          ·
            refine ⟨6825037923798309715939235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550025282532206477292823 6825037923798309715939235)
            ·
              refine ⟨10237556885697464573908853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825037923798309715939235 10237556885697464573908853)
              ·
                refine ⟨959770958034137303803955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10237556885697464573908853 959770958034137303803955)
                ·
                  refine ⟨1439656437051205955705933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959770958034137303803955 1439656437051205955705933)
                  ·
                    refine ⟨539871163894202233389725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439656437051205955705933 539871163894202233389725)
                    ·
                      rfl

theorem cell22_1577093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_1577093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577093 prefixEnd_1577093 := by exact prefixLift 1577093
  have htrace : WordTrace (prefixWord ++ tailWord_1577093) baseStart_1577093 baseEnd_1577093 := by
    simpa [prefixWord, tailWord_1577093, baseEnd_1577093] using wordTrace_append hprefix tailTrace_1577093
  have hstable : (prefixWord ++ tailWord_1577093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577093).length < 2 ^ (prefixWord ++ tailWord_1577093).sum := by decide
  have hdescent : baseEnd_1577093 < baseStart_1577093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577149 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1577149 : Nat := 118140960795 + 1577149 * 2 ^ 59
def prefixEnd_1577149 : Nat := 4983230072969 + 3 ^ 40 * 1577149 * 2
def baseEnd_1577149 : Nat := 539890333838636753989553

theorem tailTrace_1577149 : CollatzResearch.WordTrace tailWord_1577149 prefixEnd_1577149 539890333838636753989553 := by
  unfold tailWord_1577149
  simp only [CollatzResearch.WordTrace]
  refine ⟨57523349763266003449814501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38348899842177335633209667 57523349763266003449814501)
  ·
    refine ⟨10785628080612375646840219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57523349763266003449814501 10785628080612375646840219)
    ·
      refine ⟨16178442120918563470260329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10785628080612375646840219 16178442120918563470260329)
      ·
        refine ⟨12133831590688922602695247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16178442120918563470260329 12133831590688922602695247)
        ·
          refine ⟨18200747386033383904042871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133831590688922602695247 18200747386033383904042871)
          ·
            refine ⟨27301121079050075856064307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18200747386033383904042871 27301121079050075856064307)
            ·
              refine ⟨40951681618575113784096461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27301121079050075856064307 40951681618575113784096461)
              ·
                refine ⟨15356880606965667669036173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40951681618575113784096461 15356880606965667669036173)
                ·
                  refine ⟨5758830227612125375888565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15356880606965667669036173 5758830227612125375888565)
                  ·
                    refine ⟨539890333838636753989553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5758830227612125375888565 539890333838636753989553)
                    ·
                      rfl

theorem cell22_1577149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1577149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577149 prefixEnd_1577149 := by exact prefixLift 1577149
  have htrace : WordTrace (prefixWord ++ tailWord_1577149) baseStart_1577149 baseEnd_1577149 := by
    simpa [prefixWord, tailWord_1577149, baseEnd_1577149] using wordTrace_append hprefix tailTrace_1577149
  have hstable : (prefixWord ++ tailWord_1577149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577149).length < 2 ^ (prefixWord ++ tailWord_1577149).sum := by decide
  have hdescent : baseEnd_1577149 < baseStart_1577149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577187 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 1, 4]
def baseStart_1577187 : Nat := 118140960795 + 1577187 * 2 ^ 59
def prefixEnd_1577187 : Nat := 4983230072969 + 3 ^ 40 * 1577187 * 2
def baseEnd_1577187 : Nat := 539903342015217321539437

theorem tailTrace_1577187 : CollatzResearch.WordTrace tailWord_1577187 prefixEnd_1577187 539903342015217321539437 := by
  unfold tailWord_1577187
  simp only [CollatzResearch.WordTrace]
  refine ⟨57524735737128335939697815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38349823824752223959798543 57524735737128335939697815)
  ·
    refine ⟨86287103605692503909546723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57524735737128335939697815 86287103605692503909546723)
    ·
      refine ⟨129430655408538755864320085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86287103605692503909546723 129430655408538755864320085)
      ·
        refine ⟨1516765493068813545285001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 129430655408538755864320085 1516765493068813545285001)
        ·
          refine ⟨1137574119801610158963751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516765493068813545285001 1137574119801610158963751)
          ·
            refine ⟨1706361179702415238445627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137574119801610158963751 1706361179702415238445627)
            ·
              refine ⟨2559541769553622857668441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706361179702415238445627 2559541769553622857668441)
              ·
                refine ⟨1919656327165217143251331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559541769553622857668441 1919656327165217143251331)
                ·
                  refine ⟨2879484490747825714876997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919656327165217143251331 2879484490747825714876997)
                  ·
                    refine ⟨539903342015217321539437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879484490747825714876997 539903342015217321539437)
                    ·
                      rfl

theorem cell22_1577187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 4].length) (baseStart_1577187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577187 prefixEnd_1577187 := by exact prefixLift 1577187
  have htrace : WordTrace (prefixWord ++ tailWord_1577187) baseStart_1577187 baseEnd_1577187 := by
    simpa [prefixWord, tailWord_1577187, baseEnd_1577187] using wordTrace_append hprefix tailTrace_1577187
  have hstable : (prefixWord ++ tailWord_1577187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577187).length < 2 ^ (prefixWord ++ tailWord_1577187).sum := by decide
  have hdescent : baseEnd_1577187 < baseStart_1577187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577245 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1577245 : Nat := 118140960795 + 1577245 * 2 ^ 59
def prefixEnd_1577245 : Nat := 4983230072969 + 3 ^ 40 * 1577245 * 2
def baseEnd_1577245 : Nat := 539923196600524503589259

theorem tailTrace_1577245 : CollatzResearch.WordTrace tailWord_1577245 prefixEnd_1577245 539923196600524503589259 := by
  unfold tailWord_1577245
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526851170918211845309189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38351234113945474563539459 57526851170918211845309189)
  ·
    refine ⟨10786284594547164720995473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57526851170918211845309189 10786284594547164720995473)
    ·
      refine ⟨8089713445910373540746605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10786284594547164720995473 8089713445910373540746605)
      ·
        refine ⟨3033642542216390077779977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8089713445910373540746605 3033642542216390077779977)
        ·
          refine ⟨2275231906662292558334983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3033642542216390077779977 2275231906662292558334983)
          ·
            refine ⟨3412847859993438837502475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275231906662292558334983 3412847859993438837502475)
            ·
              refine ⟨5119271789990158256253713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412847859993438837502475 5119271789990158256253713)
              ·
                refine ⟨3839453842492618692190285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119271789990158256253713 3839453842492618692190285)
                ·
                  refine ⟨1439795190934732009571357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3839453842492618692190285 1439795190934732009571357)
                  ·
                    refine ⟨539923196600524503589259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439795190934732009571357 539923196600524503589259)
                    ·
                      rfl

theorem cell22_1577245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1577245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577245 prefixEnd_1577245 := by exact prefixLift 1577245
  have htrace : WordTrace (prefixWord ++ tailWord_1577245) baseStart_1577245 baseEnd_1577245 := by
    simpa [prefixWord, tailWord_1577245, baseEnd_1577245] using wordTrace_append hprefix tailTrace_1577245
  have hstable : (prefixWord ++ tailWord_1577245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577245).length < 2 ^ (prefixWord ++ tailWord_1577245).sum := by decide
  have hdescent : baseEnd_1577245 < baseStart_1577245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577316 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1577316 : Nat := 118140960795 + 1577316 * 2 ^ 59
def prefixEnd_1577316 : Nat := 4983230072969 + 3 ^ 40 * 1577316 * 2
def baseEnd_1577316 : Nat := 539947501351503985064041

theorem tailTrace_1577316 : CollatzResearch.WordTrace tailWord_1577316 prefixEnd_1577316 539947501351503985064041 := by
  unfold tailWord_1577316
  simp only [CollatzResearch.WordTrace]
  refine ⟨28764720376830495485571901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38352960502440660647429201 28764720376830495485571901)
  ·
    refine ⟨10786770141311435807089463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28764720376830495485571901 10786770141311435807089463)
    ·
      refine ⟨16180155211967153710634195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786770141311435807089463 16180155211967153710634195)
      ·
        refine ⟨24270232817950730565951293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180155211967153710634195 24270232817950730565951293)
        ·
          refine ⟨9101337306731523962231735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24270232817950730565951293 9101337306731523962231735)
          ·
            refine ⟨13652005960097285943347603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9101337306731523962231735 13652005960097285943347603)
            ·
              refine ⟨20478008940145928915021405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13652005960097285943347603 20478008940145928915021405)
              ·
                refine ⟨7679253352554723343133027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20478008940145928915021405 7679253352554723343133027)
                ·
                  refine ⟨11518880028832085014699541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679253352554723343133027 11518880028832085014699541)
                  ·
                    refine ⟨539947501351503985064041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11518880028832085014699541 539947501351503985064041)
                    ·
                      rfl

theorem cell22_1577316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1577316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577316 prefixEnd_1577316 := by exact prefixLift 1577316
  have htrace : WordTrace (prefixWord ++ tailWord_1577316) baseStart_1577316 baseEnd_1577316 := by
    simpa [prefixWord, tailWord_1577316, baseEnd_1577316] using wordTrace_append hprefix tailTrace_1577316
  have hstable : (prefixWord ++ tailWord_1577316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577316).length < 2 ^ (prefixWord ++ tailWord_1577316).sum := by decide
  have hdescent : baseEnd_1577316 < baseStart_1577316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577320 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 4]
def baseStart_1577320 : Nat := 118140960795 + 1577320 * 2 ^ 59
def prefixEnd_1577320 : Nat := 4983230072969 + 3 ^ 40 * 1577320 * 2
def baseEnd_1577320 : Nat := 179982956877749769321343

theorem tailTrace_1577320 : CollatzResearch.WordTrace tailWord_1577320 prefixEnd_1577320 179982956877749769321343 := by
  unfold tailWord_1577320
  simp only [CollatzResearch.WordTrace]
  refine ⟨28764793322823249827144707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38353057763764333102859609 28764793322823249827144707)
  ·
    refine ⟨43147189984234874740717061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28764793322823249827144707 43147189984234874740717061)
    ·
      refine ⟨8090098122044039013884449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43147189984234874740717061 8090098122044039013884449)
      ·
        refine ⟨6067573591533029260413337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8090098122044039013884449 6067573591533029260413337)
        ·
          refine ⟨4550680193649771945310003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6067573591533029260413337 4550680193649771945310003)
          ·
            refine ⟨6826020290474657917965005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550680193649771945310003 6826020290474657917965005)
            ·
              refine ⟨2559757608927996719236877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6826020290474657917965005 2559757608927996719236877)
              ·
                refine ⟨959909103347998769713829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2559757608927996719236877 959909103347998769713829)
                ·
                  refine ⟨179982956877749769321343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959909103347998769713829 179982956877749769321343)
                  ·
                    rfl

theorem cell22_1577320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_1577320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577320 prefixEnd_1577320 := by exact prefixLift 1577320
  have htrace : WordTrace (prefixWord ++ tailWord_1577320) baseStart_1577320 baseEnd_1577320 := by
    simpa [prefixWord, tailWord_1577320, baseEnd_1577320] using wordTrace_append hprefix tailTrace_1577320
  have hstable : (prefixWord ++ tailWord_1577320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577320).length < 2 ^ (prefixWord ++ tailWord_1577320).sum := by decide
  have hdescent : baseEnd_1577320 < baseStart_1577320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577333 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1577333 : Nat := 118140960795 + 1577333 * 2 ^ 59
def prefixEnd_1577333 : Nat := 4983230072969 + 3 ^ 40 * 1577333 * 2
def baseEnd_1577333 : Nat := 539953320798921607388989

theorem tailTrace_1577333 : CollatzResearch.WordTrace tailWord_1577333 prefixEnd_1577333 539953320798921607388989 := by
  unfold tailWord_1577333
  simp only [CollatzResearch.WordTrace]
  refine ⟨57530060794599402874512653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38353373863066268583008435 57530060794599402874512653)
  ·
    refine ⟨21573772797974776077942245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57530060794599402874512653 21573772797974776077942245)
    ·
      refine ⟨4045082399620270514614171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21573772797974776077942245 4045082399620270514614171)
      ·
        refine ⟨6067623599430405771921257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045082399620270514614171 6067623599430405771921257)
        ·
          refine ⟨4550717699572804328940943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6067623599430405771921257 4550717699572804328940943)
          ·
            refine ⟨6826076549359206493411415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550717699572804328940943 6826076549359206493411415)
            ·
              refine ⟨10239114824038809740117123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826076549359206493411415 10239114824038809740117123)
              ·
                refine ⟨15358672236058214610175685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239114824038809740117123 15358672236058214610175685)
                ·
                  refine ⟨2879751044260915239407941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15358672236058214610175685 2879751044260915239407941)
                  ·
                    refine ⟨539953320798921607388989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879751044260915239407941 539953320798921607388989)
                    ·
                      rfl

theorem cell22_1577333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1577333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577333 prefixEnd_1577333 := by exact prefixLift 1577333
  have htrace : WordTrace (prefixWord ++ tailWord_1577333) baseStart_1577333 baseEnd_1577333 := by
    simpa [prefixWord, tailWord_1577333, baseEnd_1577333] using wordTrace_append hprefix tailTrace_1577333
  have hstable : (prefixWord ++ tailWord_1577333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577333).length < 2 ^ (prefixWord ++ tailWord_1577333).sum := by decide
  have hdescent : baseEnd_1577333 < baseStart_1577333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577386 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1577386 : Nat := 118140960795 + 1577386 * 2 ^ 59
def prefixEnd_1577386 : Nat := 4983230072969 + 3 ^ 40 * 1577386 * 2
def baseEnd_1577386 : Nat := 539971463782047135813827

theorem tailTrace_1577386 : CollatzResearch.WordTrace tailWord_1577386 prefixEnd_1577386 539971463782047135813827 := by
  unfold tailWord_1577386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14382998465851848231548003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38354662575604928617461341 14382998465851848231548003)
  ·
    refine ⟨21574497698777772347322005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14382998465851848231548003 21574497698777772347322005)
    ·
      refine ⟨1011304579630208078780719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21574497698777772347322005 1011304579630208078780719)
      ·
        refine ⟨1516956869445312118171079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011304579630208078780719 1516956869445312118171079)
        ·
          refine ⟨2275435304167968177256619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516956869445312118171079 2275435304167968177256619)
          ·
            refine ⟨3413152956251952265884929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275435304167968177256619 3413152956251952265884929)
            ·
              refine ⟨2559864717188964199413697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413152956251952265884929 2559864717188964199413697)
              ·
                refine ⟨1919898537891723149560273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559864717188964199413697 1919898537891723149560273)
                ·
                  refine ⟨1439923903418792362170205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1919898537891723149560273 1439923903418792362170205)
                  ·
                    refine ⟨539971463782047135813827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439923903418792362170205 539971463782047135813827)
                    ·
                      rfl

theorem cell22_1577386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1577386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577386 prefixEnd_1577386 := by exact prefixLift 1577386
  have htrace : WordTrace (prefixWord ++ tailWord_1577386) baseStart_1577386 baseEnd_1577386 := by
    simpa [prefixWord, tailWord_1577386, baseEnd_1577386] using wordTrace_append hprefix tailTrace_1577386
  have hstable : (prefixWord ++ tailWord_1577386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577386).length < 2 ^ (prefixWord ++ tailWord_1577386).sum := by decide
  have hdescent : baseEnd_1577386 < baseStart_1577386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577393 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 5]
def baseStart_1577393 : Nat := 118140960795 + 1577393 * 2 ^ 59
def prefixEnd_1577393 : Nat := 4983230072969 + 3 ^ 40 * 1577393 * 2
def baseEnd_1577393 : Nat := 179991286675033816962935

theorem tailTrace_1577393 : CollatzResearch.WordTrace tailWord_1577393 prefixEnd_1577393 179991286675033816962935 := by
  unfold tailWord_1577393
  simp only [CollatzResearch.WordTrace]
  refine ⟨57532249174382033121696833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38354832782921355414464555 57532249174382033121696833)
  ·
    refine ⟨43149186880786524841272625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57532249174382033121696833 43149186880786524841272625)
    ·
      refine ⟨32361890160589893630954469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43149186880786524841272625 32361890160589893630954469)
      ·
        refine ⟨6067854405110605055803963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32361890160589893630954469 6067854405110605055803963)
        ·
          refine ⟨9101781607665907583705945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067854405110605055803963 9101781607665907583705945)
          ·
            refine ⟨6826336205749430687779459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9101781607665907583705945 6826336205749430687779459)
            ·
              refine ⟨10239504308624146031669189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826336205749430687779459 10239504308624146031669189)
              ·
                refine ⟨1919907057867027380937973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10239504308624146031669189 1919907057867027380937973)
                ·
                  refine ⟨179991286675033816962935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1919907057867027380937973 179991286675033816962935)
                  ·
                    rfl

theorem cell22_1577393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_1577393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577393 prefixEnd_1577393 := by exact prefixLift 1577393
  have htrace : WordTrace (prefixWord ++ tailWord_1577393) baseStart_1577393 baseEnd_1577393 := by
    simpa [prefixWord, tailWord_1577393, baseEnd_1577393] using wordTrace_append hprefix tailTrace_1577393
  have hstable : (prefixWord ++ tailWord_1577393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577393).length < 2 ^ (prefixWord ++ tailWord_1577393).sum := by decide
  have hdescent : baseEnd_1577393 < baseStart_1577393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577423 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 1, 4]
def baseStart_1577423 : Nat := 118140960795 + 1577423 * 2 ^ 59
def prefixEnd_1577423 : Nat := 4983230072969 + 3 ^ 40 * 1577423 * 2
def baseEnd_1577423 : Nat := 539984129638191372638713

theorem tailTrace_1577423 : CollatzResearch.WordTrace tailWord_1577423 prefixEnd_1577423 539984129638191372638713 := by
  unfold tailWord_1577423
  simp only [CollatzResearch.WordTrace]
  refine ⟨57533343364273348245288923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38355562242848898830192615 57533343364273348245288923)
  ·
    refine ⟨86300015046410022367933385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57533343364273348245288923 86300015046410022367933385)
    ·
      refine ⟨64725011284807516775950039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86300015046410022367933385 64725011284807516775950039)
      ·
        refine ⟨97087516927211275163925059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64725011284807516775950039 97087516927211275163925059)
        ·
          refine ⟨145631275390816912745887589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97087516927211275163925059 145631275390816912745887589)
          ·
            refine ⟨27305864135778171139853923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145631275390816912745887589 27305864135778171139853923)
            ·
              refine ⟨40958796203667256709780885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27305864135778171139853923 40958796203667256709780885)
              ·
                refine ⟨1919943572046902658270979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40958796203667256709780885 1919943572046902658270979)
                ·
                  refine ⟨2879915358070353987406469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919943572046902658270979 2879915358070353987406469)
                  ·
                    refine ⟨539984129638191372638713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879915358070353987406469 539984129638191372638713)
                    ·
                      rfl

theorem cell22_1577423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_1577423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577423 prefixEnd_1577423 := by exact prefixLift 1577423
  have htrace : WordTrace (prefixWord ++ tailWord_1577423) baseStart_1577423 baseEnd_1577423 := by
    simpa [prefixWord, tailWord_1577423, baseEnd_1577423] using wordTrace_append hprefix tailTrace_1577423
  have hstable : (prefixWord ++ tailWord_1577423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577423).length < 2 ^ (prefixWord ++ tailWord_1577423).sum := by decide
  have hdescent : baseEnd_1577423 < baseStart_1577423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577474 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1577474 : Nat := 118140960795 + 1577474 * 2 ^ 59
def prefixEnd_1577474 : Nat := 4983230072969 + 3 ^ 40 * 1577474 * 2
def baseEnd_1577474 : Nat := 540001587980444239613557

theorem tailTrace_1577474 : CollatzResearch.WordTrace tailWord_1577474 prefixEnd_1577474 540001587980444239613557 := by
  unfold tailWord_1577474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383800871772145988848869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38356802324725722636930317 14383800871772145988848869)
  ·
    refine ⟨2696962663457277372909163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14383800871772145988848869 2696962663457277372909163)
    ·
      refine ⟨4045443995185916059363745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2696962663457277372909163 4045443995185916059363745)
      ·
        refine ⟨3034082996389437044522809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4045443995185916059363745 3034082996389437044522809)
        ·
          refine ⟨2275562247292077783392107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3034082996389437044522809 2275562247292077783392107)
          ·
            refine ⟨3413343370938116675088161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275562247292077783392107 3413343370938116675088161)
            ·
              refine ⟨2560007528203587506316121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413343370938116675088161 2560007528203587506316121)
              ·
                refine ⟨1920005646152690629737091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560007528203587506316121 1920005646152690629737091)
                ·
                  refine ⟨2880008469229035944605637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920005646152690629737091 2880008469229035944605637)
                  ·
                    refine ⟨540001587980444239613557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880008469229035944605637 540001587980444239613557)
                    ·
                      rfl

theorem cell22_1577474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1577474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577474 prefixEnd_1577474 := by exact prefixLift 1577474
  have htrace : WordTrace (prefixWord ++ tailWord_1577474) baseStart_1577474 baseEnd_1577474 := by
    simpa [prefixWord, tailWord_1577474, baseEnd_1577474] using wordTrace_append hprefix tailTrace_1577474
  have hstable : (prefixWord ++ tailWord_1577474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577474).length < 2 ^ (prefixWord ++ tailWord_1577474).sum := by decide
  have hdescent : baseEnd_1577474 < baseStart_1577474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577483 : List Nat := [1, 1, 1, 1, 7, 2, 1, 8]
def baseStart_1577483 : Nat := 118140960795 + 1577483 * 2 ^ 59
def prefixEnd_1577483 : Nat := 4983230072969 + 3 ^ 40 * 1577483 * 2
def baseEnd_1577483 : Nat := 60000518762707912904281

theorem tailTrace_1577483 : CollatzResearch.WordTrace tailWord_1577483 prefixEnd_1577483 60000518762707912904281 := by
  unfold tailWord_1577483
  simp only [CollatzResearch.WordTrace]
  refine ⟨57535531744055978492473103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38357021162703985661648735 57535531744055978492473103)
  ·
    refine ⟨86303297616083967738709655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57535531744055978492473103 86303297616083967738709655)
    ·
      refine ⟨129454946424125951608064483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86303297616083967738709655 129454946424125951608064483)
      ·
        refine ⟨194182419636188927412096725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129454946424125951608064483 194182419636188927412096725)
        ·
          refine ⟨4551150460223177986221017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194182419636188927412096725 4551150460223177986221017)
          ·
            refine ⟨3413362845167383489665763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551150460223177986221017 3413362845167383489665763)
            ·
              refine ⟨5120044267751075234498645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413362845167383489665763 5120044267751075234498645)
              ·
                refine ⟨60000518762707912904281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5120044267751075234498645 60000518762707912904281)
                ·
                  rfl

theorem cell22_1577483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 8].length) (baseStart_1577483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577483 prefixEnd_1577483 := by exact prefixLift 1577483
  have htrace : WordTrace (prefixWord ++ tailWord_1577483) baseStart_1577483 baseEnd_1577483 := by
    simpa [prefixWord, tailWord_1577483, baseEnd_1577483] using wordTrace_append hprefix tailTrace_1577483
  have hstable : (prefixWord ++ tailWord_1577483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577483).length < 2 ^ (prefixWord ++ tailWord_1577483).sum := by decide
  have hdescent : baseEnd_1577483 < baseStart_1577483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577605 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_1577605 : Nat := 118140960795 + 1577605 * 2 ^ 59
def prefixEnd_1577605 : Nat := 4983230072969 + 3 ^ 40 * 1577605 * 2
def baseEnd_1577605 : Nat := 540046431957603564588155

theorem tailTrace_1577605 : CollatzResearch.WordTrace tailWord_1577605 prefixEnd_1577605 540046431957603564588155 := by
  unfold tailWord_1577605
  simp only [CollatzResearch.WordTrace]
  refine ⟨57539981449613993328414269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38359987633075995552276179 57539981449613993328414269)
  ·
    refine ⟨21577493043605247498155351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57539981449613993328414269 21577493043605247498155351)
    ·
      refine ⟨32366239565407871247233027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21577493043605247498155351 32366239565407871247233027)
      ·
        refine ⟨48549359348111806870849541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32366239565407871247233027 48549359348111806870849541)
        ·
          refine ⟨9103004877770963788284289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48549359348111806870849541 9103004877770963788284289)
          ·
            refine ⟨6827253658328222841213217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9103004877770963788284289 6827253658328222841213217)
            ·
              refine ⟨5120440243746167130909913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6827253658328222841213217 5120440243746167130909913)
              ·
                refine ⟨3840330182809625348182435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5120440243746167130909913 3840330182809625348182435)
                ·
                  refine ⟨5760495274214438022273653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840330182809625348182435 5760495274214438022273653)
                  ·
                    refine ⟨540046431957603564588155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5760495274214438022273653 540046431957603564588155)
                    ·
                      rfl

theorem cell22_1577605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_1577605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577605 prefixEnd_1577605 := by exact prefixLift 1577605
  have htrace : WordTrace (prefixWord ++ tailWord_1577605) baseStart_1577605 baseEnd_1577605 := by
    simpa [prefixWord, tailWord_1577605, baseEnd_1577605] using wordTrace_append hprefix tailTrace_1577605
  have hstable : (prefixWord ++ tailWord_1577605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577605).length < 2 ^ (prefixWord ++ tailWord_1577605).sum := by decide
  have hdescent : baseEnd_1577605 < baseStart_1577605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577607 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 4]
def baseStart_1577607 : Nat := 118140960795 + 1577607 * 2 ^ 59
def prefixEnd_1577607 : Nat := 4983230072969 + 3 ^ 40 * 1577607 * 2
def baseEnd_1577607 : Nat := 180015705532825408679383

theorem tailTrace_1577607 : CollatzResearch.WordTrace tailWord_1577607 prefixEnd_1577607 180015705532825408679383 := by
  unfold tailWord_1577607
  simp only [CollatzResearch.WordTrace]
  refine ⟨57540054395606747669987075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38360036263737831779991383 57540054395606747669987075)
  ·
    refine ⟨86310081593410121504980613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57540054395606747669987075 86310081593410121504980613)
    ·
      refine ⟨16183140298764397782183865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86310081593410121504980613 16183140298764397782183865)
      ·
        refine ⟨12137355224073298336637899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16183140298764397782183865 12137355224073298336637899)
        ·
          refine ⟨18206032836109947504956849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12137355224073298336637899 18206032836109947504956849)
          ·
            refine ⟨13654524627082460628717637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18206032836109947504956849 13654524627082460628717637)
            ·
              refine ⟨2560223367577961367884557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13654524627082460628717637 2560223367577961367884557)
              ·
                refine ⟨960083762841735512956709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2560223367577961367884557 960083762841735512956709)
                ·
                  refine ⟨180015705532825408679383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960083762841735512956709 180015705532825408679383)
                  ·
                    rfl

theorem cell22_1577607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 4].length) (baseStart_1577607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577607 prefixEnd_1577607 := by exact prefixLift 1577607
  have htrace : WordTrace (prefixWord ++ tailWord_1577607) baseStart_1577607 baseEnd_1577607 := by
    simpa [prefixWord, tailWord_1577607, baseEnd_1577607] using wordTrace_append hprefix tailTrace_1577607
  have hstable : (prefixWord ++ tailWord_1577607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577607).length < 2 ^ (prefixWord ++ tailWord_1577607).sum := by decide
  have hdescent : baseEnd_1577607 < baseStart_1577607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577697 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 5]
def baseStart_1577697 : Nat := 118140960795 + 1577697 * 2 ^ 59
def prefixEnd_1577697 : Nat := 4983230072969 + 3 ^ 40 * 1577697 * 2
def baseEnd_1577697 : Nat := 180025975145915330429291

theorem tailTrace_1577697 : CollatzResearch.WordTrace tailWord_1577697 prefixEnd_1577697 180025975145915330429291 := by
  unfold tailWord_1577697
  simp only [CollatzResearch.WordTrace]
  refine ⟨57543336965280693040763345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38362224643520462027175563 57543336965280693040763345)
  ·
    refine ⟨43157502723960519780572509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57543336965280693040763345 43157502723960519780572509)
    ·
      refine ⟨16184063521485194917714691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43157502723960519780572509 16184063521485194917714691)
      ·
        refine ⟨24276095282227792376572037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16184063521485194917714691 24276095282227792376572037)
        ·
          refine ⟨4551767865417711070607257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24276095282227792376572037 4551767865417711070607257)
          ·
            refine ⟨3413825899063283302955443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551767865417711070607257 3413825899063283302955443)
            ·
              refine ⟨5120738848594924954433165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413825899063283302955443 5120738848594924954433165)
              ·
                refine ⟨1920277068223096857912437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5120738848594924954433165 1920277068223096857912437)
                ·
                  refine ⟨180025975145915330429291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1920277068223096857912437 180025975145915330429291)
                  ·
                    rfl

theorem cell22_1577697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_1577697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577697 prefixEnd_1577697 := by exact prefixLift 1577697
  have htrace : WordTrace (prefixWord ++ tailWord_1577697) baseStart_1577697 baseEnd_1577697 := by
    simpa [prefixWord, tailWord_1577697, baseEnd_1577697] using wordTrace_append hprefix tailTrace_1577697
  have hstable : (prefixWord ++ tailWord_1577697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577697).length < 2 ^ (prefixWord ++ tailWord_1577697).sum := by decide
  have hdescent : baseEnd_1577697 < baseStart_1577697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577740 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1577740 : Nat := 118140960795 + 1577740 * 2 ^ 59
def prefixEnd_1577740 : Nat := 4983230072969 + 3 ^ 40 * 1577740 * 2
def baseEnd_1577740 : Nat := 540092645216508212462741

theorem tailTrace_1577740 : CollatzResearch.WordTrace tailWord_1577740 prefixEnd_1577740 540092645216508212462741 := by
  unfold tailWord_1577740
  simp only [CollatzResearch.WordTrace]
  refine ⟨28772452652062455692289337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38363270202749940923052449 28772452652062455692289337)
  ·
    refine ⟨21579339489046841769217003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28772452652062455692289337 21579339489046841769217003)
    ·
      refine ⟨32369009233570262653825505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21579339489046841769217003 32369009233570262653825505)
      ·
        refine ⟨24276756925177696990369129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32369009233570262653825505 24276756925177696990369129)
        ·
          refine ⟨18207567693883272742776847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24276756925177696990369129 18207567693883272742776847)
          ·
            refine ⟨27311351540824909114165271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18207567693883272742776847 27311351540824909114165271)
            ·
              refine ⟨40967027311237363671247907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27311351540824909114165271 40967027311237363671247907)
              ·
                refine ⟨61450540966856045506871861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40967027311237363671247907 61450540966856045506871861)
                ·
                  refine ⟨5760988215642754266269237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61450540966856045506871861 5760988215642754266269237)
                  ·
                    refine ⟨540092645216508212462741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5760988215642754266269237 540092645216508212462741)
                    ·
                      rfl

theorem cell22_1577740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1577740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577740 prefixEnd_1577740 := by exact prefixLift 1577740
  have htrace : WordTrace (prefixWord ++ tailWord_1577740) baseStart_1577740 baseEnd_1577740 := by
    simpa [prefixWord, tailWord_1577740, baseEnd_1577740] using wordTrace_append hprefix tailTrace_1577740
  have hstable : (prefixWord ++ tailWord_1577740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577740).length < 2 ^ (prefixWord ++ tailWord_1577740).sum := by decide
  have hdescent : baseEnd_1577740 < baseStart_1577740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577774 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1577774 : Nat := 118140960795 + 1577774 * 2 ^ 59
def prefixEnd_1577774 : Nat := 4983230072969 + 3 ^ 40 * 1577774 * 2
def baseEnd_1577774 : Nat := 540104284111343457112637

theorem tailTrace_1577774 : CollatzResearch.WordTrace tailWord_1577774 prefixEnd_1577774 540104284111343457112637 := by
  unfold tailWord_1577774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193268173250216898914547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38364096924001156794210917 7193268173250216898914547)
  ·
    refine ⟨10789902259875325348371821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7193268173250216898914547 10789902259875325348371821)
    ·
      refine ⟨4046213347453247005639433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10789902259875325348371821 4046213347453247005639433)
      ·
        refine ⟨3034660010589935254229575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4046213347453247005639433 3034660010589935254229575)
        ·
          refine ⟨4551990015884902881344363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034660010589935254229575 4551990015884902881344363)
          ·
            refine ⟨6827985023827354322016545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551990015884902881344363 6827985023827354322016545)
            ·
              refine ⟨5120988767870515741512409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6827985023827354322016545 5120988767870515741512409)
              ·
                refine ⟨3840741575902886806134307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5120988767870515741512409 3840741575902886806134307)
                ·
                  refine ⟨5761112363854330209201461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840741575902886806134307 5761112363854330209201461)
                  ·
                    refine ⟨540104284111343457112637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5761112363854330209201461 540104284111343457112637)
                    ·
                      rfl

theorem cell22_1577774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1577774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577774 prefixEnd_1577774 := by exact prefixLift 1577774
  have htrace : WordTrace (prefixWord ++ tailWord_1577774) baseStart_1577774 baseEnd_1577774 := by
    simpa [prefixWord, tailWord_1577774, baseEnd_1577774] using wordTrace_append hprefix tailTrace_1577774
  have hstable : (prefixWord ++ tailWord_1577774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577774).length < 2 ^ (prefixWord ++ tailWord_1577774).sum := by decide
  have hdescent : baseEnd_1577774 < baseStart_1577774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577791 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 2, 3]
def baseStart_1577791 : Nat := 118140960795 + 1577791 * 2 ^ 59
def prefixEnd_1577791 : Nat := 4983230072969 + 3 ^ 40 * 1577791 * 2
def baseEnd_1577791 : Nat := 540110103558761079437585

theorem tailTrace_1577791 : CollatzResearch.WordTrace tailWord_1577791 prefixEnd_1577791 540110103558761079437585 := by
  unfold tailWord_1577791
  simp only [CollatzResearch.WordTrace]
  refine ⟨57546765426940147094685227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38364510284626764729790151 57546765426940147094685227)
  ·
    refine ⟨86320148140410220642027841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57546765426940147094685227 86320148140410220642027841)
    ·
      refine ⟨64740111105307665481520881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86320148140410220642027841 64740111105307665481520881)
      ·
        refine ⟨48555083328980749111140661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64740111105307665481520881 48555083328980749111140661)
        ·
          refine ⟨4552039062091945229169437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48555083328980749111140661 4552039062091945229169437)
          ·
            refine ⟨1707014648284479460938539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552039062091945229169437 1707014648284479460938539)
            ·
              refine ⟨2560521972426719191407809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707014648284479460938539 2560521972426719191407809)
              ·
                refine ⟨1920391479320039393555857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560521972426719191407809 1920391479320039393555857)
                ·
                  refine ⟨1440293609490029545166893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1920391479320039393555857 1440293609490029545166893)
                  ·
                    refine ⟨540110103558761079437585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440293609490029545166893 540110103558761079437585)
                    ·
                      rfl

theorem cell22_1577791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_1577791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577791 prefixEnd_1577791 := by exact prefixLift 1577791
  have htrace : WordTrace (prefixWord ++ tailWord_1577791) baseStart_1577791 baseEnd_1577791 := by
    simpa [prefixWord, tailWord_1577791, baseEnd_1577791] using wordTrace_append hprefix tailTrace_1577791
  have hstable : (prefixWord ++ tailWord_1577791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577791).length < 2 ^ (prefixWord ++ tailWord_1577791).sum := by decide
  have hdescent : baseEnd_1577791 < baseStart_1577791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577832 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_1577832 : Nat := 118140960795 + 1577832 * 2 ^ 59
def prefixEnd_1577832 : Nat := 4983230072969 + 3 ^ 40 * 1577832 * 2
def baseEnd_1577832 : Nat := 180041379565550213054153

theorem tailTrace_1577832 : CollatzResearch.WordTrace tailWord_1577832 prefixEnd_1577832 180041379565550213054153 := by
  unfold tailWord_1577832
  simp only [CollatzResearch.WordTrace]
  refine ⟨28774130409895805548463875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38365507213194407397951833 28774130409895805548463875)
  ·
    refine ⟨43161195614843708322695813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28774130409895805548463875 43161195614843708322695813)
    ·
      refine ⟨8092724177783195310505465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43161195614843708322695813 8092724177783195310505465)
      ·
        refine ⟨6069543133337396482879099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8092724177783195310505465 6069543133337396482879099)
        ·
          refine ⟨9104314700006094724318649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6069543133337396482879099 9104314700006094724318649)
          ·
            refine ⟨6828236025004571043238987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9104314700006094724318649 6828236025004571043238987)
            ·
              refine ⟨10242354037506856564858481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828236025004571043238987 10242354037506856564858481)
              ·
                refine ⟨7681765528130142423643861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10242354037506856564858481 7681765528130142423643861)
                ·
                  refine ⟨180041379565550213054153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7681765528130142423643861 180041379565550213054153)
                  ·
                    rfl

theorem cell22_1577832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_1577832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577832 prefixEnd_1577832 := by exact prefixLift 1577832
  have htrace : WordTrace (prefixWord ++ tailWord_1577832) baseStart_1577832 baseEnd_1577832 := by
    simpa [prefixWord, tailWord_1577832, baseEnd_1577832] using wordTrace_append hprefix tailTrace_1577832
  have hstable : (prefixWord ++ tailWord_1577832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577832).length < 2 ^ (prefixWord ++ tailWord_1577832).sum := by decide
  have hdescent : baseEnd_1577832 < baseStart_1577832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577866 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_1577866 : Nat := 118140960795 + 1577866 * 2 ^ 59
def prefixEnd_1577866 : Nat := 4983230072969 + 3 ^ 40 * 1577866 * 2
def baseEnd_1577866 : Nat := 180045259197161961270785

theorem tailTrace_1577866 : CollatzResearch.WordTrace tailWord_1577866 prefixEnd_1577866 180045259197161961270785 := by
  unfold tailWord_1577866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14387375225417108725916363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38366333934445623269110301 14387375225417108725916363)
  ·
    refine ⟨21581062838125663088874545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14387375225417108725916363 21581062838125663088874545)
    ·
      refine ⟨16185797128594247316655909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21581062838125663088874545 16185797128594247316655909)
      ·
        refine ⟨3034836961611421371872983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16185797128594247316655909 3034836961611421371872983)
        ·
          refine ⟨4552255442417132057809475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034836961611421371872983 4552255442417132057809475)
          ·
            refine ⟨6828383163625698086714213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552255442417132057809475 6828383163625698086714213)
            ·
              refine ⟨1280321843179818391258915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6828383163625698086714213 1280321843179818391258915)
              ·
                refine ⟨1920482764769727586888373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280321843179818391258915 1920482764769727586888373)
                ·
                  refine ⟨180045259197161961270785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1920482764769727586888373 180045259197161961270785)
                  ·
                    rfl

theorem cell22_1577866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_1577866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577866 prefixEnd_1577866 := by exact prefixLift 1577866
  have htrace : WordTrace (prefixWord ++ tailWord_1577866) baseStart_1577866 baseEnd_1577866 := by
    simpa [prefixWord, tailWord_1577866, baseEnd_1577866] using wordTrace_append hprefix tailTrace_1577866
  have hstable : (prefixWord ++ tailWord_1577866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577866).length < 2 ^ (prefixWord ++ tailWord_1577866).sum := by decide
  have hdescent : baseEnd_1577866 < baseStart_1577866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577907 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 4, 4]
def baseStart_1577907 : Nat := 118140960795 + 1577907 * 2 ^ 59
def prefixEnd_1577907 : Nat := 4983230072969 + 3 ^ 40 * 1577907 * 2
def baseEnd_1577907 : Nat := 540149812729375443537229

theorem tailTrace_1577907 : CollatzResearch.WordTrace tailWord_1577907 prefixEnd_1577907 540149812729375443537229 := by
  unfold tailWord_1577907
  simp only [CollatzResearch.WordTrace]
  refine ⟨57550996294519898905907975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38367330863013265937271983 57550996294519898905907975)
  ·
    refine ⟨86326494441779848358861963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57550996294519898905907975 86326494441779848358861963)
    ·
      refine ⟨129489741662669772538292945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86326494441779848358861963 129489741662669772538292945)
      ·
        refine ⟨97117306247002329403719709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129489741662669772538292945 97117306247002329403719709)
        ·
          refine ⟨36418989842625873526394891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97117306247002329403719709 36418989842625873526394891)
          ·
            refine ⟨54628484763938810289592337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36418989842625873526394891 54628484763938810289592337)
            ·
              refine ⟨40971363572954107717194253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54628484763938810289592337 40971363572954107717194253)
              ·
                refine ⟨15364261339857790393947845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40971363572954107717194253 15364261339857790393947845)
                ·
                  refine ⟨2880799001223335698865221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15364261339857790393947845 2880799001223335698865221)
                  ·
                    refine ⟨540149812729375443537229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880799001223335698865221 540149812729375443537229)
                    ·
                      rfl

theorem cell22_1577907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_1577907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577907 prefixEnd_1577907 := by exact prefixLift 1577907
  have htrace : WordTrace (prefixWord ++ tailWord_1577907) baseStart_1577907 baseEnd_1577907 := by
    simpa [prefixWord, tailWord_1577907, baseEnd_1577907] using wordTrace_append hprefix tailTrace_1577907
  have hstable : (prefixWord ++ tailWord_1577907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577907).length < 2 ^ (prefixWord ++ tailWord_1577907).sum := by decide
  have hdescent : baseEnd_1577907 < baseStart_1577907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577911 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 4]
def baseStart_1577911 : Nat := 118140960795 + 1577911 * 2 ^ 59
def prefixEnd_1577911 : Nat := 4983230072969 + 3 ^ 40 * 1577911 * 2
def baseEnd_1577911 : Nat := 180050394003706922145739

theorem tailTrace_1577911 : CollatzResearch.WordTrace tailWord_1577911 prefixEnd_1577911 180050394003706922145739 := by
  unfold tailWord_1577911
  simp only [CollatzResearch.WordTrace]
  refine ⟨57551142186505407589053587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38367428124336938392702391 57551142186505407589053587)
  ·
    refine ⟨86326713279758111383580381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57551142186505407589053587 86326713279758111383580381)
    ·
      refine ⟨32372517479909291768842643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86326713279758111383580381 32372517479909291768842643)
      ·
        refine ⟨48558776219863937653263965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32372517479909291768842643 48558776219863937653263965)
        ·
          refine ⟨18209541082448976619973987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48558776219863937653263965 18209541082448976619973987)
          ·
            refine ⟨27314311623673464929960981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18209541082448976619973987 27314311623673464929960981)
            ·
              refine ⟨1280358357359693668591921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27314311623673464929960981 1280358357359693668591921)
              ·
                refine ⟨960268768019770251443941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280358357359693668591921 960268768019770251443941)
                ·
                  refine ⟨180050394003706922145739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960268768019770251443941 180050394003706922145739)
                  ·
                    rfl

theorem cell22_1577911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 4].length) (baseStart_1577911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1577911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1577911 prefixEnd_1577911 := by exact prefixLift 1577911
  have htrace : WordTrace (prefixWord ++ tailWord_1577911) baseStart_1577911 baseEnd_1577911 := by
    simpa [prefixWord, tailWord_1577911, baseEnd_1577911] using wordTrace_append hprefix tailTrace_1577911
  have hstable : (prefixWord ++ tailWord_1577911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577911).length < 2 ^ (prefixWord ++ tailWord_1577911).sum := by decide
  have hdescent : baseEnd_1577911 < baseStart_1577911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578005 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_1578005 : Nat := 118140960795 + 1578005 * 2 ^ 59
def prefixEnd_1578005 : Nat := 4983230072969 + 3 ^ 40 * 1578005 * 2
def baseEnd_1578005 : Nat := 540183360132135854586929

theorem tailTrace_1578005 : CollatzResearch.WordTrace tailWord_1578005 prefixEnd_1578005 540183360132135854586929 := by
  unfold tailWord_1578005
  simp only [CollatzResearch.WordTrace]
  refine ⟨57554570648164861642975469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38369713765443241095316979 57554570648164861642975469)
  ·
    refine ⟨21582963993061823116115801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57554570648164861642975469 21582963993061823116115801)
    ·
      refine ⟨16187222994796367337086851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21582963993061823116115801 16187222994796367337086851)
      ·
        refine ⟨24280834492194551005630277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16187222994796367337086851 24280834492194551005630277)
        ·
          refine ⟨4552656467286478313555677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24280834492194551005630277 4552656467286478313555677)
          ·
            refine ⟨1707246175232429367583379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552656467286478313555677 1707246175232429367583379)
            ·
              refine ⟨2560869262848644051375069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707246175232429367583379 2560869262848644051375069)
              ·
                refine ⟨960325973568241519265651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2560869262848644051375069 960325973568241519265651)
                ·
                  refine ⟨1440488960352362278898477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960325973568241519265651 1440488960352362278898477)
                  ·
                    refine ⟨540183360132135854586929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440488960352362278898477 540183360132135854586929)
                    ·
                      rfl

theorem cell22_1578005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_1578005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578005 prefixEnd_1578005 := by exact prefixLift 1578005
  have htrace : WordTrace (prefixWord ++ tailWord_1578005) baseStart_1578005 baseEnd_1578005 := by
    simpa [prefixWord, tailWord_1578005, baseEnd_1578005] using wordTrace_append hprefix tailTrace_1578005
  have hstable : (prefixWord ++ tailWord_1578005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578005).length < 2 ^ (prefixWord ++ tailWord_1578005).sum := by decide
  have hdescent : baseEnd_1578005 < baseStart_1578005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578061 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1578061 : Nat := 118140960795 + 1578061 * 2 ^ 59
def prefixEnd_1578061 : Nat := 4983230072969 + 3 ^ 40 * 1578061 * 2
def baseEnd_1578061 : Nat := 540202530076570375186757

theorem tailTrace_1578061 : CollatzResearch.WordTrace tailWord_1578061 prefixEnd_1578061 540202530076570375186757 := by
  unfold tailWord_1578061
  simp only [CollatzResearch.WordTrace]
  refine ⟨57556613135961983207014037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38371075423974655471342691 57556613135961983207014037)
  ·
    refine ⟨2697966240748217962828783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57556613135961983207014037 2697966240748217962828783)
    ·
      refine ⟨4046949361122326944243175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2697966240748217962828783 4046949361122326944243175)
      ·
        refine ⟨6070424041683490416364763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046949361122326944243175 6070424041683490416364763)
        ·
          refine ⟨9105636062525235624547145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070424041683490416364763 9105636062525235624547145)
          ·
            refine ⟨6829227046893926718410359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9105636062525235624547145 6829227046893926718410359)
            ·
              refine ⟨10243840570340890077615539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829227046893926718410359 10243840570340890077615539)
              ·
                refine ⟨15365760855511335116423309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10243840570340890077615539 15365760855511335116423309)
                ·
                  refine ⟨5762160320816750668658741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15365760855511335116423309 5762160320816750668658741)
                  ·
                    refine ⟨540202530076570375186757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5762160320816750668658741 540202530076570375186757)
                    ·
                      rfl

theorem cell22_1578061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1578061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578061 prefixEnd_1578061 := by exact prefixLift 1578061
  have htrace : WordTrace (prefixWord ++ tailWord_1578061) baseStart_1578061 baseEnd_1578061 := by
    simpa [prefixWord, tailWord_1578061, baseEnd_1578061] using wordTrace_append hprefix tailTrace_1578061
  have hstable : (prefixWord ++ tailWord_1578061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578061).length < 2 ^ (prefixWord ++ tailWord_1578061).sum := by decide
  have hdescent : baseEnd_1578061 < baseStart_1578061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578076 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1578076 : Nat := 118140960795 + 1578076 * 2 ^ 59
def prefixEnd_1578076 : Nat := 4983230072969 + 3 ^ 40 * 1578076 * 2
def baseEnd_1578076 : Nat := 540207664883115336061711

theorem tailTrace_1578076 : CollatzResearch.WordTrace tailWord_1578076 prefixEnd_1578076 540207664883115336061711 := by
  unfold tailWord_1578076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28778580115453820384405041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38371440153938427179206721 28778580115453820384405041)
  ·
    refine ⟨21583935086590365288303781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28778580115453820384405041 21583935086590365288303781)
    ·
      refine ⟨4046987828735693491556959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21583935086590365288303781 4046987828735693491556959)
      ·
        refine ⟨6070481743103540237335439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046987828735693491556959 6070481743103540237335439)
        ·
          refine ⟨9105722614655310356003159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070481743103540237335439 9105722614655310356003159)
          ·
            refine ⟨13658583921982965534004739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105722614655310356003159 13658583921982965534004739)
            ·
              refine ⟨20487875882974448301007109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13658583921982965534004739 20487875882974448301007109)
              ·
                refine ⟨3841476728057709056438833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20487875882974448301007109 3841476728057709056438833)
                ·
                  refine ⟨2881107546043281792329125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841476728057709056438833 2881107546043281792329125)
                  ·
                    refine ⟨540207664883115336061711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2881107546043281792329125 540207664883115336061711)
                    ·
                      rfl

theorem cell22_1578076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1578076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578076 prefixEnd_1578076 := by exact prefixLift 1578076
  have htrace : WordTrace (prefixWord ++ tailWord_1578076) baseStart_1578076 baseEnd_1578076 := by
    simpa [prefixWord, tailWord_1578076, baseEnd_1578076] using wordTrace_append hprefix tailTrace_1578076
  have hstable : (prefixWord ++ tailWord_1578076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578076).length < 2 ^ (prefixWord ++ tailWord_1578076).sum := by decide
  have hdescent : baseEnd_1578076 < baseStart_1578076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578119 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 7]
def baseStart_1578119 : Nat := 118140960795 + 1578119 * 2 ^ 59
def prefixEnd_1578119 : Nat := 4983230072969 + 3 ^ 40 * 1578119 * 2
def baseEnd_1578119 : Nat := 180074128220625852412193

theorem tailTrace_1578119 : CollatzResearch.WordTrace tailWord_1578119 prefixEnd_1578119 180074128220625852412193 := by
  unfold tailWord_1578119
  simp only [CollatzResearch.WordTrace]
  refine ⟨57558728569751859112625411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38372485713167906075083607 57558728569751859112625411)
  ·
    refine ⟨86338092854627788668938117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57558728569751859112625411 86338092854627788668938117)
    ·
      refine ⟨16188392410242710375425897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86338092854627788668938117 16188392410242710375425897)
      ·
        refine ⟨12141294307682032781569423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16188392410242710375425897 12141294307682032781569423)
        ·
          refine ⟨18211941461523049172354135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12141294307682032781569423 18211941461523049172354135)
          ·
            refine ⟨27317912192284573758531203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18211941461523049172354135 27317912192284573758531203)
            ·
              refine ⟨40976868288426860637796805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27317912192284573758531203 40976868288426860637796805)
              ·
                refine ⟨7683162804080036369586901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40976868288426860637796805 7683162804080036369586901)
                ·
                  refine ⟨180074128220625852412193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7683162804080036369586901 180074128220625852412193)
                  ·
                    rfl

theorem cell22_1578119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_1578119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578119 prefixEnd_1578119 := by exact prefixLift 1578119
  have htrace : WordTrace (prefixWord ++ tailWord_1578119) baseStart_1578119 baseEnd_1578119 := by
    simpa [prefixWord, tailWord_1578119, baseEnd_1578119] using wordTrace_append hprefix tailTrace_1578119
  have hstable : (prefixWord ++ tailWord_1578119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578119).length < 2 ^ (prefixWord ++ tailWord_1578119).sum := by decide
  have hdescent : baseEnd_1578119 < baseStart_1578119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578136 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_1578136 : Nat := 118140960795 + 1578136 * 2 ^ 59
def prefixEnd_1578136 : Nat := 4983230072969 + 3 ^ 40 * 1578136 * 2
def baseEnd_1578136 : Nat := 180076068036431726520509

theorem tailTrace_1578136 : CollatzResearch.WordTrace tailWord_1578136 prefixEnd_1578136 180076068036431726520509 := by
  unfold tailWord_1578136
  simp only [CollatzResearch.WordTrace]
  refine ⟨28779674305345135507997131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38372899073793514010662841 28779674305345135507997131)
  ·
    refine ⟨43169511458017703261995697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28779674305345135507997131 43169511458017703261995697)
    ·
      refine ⟨32377133593513277446496773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43169511458017703261995697 32377133593513277446496773)
      ·
        refine ⟨6070712548783739521218145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32377133593513277446496773 6070712548783739521218145)
        ·
          refine ⟨4553034411587804640913609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6070712548783739521218145 4553034411587804640913609)
          ·
            refine ⟨3414775808690853480685207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4553034411587804640913609 3414775808690853480685207)
            ·
              refine ⟨5122163713036280221027811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414775808690853480685207 5122163713036280221027811)
              ·
                refine ⟨7683245569554420331541717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122163713036280221027811 7683245569554420331541717)
                ·
                  refine ⟨180076068036431726520509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7683245569554420331541717 180076068036431726520509)
                  ·
                    rfl

theorem cell22_1578136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_1578136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578136 prefixEnd_1578136 := by exact prefixLift 1578136
  have htrace : WordTrace (prefixWord ++ tailWord_1578136) baseStart_1578136 baseEnd_1578136 := by
    simpa [prefixWord, tailWord_1578136, baseEnd_1578136] using wordTrace_append hprefix tailTrace_1578136
  have hstable : (prefixWord ++ tailWord_1578136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578136).length < 2 ^ (prefixWord ++ tailWord_1578136).sum := by decide
  have hdescent : baseEnd_1578136 < baseStart_1578136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578140 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1578140 : Nat := 118140960795 + 1578140 * 2 ^ 59
def prefixEnd_1578140 : Nat := 4983230072969 + 3 ^ 40 * 1578140 * 2
def baseEnd_1578140 : Nat := 540229573391040502461515

theorem tailTrace_1578140 : CollatzResearch.WordTrace tailWord_1578140 prefixEnd_1578140 540229573391040502461515 := by
  unfold tailWord_1578140
  simp only [CollatzResearch.WordTrace]
  refine ⟨28779747251337889849569937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38372996335117186466093249 28779747251337889849569937)
  ·
    refine ⟨21584810438503417387177453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28779747251337889849569937 21584810438503417387177453)
    ·
      refine ⟨8094303914438781520191545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21584810438503417387177453 8094303914438781520191545)
      ·
        refine ⟨6070727935829086140143659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8094303914438781520191545 6070727935829086140143659)
        ·
          refine ⟨9106091903743629210215489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070727935829086140143659 9106091903743629210215489)
          ·
            refine ⟨6829568927807721907661617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9106091903743629210215489 6829568927807721907661617)
            ·
              refine ⟨5122176695855791430746213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829568927807721907661617 5122176695855791430746213)
              ·
                refine ⟨960408130472960893264915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5122176695855791430746213 960408130472960893264915)
                ·
                  refine ⟨1440612195709441339897373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960408130472960893264915 1440612195709441339897373)
                  ·
                    refine ⟨540229573391040502461515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440612195709441339897373 540229573391040502461515)
                    ·
                      rfl

theorem cell22_1578140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1578140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578140 prefixEnd_1578140 := by exact prefixLift 1578140
  have htrace : WordTrace (prefixWord ++ tailWord_1578140) baseStart_1578140 baseEnd_1578140 := by
    simpa [prefixWord, tailWord_1578140, baseEnd_1578140] using wordTrace_append hprefix tailTrace_1578140
  have hstable : (prefixWord ++ tailWord_1578140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578140).length < 2 ^ (prefixWord ++ tailWord_1578140).sum := by decide
  have hdescent : baseEnd_1578140 < baseStart_1578140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578305 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 5]
def baseStart_1578305 : Nat := 118140960795 + 1578305 * 2 ^ 59
def prefixEnd_1578305 : Nat := 4983230072969 + 3 ^ 40 * 1578305 * 2
def baseEnd_1578305 : Nat := 180095352087678357362003

theorem tailTrace_1578305 : CollatzResearch.WordTrace tailWord_1578305 prefixEnd_1578305 180095352087678357362003 := by
  unfold tailWord_1578305
  simp only [CollatzResearch.WordTrace]
  refine ⟨57565512547078012878896369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38377008364718675252597579 57565512547078012878896369)
  ·
    refine ⟨43174134410308509659172277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57565512547078012878896369 43174134410308509659172277)
    ·
      refine ⟨4047575100966422780547401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43174134410308509659172277 4047575100966422780547401)
      ·
        refine ⟨3035681325724817085410551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047575100966422780547401 3035681325724817085410551)
        ·
          refine ⟨4553521988587225628115827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035681325724817085410551 4553521988587225628115827)
          ·
            refine ⟨6830282982880838442173741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553521988587225628115827 6830282982880838442173741)
            ·
              refine ⟨2561356118580314415815153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6830282982880838442173741 2561356118580314415815153)
              ·
                refine ⟨1921017088935235811861365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561356118580314415815153 1921017088935235811861365)
                ·
                  refine ⟨180095352087678357362003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1921017088935235811861365 180095352087678357362003)
                  ·
                    rfl

theorem cell22_1578305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_1578305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578305 prefixEnd_1578305 := by exact prefixLift 1578305
  have htrace : WordTrace (prefixWord ++ tailWord_1578305) baseStart_1578305 baseEnd_1578305 := by
    simpa [prefixWord, tailWord_1578305, baseEnd_1578305] using wordTrace_append hprefix tailTrace_1578305
  have hstable : (prefixWord ++ tailWord_1578305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578305).length < 2 ^ (prefixWord ++ tailWord_1578305).sum := by decide
  have hdescent : baseEnd_1578305 < baseStart_1578305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578361 : List Nat := [1, 2, 1, 3, 2, 1, 12]
def baseStart_1578361 : Nat := 118140960795 + 1578361 * 2 ^ 59
def prefixEnd_1578361 : Nat := 4983230072969 + 3 ^ 40 * 1578361 * 2
def baseEnd_1578361 : Nat := 20011304674350725655031

theorem tailTrace_1578361 : CollatzResearch.WordTrace tailWord_1578361 prefixEnd_1578361 20011304674350725655031 := by
  unfold tailWord_1578361
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567555034875134442934937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38378370023250089628623291 57567555034875134442934937)
  ·
    refine ⟨43175666276156350832201203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57567555034875134442934937 43175666276156350832201203)
    ·
      refine ⟨64763499414234526248301805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43175666276156350832201203 64763499414234526248301805)
      ·
        refine ⟨24286312280337947343113177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64763499414234526248301805 24286312280337947343113177)
        ·
          refine ⟨18214734210253460507334883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24286312280337947343113177 18214734210253460507334883)
          ·
            refine ⟨27322101315380190761002325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18214734210253460507334883 27322101315380190761002325)
            ·
              refine ⟨20011304674350725655031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27322101315380190761002325 20011304674350725655031)
              ·
                rfl

theorem cell22_1578361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 12].length) (baseStart_1578361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578361 prefixEnd_1578361 := by exact prefixLift 1578361
  have htrace : WordTrace (prefixWord ++ tailWord_1578361) baseStart_1578361 baseEnd_1578361 := by
    simpa [prefixWord, tailWord_1578361, baseEnd_1578361] using wordTrace_append hprefix tailTrace_1578361
  have hstable : (prefixWord ++ tailWord_1578361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578361).length < 2 ^ (prefixWord ++ tailWord_1578361).sum := by decide
  have hdescent : baseEnd_1578361 < baseStart_1578361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578363 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 2, 4]
def baseStart_1578363 : Nat := 118140960795 + 1578363 * 2 ^ 59
def prefixEnd_1578363 : Nat := 4983230072969 + 3 ^ 40 * 1578363 * 2
def baseEnd_1578363 : Nat := 540305910848342254135831

theorem tailTrace_1578363 : CollatzResearch.WordTrace tailWord_1578363 prefixEnd_1578363 540305910848342254135831 := by
  unfold tailWord_1578363
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567627980867888784507743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38378418653911925856338495 57567627980867888784507743)
  ·
    refine ⟨86351441971301833176761615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57567627980867888784507743 86351441971301833176761615)
    ·
      refine ⟨129527162956952749765142423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86351441971301833176761615 129527162956952749765142423)
      ·
        refine ⟨194290744435429124647713635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129527162956952749765142423 194290744435429124647713635)
        ·
          refine ⟨291436116653143686971570453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194290744435429124647713635 291436116653143686971570453)
          ·
            refine ⟨13661067968116110326792365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 291436116653143686971570453 13661067968116110326792365)
            ·
              refine ⟨5122900488043541372547137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13661067968116110326792365 5122900488043541372547137)
              ·
                refine ⟨3842175366032656029410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5122900488043541372547137 3842175366032656029410353)
                ·
                  refine ⟨2881631524524492022057765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842175366032656029410353 2881631524524492022057765)
                  ·
                    refine ⟨540305910848342254135831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2881631524524492022057765 540305910848342254135831)
                    ·
                      rfl

theorem cell22_1578363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_1578363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578363 prefixEnd_1578363 := by exact prefixLift 1578363
  have htrace : WordTrace (prefixWord ++ tailWord_1578363) baseStart_1578363 baseEnd_1578363 := by
    simpa [prefixWord, tailWord_1578363, baseEnd_1578363] using wordTrace_append hprefix tailTrace_1578363
  have hstable : (prefixWord ++ tailWord_1578363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578363).length < 2 ^ (prefixWord ++ tailWord_1578363).sum := by decide
  have hdescent : baseEnd_1578363 < baseStart_1578363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578365 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_1578365 : Nat := 118140960795 + 1578365 * 2 ^ 59
def prefixEnd_1578365 : Nat := 4983230072969 + 3 ^ 40 * 1578365 * 2
def baseEnd_1578365 : Nat := 540306595489214915585825

theorem tailTrace_1578365 : CollatzResearch.WordTrace tailWord_1578365 prefixEnd_1578365 540306595489214915585825 := by
  unfold tailWord_1578365
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567700926860643126080549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38378467284573762084053699 57567700926860643126080549)
  ·
    refine ⟨10793943923786370586140103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57567700926860643126080549 10793943923786370586140103)
    ·
      refine ⟨16190915885679555879210155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10793943923786370586140103 16190915885679555879210155)
      ·
        refine ⟨24286373828519333818815233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16190915885679555879210155 24286373828519333818815233)
        ·
          refine ⟨18214780371389500364111425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24286373828519333818815233 18214780371389500364111425)
          ·
            refine ⟨13661085278542125273083569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18214780371389500364111425 13661085278542125273083569)
            ·
              refine ⟨10245813958906593954812677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13661085278542125273083569 10245813958906593954812677)
              ·
                refine ⟨1921090117294986366527377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10245813958906593954812677 1921090117294986366527377)
                ·
                  refine ⟨1440817587971239774895533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921090117294986366527377 1440817587971239774895533)
                  ·
                    refine ⟨540306595489214915585825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440817587971239774895533 540306595489214915585825)
                    ·
                      rfl

theorem cell22_1578365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_1578365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578365 prefixEnd_1578365 := by exact prefixLift 1578365
  have htrace : WordTrace (prefixWord ++ tailWord_1578365) baseStart_1578365 baseEnd_1578365 := by
    simpa [prefixWord, tailWord_1578365, baseEnd_1578365] using wordTrace_append hprefix tailTrace_1578365
  have hstable : (prefixWord ++ tailWord_1578365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578365).length < 2 ^ (prefixWord ++ tailWord_1578365).sum := by decide
  have hdescent : baseEnd_1578365 < baseStart_1578365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578386 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1578386 : Nat := 118140960795 + 1578386 * 2 ^ 59
def prefixEnd_1578386 : Nat := 4983230072969 + 3 ^ 40 * 1578386 * 2
def baseEnd_1578386 : Nat := 540313784218377860810761

theorem tailTrace_1578386 : CollatzResearch.WordTrace tailWord_1578386 prefixEnd_1578386 540313784218377860810761 := by
  unfold tailWord_1578386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392116714946140928148753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38378977906523042475063341 14392116714946140928148753)
  ·
    refine ⟨10794087536209605696111565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14392116714946140928148753 10794087536209605696111565)
    ·
      refine ⟨4047782826078602136041837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10794087536209605696111565 4047782826078602136041837)
      ·
        refine ⟨1517918559779475801015689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4047782826078602136041837 1517918559779475801015689)
        ·
          refine ⟨1138438919834606850761767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1517918559779475801015689 1138438919834606850761767)
          ·
            refine ⟨1707658379751910276142651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138438919834606850761767 1707658379751910276142651)
            ·
              refine ⟨2561487569627865414213977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707658379751910276142651 2561487569627865414213977)
              ·
                refine ⟨1921115677220899060660483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561487569627865414213977 1921115677220899060660483)
                ·
                  refine ⟨2881673515831348590990725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921115677220899060660483 2881673515831348590990725)
                  ·
                    refine ⟨540313784218377860810761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2881673515831348590990725 540313784218377860810761)
                    ·
                      rfl

theorem cell22_1578386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1578386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578386 prefixEnd_1578386 := by exact prefixLift 1578386
  have htrace : WordTrace (prefixWord ++ tailWord_1578386) baseStart_1578386 baseEnd_1578386 := by
    simpa [prefixWord, tailWord_1578386, baseEnd_1578386] using wordTrace_append hprefix tailTrace_1578386
  have hstable : (prefixWord ++ tailWord_1578386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578386).length < 2 ^ (prefixWord ++ tailWord_1578386).sum := by decide
  have hdescent : baseEnd_1578386 < baseStart_1578386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578474 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_1578474 : Nat := 118140960795 + 1578474 * 2 ^ 59
def prefixEnd_1578474 : Nat := 4983230072969 + 3 ^ 40 * 1578474 * 2
def baseEnd_1578474 : Nat := 180114636138924988203497

theorem tailTrace_1578474 : CollatzResearch.WordTrace tailWord_1578474 prefixEnd_1578474 180114636138924988203497 := by
  unfold tailWord_1578474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392919120866438685449619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38381117655643836494532317 14392919120866438685449619)
  ·
    refine ⟨21589378681299658028174429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14392919120866438685449619 21589378681299658028174429)
    ·
      refine ⟨8096017005487371760565411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21589378681299658028174429 8096017005487371760565411)
      ·
        refine ⟨12144025508231057640848117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096017005487371760565411 12144025508231057640848117)
        ·
          refine ⟨1138502391396661653829511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12144025508231057640848117 1138502391396661653829511)
          ·
            refine ⟨1707753587094992480744267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138502391396661653829511 1707753587094992480744267)
            ·
              refine ⟨2561630380642488721116401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707753587094992480744267 2561630380642488721116401)
              ·
                refine ⟨1921222785481866540837301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561630380642488721116401 1921222785481866540837301)
                ·
                  refine ⟨180114636138924988203497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1921222785481866540837301 180114636138924988203497)
                  ·
                    rfl

theorem cell22_1578474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_1578474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578474 prefixEnd_1578474 := by exact prefixLift 1578474
  have htrace : WordTrace (prefixWord ++ tailWord_1578474) baseStart_1578474 baseEnd_1578474 := by
    simpa [prefixWord, tailWord_1578474, baseEnd_1578474] using wordTrace_append hprefix tailTrace_1578474
  have hstable : (prefixWord ++ tailWord_1578474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578474).length < 2 ^ (prefixWord ++ tailWord_1578474).sum := by decide
  have hdescent : baseEnd_1578474 < baseStart_1578474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578513 : List Nat := [1, 2, 2, 1, 1, 2, 5, 8]
def baseStart_1578513 : Nat := 118140960795 + 1578513 * 2 ^ 59
def prefixEnd_1578513 : Nat := 4983230072969 + 3 ^ 40 * 1578513 * 2
def baseEnd_1578513 : Nat := 60039695434865762542819

theorem tailTrace_1578513 : CollatzResearch.WordTrace tailWord_1578513 prefixEnd_1578513 60039695434865762542819 := by
  unfold tailWord_1578513
  simp only [CollatzResearch.WordTrace]
  refine ⟨57573098930324464402468193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38382065953549642934978795 57573098930324464402468193)
  ·
    refine ⟨43179824197743348301851145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57573098930324464402468193 43179824197743348301851145)
    ·
      refine ⟨32384868148307511226388359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43179824197743348301851145 32384868148307511226388359)
      ·
        refine ⟨48577302222461266839582539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32384868148307511226388359 48577302222461266839582539)
        ·
          refine ⟨72865953333691900259373809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48577302222461266839582539 72865953333691900259373809)
          ·
            refine ⟨54649465000268925194530357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72865953333691900259373809 54649465000268925194530357)
            ·
              refine ⟨5123387343775211736987221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54649465000268925194530357 5123387343775211736987221)
              ·
                refine ⟨60039695434865762542819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5123387343775211736987221 60039695434865762542819)
                ·
                  rfl

theorem cell22_1578513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 8].length) (baseStart_1578513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578513 prefixEnd_1578513 := by exact prefixLift 1578513
  have htrace : WordTrace (prefixWord ++ tailWord_1578513) baseStart_1578513 baseEnd_1578513 := by
    simpa [prefixWord, tailWord_1578513, baseEnd_1578513] using wordTrace_append hprefix tailTrace_1578513
  have hstable : (prefixWord ++ tailWord_1578513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578513).length < 2 ^ (prefixWord ++ tailWord_1578513).sum := by decide
  have hdescent : baseEnd_1578513 < baseStart_1578513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578536 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 4]
def baseStart_1578536 : Nat := 118140960795 + 1578536 * 2 ^ 59
def prefixEnd_1578536 : Nat := 4983230072969 + 3 ^ 40 * 1578536 * 2
def baseEnd_1578536 : Nat := 180121710761275823186767

theorem tailTrace_1578536 : CollatzResearch.WordTrace tailWord_1578536 prefixEnd_1578536 180121710761275823186767 := by
  unfold tailWord_1578536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786968904620569665277731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38382625206160759553703641 28786968904620569665277731)
  ·
    refine ⟨43180453356930854497916597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28786968904620569665277731 43180453356930854497916597)
    ·
      refine ⟨4048167502212267609179681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43180453356930854497916597 4048167502212267609179681)
      ·
        refine ⟨3036125626659200706884761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4048167502212267609179681 3036125626659200706884761)
        ·
          refine ⟨2277094219994400530163571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3036125626659200706884761 2277094219994400530163571)
          ·
            refine ⟨3415641329991600795245357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277094219994400530163571 3415641329991600795245357)
            ·
              refine ⟨1280865498746850298217009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3415641329991600795245357 1280865498746850298217009)
              ·
                refine ⟨960649124060137723662757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280865498746850298217009 960649124060137723662757)
                ·
                  refine ⟨180121710761275823186767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960649124060137723662757 180121710761275823186767)
                  ·
                    rfl

theorem cell22_1578536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_1578536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578536 prefixEnd_1578536 := by exact prefixLift 1578536
  have htrace : WordTrace (prefixWord ++ tailWord_1578536) baseStart_1578536 baseEnd_1578536 := by
    simpa [prefixWord, tailWord_1578536, baseEnd_1578536] using wordTrace_append hprefix tailTrace_1578536
  have hstable : (prefixWord ++ tailWord_1578536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578536).length < 2 ^ (prefixWord ++ tailWord_1578536).sum := by decide
  have hdescent : baseEnd_1578536 < baseStart_1578536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578566 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1578566 : Nat := 118140960795 + 1578566 * 2 ^ 59
def prefixEnd_1578566 : Nat := 4983230072969 + 3 ^ 40 * 1578566 * 2
def baseEnd_1578566 : Nat := 540375401896917391310209

theorem tailTrace_1578566 : CollatzResearch.WordTrace tailWord_1578566 prefixEnd_1578566 540375401896917391310209 := by
  unfold tailWord_1578566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1799219749972889201692111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38383354666088302969431701 1799219749972889201692111)
  ·
    refine ⟨2698829624959333802538167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1799219749972889201692111 2698829624959333802538167)
    ·
      refine ⟨4048244437439000703807251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698829624959333802538167 4048244437439000703807251)
      ·
        refine ⟨6072366656158501055710877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048244437439000703807251 6072366656158501055710877)
        ·
          refine ⟨2277137496059437895891579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6072366656158501055710877 2277137496059437895891579)
          ·
            refine ⟨3415706244089156843837369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277137496059437895891579 3415706244089156843837369)
            ·
              refine ⟨2561779683066867632878027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3415706244089156843837369 2561779683066867632878027)
              ·
                refine ⟨3842669524600301449317041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561779683066867632878027 3842669524600301449317041)
                ·
                  refine ⟨2882002143450226086987781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842669524600301449317041 2882002143450226086987781)
                  ·
                    refine ⟨540375401896917391310209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882002143450226086987781 540375401896917391310209)
                    ·
                      rfl

theorem cell22_1578566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1578566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578566 prefixEnd_1578566 := by exact prefixLift 1578566
  have htrace : WordTrace (prefixWord ++ tailWord_1578566) baseStart_1578566 baseEnd_1578566 := by
    simpa [prefixWord, tailWord_1578566, baseEnd_1578566] using wordTrace_append hprefix tailTrace_1578566
  have hstable : (prefixWord ++ tailWord_1578566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578566).length < 2 ^ (prefixWord ++ tailWord_1578566).sum := by decide
  have hdescent : baseEnd_1578566 < baseStart_1578566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578596 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1578596 : Nat := 118140960795 + 1578596 * 2 ^ 59
def prefixEnd_1578596 : Nat := 4983230072969 + 3 ^ 40 * 1578596 * 2
def baseEnd_1578596 : Nat := 540385671510007313060117

theorem tailTrace_1578596 : CollatzResearch.WordTrace tailWord_1578596 prefixEnd_1578596 540385671510007313060117 := by
  unfold tailWord_1578596
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788063094511884788869821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38384084126015846385159761 28788063094511884788869821)
  ·
    refine ⟨10795523660441956795826183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28788063094511884788869821 10795523660441956795826183)
    ·
      refine ⟨16193285490662935193739275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10795523660441956795826183 16193285490662935193739275)
      ·
        refine ⟨24289928235994402790608913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16193285490662935193739275 24289928235994402790608913)
        ·
          refine ⟨18217446176995802092956685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24289928235994402790608913 18217446176995802092956685)
          ·
            refine ⟨6831542316373425784858757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18217446176995802092956685 6831542316373425784858757)
            ·
              refine ⟨1280914184320017334661017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6831542316373425784858757 1280914184320017334661017)
              ·
                refine ⟨960685638240013000995763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280914184320017334661017 960685638240013000995763)
                ·
                  refine ⟨1441028457360019501493645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960685638240013000995763 1441028457360019501493645)
                  ·
                    refine ⟨540385671510007313060117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441028457360019501493645 540385671510007313060117)
                    ·
                      rfl

theorem cell22_1578596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1578596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578596 prefixEnd_1578596 := by exact prefixLift 1578596
  have htrace : WordTrace (prefixWord ++ tailWord_1578596) baseStart_1578596 baseEnd_1578596 := by
    simpa [prefixWord, tailWord_1578596, baseEnd_1578596] using wordTrace_append hprefix tailTrace_1578596
  have hstable : (prefixWord ++ tailWord_1578596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578596).length < 2 ^ (prefixWord ++ tailWord_1578596).sum := by decide
  have hdescent : baseEnd_1578596 < baseStart_1578596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578635 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 1, 5]
def baseStart_1578635 : Nat := 118140960795 + 1578635 * 2 ^ 59
def prefixEnd_1578635 : Nat := 4983230072969 + 3 ^ 40 * 1578635 * 2
def baseEnd_1578635 : Nat := 540399022007024211334997

theorem tailTrace_1578635 : CollatzResearch.WordTrace tailWord_1578635 prefixEnd_1578635 540399022007024211334997 := by
  unfold tailWord_1578635
  simp only [CollatzResearch.WordTrace]
  refine ⟨57577548635882479238409359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38385032423921652825606239 57577548635882479238409359)
  ·
    refine ⟨86366322953823718857614039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57577548635882479238409359 86366322953823718857614039)
    ·
      refine ⟨129549484430735578286421059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86366322953823718857614039 129549484430735578286421059)
      ·
        refine ⟨194324226646103367429631589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129549484430735578286421059 194324226646103367429631589)
        ·
          refine ⟨36435792496144381393055923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194324226646103367429631589 36435792496144381393055923)
          ·
            refine ⟨54653688744216572089583885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36435792496144381393055923 54653688744216572089583885)
            ·
              refine ⟨20495133279081214533593957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54653688744216572089583885 20495133279081214533593957)
              ·
                refine ⟨3842837489827727725048867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20495133279081214533593957 3842837489827727725048867)
                ·
                  refine ⟨5764256234741591587573301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842837489827727725048867 5764256234741591587573301)
                  ·
                    refine ⟨540399022007024211334997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5764256234741591587573301 540399022007024211334997)
                    ·
                      rfl

theorem cell22_1578635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_1578635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578635 prefixEnd_1578635 := by exact prefixLift 1578635
  have htrace : WordTrace (prefixWord ++ tailWord_1578635) baseStart_1578635 baseEnd_1578635 := by
    simpa [prefixWord, tailWord_1578635, baseEnd_1578635] using wordTrace_append hprefix tailTrace_1578635
  have hstable : (prefixWord ++ tailWord_1578635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578635).length < 2 ^ (prefixWord ++ tailWord_1578635).sum := by decide
  have hdescent : baseEnd_1578635 < baseStart_1578635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578654 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1578654 : Nat := 118140960795 + 1578654 * 2 ^ 59
def prefixEnd_1578654 : Nat := 4983230072969 + 3 ^ 40 * 1578654 * 2
def baseEnd_1578654 : Nat := 180135175365104831703313

theorem tailTrace_1578654 : CollatzResearch.WordTrace tailWord_1578654 prefixEnd_1578654 180135175365104831703313 := by
  unfold tailWord_1578654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197280202851705685418877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38385494415209096988900677 7197280202851705685418877)
  ·
    refine ⟨2698980076069389632032079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7197280202851705685418877 2698980076069389632032079)
    ·
      refine ⟨4048470114104084448048119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698980076069389632032079 4048470114104084448048119)
      ·
        refine ⟨6072705171156126672072179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048470114104084448048119 6072705171156126672072179)
        ·
          refine ⟨9109057756734190008108269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072705171156126672072179 9109057756734190008108269)
          ·
            refine ⟨3415896658775321253040601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9109057756734190008108269 3415896658775321253040601)
            ·
              refine ⟨2561922494081490939780451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3415896658775321253040601 2561922494081490939780451)
              ·
                refine ⟨3842883741122236409670677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561922494081490939780451 3842883741122236409670677)
                ·
                  refine ⟨180135175365104831703313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3842883741122236409670677 180135175365104831703313)
                  ·
                    rfl

theorem cell22_1578654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1578654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578654 prefixEnd_1578654 := by exact prefixLift 1578654
  have htrace : WordTrace (prefixWord ++ tailWord_1578654) baseStart_1578654 baseEnd_1578654 := by
    simpa [prefixWord, tailWord_1578654, baseEnd_1578654] using wordTrace_append hprefix tailTrace_1578654
  have hstable : (prefixWord ++ tailWord_1578654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578654).length < 2 ^ (prefixWord ++ tailWord_1578654).sum := by decide
  have hdescent : baseEnd_1578654 < baseStart_1578654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578682 : List Nat := [3, 1, 1, 1, 2, 4, 4, 6]
def baseStart_1578682 : Nat := 118140960795 + 1578682 * 2 ^ 59
def prefixEnd_1578682 : Nat := 4983230072969 + 3 ^ 40 * 1578682 * 2
def baseEnd_1578682 : Nat := 60046123451947972823317

theorem tailTrace_1578682 : CollatzResearch.WordTrace tailWord_1578682 prefixEnd_1578682 60046123451947972823317 := by
  unfold tailWord_1578682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394815716678051566342575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38386175244474804176913533 14394815716678051566342575)
  ·
    refine ⟨21592223575017077349513863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14394815716678051566342575 21592223575017077349513863)
    ·
      refine ⟨32388335362525616024270795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21592223575017077349513863 32388335362525616024270795)
      ·
        refine ⟨48582503043788424036406193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32388335362525616024270795 48582503043788424036406193)
        ·
          refine ⟨36436877282841318027304645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48582503043788424036406193 36436877282841318027304645)
          ·
            refine ⟨6831914490532747130119621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36436877282841318027304645 6831914490532747130119621)
            ·
              refine ⟨1280983966974890086897429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6831914490532747130119621 1280983966974890086897429)
              ·
                refine ⟨60046123451947972823317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1280983966974890086897429 60046123451947972823317)
                ·
                  rfl

theorem cell22_1578682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_1578682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578682 prefixEnd_1578682 := by exact prefixLift 1578682
  have htrace : WordTrace (prefixWord ++ tailWord_1578682) baseStart_1578682 baseEnd_1578682 := by
    simpa [prefixWord, tailWord_1578682, baseEnd_1578682] using wordTrace_append hprefix tailTrace_1578682
  have hstable : (prefixWord ++ tailWord_1578682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578682).length < 2 ^ (prefixWord ++ tailWord_1578682).sum := by decide
  have hdescent : baseEnd_1578682 < baseStart_1578682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578701 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1578701 : Nat := 118140960795 + 1578701 * 2 ^ 59
def prefixEnd_1578701 : Nat := 4983230072969 + 3 ^ 40 * 1578701 * 2
def baseEnd_1578701 : Nat := 540421615155822039184795

theorem tailTrace_1578701 : CollatzResearch.WordTrace tailWord_1578701 prefixEnd_1578701 540421615155822039184795 := by
  unfold tailWord_1578701
  simp only [CollatzResearch.WordTrace]
  refine ⟨57579955853643372510311957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38386637235762248340207971 57579955853643372510311957)
  ·
    refine ⟨2699060430639533086420873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57579955853643372510311957 2699060430639533086420873)
    ·
      refine ⟨2024295322979649814815655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2699060430639533086420873 2024295322979649814815655)
      ·
        refine ⟨3036442984469474722223483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024295322979649814815655 3036442984469474722223483)
        ·
          refine ⟨4554664476704212083335225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036442984469474722223483 4554664476704212083335225)
          ·
            refine ⟨3415998357528159062501419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4554664476704212083335225 3415998357528159062501419)
            ·
              refine ⟨5123997536292238593752129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415998357528159062501419 5123997536292238593752129)
              ·
                refine ⟨3842998152219178945314097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123997536292238593752129 3842998152219178945314097)
                ·
                  refine ⟨2882248614164384208985573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842998152219178945314097 2882248614164384208985573)
                  ·
                    refine ⟨540421615155822039184795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882248614164384208985573 540421615155822039184795)
                    ·
                      rfl

theorem cell22_1578701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1578701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578701 prefixEnd_1578701 := by exact prefixLift 1578701
  have htrace : WordTrace (prefixWord ++ tailWord_1578701) baseStart_1578701 baseEnd_1578701 := by
    simpa [prefixWord, tailWord_1578701, baseEnd_1578701] using wordTrace_append hprefix tailTrace_1578701
  have hstable : (prefixWord ++ tailWord_1578701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578701).length < 2 ^ (prefixWord ++ tailWord_1578701).sum := by decide
  have hdescent : baseEnd_1578701 < baseStart_1578701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578714 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_1578714 : Nat := 118140960795 + 1578714 * 2 ^ 59
def prefixEnd_1578714 : Nat := 4983230072969 + 3 ^ 40 * 1578714 * 2
def baseEnd_1578714 : Nat := 540426065321494338609755

theorem tailTrace_1578714 : CollatzResearch.WordTrace tailWord_1578714 prefixEnd_1578714 540426065321494338609755 := by
  unfold tailWord_1578714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14395107500649068932633799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38386953335064183820356797 14395107500649068932633799)
  ·
    refine ⟨21592661250973603398950699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14395107500649068932633799 21592661250973603398950699)
    ·
      refine ⟨32388991876460405098426049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21592661250973603398950699 32388991876460405098426049)
      ·
        refine ⟨24291743907345303823819537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32388991876460405098426049 24291743907345303823819537)
        ·
          refine ⟨18218807930508977867864653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24291743907345303823819537 18218807930508977867864653)
          ·
            refine ⟨6832052973940866700449245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18218807930508977867864653 6832052973940866700449245)
            ·
              refine ⟨2562019865227825012668467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6832052973940866700449245 2562019865227825012668467)
              ·
                refine ⟨3843029797841737519002701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562019865227825012668467 3843029797841737519002701)
                ·
                  refine ⟨1441136174190651569626013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3843029797841737519002701 1441136174190651569626013)
                  ·
                    refine ⟨540426065321494338609755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441136174190651569626013 540426065321494338609755)
                    ·
                      rfl

theorem cell22_1578714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_1578714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578714 prefixEnd_1578714 := by exact prefixLift 1578714
  have htrace : WordTrace (prefixWord ++ tailWord_1578714) baseStart_1578714 baseEnd_1578714 := by
    simpa [prefixWord, tailWord_1578714, baseEnd_1578714] using wordTrace_append hprefix tailTrace_1578714
  have hstable : (prefixWord ++ tailWord_1578714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578714).length < 2 ^ (prefixWord ++ tailWord_1578714).sum := by decide
  have hdescent : baseEnd_1578714 < baseStart_1578714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578787 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 1, 5]
def baseStart_1578787 : Nat := 118140960795 + 1578787 * 2 ^ 59
def prefixEnd_1578787 : Nat := 4983230072969 + 3 ^ 40 * 1578787 * 2
def baseEnd_1578787 : Nat := 540451054713346481534531

theorem tailTrace_1578787 : CollatzResearch.WordTrace tailWord_1578787 prefixEnd_1578787 540451054713346481534531 := by
  unfold tailWord_1578787
  simp only [CollatzResearch.WordTrace]
  refine ⟨57583092531331809197942615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38388728354221206131961743 57583092531331809197942615)
  ·
    refine ⟨86374638796997713796913923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57583092531331809197942615 86374638796997713796913923)
    ·
      refine ⟨129561958195496570695370885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86374638796997713796913923 129561958195496570695370885)
      ·
        refine ⟨24292867161655607005382041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129561958195496570695370885 24292867161655607005382041)
        ·
          refine ⟨18219650371241705254036531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24292867161655607005382041 18219650371241705254036531)
          ·
            refine ⟨27329475556862557881054797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18219650371241705254036531 27329475556862557881054797)
            ·
              refine ⟨10248553333823459205395549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27329475556862557881054797 10248553333823459205395549)
              ·
                refine ⟨3843207500183797202023331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10248553333823459205395549 3843207500183797202023331)
                ·
                  refine ⟨5764811250275695803034997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843207500183797202023331 5764811250275695803034997)
                  ·
                    refine ⟨540451054713346481534531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5764811250275695803034997 540451054713346481534531)
                    ·
                      rfl

theorem cell22_1578787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_1578787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578787 prefixEnd_1578787 := by exact prefixLift 1578787
  have htrace : WordTrace (prefixWord ++ tailWord_1578787) baseStart_1578787 baseEnd_1578787 := by
    simpa [prefixWord, tailWord_1578787, baseEnd_1578787] using wordTrace_append hprefix tailTrace_1578787
  have hstable : (prefixWord ++ tailWord_1578787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578787).length < 2 ^ (prefixWord ++ tailWord_1578787).sum := by decide
  have hdescent : baseEnd_1578787 < baseStart_1578787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578849 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1578849 : Nat := 118140960795 + 1578849 * 2 ^ 59
def prefixEnd_1578849 : Nat := 4983230072969 + 3 ^ 40 * 1578849 * 2
def baseEnd_1578849 : Nat := 540472278580398986484341

theorem tailTrace_1578849 : CollatzResearch.WordTrace tailWord_1578849 prefixEnd_1578849 540472278580398986484341 := by
  unfold tailWord_1578849
  simp only [CollatzResearch.WordTrace]
  refine ⟨57585353857107193786699601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38390235904738129191133067 57585353857107193786699601)
  ·
    refine ⟨43189015392830395340024701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57585353857107193786699601 43189015392830395340024701)
    ·
      refine ⟨16195880772311398252509263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43189015392830395340024701 16195880772311398252509263)
      ·
        refine ⟨24293821158467097378763895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16195880772311398252509263 24293821158467097378763895)
        ·
          refine ⟨36440731737700646068145843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24293821158467097378763895 36440731737700646068145843)
          ·
            refine ⟨54661097606550969102218765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36440731737700646068145843 54661097606550969102218765)
            ·
              refine ⟨20497911602456613413332037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54661097606550969102218765 20497911602456613413332037)
              ·
                refine ⟨3843358425460615014999757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20497911602456613413332037 3843358425460615014999757)
                ·
                  refine ⟨1441259409547730630624909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3843358425460615014999757 1441259409547730630624909)
                  ·
                    refine ⟨540472278580398986484341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441259409547730630624909 540472278580398986484341)
                    ·
                      rfl

theorem cell22_1578849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1578849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578849 prefixEnd_1578849 := by exact prefixLift 1578849
  have htrace : WordTrace (prefixWord ++ tailWord_1578849) baseStart_1578849 baseEnd_1578849 := by
    simpa [prefixWord, tailWord_1578849, baseEnd_1578849] using wordTrace_append hprefix tailTrace_1578849
  have hstable : (prefixWord ++ tailWord_1578849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578849).length < 2 ^ (prefixWord ++ tailWord_1578849).sum := by decide
  have hdescent : baseEnd_1578849 < baseStart_1578849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578851 : List Nat := [1, 1, 1, 5, 4, 2, 2, 6]
def baseStart_1578851 : Nat := 118140960795 + 1578851 * 2 ^ 59
def prefixEnd_1578851 : Nat := 4983230072969 + 3 ^ 40 * 1578851 * 2
def baseEnd_1578851 : Nat := 60052551469030183103815

theorem tailTrace_1578851 : CollatzResearch.WordTrace tailWord_1578851 prefixEnd_1578851 60052551469030183103815 := by
  unfold tailWord_1578851
  simp only [CollatzResearch.WordTrace]
  refine ⟨57585426803099948128272407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38390284535399965418848271 57585426803099948128272407)
  ·
    refine ⟨86378140204649922192408611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57585426803099948128272407 86378140204649922192408611)
    ·
      refine ⟨129567210306974883288612917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86378140204649922192408611 129567210306974883288612917)
      ·
        refine ⟨12146925966278895308307461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129567210306974883288612917 12146925966278895308307461)
        ·
          refine ⟨2277548618677292870307649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12146925966278895308307461 2277548618677292870307649)
          ·
            refine ⟨1708161464007969652730737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277548618677292870307649 1708161464007969652730737)
            ·
              refine ⟨1281121098005977239548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708161464007969652730737 1281121098005977239548053)
              ·
                refine ⟨60052551469030183103815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1281121098005977239548053 60052551469030183103815)
                ·
                  rfl

theorem cell22_1578851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 6].length) (baseStart_1578851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578851 prefixEnd_1578851 := by exact prefixLift 1578851
  have htrace : WordTrace (prefixWord ++ tailWord_1578851) baseStart_1578851 baseEnd_1578851 := by
    simpa [prefixWord, tailWord_1578851, baseEnd_1578851] using wordTrace_append hprefix tailTrace_1578851
  have hstable : (prefixWord ++ tailWord_1578851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578851).length < 2 ^ (prefixWord ++ tailWord_1578851).sum := by decide
  have hdescent : baseEnd_1578851 < baseStart_1578851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578892 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1578892 : Nat := 118140960795 + 1578892 * 2 ^ 59
def prefixEnd_1578892 : Nat := 4983230072969 + 3 ^ 40 * 1578892 * 2
def baseEnd_1578892 : Nat := 540486998359161207659209

theorem tailTrace_1578892 : CollatzResearch.WordTrace tailWord_1578892 prefixEnd_1578892 540486998359161207659209 := by
  unfold tailWord_1578892
  simp only [CollatzResearch.WordTrace]
  refine ⟨28793461097975706065257465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38391281463967608087009953 28793461097975706065257465)
  ·
    refine ⟨21595095823481779548943099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28793461097975706065257465 21595095823481779548943099)
    ·
      refine ⟨32392643735222669323414649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21595095823481779548943099 32392643735222669323414649)
      ·
        refine ⟨24294482801417001992560987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32392643735222669323414649 24294482801417001992560987)
        ·
          refine ⟨36441724202125502988841481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24294482801417001992560987 36441724202125502988841481)
          ·
            refine ⟨27331293151594127241631111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36441724202125502988841481 27331293151594127241631111)
            ·
              refine ⟨40996939727391190862446667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27331293151594127241631111 40996939727391190862446667)
              ·
                refine ⟨61495409591086786293670001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40996939727391190862446667 61495409591086786293670001)
                ·
                  refine ⟨46121557193315089720252501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61495409591086786293670001 46121557193315089720252501)
                  ·
                    refine ⟨540486998359161207659209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46121557193315089720252501 540486998359161207659209)
                    ·
                      rfl

theorem cell22_1578892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1578892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578892 prefixEnd_1578892 := by exact prefixLift 1578892
  have htrace : WordTrace (prefixWord ++ tailWord_1578892) baseStart_1578892 baseEnd_1578892 := by
    simpa [prefixWord, tailWord_1578892, baseEnd_1578892] using wordTrace_append hprefix tailTrace_1578892
  have hstable : (prefixWord ++ tailWord_1578892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578892).length < 2 ^ (prefixWord ++ tailWord_1578892).sum := by decide
  have hdescent : baseEnd_1578892 < baseStart_1578892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578954 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1578954 : Nat := 118140960795 + 1578954 * 2 ^ 59
def prefixEnd_1578954 : Nat := 4983230072969 + 3 ^ 40 * 1578954 * 2
def baseEnd_1578954 : Nat := 540508222226213712609019

theorem tailTrace_1578954 : CollatzResearch.WordTrace tailWord_1578954 prefixEnd_1578954 540508222226213712609019 := by
  unfold tailWord_1578954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14397295880431699179817979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38392789014484531146181277 14397295880431699179817979)
  ·
    refine ⟨21595943820647548769726969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14397295880431699179817979 21595943820647548769726969)
    ·
      refine ⟨16196957865485661577295227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21595943820647548769726969 16196957865485661577295227)
      ·
        refine ⟨24295436798228492365942841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16196957865485661577295227 24295436798228492365942841)
        ·
          refine ⟨18221577598671369274457131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24295436798228492365942841 18221577598671369274457131)
          ·
            refine ⟨27332366398007053911685697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18221577598671369274457131 27332366398007053911685697)
            ·
              refine ⟨20499274798505290433764273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27332366398007053911685697 20499274798505290433764273)
              ·
                refine ⟨15374456098878967825323205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20499274798505290433764273 15374456098878967825323205)
                ·
                  refine ⟨2882710518539806467248101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15374456098878967825323205 2882710518539806467248101)
                  ·
                    refine ⟨540508222226213712609019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882710518539806467248101 540508222226213712609019)
                    ·
                      rfl

theorem cell22_1578954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1578954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578954 prefixEnd_1578954 := by exact prefixLift 1578954
  have htrace : WordTrace (prefixWord ++ tailWord_1578954) baseStart_1578954 baseEnd_1578954 := by
    simpa [prefixWord, tailWord_1578954, baseEnd_1578954] using wordTrace_append hprefix tailTrace_1578954
  have hstable : (prefixWord ++ tailWord_1578954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578954).length < 2 ^ (prefixWord ++ tailWord_1578954).sum := by decide
  have hdescent : baseEnd_1578954 < baseStart_1578954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578956 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_1578956 : Nat := 118140960795 + 1578956 * 2 ^ 59
def prefixEnd_1578956 : Nat := 4983230072969 + 3 ^ 40 * 1578956 * 2
def baseEnd_1578956 : Nat := 540508906867086374059013

theorem tailTrace_1578956 : CollatzResearch.WordTrace tailWord_1578956 prefixEnd_1578956 540508906867086374059013 := by
  unfold tailWord_1578956
  simp only [CollatzResearch.WordTrace]
  refine ⟨28794628233859775530422361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38392837645146367373896481 28794628233859775530422361)
  ·
    refine ⟨21595971175394831647816771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28794628233859775530422361 21595971175394831647816771)
    ·
      refine ⟨32393956763092247471725157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21595971175394831647816771 32393956763092247471725157)
      ·
        refine ⟨6073866893079796400948467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32393956763092247471725157 6073866893079796400948467)
        ·
          refine ⟨9110800339619694601422701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073866893079796400948467 9110800339619694601422701)
          ·
            refine ⟨3416550127357385475533513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9110800339619694601422701 3416550127357385475533513)
            ·
              refine ⟨2562412595518039106650135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3416550127357385475533513 2562412595518039106650135)
              ·
                refine ⟨3843618893277058659975203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562412595518039106650135 3843618893277058659975203)
                ·
                  refine ⟨5765428339915587989962805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843618893277058659975203 5765428339915587989962805)
                  ·
                    refine ⟨540508906867086374059013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5765428339915587989962805 540508906867086374059013)
                    ·
                      rfl

theorem cell22_1578956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_1578956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578956 prefixEnd_1578956 := by exact prefixLift 1578956
  have htrace : WordTrace (prefixWord ++ tailWord_1578956) baseStart_1578956 baseEnd_1578956 := by
    simpa [prefixWord, tailWord_1578956, baseEnd_1578956] using wordTrace_append hprefix tailTrace_1578956
  have hstable : (prefixWord ++ tailWord_1578956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578956).length < 2 ^ (prefixWord ++ tailWord_1578956).sum := by decide
  have hdescent : baseEnd_1578956 < baseStart_1578956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578990 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1578990 : Nat := 118140960795 + 1578990 * 2 ^ 59
def prefixEnd_1578990 : Nat := 4983230072969 + 3 ^ 40 * 1578990 * 2
def baseEnd_1578990 : Nat := 540520545761921618708909

theorem tailTrace_1578990 : CollatzResearch.WordTrace tailWord_1578990 prefixEnd_1578990 540520545761921618708909 := by
  unfold tailWord_1578990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198812068699546858447803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38393664366397583245054949 7198812068699546858447803)
  ·
    refine ⟨10798218103049320287671705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7198812068699546858447803 10798218103049320287671705)
    ·
      refine ⟨8098663577286990215753779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10798218103049320287671705 8098663577286990215753779)
      ·
        refine ⟨12147995365930485323630669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098663577286990215753779 12147995365930485323630669)
        ·
          refine ⟨4555498262223931996361501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12147995365930485323630669 4555498262223931996361501)
          ·
            refine ⟨1708311848333974498635563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4555498262223931996361501 1708311848333974498635563)
            ·
              refine ⟨2562467772500961747953345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708311848333974498635563 2562467772500961747953345)
              ·
                refine ⟨1921850829375721310965009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562467772500961747953345 1921850829375721310965009)
                ·
                  refine ⟨1441388122031790983223757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921850829375721310965009 1441388122031790983223757)
                  ·
                    refine ⟨540520545761921618708909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441388122031790983223757 540520545761921618708909)
                    ·
                      rfl

theorem cell22_1578990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1578990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1578990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1578990 prefixEnd_1578990 := by exact prefixLift 1578990
  have htrace : WordTrace (prefixWord ++ tailWord_1578990) baseStart_1578990 baseEnd_1578990 := by
    simpa [prefixWord, tailWord_1578990, baseEnd_1578990] using wordTrace_append hprefix tailTrace_1578990
  have hstable : (prefixWord ++ tailWord_1578990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578990).length < 2 ^ (prefixWord ++ tailWord_1578990).sum := by decide
  have hdescent : baseEnd_1578990 < baseStart_1578990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579001 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_1579001 : Nat := 118140960795 + 1579001 * 2 ^ 59
def prefixEnd_1579001 : Nat := 4983230072969 + 3 ^ 40 * 1579001 * 2
def baseEnd_1579001 : Nat := 540524311286721256683875

theorem tailTrace_1579001 : CollatzResearch.WordTrace tailWord_1579001 prefixEnd_1579001 540524311286721256683875 := by
  unfold tailWord_1579001
  simp only [CollatzResearch.WordTrace]
  refine ⟨57590897752556523746232857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38393931835037682497488571 57590897752556523746232857)
  ·
    refine ⟨43193173314417392809674643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57590897752556523746232857 43193173314417392809674643)
    ·
      refine ⟨64789759971626089214511965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43193173314417392809674643 64789759971626089214511965)
      ·
        refine ⟨24296159989359783455441987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64789759971626089214511965 24296159989359783455441987)
        ·
          refine ⟨36444239984039675183162981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24296159989359783455441987 36444239984039675183162981)
          ·
            refine ⟨6833294997007439096843059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36444239984039675183162981 6833294997007439096843059)
            ·
              refine ⟨10249942495511158645264589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833294997007439096843059 10249942495511158645264589)
              ·
                refine ⟨3843728435816684491974221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10249942495511158645264589 3843728435816684491974221)
                ·
                  refine ⟨1441398163431256684490333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3843728435816684491974221 1441398163431256684490333)
                  ·
                    refine ⟨540524311286721256683875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441398163431256684490333 540524311286721256683875)
                    ·
                      rfl

theorem cell22_1579001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_1579001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579001 prefixEnd_1579001 := by exact prefixLift 1579001
  have htrace : WordTrace (prefixWord ++ tailWord_1579001) baseStart_1579001 baseEnd_1579001 := by
    simpa [prefixWord, tailWord_1579001, baseEnd_1579001] using wordTrace_append hprefix tailTrace_1579001
  have hstable : (prefixWord ++ tailWord_1579001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579001).length < 2 ^ (prefixWord ++ tailWord_1579001).sum := by decide
  have hdescent : baseEnd_1579001 < baseStart_1579001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579065 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 5]
def baseStart_1579065 : Nat := 118140960795 + 1579065 * 2 ^ 59
def prefixEnd_1579065 : Nat := 4983230072969 + 3 ^ 40 * 1579065 * 2
def baseEnd_1579065 : Nat := 180182073264882141027893

theorem tailTrace_1579065 : CollatzResearch.WordTrace tailWord_1579065 prefixEnd_1579065 180182073264882141027893 := by
  unfold tailWord_1579065
  simp only [CollatzResearch.WordTrace]
  refine ⟨57593232024324662676562649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38395488016216441784375099 57593232024324662676562649)
  ·
    refine ⟨43194924018243497007421987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57593232024324662676562649 43194924018243497007421987)
    ·
      refine ⟨64792386027365245511132981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43194924018243497007421987 64792386027365245511132981)
      ·
        refine ⟨6074286190065491766668717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64792386027365245511132981 6074286190065491766668717)
        ·
          refine ⟨2277857321274559412500769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6074286190065491766668717 2277857321274559412500769)
          ·
            refine ⟨1708392990955919559375577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277857321274559412500769 1708392990955919559375577)
            ·
              refine ⟨1281294743216939669531683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708392990955919559375577 1281294743216939669531683)
              ·
                refine ⟨1921942114825409504297525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281294743216939669531683 1921942114825409504297525)
                ·
                  refine ⟨180182073264882141027893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1921942114825409504297525 180182073264882141027893)
                  ·
                    rfl

theorem cell22_1579065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_1579065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579065 prefixEnd_1579065 := by exact prefixLift 1579065
  have htrace : WordTrace (prefixWord ++ tailWord_1579065) baseStart_1579065 baseEnd_1579065 := by
    simpa [prefixWord, tailWord_1579065, baseEnd_1579065] using wordTrace_append hprefix tailTrace_1579065
  have hstable : (prefixWord ++ tailWord_1579065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579065).length < 2 ^ (prefixWord ++ tailWord_1579065).sum := by decide
  have hdescent : baseEnd_1579065 < baseStart_1579065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579104 : List Nat := [2, 1, 1, 3, 2, 13]
def baseStart_1579104 : Nat := 118140960795 + 1579104 * 2 ^ 59
def prefixEnd_1579104 : Nat := 4983230072969 + 3 ^ 40 * 1579104 * 2
def baseEnd_1579104 : Nat := 6673574941872386683439

theorem tailTrace_1579104 : CollatzResearch.WordTrace tailWord_1579104 prefixEnd_1579104 6673574941872386683439 := by
  unfold tailWord_1579104
  simp only [CollatzResearch.WordTrace]
  refine ⟨28797327235591686168616183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38396436314122248224821577 28797327235591686168616183)
  ·
    refine ⟨43195990853387529252924275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28797327235591686168616183 43195990853387529252924275)
    ·
      refine ⟨64793986280081293879386413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43195990853387529252924275 64793986280081293879386413)
      ·
        refine ⟨24297744855030485204769905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64793986280081293879386413 24297744855030485204769905)
        ·
          refine ⟨18223308641272863903577429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24297744855030485204769905 18223308641272863903577429)
          ·
            refine ⟨6673574941872386683439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 18223308641272863903577429 6673574941872386683439)
            ·
              rfl

theorem cell22_1579104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 13].length) (baseStart_1579104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579104 prefixEnd_1579104 := by exact prefixLift 1579104
  have htrace : WordTrace (prefixWord ++ tailWord_1579104) baseStart_1579104 baseEnd_1579104 := by
    simpa [prefixWord, tailWord_1579104, baseEnd_1579104] using wordTrace_append hprefix tailTrace_1579104
  have hstable : (prefixWord ++ tailWord_1579104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579104).length < 2 ^ (prefixWord ++ tailWord_1579104).sum := by decide
  have hdescent : baseEnd_1579104 < baseStart_1579104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579108 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_1579108 : Nat := 118140960795 + 1579108 * 2 ^ 59
def prefixEnd_1579108 : Nat := 4983230072969 + 3 ^ 40 * 1579108 * 2
def baseEnd_1579108 : Nat := 540560939573408644258547

theorem tailTrace_1579108 : CollatzResearch.WordTrace tailWord_1579108 prefixEnd_1579108 540560939573408644258547 := by
  unfold tailWord_1579108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28797400181584440510188989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38396533575445920680251985 28797400181584440510188989)
  ·
    refine ⟨10799025068094165191320871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28797400181584440510188989 10799025068094165191320871)
    ·
      refine ⟨16198537602141247786981307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799025068094165191320871 16198537602141247786981307)
      ·
        refine ⟨24297806403211871680471961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16198537602141247786981307 24297806403211871680471961)
        ·
          refine ⟨18223354802408903760353971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24297806403211871680471961 18223354802408903760353971)
          ·
            refine ⟨27335032203613355640530957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18223354802408903760353971 27335032203613355640530957)
            ·
              refine ⟨10250637076355008365199109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27335032203613355640530957 10250637076355008365199109)
              ·
                refine ⟨1921994451816564068474833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10250637076355008365199109 1921994451816564068474833)
                ·
                  refine ⟨1441495838862423051356125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921994451816564068474833 1441495838862423051356125)
                  ·
                    refine ⟨540560939573408644258547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441495838862423051356125 540560939573408644258547)
                    ·
                      rfl

theorem cell22_1579108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_1579108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579108 prefixEnd_1579108 := by exact prefixLift 1579108
  have htrace : WordTrace (prefixWord ++ tailWord_1579108) baseStart_1579108 baseEnd_1579108 := by
    simpa [prefixWord, tailWord_1579108, baseEnd_1579108] using wordTrace_append hprefix tailTrace_1579108
  have hstable : (prefixWord ++ tailWord_1579108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579108).length < 2 ^ (prefixWord ++ tailWord_1579108).sum := by decide
  have hdescent : baseEnd_1579108 < baseStart_1579108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579170 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1579170 : Nat := 118140960795 + 1579170 * 2 ^ 59
def prefixEnd_1579170 : Nat := 4983230072969 + 3 ^ 40 * 1579170 * 2
def baseEnd_1579170 : Nat := 540582163440461149208357

theorem tailTrace_1579170 : CollatzResearch.WordTrace tailWord_1579170 prefixEnd_1579170 540582163440461149208357 := by
  unfold tailWord_1579170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399265422236066402283741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38398041125962843739423309 14399265422236066402283741)
  ·
    refine ⟨5399724533338524900856403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14399265422236066402283741 5399724533338524900856403)
    ·
      refine ⟨8099586800007787351284605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399724533338524900856403 8099586800007787351284605)
      ·
        refine ⟨3037345050002920256731727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8099586800007787351284605 3037345050002920256731727)
        ·
          refine ⟨4556017575004380385097591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037345050002920256731727 4556017575004380385097591)
          ·
            refine ⟨6834026362506570577646387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556017575004380385097591 6834026362506570577646387)
            ·
              refine ⟨10251039543759855866469581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834026362506570577646387 10251039543759855866469581)
              ·
                refine ⟨3844139828909945949926093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10251039543759855866469581 3844139828909945949926093)
                ·
                  refine ⟨1441552435841229731222285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3844139828909945949926093 1441552435841229731222285)
                  ·
                    refine ⟨540582163440461149208357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441552435841229731222285 540582163440461149208357)
                    ·
                      rfl

theorem cell22_1579170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1579170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579170 prefixEnd_1579170 := by exact prefixLift 1579170
  have htrace : WordTrace (prefixWord ++ tailWord_1579170) baseStart_1579170 baseEnd_1579170 := by
    simpa [prefixWord, tailWord_1579170, baseEnd_1579170] using wordTrace_append hprefix tailTrace_1579170
  have hstable : (prefixWord ++ tailWord_1579170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579170).length < 2 ^ (prefixWord ++ tailWord_1579170).sum := by decide
  have hdescent : baseEnd_1579170 < baseStart_1579170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579204 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1579204 : Nat := 118140960795 + 1579204 * 2 ^ 59
def prefixEnd_1579204 : Nat := 4983230072969 + 3 ^ 40 * 1579204 * 2
def baseEnd_1579204 : Nat := 540593802335296393858253

theorem tailTrace_1579204 : CollatzResearch.WordTrace tailWord_1579204 prefixEnd_1579204 540593802335296393858253 := by
  unfold tailWord_1579204
  simp only [CollatzResearch.WordTrace]
  refine ⟨28799150885410544707936333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38398867847214059610581777 28799150885410544707936333)
  ·
    refine ⟨10799681582028954265476125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28799150885410544707936333 10799681582028954265476125)
    ·
      refine ⟨4049880593260857849553547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10799681582028954265476125 4049880593260857849553547)
      ·
        refine ⟨6074820889891286774330321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049880593260857849553547 6074820889891286774330321)
        ·
          refine ⟨4556115667418465080747741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074820889891286774330321 4556115667418465080747741)
          ·
            refine ⟨1708543375281924405280403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4556115667418465080747741 1708543375281924405280403)
            ·
              refine ⟨2562815062922886607920605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708543375281924405280403 2562815062922886607920605)
              ·
                refine ⟨961055648596082477970227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562815062922886607920605 961055648596082477970227)
                ·
                  refine ⟨1441583472894123716955341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961055648596082477970227 1441583472894123716955341)
                  ·
                    refine ⟨540593802335296393858253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441583472894123716955341 540593802335296393858253)
                    ·
                      rfl

theorem cell22_1579204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1579204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579204 prefixEnd_1579204 := by exact prefixLift 1579204
  have htrace : WordTrace (prefixWord ++ tailWord_1579204) baseStart_1579204 baseEnd_1579204 := by
    simpa [prefixWord, tailWord_1579204, baseEnd_1579204] using wordTrace_append hprefix tailTrace_1579204
  have hstable : (prefixWord ++ tailWord_1579204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579204).length < 2 ^ (prefixWord ++ tailWord_1579204).sum := by decide
  have hdescent : baseEnd_1579204 < baseStart_1579204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579234 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1579234 : Nat := 118140960795 + 1579234 * 2 ^ 59
def prefixEnd_1579234 : Nat := 4983230072969 + 3 ^ 40 * 1579234 * 2
def baseEnd_1579234 : Nat := 180201357316128771869387

theorem tailTrace_1579234 : CollatzResearch.WordTrace tailWord_1579234 prefixEnd_1579234 180201357316128771869387 := by
  unfold tailWord_1579234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399848990178101134866189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38399597307141603026309837 14399848990178101134866189)
  ·
    refine ⟨5399943371316787925574821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14399848990178101134866189 5399943371316787925574821)
    ·
      refine ⟨1012489382121897736045279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5399943371316787925574821 1012489382121897736045279)
      ·
        refine ⟨1518734073182846604067919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012489382121897736045279 1518734073182846604067919)
        ·
          refine ⟨2278101109774269906101879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518734073182846604067919 2278101109774269906101879)
          ·
            refine ⟨3417151664661404859152819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278101109774269906101879 3417151664661404859152819)
            ·
              refine ⟨5125727496992107288729229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417151664661404859152819 5125727496992107288729229)
              ·
                refine ⟨1922147811372040233273461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125727496992107288729229 1922147811372040233273461)
                ·
                  refine ⟨180201357316128771869387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1922147811372040233273461 180201357316128771869387)
                  ·
                    rfl

theorem cell22_1579234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1579234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579234 prefixEnd_1579234 := by exact prefixLift 1579234
  have htrace : WordTrace (prefixWord ++ tailWord_1579234) baseStart_1579234 baseEnd_1579234 := by
    simpa [prefixWord, tailWord_1579234, baseEnd_1579234] using wordTrace_append hprefix tailTrace_1579234
  have hstable : (prefixWord ++ tailWord_1579234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579234).length < 2 ^ (prefixWord ++ tailWord_1579234).sum := by decide
  have hdescent : baseEnd_1579234 < baseStart_1579234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579258 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1579258 : Nat := 118140960795 + 1579258 * 2 ^ 59
def prefixEnd_1579258 : Nat := 4983230072969 + 3 ^ 40 * 1579258 * 2
def baseEnd_1579258 : Nat := 540612287638858253008087

theorem tailTrace_1579258 : CollatzResearch.WordTrace tailWord_1579258 prefixEnd_1579258 540612287638858253008087 := by
  unfold tailWord_1579258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400067828156364159584607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38400180875083637758892285 14400067828156364159584607)
  ·
    refine ⟨21600101742234546239376911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14400067828156364159584607 21600101742234546239376911)
    ·
      refine ⟨32400152613351819359065367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21600101742234546239376911 32400152613351819359065367)
      ·
        refine ⟨48600228920027729038598051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32400152613351819359065367 48600228920027729038598051)
        ·
          refine ⟨72900343380041593557897077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48600228920027729038598051 72900343380041593557897077)
          ·
            refine ⟨6834407191878899396052851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72900343380041593557897077 6834407191878899396052851)
            ·
              refine ⟨10251610787818349094079277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834407191878899396052851 10251610787818349094079277)
              ·
                refine ⟨3844354045431880910279729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10251610787818349094079277 3844354045431880910279729)
                ·
                  refine ⟨2883265534073910682709797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844354045431880910279729 2883265534073910682709797)
                  ·
                    refine ⟨540612287638858253008087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883265534073910682709797 540612287638858253008087)
                    ·
                      rfl

theorem cell22_1579258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1579258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579258 prefixEnd_1579258 := by exact prefixLift 1579258
  have htrace : WordTrace (prefixWord ++ tailWord_1579258) baseStart_1579258 baseEnd_1579258 := by
    simpa [prefixWord, tailWord_1579258, baseEnd_1579258] using wordTrace_append hprefix tailTrace_1579258
  have hstable : (prefixWord ++ tailWord_1579258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579258).length < 2 ^ (prefixWord ++ tailWord_1579258).sum := by decide
  have hdescent : baseEnd_1579258 < baseStart_1579258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579290 : List Nat := [3, 1, 1, 3, 4, 2, 1, 7]
def baseStart_1579290 : Nat := 118140960795 + 1579290 * 2 ^ 59
def prefixEnd_1579290 : Nat := 4983230072969 + 3 ^ 40 * 1579290 * 2
def baseEnd_1579290 : Nat := 60069249099202315134221

theorem tailTrace_1579290 : CollatzResearch.WordTrace tailWord_1579290 prefixEnd_1579290 60069249099202315134221 := by
  unfold tailWord_1579290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400359612127381525875831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38400958965673017402335549 14400359612127381525875831)
  ·
    refine ⟨21600539418191072288813747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14400359612127381525875831 21600539418191072288813747)
    ·
      refine ⟨32400809127286608433220621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21600539418191072288813747 32400809127286608433220621)
      ·
        refine ⟨12150303422732478162457733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32400809127286608433220621 12150303422732478162457733)
        ·
          refine ⟨2278181891762339655460825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12150303422732478162457733 2278181891762339655460825)
          ·
            refine ⟨1708636418821754741595619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278181891762339655460825 1708636418821754741595619)
            ·
              refine ⟨2562954628232632112393429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708636418821754741595619 2562954628232632112393429)
              ·
                refine ⟨60069249099202315134221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2562954628232632112393429 60069249099202315134221)
                ·
                  rfl

theorem cell22_1579290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_1579290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579290 prefixEnd_1579290 := by exact prefixLift 1579290
  have htrace : WordTrace (prefixWord ++ tailWord_1579290) baseStart_1579290 baseEnd_1579290 := by
    simpa [prefixWord, tailWord_1579290, baseEnd_1579290] using wordTrace_append hprefix tailTrace_1579290
  have hstable : (prefixWord ++ tailWord_1579290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579290).length < 2 ^ (prefixWord ++ tailWord_1579290).sum := by decide
  have hdescent : baseEnd_1579290 < baseStart_1579290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579294 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1579294 : Nat := 118140960795 + 1579294 * 2 ^ 59
def prefixEnd_1579294 : Nat := 4983230072969 + 3 ^ 40 * 1579294 * 2
def baseEnd_1579294 : Nat := 540624611174566159107977

theorem tailTrace_1579294 : CollatzResearch.WordTrace tailWord_1579294 prefixEnd_1579294 540624611174566159107977 := by
  unfold tailWord_1579294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200198042561879348331117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38401056226996689857765957 7200198042561879348331117)
  ·
    refine ⟨2700074265960704755624169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7200198042561879348331117 2700074265960704755624169)
    ·
      refine ⟨2025055699470528566718127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2700074265960704755624169 2025055699470528566718127)
      ·
        refine ⟨3037583549205792850077191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025055699470528566718127 3037583549205792850077191)
        ·
          refine ⟨4556375323808689275115787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037583549205792850077191 4556375323808689275115787)
          ·
            refine ⟨6834562985713033912673681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556375323808689275115787 6834562985713033912673681)
            ·
              refine ⟨5125922239284775434505261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834562985713033912673681 5125922239284775434505261)
              ·
                refine ⟨1922220839731790787939473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125922239284775434505261 1922220839731790787939473)
                ·
                  refine ⟨1441665629798843090954605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922220839731790787939473 1441665629798843090954605)
                  ·
                    refine ⟨540624611174566159107977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441665629798843090954605 540624611174566159107977)
                    ·
                      rfl

theorem cell22_1579294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1579294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579294 prefixEnd_1579294 := by exact prefixLift 1579294
  have htrace : WordTrace (prefixWord ++ tailWord_1579294) baseStart_1579294 baseEnd_1579294 := by
    simpa [prefixWord, tailWord_1579294, baseEnd_1579294] using wordTrace_append hprefix tailTrace_1579294
  have hstable : (prefixWord ++ tailWord_1579294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579294).length < 2 ^ (prefixWord ++ tailWord_1579294).sum := by decide
  have hdescent : baseEnd_1579294 < baseStart_1579294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579309 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1579309 : Nat := 118140960795 + 1579309 * 2 ^ 59
def prefixEnd_1579309 : Nat := 4983230072969 + 3 ^ 40 * 1579309 * 2
def baseEnd_1579309 : Nat := 540629745981111119982931

theorem tailTrace_1579309 : CollatzResearch.WordTrace tailWord_1579309 prefixEnd_1579309 540629745981111119982931 := by
  unfold tailWord_1579309
  simp only [CollatzResearch.WordTrace]
  refine ⟨57602131435440692348444981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38401420956960461565629987 57602131435440692348444981)
  ·
    refine ⟨5400199822072564907666717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57602131435440692348444981 5400199822072564907666717)
    ·
      refine ⟨2025074933277211840375019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5400199822072564907666717 2025074933277211840375019)
      ·
        refine ⟨3037612399915817760562529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025074933277211840375019 3037612399915817760562529)
        ·
          refine ⟨2278209299936863320421897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3037612399915817760562529 2278209299936863320421897)
          ·
            refine ⟨1708656974952647490316423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278209299936863320421897 1708656974952647490316423)
            ·
              refine ⟨2562985462428971235474635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708656974952647490316423 2562985462428971235474635)
              ·
                refine ⟨3844478193643456853211953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562985462428971235474635 3844478193643456853211953)
                ·
                  refine ⟨2883358645232592639908965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844478193643456853211953 2883358645232592639908965)
                  ·
                    refine ⟨540629745981111119982931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883358645232592639908965 540629745981111119982931)
                    ·
                      rfl

theorem cell22_1579309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1579309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579309 prefixEnd_1579309 := by exact prefixLift 1579309
  have htrace : WordTrace (prefixWord ++ tailWord_1579309) baseStart_1579309 baseEnd_1579309 := by
    simpa [prefixWord, tailWord_1579309, baseEnd_1579309] using wordTrace_append hprefix tailTrace_1579309
  have hstable : (prefixWord ++ tailWord_1579309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579309).length < 2 ^ (prefixWord ++ tailWord_1579309).sum := by decide
  have hdescent : baseEnd_1579309 < baseStart_1579309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579322 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_1579322 : Nat := 118140960795 + 1579322 * 2 ^ 59
def prefixEnd_1579322 : Nat := 4983230072969 + 3 ^ 40 * 1579322 * 2
def baseEnd_1579322 : Nat := 540634196146783419407891

theorem tailTrace_1579322 : CollatzResearch.WordTrace tailWord_1579322 prefixEnd_1579322 540634196146783419407891 := by
  unfold tailWord_1579322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400651396098398892167055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38401737056262397045778813 14400651396098398892167055)
  ·
    refine ⟨21600977094147598338250583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14400651396098398892167055 21600977094147598338250583)
    ·
      refine ⟨32401465641221397507375875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21600977094147598338250583 32401465641221397507375875)
      ·
        refine ⟨48602198461832096261063813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32401465641221397507375875 48602198461832096261063813)
        ·
          refine ⟨9112912211593518048949465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48602198461832096261063813 9112912211593518048949465)
          ·
            refine ⟨6834684158695138536712099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9112912211593518048949465 6834684158695138536712099)
            ·
              refine ⟨10252026238042707805068149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834684158695138536712099 10252026238042707805068149)
              ·
                refine ⟨961127459816503856725139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10252026238042707805068149 961127459816503856725139)
                ·
                  refine ⟨1441691189724755785087709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961127459816503856725139 1441691189724755785087709)
                  ·
                    refine ⟨540634196146783419407891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441691189724755785087709 540634196146783419407891)
                    ·
                      rfl

theorem cell22_1579322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_1579322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579322 prefixEnd_1579322 := by exact prefixLift 1579322
  have htrace : WordTrace (prefixWord ++ tailWord_1579322) baseStart_1579322 baseEnd_1579322 := by
    simpa [prefixWord, tailWord_1579322, baseEnd_1579322] using wordTrace_append hprefix tailTrace_1579322
  have hstable : (prefixWord ++ tailWord_1579322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579322).length < 2 ^ (prefixWord ++ tailWord_1579322).sum := by decide
  have hdescent : baseEnd_1579322 < baseStart_1579322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579358 : List Nat := [4, 4, 2, 1, 1, 2, 2, 6]
def baseStart_1579358 : Nat := 118140960795 + 1579358 * 2 ^ 59
def prefixEnd_1579358 : Nat := 4983230072969 + 3 ^ 40 * 1579358 * 2
def baseEnd_1579358 : Nat := 60071835520276813945309

theorem tailTrace_1579358 : CollatzResearch.WordTrace tailWord_1579358 prefixEnd_1579358 60071835520276813945309 := by
  unfold tailWord_1579358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200489826532896714622341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38402612408175449144652485 7200489826532896714622341)
  ·
    refine ⟨1350091842474918133991689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7200489826532896714622341 1350091842474918133991689)
    ·
      refine ⟨1012568881856188600493767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1350091842474918133991689 1012568881856188600493767)
      ·
        refine ⟨1518853322784282900740651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012568881856188600493767 1518853322784282900740651)
        ·
          refine ⟨2278279984176424351110977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518853322784282900740651 2278279984176424351110977)
          ·
            refine ⟨1708709988132318263333233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278279984176424351110977 1708709988132318263333233)
            ·
              refine ⟨1281532491099238697499925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708709988132318263333233 1281532491099238697499925)
              ·
                refine ⟨60071835520276813945309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1281532491099238697499925 60071835520276813945309)
                ·
                  rfl

theorem cell22_1579358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_1579358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579358 prefixEnd_1579358 := by exact prefixLift 1579358
  have htrace : WordTrace (prefixWord ++ tailWord_1579358) baseStart_1579358 baseEnd_1579358 := by
    simpa [prefixWord, tailWord_1579358, baseEnd_1579358] using wordTrace_append hprefix tailTrace_1579358
  have hstable : (prefixWord ++ tailWord_1579358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579358).length < 2 ^ (prefixWord ++ tailWord_1579358).sum := by decide
  have hdescent : baseEnd_1579358 < baseStart_1579358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579363 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 6]
def baseStart_1579363 : Nat := 118140960795 + 1579363 * 2 ^ 59
def prefixEnd_1579363 : Nat := 4983230072969 + 3 ^ 40 * 1579363 * 2
def baseEnd_1579363 : Nat := 180216077094890993044255

theorem tailTrace_1579363 : CollatzResearch.WordTrace tailWord_1579363 prefixEnd_1579363 180216077094890993044255 := by
  unfold tailWord_1579363
  simp only [CollatzResearch.WordTrace]
  refine ⟨57604100977245059570910743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38402733984830039713940495 57604100977245059570910743)
  ·
    refine ⟨86406151465867589356366115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57604100977245059570910743 86406151465867589356366115)
    ·
      refine ⟨129609227198801384034549173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86406151465867589356366115 129609227198801384034549173)
      ·
        refine ⟨12150865049887629753238985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129609227198801384034549173 12150865049887629753238985)
        ·
          refine ⟨9113148787415722314929239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12150865049887629753238985 9113148787415722314929239)
          ·
            refine ⟨13669723181123583472393859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113148787415722314929239 13669723181123583472393859)
            ·
              refine ⟨20504584771685375208590789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13669723181123583472393859 20504584771685375208590789)
              ·
                refine ⟨3844609644691007851610773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20504584771685375208590789 3844609644691007851610773)
                ·
                  refine ⟨180216077094890993044255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3844609644691007851610773 180216077094890993044255)
                  ·
                    rfl

theorem cell22_1579363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_1579363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579363 prefixEnd_1579363 := by exact prefixLift 1579363
  have htrace : WordTrace (prefixWord ++ tailWord_1579363) baseStart_1579363 baseEnd_1579363 := by
    simpa [prefixWord, tailWord_1579363, baseEnd_1579363] using wordTrace_append hprefix tailTrace_1579363
  have hstable : (prefixWord ++ tailWord_1579363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579363).length < 2 ^ (prefixWord ++ tailWord_1579363).sum := by decide
  have hdescent : baseEnd_1579363 < baseStart_1579363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579365 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_1579365 : Nat := 118140960795 + 1579365 * 2 ^ 59
def prefixEnd_1579365 : Nat := 4983230072969 + 3 ^ 40 * 1579365 * 2
def baseEnd_1579365 : Nat := 540648915925545640582759

theorem tailTrace_1579365 : CollatzResearch.WordTrace tailWord_1579365 prefixEnd_1579365 540648915925545640582759 := by
  unfold tailWord_1579365
  simp only [CollatzResearch.WordTrace]
  refine ⟨57604173923237813912483549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38402782615491875941655699 57604173923237813912483549)
  ·
    refine ⟨21601565221214180217181331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57604173923237813912483549 21601565221214180217181331)
    ·
      refine ⟨32402347831821270325771997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21601565221214180217181331 32402347831821270325771997)
      ·
        refine ⟨12150880436932976372164499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32402347831821270325771997 12150880436932976372164499)
        ·
          refine ⟨18226320655399464558246749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150880436932976372164499 18226320655399464558246749)
          ·
            refine ⟨6834870245774799209342531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18226320655399464558246749 6834870245774799209342531)
            ·
              refine ⟨10252305368662198814013797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834870245774799209342531 10252305368662198814013797)
              ·
                refine ⟨1922307256624162277627587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10252305368662198814013797 1922307256624162277627587)
                ·
                  refine ⟨2883460884936243416441381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922307256624162277627587 2883460884936243416441381)
                  ·
                    refine ⟨540648915925545640582759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883460884936243416441381 540648915925545640582759)
                    ·
                      rfl

theorem cell22_1579365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_1579365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579365 prefixEnd_1579365 := by exact prefixLift 1579365
  have htrace : WordTrace (prefixWord ++ tailWord_1579365) baseStart_1579365 baseEnd_1579365 := by
    simpa [prefixWord, tailWord_1579365, baseEnd_1579365] using wordTrace_append hprefix tailTrace_1579365
  have hstable : (prefixWord ++ tailWord_1579365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579365).length < 2 ^ (prefixWord ++ tailWord_1579365).sum := by decide
  have hdescent : baseEnd_1579365 < baseStart_1579365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579485 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1579485 : Nat := 118140960795 + 1579485 * 2 ^ 59
def prefixEnd_1579485 : Nat := 4983230072969 + 3 ^ 40 * 1579485 * 2
def baseEnd_1579485 : Nat := 540689994377905327582391

theorem tailTrace_1579485 : CollatzResearch.WordTrace tailWord_1579485 prefixEnd_1579485 540689994377905327582391 := by
  unfold tailWord_1579485
  simp only [CollatzResearch.WordTrace]
  refine ⟨57608550682803074406851909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38405700455202049604567939 57608550682803074406851909)
  ·
    refine ⟨10801603253025576451284733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57608550682803074406851909 10801603253025576451284733)
    ·
      refine ⟨4050601219884591169231775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10801603253025576451284733 4050601219884591169231775)
      ·
        refine ⟨6075901829826886753847663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050601219884591169231775 6075901829826886753847663)
        ·
          refine ⟨9113852744740330130771495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075901829826886753847663 9113852744740330130771495)
          ·
            refine ⟨13670779117110495196157243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113852744740330130771495 13670779117110495196157243)
            ·
              refine ⟨20506168675665742794235865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13670779117110495196157243 20506168675665742794235865)
              ·
                refine ⟨15379626506749307095676899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20506168675665742794235865 15379626506749307095676899)
                ·
                  refine ⟨23069439760123960643515349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15379626506749307095676899 23069439760123960643515349)
                  ·
                    refine ⟨540689994377905327582391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23069439760123960643515349 540689994377905327582391)
                    ·
                      rfl

theorem cell22_1579485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1579485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579485 prefixEnd_1579485 := by exact prefixLift 1579485
  have htrace : WordTrace (prefixWord ++ tailWord_1579485) baseStart_1579485 baseEnd_1579485 := by
    simpa [prefixWord, tailWord_1579485, baseEnd_1579485] using wordTrace_append hprefix tailTrace_1579485
  have hstable : (prefixWord ++ tailWord_1579485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579485).length < 2 ^ (prefixWord ++ tailWord_1579485).sum := by decide
  have hdescent : baseEnd_1579485 < baseStart_1579485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579491 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 1, 3]
def baseStart_1579491 : Nat := 118140960795 + 1579491 * 2 ^ 59
def prefixEnd_1579491 : Nat := 4983230072969 + 3 ^ 40 * 1579491 * 2
def baseEnd_1579491 : Nat := 540692048300523311932373

theorem tailTrace_1579491 : CollatzResearch.WordTrace tailWord_1579491 prefixEnd_1579491 540692048300523311932373 := by
  unfold tailWord_1579491
  simp only [CollatzResearch.WordTrace]
  refine ⟨57608769520781337431570327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38405846347187558287713551 57608769520781337431570327)
  ·
    refine ⟨86413154281172006147355491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57608769520781337431570327 86413154281172006147355491)
    ·
      refine ⟨129619731421758009221033237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86413154281172006147355491 129619731421758009221033237)
      ·
        refine ⟨6075924910394906682235933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129619731421758009221033237 6075924910394906682235933)
        ·
          refine ⟨2278471841398090005838475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6075924910394906682235933 2278471841398090005838475)
          ·
            refine ⟨3417707762097135008757713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278471841398090005838475 3417707762097135008757713)
            ·
              refine ⟨2563280821572851256568285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417707762097135008757713 2563280821572851256568285)
              ·
                refine ⟨961230308089819221213107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2563280821572851256568285 961230308089819221213107)
                ·
                  refine ⟨1441845462134728831819661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961230308089819221213107 1441845462134728831819661)
                  ·
                    refine ⟨540692048300523311932373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441845462134728831819661 540692048300523311932373)
                    ·
                      rfl

theorem cell22_1579491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 3].length) (baseStart_1579491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579491 prefixEnd_1579491 := by exact prefixLift 1579491
  have htrace : WordTrace (prefixWord ++ tailWord_1579491) baseStart_1579491 baseEnd_1579491 := by
    simpa [prefixWord, tailWord_1579491, baseEnd_1579491] using wordTrace_append hprefix tailTrace_1579491
  have hstable : (prefixWord ++ tailWord_1579491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579491).length < 2 ^ (prefixWord ++ tailWord_1579491).sum := by decide
  have hdescent : baseEnd_1579491 < baseStart_1579491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579534 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1579534 : Nat := 118140960795 + 1579534 * 2 ^ 59
def prefixEnd_1579534 : Nat := 4983230072969 + 3 ^ 40 * 1579534 * 2
def baseEnd_1579534 : Nat := 540706768079285533107241

theorem tailTrace_1579534 : CollatzResearch.WordTrace tailWord_1579534 prefixEnd_1579534 540706768079285533107241 := by
  unfold tailWord_1579534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201292232453194471923207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38406891906417037183590437 7201292232453194471923207)
  ·
    refine ⟨10801938348679791707884811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7201292232453194471923207 10801938348679791707884811)
    ·
      refine ⟨16202907523019687561827217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10801938348679791707884811 16202907523019687561827217)
      ·
        refine ⟨12152180642264765671370413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16202907523019687561827217 12152180642264765671370413)
        ·
          refine ⟨4557067740849287126763905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12152180642264765671370413 4557067740849287126763905)
          ·
            refine ⟨3417800805636965345072929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4557067740849287126763905 3417800805636965345072929)
            ·
              refine ⟨2563350604227724008804697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417800805636965345072929 2563350604227724008804697)
              ·
                refine ⟨1922512953170793006603523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563350604227724008804697 1922512953170793006603523)
                ·
                  refine ⟨2883769429756189509905285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922512953170793006603523 2883769429756189509905285)
                  ·
                    refine ⟨540706768079285533107241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883769429756189509905285 540706768079285533107241)
                    ·
                      rfl

theorem cell22_1579534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1579534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579534 prefixEnd_1579534 := by exact prefixLift 1579534
  have htrace : WordTrace (prefixWord ++ tailWord_1579534) baseStart_1579534 baseEnd_1579534 := by
    simpa [prefixWord, tailWord_1579534, baseEnd_1579534] using wordTrace_append hprefix tailTrace_1579534
  have hstable : (prefixWord ++ tailWord_1579534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579534).length < 2 ^ (prefixWord ++ tailWord_1579534).sum := by decide
  have hdescent : baseEnd_1579534 < baseStart_1579534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579549 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 4]
def baseStart_1579549 : Nat := 118140960795 + 1579549 * 2 ^ 59
def prefixEnd_1579549 : Nat := 4983230072969 + 3 ^ 40 * 1579549 * 2
def baseEnd_1579549 : Nat := 180237300961943497994065

theorem tailTrace_1579549 : CollatzResearch.WordTrace tailWord_1579549 prefixEnd_1579549 180237300961943497994065 := by
  unfold tailWord_1579549
  simp only [CollatzResearch.WordTrace]
  refine ⟨57610884954571213337181701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38407256636380808891454467 57610884954571213337181701)
  ·
    refine ⟨10802040928982102500721569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57610884954571213337181701 10802040928982102500721569)
    ·
      refine ⟨8101530696736576875541177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10802040928982102500721569 8101530696736576875541177)
      ·
        refine ⟨6076148022552432656655883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8101530696736576875541177 6076148022552432656655883)
        ·
          refine ⟨9114222033828648984983825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076148022552432656655883 9114222033828648984983825)
          ·
            refine ⟨6835666525371486738737869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9114222033828648984983825 6835666525371486738737869)
            ·
              refine ⟨2563374947014307527026701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6835666525371486738737869 2563374947014307527026701)
              ·
                refine ⟨961265605130365322635013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2563374947014307527026701 961265605130365322635013)
                ·
                  refine ⟨180237300961943497994065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961265605130365322635013 180237300961943497994065)
                  ·
                    rfl

theorem cell22_1579549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_1579549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579549 prefixEnd_1579549 := by exact prefixLift 1579549
  have htrace : WordTrace (prefixWord ++ tailWord_1579549) baseStart_1579549 baseEnd_1579549 := by
    simpa [prefixWord, tailWord_1579549, baseEnd_1579549] using wordTrace_append hprefix tailTrace_1579549
  have hstable : (prefixWord ++ tailWord_1579549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579549).length < 2 ^ (prefixWord ++ tailWord_1579549).sum := by decide
  have hdescent : baseEnd_1579549 < baseStart_1579549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579562 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1579562 : Nat := 118140960795 + 1579562 * 2 ^ 59
def prefixEnd_1579562 : Nat := 4983230072969 + 3 ^ 40 * 1579562 * 2
def baseEnd_1579562 : Nat := 540716353051502793407155

theorem tailTrace_1579562 : CollatzResearch.WordTrace tailWord_1579562 prefixEnd_1579562 540716353051502793407155 := by
  unfold tailWord_1579562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402839775881029139351235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38407572735682744371603293 14402839775881029139351235)
  ·
    refine ⟨21604259663821543709026853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14402839775881029139351235 21604259663821543709026853)
    ·
      refine ⟨4050798686966539445442535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21604259663821543709026853 4050798686966539445442535)
      ·
        refine ⟨6076198030449809168163803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050798686966539445442535 6076198030449809168163803)
        ·
          refine ⟨9114297045674713752245705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076198030449809168163803 9114297045674713752245705)
          ·
            refine ⟨6835722784256035314184279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9114297045674713752245705 6835722784256035314184279)
            ·
              refine ⟨10253584176384052971276419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835722784256035314184279 10253584176384052971276419)
              ·
                refine ⟨15380376264576079456914629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10253584176384052971276419 15380376264576079456914629)
                ·
                  refine ⟨2883820549608014898171493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15380376264576079456914629 2883820549608014898171493)
                  ·
                    refine ⟨540716353051502793407155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883820549608014898171493 540716353051502793407155)
                    ·
                      rfl

theorem cell22_1579562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1579562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579562 prefixEnd_1579562 := by exact prefixLift 1579562
  have htrace : WordTrace (prefixWord ++ tailWord_1579562) baseStart_1579562 baseEnd_1579562 := by
    simpa [prefixWord, tailWord_1579562, baseEnd_1579562] using wordTrace_append hprefix tailTrace_1579562
  have hstable : (prefixWord ++ tailWord_1579562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579562).length < 2 ^ (prefixWord ++ tailWord_1579562).sum := by decide
  have hdescent : baseEnd_1579562 < baseStart_1579562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579566 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_1579566 : Nat := 118140960795 + 1579566 * 2 ^ 59
def prefixEnd_1579566 : Nat := 4983230072969 + 3 ^ 40 * 1579566 * 2
def baseEnd_1579566 : Nat := 180239240777749372102381

theorem tailTrace_1579566 : CollatzResearch.WordTrace tailWord_1579566 prefixEnd_1579566 180239240777749372102381 := by
  unfold tailWord_1579566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201438124438703155068819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38407669997006416827033701 7201438124438703155068819)
  ·
    refine ⟨10802157186658054732603229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7201438124438703155068819 10802157186658054732603229)
    ·
      refine ⟨4050808944996770524726211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10802157186658054732603229 4050808944996770524726211)
      ·
        refine ⟨6076213417495155787089317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050808944996770524726211 6076213417495155787089317)
        ·
          refine ⟨1139290015780341710079247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6076213417495155787089317 1139290015780341710079247)
          ·
            refine ⟨1708935023670512565118871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139290015780341710079247 1708935023670512565118871)
            ·
              refine ⟨2563402535505768847678307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708935023670512565118871 2563402535505768847678307)
              ·
                refine ⟨3845103803258653271517461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563402535505768847678307 3845103803258653271517461)
                ·
                  refine ⟨180239240777749372102381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3845103803258653271517461 180239240777749372102381)
                  ·
                    rfl

theorem cell22_1579566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_1579566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579566 prefixEnd_1579566 := by exact prefixLift 1579566
  have htrace : WordTrace (prefixWord ++ tailWord_1579566) baseStart_1579566 baseEnd_1579566 := by
    simpa [prefixWord, tailWord_1579566, baseEnd_1579566] using wordTrace_append hprefix tailTrace_1579566
  have hstable : (prefixWord ++ tailWord_1579566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579566).length < 2 ^ (prefixWord ++ tailWord_1579566).sum := by decide
  have hdescent : baseEnd_1579566 < baseStart_1579566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579581 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_1579581 : Nat := 118140960795 + 1579581 * 2 ^ 59
def prefixEnd_1579581 : Nat := 4983230072969 + 3 ^ 40 * 1579581 * 2
def baseEnd_1579581 : Nat := 540722857139793077182097

theorem tailTrace_1579581 : CollatzResearch.WordTrace tailWord_1579581 prefixEnd_1579581 540722857139793077182097 := by
  unfold tailWord_1579581
  simp only [CollatzResearch.WordTrace]
  refine ⟨57612052090455282802346597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38408034726970188534897731 57612052090455282802346597)
  ·
    refine ⟨10802259766960365525439987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57612052090455282802346597 10802259766960365525439987)
    ·
      refine ⟨16203389650440548288159981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802259766960365525439987 16203389650440548288159981)
      ·
        refine ⟨6076271118915205608059993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16203389650440548288159981 6076271118915205608059993)
        ·
          refine ⟨4557203339186404206044995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6076271118915205608059993 4557203339186404206044995)
          ·
            refine ⟨6835805008779606309067493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4557203339186404206044995 6835805008779606309067493)
            ·
              refine ⟨1281713439146176182950155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6835805008779606309067493 1281713439146176182950155)
              ·
                refine ⟨1922570158719264274425233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281713439146176182950155 1922570158719264274425233)
                ·
                  refine ⟨1441927619039448205818925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922570158719264274425233 1441927619039448205818925)
                  ·
                    refine ⟨540722857139793077182097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441927619039448205818925 540722857139793077182097)
                    ·
                      rfl

theorem cell22_1579581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_1579581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579581 prefixEnd_1579581 := by exact prefixLift 1579581
  have htrace : WordTrace (prefixWord ++ tailWord_1579581) baseStart_1579581 baseEnd_1579581 := by
    simpa [prefixWord, tailWord_1579581, baseEnd_1579581] using wordTrace_append hprefix tailTrace_1579581
  have hstable : (prefixWord ++ tailWord_1579581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579581).length < 2 ^ (prefixWord ++ tailWord_1579581).sum := by decide
  have hdescent : baseEnd_1579581 < baseStart_1579581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579592 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1579592 : Nat := 118140960795 + 1579592 * 2 ^ 59
def prefixEnd_1579592 : Nat := 4983230072969 + 3 ^ 40 * 1579592 * 2
def baseEnd_1579592 : Nat := 540726622664592715157063

theorem tailTrace_1579592 : CollatzResearch.WordTrace tailWord_1579592 prefixEnd_1579592 540726622664592715157063 := by
  unfold tailWord_1579592
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806226646707715840498515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38408302195610287787331353 28806226646707715840498515)
  ·
    refine ⟨43209339970061573760747773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28806226646707715840498515 43209339970061573760747773)
    ·
      refine ⟨16203502488773090160280415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43209339970061573760747773 16203502488773090160280415)
      ·
        refine ⟨24305253733159635240420623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16203502488773090160280415 24305253733159635240420623)
        ·
          refine ⟨36457880599739452860630935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24305253733159635240420623 36457880599739452860630935)
          ·
            refine ⟨54686820899609179290946403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36457880599739452860630935 54686820899609179290946403)
            ·
              refine ⟨82030231349413768936419605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54686820899609179290946403 82030231349413768936419605)
              ·
                refine ⟨3845167094503770418894669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82030231349413768936419605 3845167094503770418894669)
                ·
                  refine ⟨1441937660438913907085501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3845167094503770418894669 1441937660438913907085501)
                  ·
                    refine ⟨540726622664592715157063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441937660438913907085501 540726622664592715157063)
                    ·
                      rfl

theorem cell22_1579592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1579592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579592 prefixEnd_1579592 := by exact prefixLift 1579592
  have htrace : WordTrace (prefixWord ++ tailWord_1579592) baseStart_1579592 baseEnd_1579592 := by
    simpa [prefixWord, tailWord_1579592, baseEnd_1579592] using wordTrace_append hprefix tailTrace_1579592
  have hstable : (prefixWord ++ tailWord_1579592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579592).length < 2 ^ (prefixWord ++ tailWord_1579592).sum := by decide
  have hdescent : baseEnd_1579592 < baseStart_1579592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
