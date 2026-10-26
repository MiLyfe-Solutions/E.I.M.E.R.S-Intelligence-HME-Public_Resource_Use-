import V185TrunkScan23Chunk1206

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7150026 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_7150026 : Nat := 118140960795 + 7150026 * 2 ^ 59
def prefixEnd_7150026 : Nat := 4983230072969 + 3 ^ 40 * 7150026 * 2
def baseEnd_7150026 : Nat := 3671400030144147724092635

theorem tailTrace_7150026 : CollatzResearch.WordTrace tailWord_7150026 prefixEnd_7150026 3671400030144147724092635 := by
  unfold tailWord_7150026
  simp only [CollatzResearch.WordTrace]
  refine ⟨65195718098671101016751483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173855248263122936044670621 65195718098671101016751483)
  ·
    refine ⟨97793577148006651525127225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65195718098671101016751483 97793577148006651525127225)
    ·
      refine ⟨73345182861004988643845419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97793577148006651525127225 73345182861004988643845419)
      ·
        refine ⟨110017774291507482965768129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73345182861004988643845419 110017774291507482965768129)
        ·
          refine ⟨82513330718630612224326097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110017774291507482965768129 82513330718630612224326097)
          ·
            refine ⟨61884998038972959168244573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82513330718630612224326097 61884998038972959168244573)
            ·
              refine ⟨23206874264614859688091715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61884998038972959168244573 23206874264614859688091715)
              ·
                refine ⟨34810311396922289532137573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23206874264614859688091715 34810311396922289532137573)
                ·
                  refine ⟨6526933386922929287275795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34810311396922289532137573 6526933386922929287275795)
                  ·
                    refine ⟨9790400080384393930913693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526933386922929287275795 9790400080384393930913693)
                    ·
                      refine ⟨3671400030144147724092635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790400080384393930913693 3671400030144147724092635)
                      ·
                        rfl

theorem cell23_7150026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_7150026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150026 prefixEnd_7150026 := by exact prefixLift 7150026
  have htrace : WordTrace (prefixWord ++ tailWord_7150026) baseStart_7150026 baseEnd_7150026 := by
    simpa [prefixWord, tailWord_7150026, baseEnd_7150026] using wordTrace_append hprefix tailTrace_7150026
  have hstable : (prefixWord ++ tailWord_7150026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150026).length < 2 ^ (prefixWord ++ tailWord_7150026).sum := by decide
  have hdescent : baseEnd_7150026 < baseStart_7150026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150050 : List Nat := [3, 3, 3, 2, 1, 2, 2, 7]
def baseStart_7150050 : Nat := 118140960795 + 7150050 * 2 ^ 59
def prefixEnd_7150050 : Nat := 4983230072969 + 3 ^ 40 * 7150050 * 2
def baseEnd_7150050 : Nat := 135978235321476134451575

theorem tailTrace_7150050 : CollatzResearch.WordTrace tailWord_7150050 prefixEnd_7150050 135978235321476134451575 := by
  unfold tailWord_7150050
  simp only [CollatzResearch.WordTrace]
  refine ⟨65195936936649364041469901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173855831831064970777253069 65195936936649364041469901)
  ·
    refine ⟨24448476351243511515551213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65195936936649364041469901 24448476351243511515551213)
    ·
      refine ⟨9168178631716316818331705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24448476351243511515551213 9168178631716316818331705)
      ·
        refine ⟨6876133973787237613748779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9168178631716316818331705 6876133973787237613748779)
        ·
          refine ⟨10314200960680856420623169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876133973787237613748779 10314200960680856420623169)
          ·
            refine ⟨7735650720510642315467377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10314200960680856420623169 7735650720510642315467377)
            ·
              refine ⟨5801738040382981736600533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7735650720510642315467377 5801738040382981736600533)
              ·
                refine ⟨135978235321476134451575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5801738040382981736600533 135978235321476134451575)
                ·
                  rfl

theorem cell23_7150050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_7150050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150050 prefixEnd_7150050 := by exact prefixLift 7150050
  have htrace : WordTrace (prefixWord ++ tailWord_7150050) baseStart_7150050 baseEnd_7150050 := by
    simpa [prefixWord, tailWord_7150050, baseEnd_7150050] using wordTrace_append hprefix tailTrace_7150050
  have hstable : (prefixWord ++ tailWord_7150050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150050).length < 2 ^ (prefixWord ++ tailWord_7150050).sum := by decide
  have hdescent : baseEnd_7150050 < baseStart_7150050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150083 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 2, 2, 2]
def baseStart_7150083 : Nat := 118140960795 + 7150083 * 2 ^ 59
def prefixEnd_7150083 : Nat := 4983230072969 + 3 ^ 40 * 7150083 * 2
def baseEnd_7150083 : Nat := 3671429298541454001079873

theorem tailTrace_7150083 : CollatzResearch.WordTrace tailWord_7150083 prefixEnd_7150083 3671429298541454001079873 := by
  unfold tailWord_7150083
  simp only [CollatzResearch.WordTrace]
  refine ⟨260784951355477902801830903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173856634236985268534553935 260784951355477902801830903)
  ·
    refine ⟨391177427033216854202746355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260784951355477902801830903 391177427033216854202746355)
    ·
      refine ⟨586766140549825281304119533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391177427033216854202746355 586766140549825281304119533)
      ·
        refine ⟨220037302706184480489044825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586766140549825281304119533 220037302706184480489044825)
        ·
          refine ⟨165027977029638360366783619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220037302706184480489044825 165027977029638360366783619)
          ·
            refine ⟨247541965544457540550175429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165027977029638360366783619 247541965544457540550175429)
            ·
              refine ⟨46414118539585788853157893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247541965544457540550175429 46414118539585788853157893)
              ·
                refine ⟨8702647226172335409967105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46414118539585788853157893 8702647226172335409967105)
                ·
                  refine ⟨6526985419629251557475329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702647226172335409967105 6526985419629251557475329)
                  ·
                    refine ⟨4895239064721938668106497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6526985419629251557475329 4895239064721938668106497)
                    ·
                      refine ⟨3671429298541454001079873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895239064721938668106497 3671429298541454001079873)
                      ·
                        rfl

theorem cell23_7150083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_7150083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150083 prefixEnd_7150083 := by exact prefixLift 7150083
  have htrace : WordTrace (prefixWord ++ tailWord_7150083) baseStart_7150083 baseEnd_7150083 := by
    simpa [prefixWord, tailWord_7150083, baseEnd_7150083] using wordTrace_append hprefix tailTrace_7150083
  have hstable : (prefixWord ++ tailWord_7150083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150083).length < 2 ^ (prefixWord ++ tailWord_7150083).sum := by decide
  have hdescent : baseEnd_7150083 < baseStart_7150083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150099 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 3]
def baseStart_7150099 : Nat := 118140960795 + 7150099 * 2 ^ 59
def prefixEnd_7150099 : Nat := 4983230072969 + 3 ^ 40 * 7150099 * 2
def baseEnd_7150099 : Nat := 3671437514231925938479799

theorem tailTrace_7150099 : CollatzResearch.WordTrace tailWord_7150099 prefixEnd_7150099 3671437514231925938479799 := by
  unfold tailWord_7150099
  simp only [CollatzResearch.WordTrace]
  refine ⟨260785534923419937534413351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173857023282279958356275567 260785534923419937534413351)
  ·
    refine ⟨391178302385129906301620027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260785534923419937534413351 391178302385129906301620027)
    ·
      refine ⟨586767453577694859452430041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391178302385129906301620027 586767453577694859452430041)
      ·
        refine ⟨440075590183271144589322531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586767453577694859452430041 440075590183271144589322531)
        ·
          refine ⟨660113385274906716883983797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440075590183271144589322531 660113385274906716883983797)
          ·
            refine ⟨61885629869522504707873481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 660113385274906716883983797 61885629869522504707873481)
            ·
              refine ⟨46414222402141878530905111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61885629869522504707873481 46414222402141878530905111)
              ·
                refine ⟨69621333603212817796357667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46414222402141878530905111 69621333603212817796357667)
                ·
                  refine ⟨104432000404819226694536501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69621333603212817796357667 104432000404819226694536501)
                  ·
                    refine ⟨9790500037951802502612797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104432000404819226694536501 9790500037951802502612797)
                    ·
                      refine ⟨3671437514231925938479799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790500037951802502612797 3671437514231925938479799)
                      ·
                        rfl

theorem cell23_7150099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_7150099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150099 prefixEnd_7150099 := by exact prefixLift 7150099
  have htrace : WordTrace (prefixWord ++ tailWord_7150099) baseStart_7150099 baseEnd_7150099 := by
    simpa [prefixWord, tailWord_7150099, baseEnd_7150099] using wordTrace_append hprefix tailTrace_7150099
  have hstable : (prefixWord ++ tailWord_7150099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150099).length < 2 ^ (prefixWord ++ tailWord_7150099).sum := by decide
  have hdescent : baseEnd_7150099 < baseStart_7150099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150129 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_7150129 : Nat := 118140960795 + 7150129 * 2 ^ 59
def prefixEnd_7150129 : Nat := 4983230072969 + 3 ^ 40 * 7150129 * 2
def baseEnd_7150129 : Nat := 3671452918651560821104661

theorem tailTrace_7150129 : CollatzResearch.WordTrace tailWord_7150129 prefixEnd_7150129 3671452918651560821104661 := by
  unfold tailWord_7150129
  simp only [CollatzResearch.WordTrace]
  refine ⟨260786629113311252658005441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173857752742207501772003627 260786629113311252658005441)
  ·
    refine ⟨195589971834983439493504081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260786629113311252658005441 195589971834983439493504081)
    ·
      refine ⟨146692478876237579620128061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195589971834983439493504081 146692478876237579620128061)
      ·
        refine ⟨55009679578589092357548023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146692478876237579620128061 55009679578589092357548023)
        ·
          refine ⟨82514519367883638536322035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55009679578589092357548023 82514519367883638536322035)
          ·
            refine ⟨123771779051825457804483053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82514519367883638536322035 123771779051825457804483053)
            ·
              refine ⟨46414417144434546676681145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123771779051825457804483053 46414417144434546676681145)
              ·
                refine ⟨34810812858325910007510859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46414417144434546676681145 34810812858325910007510859)
                ·
                  refine ⟨52216219287488865011266289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34810812858325910007510859 52216219287488865011266289)
                  ·
                    refine ⟨39162164465616648758449717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52216219287488865011266289 39162164465616648758449717)
                    ·
                      refine ⟨3671452918651560821104661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39162164465616648758449717 3671452918651560821104661)
                      ·
                        rfl

theorem cell23_7150129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_7150129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150129 prefixEnd_7150129 := by exact prefixLift 7150129
  have htrace : WordTrace (prefixWord ++ tailWord_7150129) baseStart_7150129 baseEnd_7150129 := by
    simpa [prefixWord, tailWord_7150129, baseEnd_7150129] using wordTrace_append hprefix tailTrace_7150129
  have hstable : (prefixWord ++ tailWord_7150129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150129).length < 2 ^ (prefixWord ++ tailWord_7150129).sum := by decide
  have hdescent : baseEnd_7150129 < baseStart_7150129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150139 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 4]
def baseStart_7150139 : Nat := 118140960795 + 7150139 * 2 ^ 59
def prefixEnd_7150139 : Nat := 4983230072969 + 3 ^ 40 * 7150139 * 2
def baseEnd_7150139 : Nat := 3671458053458105781979615

theorem tailTrace_7150139 : CollatzResearch.WordTrace tailWord_7150139 prefixEnd_7150139 3671458053458105781979615 := by
  unfold tailWord_7150139
  simp only [CollatzResearch.WordTrace]
  refine ⟨260786993843275024365869471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173857995895516682910579647 260786993843275024365869471)
  ·
    refine ⟨391180490764912536548804207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260786993843275024365869471 391180490764912536548804207)
    ·
      refine ⟨586770736147368804823206311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391180490764912536548804207 586770736147368804823206311)
      ·
        refine ⟨880156104221053207234809467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586770736147368804823206311 880156104221053207234809467)
        ·
          refine ⟨1320234156331579810852214201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880156104221053207234809467 1320234156331579810852214201)
          ·
            refine ⟨990175617248684858139160651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320234156331579810852214201 990175617248684858139160651)
            ·
              refine ⟨1485263425873027287208740977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990175617248684858139160651 1485263425873027287208740977)
              ·
                refine ⟨1113947569404770465406555733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1485263425873027287208740977 1113947569404770465406555733)
                ·
                  refine ⟨13054073078962153891483075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1113947569404770465406555733 13054073078962153891483075)
                  ·
                    refine ⟨19581109618443230837224613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13054073078962153891483075 19581109618443230837224613)
                    ·
                      refine ⟨3671458053458105781979615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19581109618443230837224613 3671458053458105781979615)
                      ·
                        rfl

theorem cell23_7150139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 4].length) (baseStart_7150139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150139 prefixEnd_7150139 := by exact prefixLift 7150139
  have htrace : WordTrace (prefixWord ++ tailWord_7150139) baseStart_7150139 baseEnd_7150139 := by
    simpa [prefixWord, tailWord_7150139, baseEnd_7150139] using wordTrace_append hprefix tailTrace_7150139
  have hstable : (prefixWord ++ tailWord_7150139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150139).length < 2 ^ (prefixWord ++ tailWord_7150139).sum := by decide
  have hdescent : baseEnd_7150139 < baseStart_7150139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150140 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 5]
def baseStart_7150140 : Nat := 118140960795 + 7150140 * 2 ^ 59
def prefixEnd_7150140 : Nat := 4983230072969 + 3 ^ 40 * 7150140 * 2
def baseEnd_7150140 : Nat := 407939840770973364229679

theorem tailTrace_7150140 : CollatzResearch.WordTrace tailWord_7150140 prefixEnd_7150140 407939840770973364229679 := by
  unfold tailWord_7150140
  simp only [CollatzResearch.WordTrace]
  refine ⟨130393515158135700768327937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173858020210847601024437249 130393515158135700768327937)
  ·
    refine ⟨97795136368601775576245953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130393515158135700768327937 97795136368601775576245953)
    ·
      refine ⟨73346352276451331682184465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97795136368601775576245953 73346352276451331682184465)
      ·
        refine ⟨55009764207338498761638349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73346352276451331682184465 55009764207338498761638349)
        ·
          refine ⟨20628661577751937035614381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55009764207338498761638349 20628661577751937035614381)
          ·
            refine ⟨7735748091656976388355393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20628661577751937035614381 7735748091656976388355393)
            ·
              refine ⟨5801811068742732291266545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7735748091656976388355393 5801811068742732291266545)
              ·
                refine ⟨4351358301557049218449909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801811068742732291266545 4351358301557049218449909)
                ·
                  refine ⟨407939840770973364229679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4351358301557049218449909 407939840770973364229679)
                  ·
                    rfl

theorem cell23_7150140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_7150140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150140 prefixEnd_7150140 := by exact prefixLift 7150140
  have htrace : WordTrace (prefixWord ++ tailWord_7150140) baseStart_7150140 baseEnd_7150140 := by
    simpa [prefixWord, tailWord_7150140, baseEnd_7150140] using wordTrace_append hprefix tailTrace_7150140
  have hstable : (prefixWord ++ tailWord_7150140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150140).length < 2 ^ (prefixWord ++ tailWord_7150140).sum := by decide
  have hdescent : baseEnd_7150140 < baseStart_7150140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150150 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7150150 : Nat := 118140960795 + 7150150 * 2 ^ 59
def prefixEnd_7150150 : Nat := 4983230072969 + 3 ^ 40 * 7150150 * 2
def baseEnd_7150150 : Nat := 3671463701745305238942065

theorem tailTrace_7150150 : CollatzResearch.WordTrace tailWord_7150150 prefixEnd_7150150 3671463701745305238942065 := by
  unfold tailWord_7150150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149606095194849163891247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173858263364156782163013269 8149606095194849163891247)
  ·
    refine ⟨12224409142792273745836871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8149606095194849163891247 12224409142792273745836871)
    ·
      refine ⟨18336613714188410618755307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12224409142792273745836871 18336613714188410618755307)
      ·
        refine ⟨27504920571282615928132961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18336613714188410618755307 27504920571282615928132961)
        ·
          refine ⟨20628690428461961946099721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27504920571282615928132961 20628690428461961946099721)
          ·
            refine ⟨15471517821346471459574791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20628690428461961946099721 15471517821346471459574791)
            ·
              refine ⟨23207276732019707189362187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15471517821346471459574791 23207276732019707189362187)
              ·
                refine ⟨34810915098029560784043281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23207276732019707189362187 34810915098029560784043281)
                ·
                  refine ⟨26108186323522170588032461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34810915098029560784043281 26108186323522170588032461)
                  ·
                    refine ⟨9790569871320813970512173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26108186323522170588032461 9790569871320813970512173)
                    ·
                      refine ⟨3671463701745305238942065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790569871320813970512173 3671463701745305238942065)
                      ·
                        rfl

theorem cell23_7150150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7150150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150150 prefixEnd_7150150 := by exact prefixLift 7150150
  have htrace : WordTrace (prefixWord ++ tailWord_7150150) baseStart_7150150 baseEnd_7150150 := by
    simpa [prefixWord, tailWord_7150150, baseEnd_7150150] using wordTrace_append hprefix tailTrace_7150150
  have hstable : (prefixWord ++ tailWord_7150150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150150).length < 2 ^ (prefixWord ++ tailWord_7150150).sum := by decide
  have hdescent : baseEnd_7150150 < baseStart_7150150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150174 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7150174 : Nat := 118140960795 + 7150174 * 2 ^ 59
def prefixEnd_7150174 : Nat := 4983230072969 + 3 ^ 40 * 7150174 * 2
def baseEnd_7150174 : Nat := 407941780586779238337995

theorem tailTrace_7150174 : CollatzResearch.WordTrace tailWord_7150174 prefixEnd_7150174 407941780586779238337995 := by
  unfold tailWord_7150174
  simp only [CollatzResearch.WordTrace]
  refine ⟨32598533799768528167924197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173858846932098816895595717 32598533799768528167924197)
  ·
    refine ⟨6112225087456599031485787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32598533799768528167924197 6112225087456599031485787)
    ·
      refine ⟨9168337631184898547228681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6112225087456599031485787 9168337631184898547228681)
      ·
        refine ⟨6876253223388673910421511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9168337631184898547228681 6876253223388673910421511)
        ·
          refine ⟨10314379835083010865632267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876253223388673910421511 10314379835083010865632267)
          ·
            refine ⟨15471569752624516298448401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10314379835083010865632267 15471569752624516298448401)
            ·
              refine ⟨11603677314468387223836301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15471569752624516298448401 11603677314468387223836301)
              ·
                refine ⟨4351378992925645208938613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11603677314468387223836301 4351378992925645208938613)
                ·
                  refine ⟨407941780586779238337995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4351378992925645208938613 407941780586779238337995)
                  ·
                    rfl

theorem cell23_7150174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7150174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150174 prefixEnd_7150174 := by exact prefixLift 7150174
  have htrace : WordTrace (prefixWord ++ tailWord_7150174) baseStart_7150174 baseEnd_7150174 := by
    simpa [prefixWord, tailWord_7150174, baseEnd_7150174] using wordTrace_append hprefix tailTrace_7150174
  have hstable : (prefixWord ++ tailWord_7150174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150174).length < 2 ^ (prefixWord ++ tailWord_7150174).sum := by decide
  have hdescent : baseEnd_7150174 < baseStart_7150174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150179 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 8]
def baseStart_7150179 : Nat := 118140960795 + 7150179 * 2 ^ 59
def prefixEnd_7150179 : Nat := 4983230072969 + 3 ^ 40 * 7150179 * 2
def baseEnd_7150179 : Nat := 407942065853809513942159

theorem tailTrace_7150179 : CollatzResearch.WordTrace tailWord_7150179 prefixEnd_7150179 407942065853809513942159 := by
  unfold tailWord_7150179
  simp only [CollatzResearch.WordTrace]
  refine ⟨260788452763130111197325591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173858968508753407464883727 260788452763130111197325591)
  ·
    refine ⟨391182679144695166795988387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260788452763130111197325591 391182679144695166795988387)
    ·
      refine ⟨586774018717042750193982581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391182679144695166795988387 586774018717042750193982581)
      ·
        refine ⟨55010064254722757830685867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 586774018717042750193982581 55010064254722757830685867)
        ·
          refine ⟨82515096382084136746028801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55010064254722757830685867 82515096382084136746028801)
          ·
            refine ⟨61886322286563102559521601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82515096382084136746028801 61886322286563102559521601)
            ·
              refine ⟨46414741714922326919641201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61886322286563102559521601 46414741714922326919641201)
              ·
                refine ⟨34811056286191745189730901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46414741714922326919641201 34811056286191745189730901)
                ·
                  refine ⟨407942065853809513942159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34811056286191745189730901 407942065853809513942159)
                  ·
                    rfl

theorem cell23_7150179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 8].length) (baseStart_7150179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150179 prefixEnd_7150179 := by exact prefixLift 7150179
  have htrace : WordTrace (prefixWord ++ tailWord_7150179) baseStart_7150179 baseEnd_7150179 := by
    simpa [prefixWord, tailWord_7150179, baseEnd_7150179] using wordTrace_append hprefix tailTrace_7150179
  have hstable : (prefixWord ++ tailWord_7150179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150179).length < 2 ^ (prefixWord ++ tailWord_7150179).sum := by decide
  have hdescent : baseEnd_7150179 < baseStart_7150179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150199 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_7150199 : Nat := 118140960795 + 7150199 * 2 ^ 59
def prefixEnd_7150199 : Nat := 4983230072969 + 3 ^ 40 * 7150199 * 2
def baseEnd_7150199 : Nat := 3671488862297375547229339

theorem tailTrace_7150199 : CollatzResearch.WordTrace tailWord_7150199 prefixEnd_7150199 3671488862297375547229339 := by
  unfold tailWord_7150199
  simp only [CollatzResearch.WordTrace]
  refine ⟨260789182223057654613053651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173859454815371769742035767 260789182223057654613053651)
  ·
    refine ⟨391183773334586481919580477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260789182223057654613053651 391183773334586481919580477)
    ·
      refine ⟨146693915000469930719842679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391183773334586481919580477 146693915000469930719842679)
      ·
        refine ⟨220040872500704896079764019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146693915000469930719842679 220040872500704896079764019)
        ·
          refine ⟨330061308751057344119646029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220040872500704896079764019 330061308751057344119646029)
          ·
            refine ⟨123772990781646504044867261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330061308751057344119646029 123772990781646504044867261)
            ·
              refine ⟨46414871543117439016825223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123772990781646504044867261 46414871543117439016825223)
              ·
                refine ⟨69622307314676158525237835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46414871543117439016825223 69622307314676158525237835)
                ·
                  refine ⟨104433460972014237787856753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69622307314676158525237835 104433460972014237787856753)
                  ·
                    refine ⟨78325095729010678340892565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104433460972014237787856753 78325095729010678340892565)
                    ·
                      refine ⟨3671488862297375547229339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78325095729010678340892565 3671488862297375547229339)
                      ·
                        rfl

theorem cell23_7150199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_7150199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150199 prefixEnd_7150199 := by exact prefixLift 7150199
  have htrace : WordTrace (prefixWord ++ tailWord_7150199) baseStart_7150199 baseEnd_7150199 := by
    simpa [prefixWord, tailWord_7150199, baseEnd_7150199] using wordTrace_append hprefix tailTrace_7150199
  have hstable : (prefixWord ++ tailWord_7150199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150199).length < 2 ^ (prefixWord ++ tailWord_7150199).sum := by decide
  have hdescent : baseEnd_7150199 < baseStart_7150199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150213 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 6]
def baseStart_7150213 : Nat := 118140960795 + 7150213 * 2 ^ 59
def prefixEnd_7150213 : Nat := 4983230072969 + 3 ^ 40 * 7150213 * 2
def baseEnd_7150213 : Nat := 407944005669615388050475

theorem tailTrace_7150213 : CollatzResearch.WordTrace tailWord_7150213 prefixEnd_7150213 407944005669615388050475 := by
  unfold tailWord_7150213
  simp only [CollatzResearch.WordTrace]
  refine ⟨260789692845006935004063293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173859795230004623336042195 260789692845006935004063293)
  ·
    refine ⟨97796134816877600626523735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260789692845006935004063293 97796134816877600626523735)
    ·
      refine ⟨146694202225316400939785603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97796134816877600626523735 146694202225316400939785603)
      ·
        refine ⟨220041303337974601409678405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146694202225316400939785603 220041303337974601409678405)
        ·
          refine ⟨41257744375870237764314701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220041303337974601409678405 41257744375870237764314701)
          ·
            refine ⟨15471654140951339161618013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41257744375870237764314701 15471654140951339161618013)
            ·
              refine ⟨5801870302856752185606755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15471654140951339161618013 5801870302856752185606755)
              ·
                refine ⟨8702805454285128278410133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801870302856752185606755 8702805454285128278410133)
                ·
                  refine ⟨407944005669615388050475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8702805454285128278410133 407944005669615388050475)
                  ·
                    rfl

theorem cell23_7150213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_7150213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150213 prefixEnd_7150213 := by exact prefixLift 7150213
  have htrace : WordTrace (prefixWord ++ tailWord_7150213) baseStart_7150213 baseEnd_7150213 := by
    simpa [prefixWord, tailWord_7150213, baseEnd_7150213] using wordTrace_append hprefix tailTrace_7150213
  have hstable : (prefixWord ++ tailWord_7150213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150213).length < 2 ^ (prefixWord ++ tailWord_7150213).sum := by decide
  have hdescent : baseEnd_7150213 < baseStart_7150213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150233 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 2, 3, 2]
def baseStart_7150233 : Nat := 118140960795 + 7150233 * 2 ^ 59
def prefixEnd_7150233 : Nat := 4983230072969 + 3 ^ 40 * 7150233 * 2
def baseEnd_7150233 : Nat := 3671506320639628414204183

theorem tailTrace_7150233 : CollatzResearch.WordTrace tailWord_7150233 prefixEnd_7150233 3671506320639628414204183 := by
  unfold tailWord_7150233
  simp only [CollatzResearch.WordTrace]
  refine ⟨260790422304934478419791353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173860281536622985613194235 260790422304934478419791353)
  ·
    refine ⟨195592816728700858814843515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260790422304934478419791353 195592816728700858814843515)
    ·
      refine ⟨293389225093051288222265273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195592816728700858814843515 293389225093051288222265273)
      ·
        refine ⟨220041918819788466166698955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293389225093051288222265273 220041918819788466166698955)
        ·
          refine ⟨330062878229682699250048433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220041918819788466166698955 330062878229682699250048433)
          ·
            refine ⟨247547158672262024437536325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330062878229682699250048433 247547158672262024437536325)
            ·
              refine ⟨46415092251049129582038061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247547158672262024437536325 46415092251049129582038061)
              ·
                refine ⟨17405659594143423593264273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46415092251049129582038061 17405659594143423593264273)
                ·
                  refine ⟨13054244695607567694948205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17405659594143423593264273 13054244695607567694948205)
                  ·
                    refine ⟨4895341760852837885605577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13054244695607567694948205 4895341760852837885605577)
                    ·
                      refine ⟨3671506320639628414204183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895341760852837885605577 3671506320639628414204183)
                      ·
                        rfl

theorem cell23_7150233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_7150233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150233 prefixEnd_7150233 := by exact prefixLift 7150233
  have htrace : WordTrace (prefixWord ++ tailWord_7150233) baseStart_7150233 baseEnd_7150233 := by
    simpa [prefixWord, tailWord_7150233, baseEnd_7150233] using wordTrace_append hprefix tailTrace_7150233
  have hstable : (prefixWord ++ tailWord_7150233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150233).length < 2 ^ (prefixWord ++ tailWord_7150233).sum := by decide
  have hdescent : baseEnd_7150233 < baseStart_7150233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150234 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_7150234 : Nat := 118140960795 + 7150234 * 2 ^ 59
def prefixEnd_7150234 : Nat := 4983230072969 + 3 ^ 40 * 7150234 * 2
def baseEnd_7150234 : Nat := 1223835611373427636763893

theorem tailTrace_7150234 : CollatzResearch.WordTrace tailWord_7150234 prefixEnd_7150234 1223835611373427636763893 := by
  unfold tailWord_7150234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65197614694482713897644439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173860305851953903727051837 65197614694482713897644439)
  ·
    refine ⟨97796422041724070846466659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65197614694482713897644439 97796422041724070846466659)
    ·
      refine ⟨146694633062586106269699989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97796422041724070846466659 146694633062586106269699989)
      ·
        refine ⟨6876310924808723731392187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146694633062586106269699989 6876310924808723731392187)
        ·
          refine ⟨10314466387213085597088281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876310924808723731392187 10314466387213085597088281)
          ·
            refine ⟨7735849790409814197816211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10314466387213085597088281 7735849790409814197816211)
            ·
              refine ⟨11603774685614721296724317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735849790409814197816211 11603774685614721296724317)
              ·
                refine ⟨4351415507105520486271619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11603774685614721296724317 4351415507105520486271619)
                ·
                  refine ⟨6527123260658280729407429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351415507105520486271619 6527123260658280729407429)
                  ·
                    refine ⟨1223835611373427636763893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6527123260658280729407429 1223835611373427636763893)
                    ·
                      rfl

theorem cell23_7150234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_7150234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150234 prefixEnd_7150234 := by exact prefixLift 7150234
  have htrace : WordTrace (prefixWord ++ tailWord_7150234) baseStart_7150234 baseEnd_7150234 := by
    simpa [prefixWord, tailWord_7150234, baseEnd_7150234] using wordTrace_append hprefix tailTrace_7150234
  have hstable : (prefixWord ++ tailWord_7150234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150234).length < 2 ^ (prefixWord ++ tailWord_7150234).sum := by decide
  have hdescent : baseEnd_7150234 < baseStart_7150234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150266 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_7150266 : Nat := 118140960795 + 7150266 * 2 ^ 59
def prefixEnd_7150266 : Nat := 4983230072969 + 3 ^ 40 * 7150266 * 2
def baseEnd_7150266 : Nat := 3671523265501226785091531

theorem tailTrace_7150266 : CollatzResearch.WordTrace tailWord_7150266 prefixEnd_7150266 3671523265501226785091531 := by
  unfold tailWord_7150266
  simp only [CollatzResearch.WordTrace]
  refine ⟨65197906478453731263935663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173861083942543283370495101 65197906478453731263935663)
  ·
    refine ⟨97796859717680596895903495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65197906478453731263935663 97796859717680596895903495)
    ·
      refine ⟨146695289576520895343855243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97796859717680596895903495 146695289576520895343855243)
      ·
        refine ⟨220042934364781343015782865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146695289576520895343855243 220042934364781343015782865)
        ·
          refine ⟨165032200773586007261837149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220042934364781343015782865 165032200773586007261837149)
          ·
            refine ⟨61887075290094752723188931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165032200773586007261837149 61887075290094752723188931)
            ·
              refine ⟨92830612935142129084783397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61887075290094752723188931 92830612935142129084783397)
              ·
                refine ⟨17405739925339149203396887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92830612935142129084783397 17405739925339149203396887)
                ·
                  refine ⟨26108609888008723805095331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17405739925339149203396887 26108609888008723805095331)
                  ·
                    refine ⟨39162914832013085707642997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26108609888008723805095331 39162914832013085707642997)
                    ·
                      refine ⟨3671523265501226785091531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39162914832013085707642997 3671523265501226785091531)
                      ·
                        rfl

theorem cell23_7150266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_7150266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150266 prefixEnd_7150266 := by exact prefixLift 7150266
  have htrace : WordTrace (prefixWord ++ tailWord_7150266) baseStart_7150266 baseEnd_7150266 := by
    simpa [prefixWord, tailWord_7150266, baseEnd_7150266] using wordTrace_append hprefix tailTrace_7150266
  have hstable : (prefixWord ++ tailWord_7150266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150266).length < 2 ^ (prefixWord ++ tailWord_7150266).sum := by decide
  have hdescent : baseEnd_7150266 < baseStart_7150266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150280 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_7150280 : Nat := 118140960795 + 7150280 * 2 ^ 59
def prefixEnd_7150280 : Nat := 4983230072969 + 3 ^ 40 * 7150280 * 2
def baseEnd_7150280 : Nat := 3671530454230389730316467

theorem tailTrace_7150280 : CollatzResearch.WordTrace tailWord_7150280 prefixEnd_7150280 3671530454230389730316467 := by
  unfold tailWord_7150280
  simp only [CollatzResearch.WordTrace]
  refine ⟨130396068267882102723376147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173861424357176136964501529 130396068267882102723376147)
  ·
    refine ⟨195594102401823154085064221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130396068267882102723376147 195594102401823154085064221)
    ·
      refine ⟨73347788400683682781899083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195594102401823154085064221 73347788400683682781899083)
      ·
        refine ⟨110021682601025524172848625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73347788400683682781899083 110021682601025524172848625)
        ·
          refine ⟨82516261950769143129636469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110021682601025524172848625 82516261950769143129636469)
          ·
            refine ⟨7735899557884607168403419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82516261950769143129636469 7735899557884607168403419)
            ·
              refine ⟨11603849336826910752605129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735899557884607168403419 11603849336826910752605129)
              ·
                refine ⟨8702887002620183064453847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11603849336826910752605129 8702887002620183064453847)
                ·
                  refine ⟨13054330503930274596680771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702887002620183064453847 13054330503930274596680771)
                  ·
                    refine ⟨19581495755895411895021157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13054330503930274596680771 19581495755895411895021157)
                    ·
                      refine ⟨3671530454230389730316467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19581495755895411895021157 3671530454230389730316467)
                      ·
                        rfl

theorem cell23_7150280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_7150280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150280 prefixEnd_7150280 := by exact prefixLift 7150280
  have htrace : WordTrace (prefixWord ++ tailWord_7150280) baseStart_7150280 baseEnd_7150280 := by
    simpa [prefixWord, tailWord_7150280, baseEnd_7150280] using wordTrace_append hprefix tailTrace_7150280
  have hstable : (prefixWord ++ tailWord_7150280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150280).length < 2 ^ (prefixWord ++ tailWord_7150280).sum := by decide
  have hdescent : baseEnd_7150280 < baseStart_7150280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150286 : List Nat := [4, 1, 1, 1, 3, 2, 2, 9]
def baseStart_7150286 : Nat := 118140960795 + 7150286 * 2 ^ 59
def prefixEnd_7150286 : Nat := 4983230072969 + 3 ^ 40 * 7150286 * 2
def baseEnd_7150286 : Nat := 135982723522752470623757

theorem tailTrace_7150286 : CollatzResearch.WordTrace tailWord_7150286 prefixEnd_7150286 135982723522752470623757 := by
  unfold tailWord_7150286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32599044421717808558933839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173861570249161645647647141 32599044421717808558933839)
  ·
    refine ⟨48898566632576712838400759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32599044421717808558933839 48898566632576712838400759)
    ·
      refine ⟨73347849948865069257601139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48898566632576712838400759 73347849948865069257601139)
      ·
        refine ⟨110021774923297603886401709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73347849948865069257601139 110021774923297603886401709)
        ·
          refine ⟨41258165596236601457400641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110021774923297603886401709 41258165596236601457400641)
          ·
            refine ⟨30943624197177451093050481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41258165596236601457400641 30943624197177451093050481)
            ·
              refine ⟨23207718147883088319787861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30943624197177451093050481 23207718147883088319787861)
              ·
                refine ⟨135982723522752470623757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23207718147883088319787861 135982723522752470623757)
                ·
                  rfl

theorem cell23_7150286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_7150286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150286 prefixEnd_7150286 := by exact prefixLift 7150286
  have htrace : WordTrace (prefixWord ++ tailWord_7150286) baseStart_7150286 baseEnd_7150286 := by
    simpa [prefixWord, tailWord_7150286, baseEnd_7150286] using wordTrace_append hprefix tailTrace_7150286
  have hstable : (prefixWord ++ tailWord_7150286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150286).length < 2 ^ (prefixWord ++ tailWord_7150286).sum := by decide
  have hdescent : baseEnd_7150286 < baseStart_7150286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150297 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 1, 2, 2]
def baseStart_7150297 : Nat := 118140960795 + 7150297 * 2 ^ 59
def prefixEnd_7150297 : Nat := 4983230072969 + 3 ^ 40 * 7150297 * 2
def baseEnd_7150297 : Nat := 3671539183401516163803889

theorem tailTrace_7150297 : CollatzResearch.WordTrace tailWord_7150297 prefixEnd_7150297 3671539183401516163803889 := by
  unfold tailWord_7150297
  simp only [CollatzResearch.WordTrace]
  refine ⟨260792756576702617350121145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173861837717801744900080763 260792756576702617350121145)
  ·
    refine ⟨195594567432526963012590859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260792756576702617350121145 195594567432526963012590859)
    ·
      refine ⟨293391851148790444518886289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195594567432526963012590859 293391851148790444518886289)
      ·
        refine ⟨220043888361592833389164717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293391851148790444518886289 220043888361592833389164717)
        ·
          refine ⟨82516458135597312520936769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220043888361592833389164717 82516458135597312520936769)
          ·
            refine ⟨61887343601697984390702577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82516458135597312520936769 61887343601697984390702577)
            ·
              refine ⟨46415507701273488293026933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61887343601697984390702577 46415507701273488293026933)
              ·
                refine ⟨4351453846994389527471275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46415507701273488293026933 4351453846994389527471275)
                ·
                  refine ⟨6527180770491584291206913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351453846994389527471275 6527180770491584291206913)
                  ·
                    refine ⟨4895385577868688218405185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6527180770491584291206913 4895385577868688218405185)
                    ·
                      refine ⟨3671539183401516163803889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895385577868688218405185 3671539183401516163803889)
                      ·
                        rfl

theorem cell23_7150297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_7150297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150297 prefixEnd_7150297 := by exact prefixLift 7150297
  have htrace : WordTrace (prefixWord ++ tailWord_7150297) baseStart_7150297 baseEnd_7150297 := by
    simpa [prefixWord, tailWord_7150297, baseEnd_7150297] using wordTrace_append hprefix tailTrace_7150297
  have hstable : (prefixWord ++ tailWord_7150297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150297).length < 2 ^ (prefixWord ++ tailWord_7150297).sum := by decide
  have hdescent : baseEnd_7150297 < baseStart_7150297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150300 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7150300 : Nat := 118140960795 + 7150300 * 2 ^ 59
def prefixEnd_7150300 : Nat := 4983230072969 + 3 ^ 40 * 7150300 * 2
def baseEnd_7150300 : Nat := 3671540723843479652066375

theorem tailTrace_7150300 : CollatzResearch.WordTrace tailWord_7150300 prefixEnd_7150300 3671540723843479652066375 := by
  unfold tailWord_7150300
  simp only [CollatzResearch.WordTrace]
  refine ⟨130396432997845874431240177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173861910663794499241653569 130396432997845874431240177)
  ·
    refine ⟨97797324748384405823430133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130396432997845874431240177 97797324748384405823430133)
    ·
      refine ⟨9168499195161038045946575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97797324748384405823430133 9168499195161038045946575)
      ·
        refine ⟨13752748792741557068919863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9168499195161038045946575 13752748792741557068919863)
        ·
          refine ⟨20629123189112335603379795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13752748792741557068919863 20629123189112335603379795)
          ·
            refine ⟨30943684783668503405069693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20629123189112335603379795 30943684783668503405069693)
            ·
              refine ⟨11603881793875688776901135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30943684783668503405069693 11603881793875688776901135)
              ·
                refine ⟨17405822690813533165351703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11603881793875688776901135 17405822690813533165351703)
                ·
                  refine ⟨26108734036220299748027555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17405822690813533165351703 26108734036220299748027555)
                  ·
                    refine ⟨39163101054330449622041333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26108734036220299748027555 39163101054330449622041333)
                    ·
                      refine ⟨3671540723843479652066375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39163101054330449622041333 3671540723843479652066375)
                      ·
                        rfl

theorem cell23_7150300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7150300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150300 prefixEnd_7150300 := by exact prefixLift 7150300
  have htrace : WordTrace (prefixWord ++ tailWord_7150300) baseStart_7150300 baseEnd_7150300 := by
    simpa [prefixWord, tailWord_7150300, baseEnd_7150300] using wordTrace_append hprefix tailTrace_7150300
  have hstable : (prefixWord ++ tailWord_7150300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150300).length < 2 ^ (prefixWord ++ tailWord_7150300).sum := by decide
  have hdescent : baseEnd_7150300 < baseStart_7150300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150313 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 3]
def baseStart_7150313 : Nat := 118140960795 + 7150313 * 2 ^ 59
def prefixEnd_7150313 : Nat := 4983230072969 + 3 ^ 40 * 7150313 * 2
def baseEnd_7150313 : Nat := 3671547399091988101203815

theorem tailTrace_7150313 : CollatzResearch.WordTrace tailWord_7150313 prefixEnd_7150313 3671547399091988101203815 := by
  unfold tailWord_7150313
  simp only [CollatzResearch.WordTrace]
  refine ⟨260793340144644652082703593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173862226763096434721802395 260793340144644652082703593)
  ·
    refine ⟨195595005108483489062027695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260793340144644652082703593 195595005108483489062027695)
    ·
      refine ⟨293392507662725233593041543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195595005108483489062027695 293392507662725233593041543)
      ·
        refine ⟨440088761494087850389562315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293392507662725233593041543 440088761494087850389562315)
        ·
          refine ⟨660133142241131775584343473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440088761494087850389562315 660133142241131775584343473)
          ·
            refine ⟨495099856680848831688257605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660133142241131775584343473 495099856680848831688257605)
            ·
              refine ⟨92831223127659155941548301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 495099856680848831688257605 92831223127659155941548301)
              ·
                refine ⟨34811708672872183478080613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92831223127659155941548301 34811708672872183478080613)
                ·
                  refine ⟨6527195376163534402140115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34811708672872183478080613 6527195376163534402140115)
                  ·
                    refine ⟨9790793064245301603210173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6527195376163534402140115 9790793064245301603210173)
                    ·
                      refine ⟨3671547399091988101203815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790793064245301603210173 3671547399091988101203815)
                      ·
                        rfl

theorem cell23_7150313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_7150313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150313 prefixEnd_7150313 := by exact prefixLift 7150313
  have htrace : WordTrace (prefixWord ++ tailWord_7150313) baseStart_7150313 baseEnd_7150313 := by
    simpa [prefixWord, tailWord_7150313, baseEnd_7150313] using wordTrace_append hprefix tailTrace_7150313
  have hstable : (prefixWord ++ tailWord_7150313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150313).length < 2 ^ (prefixWord ++ tailWord_7150313).sum := by decide
  have hdescent : baseEnd_7150313 < baseStart_7150313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150330 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_7150330 : Nat := 118140960795 + 7150330 * 2 ^ 59
def prefixEnd_7150330 : Nat := 4983230072969 + 3 ^ 40 * 7150330 * 2
def baseEnd_7150330 : Nat := 3671556128263114534691237

theorem tailTrace_7150330 : CollatzResearch.WordTrace tailWord_7150330 prefixEnd_7150330 3671556128263114534691237 := by
  unfold tailWord_7150330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65198490046395765996518111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173862640123722042657381629 65198490046395765996518111)
  ·
    refine ⟨97797735069593648994777167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65198490046395765996518111 97797735069593648994777167)
    ·
      refine ⟨146696602604390473492165751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97797735069593648994777167 146696602604390473492165751)
      ·
        refine ⟨220044903906585710238248627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146696602604390473492165751 220044903906585710238248627)
        ·
          refine ⟨330067355859878565357372941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220044903906585710238248627 330067355859878565357372941)
          ·
            refine ⟨123775258447454462009014853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330067355859878565357372941 123775258447454462009014853)
            ·
              refine ⟨23207860958897711626690285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123775258447454462009014853 23207860958897711626690285)
              ·
                refine ⟨8702947859586641860008857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23207860958897711626690285 8702947859586641860008857)
                ·
                  refine ⟨6527210894689981395006643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702947859586641860008857 6527210894689981395006643)
                  ·
                    refine ⟨9790816342034972092509965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6527210894689981395006643 9790816342034972092509965)
                    ·
                      refine ⟨3671556128263114534691237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790816342034972092509965 3671556128263114534691237)
                      ·
                        rfl

theorem cell23_7150330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_7150330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150330 prefixEnd_7150330 := by exact prefixLift 7150330
  have htrace : WordTrace (prefixWord ++ tailWord_7150330) baseStart_7150330 baseEnd_7150330 := by
    simpa [prefixWord, tailWord_7150330, baseEnd_7150330] using wordTrace_append hprefix tailTrace_7150330
  have hstable : (prefixWord ++ tailWord_7150330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150330).length < 2 ^ (prefixWord ++ tailWord_7150330).sum := by decide
  have hdescent : baseEnd_7150330 < baseStart_7150330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150340 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_7150340 : Nat := 118140960795 + 7150340 * 2 ^ 59
def prefixEnd_7150340 : Nat := 4983230072969 + 3 ^ 40 * 7150340 * 2
def baseEnd_7150340 : Nat := 3671561263069659495566191

theorem tailTrace_7150340 : CollatzResearch.WordTrace tailWord_7150340 prefixEnd_7150340 3671561263069659495566191 := by
  unfold tailWord_7150340
  simp only [CollatzResearch.WordTrace]
  refine ⟨130397162457773417846968237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173862883277031223795957649 130397162457773417846968237)
  ·
    refine ⟨48898935921665031692613089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130397162457773417846968237 48898935921665031692613089)
    ·
      refine ⟨36674201941248773769459817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48898935921665031692613089 36674201941248773769459817)
      ·
        refine ⟨27505651455936580327094863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36674201941248773769459817 27505651455936580327094863)
        ·
          refine ⟨41258477183904870490642295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27505651455936580327094863 41258477183904870490642295)
          ·
            refine ⟨61887715775857305735963443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41258477183904870490642295 61887715775857305735963443)
            ·
              refine ⟨92831573663785958603945165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61887715775857305735963443 92831573663785958603945165)
              ·
                refine ⟨34811840123919734476479437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92831573663785958603945165 34811840123919734476479437)
                ·
                  refine ⟨13054440046469900428679789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34811840123919734476479437 13054440046469900428679789)
                  ·
                    refine ⟨4895415017426212660754921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13054440046469900428679789 4895415017426212660754921)
                    ·
                      refine ⟨3671561263069659495566191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895415017426212660754921 3671561263069659495566191)
                      ·
                        rfl

theorem cell23_7150340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_7150340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150340 prefixEnd_7150340 := by exact prefixLift 7150340
  have htrace : WordTrace (prefixWord ++ tailWord_7150340) baseStart_7150340 baseEnd_7150340 := by
    simpa [prefixWord, tailWord_7150340, baseEnd_7150340] using wordTrace_append hprefix tailTrace_7150340
  have hstable : (prefixWord ++ tailWord_7150340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150340).length < 2 ^ (prefixWord ++ tailWord_7150340).sum := by decide
  have hdescent : baseEnd_7150340 < baseStart_7150340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150346 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_7150346 : Nat := 118140960795 + 7150346 * 2 ^ 59
def prefixEnd_7150346 : Nat := 4983230072969 + 3 ^ 40 * 7150346 * 2
def baseEnd_7150346 : Nat := 1223854781317862157363721

theorem tailTrace_7150346 : CollatzResearch.WordTrace tailWord_7150346 prefixEnd_7150346 1223854781317862157363721 := by
  unfold tailWord_7150346
  simp only [CollatzResearch.WordTrace]
  refine ⟨65198635938381274679663723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173863029169016732479103261 65198635938381274679663723)
  ·
    refine ⟨97797953907571912019495585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65198635938381274679663723 97797953907571912019495585)
    ·
      refine ⟨73348465430678934014621689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97797953907571912019495585 73348465430678934014621689)
      ·
        refine ⟨55011349073009200510966267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73348465430678934014621689 55011349073009200510966267)
        ·
          refine ⟨82517023609513800766449401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55011349073009200510966267 82517023609513800766449401)
          ·
            refine ⟨61887767707135350574837051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82517023609513800766449401 61887767707135350574837051)
            ·
              refine ⟨92831651560703025862255577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61887767707135350574837051 92831651560703025862255577)
              ·
                refine ⟨69623738670527269396691683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92831651560703025862255577 69623738670527269396691683)
                ·
                  refine ⟨104435608005790904095037525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69623738670527269396691683 104435608005790904095037525)
                  ·
                    refine ⟨1223854781317862157363721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104435608005790904095037525 1223854781317862157363721)
                    ·
                      rfl

theorem cell23_7150346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_7150346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150346 prefixEnd_7150346 := by exact prefixLift 7150346
  have htrace : WordTrace (prefixWord ++ tailWord_7150346) baseStart_7150346 baseEnd_7150346 := by
    simpa [prefixWord, tailWord_7150346, baseEnd_7150346] using wordTrace_append hprefix tailTrace_7150346
  have hstable : (prefixWord ++ tailWord_7150346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150346).length < 2 ^ (prefixWord ++ tailWord_7150346).sum := by decide
  have hdescent : baseEnd_7150346 < baseStart_7150346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150381 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7150381 : Nat := 118140960795 + 7150381 * 2 ^ 59
def prefixEnd_7150381 : Nat := 4983230072969 + 3 ^ 40 * 7150381 * 2
def baseEnd_7150381 : Nat := 3671582315776493835153503

theorem tailTrace_7150381 : CollatzResearch.WordTrace tailWord_7150381 prefixEnd_7150381 3671582315776493835153503 := by
  unfold tailWord_7150381
  simp only [CollatzResearch.WordTrace]
  refine ⟨260795820308398299696178997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173863880205598866464119331 260795820308398299696178997)
  ·
    refine ⟨24449608153912340596516781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260795820308398299696178997 24449608153912340596516781)
    ·
      refine ⟨9168603057717127723693793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24449608153912340596516781 9168603057717127723693793)
      ·
        refine ⟨6876452293287845792770345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9168603057717127723693793 6876452293287845792770345)
        ·
          refine ⟨5157339219965884344577759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6876452293287845792770345 5157339219965884344577759)
          ·
            refine ⟨7736008829948826516866639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157339219965884344577759 7736008829948826516866639)
            ·
              refine ⟨11604013244923239775299959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736008829948826516866639 11604013244923239775299959)
              ·
                refine ⟨17406019867384859662949939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604013244923239775299959 17406019867384859662949939)
                ·
                  refine ⟨26109029801077289494424909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17406019867384859662949939 26109029801077289494424909)
                  ·
                    refine ⟨9790886175403983560409341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26109029801077289494424909 9790886175403983560409341)
                    ·
                      refine ⟨3671582315776493835153503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790886175403983560409341 3671582315776493835153503)
                      ·
                        rfl

theorem cell23_7150381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7150381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150381 prefixEnd_7150381 := by exact prefixLift 7150381
  have htrace : WordTrace (prefixWord ++ tailWord_7150381) baseStart_7150381 baseEnd_7150381 := by
    simpa [prefixWord, tailWord_7150381, baseEnd_7150381] using wordTrace_append hprefix tailTrace_7150381
  have hstable : (prefixWord ++ tailWord_7150381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150381).length < 2 ^ (prefixWord ++ tailWord_7150381).sum := by decide
  have hdescent : baseEnd_7150381 < baseStart_7150381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150387 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 1, 4, 2]
def baseStart_7150387 : Nat := 118140960795 + 7150387 * 2 ^ 59
def prefixEnd_7150387 : Nat := 4983230072969 + 3 ^ 40 * 7150387 * 2
def baseEnd_7150387 : Nat := 3671585396660420811678475

theorem tailTrace_7150387 : CollatzResearch.WordTrace tailWord_7150387 prefixEnd_7150387 3671585396660420811678475 := by
  unfold tailWord_7150387
  simp only [CollatzResearch.WordTrace]
  refine ⟨260796039146376562720897415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173864026097584375147264943 260796039146376562720897415)
  ·
    refine ⟨391194058719564844081346123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260796039146376562720897415 391194058719564844081346123)
    ·
      refine ⟨586791088079347266122019185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391194058719564844081346123 586791088079347266122019185)
      ·
        refine ⟨440093316059510449591514389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586791088079347266122019185 440093316059510449591514389)
        ·
          refine ⟨20629374190289552324602237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 440093316059510449591514389 20629374190289552324602237)
          ·
            refine ⟨7736015321358582121725839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20629374190289552324602237 7736015321358582121725839)
            ·
              refine ⟨11604022982037873182588759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736015321358582121725839 11604022982037873182588759)
              ·
                refine ⟨17406034473056809773883139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604022982037873182588759 17406034473056809773883139)
                ·
                  refine ⟨26109051709585214660824709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17406034473056809773883139 26109051709585214660824709)
                  ·
                    refine ⟨4895447195547227748904633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26109051709585214660824709 4895447195547227748904633)
                    ·
                      refine ⟨3671585396660420811678475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895447195547227748904633 3671585396660420811678475)
                      ·
                        rfl

theorem cell23_7150387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 4, 2].length) (baseStart_7150387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150387 prefixEnd_7150387 := by exact prefixLift 7150387
  have htrace : WordTrace (prefixWord ++ tailWord_7150387) baseStart_7150387 baseEnd_7150387 := by
    simpa [prefixWord, tailWord_7150387, baseEnd_7150387] using wordTrace_append hprefix tailTrace_7150387
  have hstable : (prefixWord ++ tailWord_7150387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150387).length < 2 ^ (prefixWord ++ tailWord_7150387).sum := by decide
  have hdescent : baseEnd_7150387 < baseStart_7150387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150423 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 4, 5]
def baseStart_7150423 : Nat := 118140960795 + 7150423 * 2 ^ 59
def prefixEnd_7150423 : Nat := 4983230072969 + 3 ^ 40 * 7150423 * 2
def baseEnd_7150423 : Nat := 1223867960654660890276103

theorem tailTrace_7150423 : CollatzResearch.WordTrace tailWord_7150423 prefixEnd_7150423 1223867960654660890276103 := by
  unfold tailWord_7150423
  simp only [CollatzResearch.WordTrace]
  refine ⟨260797352174246140869207923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173864901449497427246138615 260797352174246140869207923)
  ·
    refine ⟨391196028261369211303811885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260797352174246140869207923 391196028261369211303811885)
    ·
      refine ⟨146698510598013454238929457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391196028261369211303811885 146698510598013454238929457)
      ·
        refine ⟨110023882948510090679197093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146698510598013454238929457 110023882948510090679197093)
        ·
          refine ⟨20629478052845642002349455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110023882948510090679197093 20629478052845642002349455)
          ·
            refine ⟨30944217079268463003524183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20629478052845642002349455 30944217079268463003524183)
            ·
              refine ⟨46416325618902694505286275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30944217079268463003524183 46416325618902694505286275)
              ·
                refine ⟨69624488428354041757929413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46416325618902694505286275 69624488428354041757929413)
                ·
                  refine ⟨13054591580316382829611765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69624488428354041757929413 13054591580316382829611765)
                  ·
                    refine ⟨1223867960654660890276103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13054591580316382829611765 1223867960654660890276103)
                    ·
                      rfl

theorem cell23_7150423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_7150423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150423 prefixEnd_7150423 := by exact prefixLift 7150423
  have htrace : WordTrace (prefixWord ++ tailWord_7150423) baseStart_7150423 baseEnd_7150423 := by
    simpa [prefixWord, tailWord_7150423, baseEnd_7150423] using wordTrace_append hprefix tailTrace_7150423
  have hstable : (prefixWord ++ tailWord_7150423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150423).length < 2 ^ (prefixWord ++ tailWord_7150423).sum := by decide
  have hdescent : baseEnd_7150423 < baseStart_7150423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150463 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_7150463 : Nat := 118140960795 + 7150463 * 2 ^ 59
def prefixEnd_7150463 : Nat := 4983230072969 + 3 ^ 40 * 7150463 * 2
def baseEnd_7150463 : Nat := 3671624421190162514328125

theorem tailTrace_7150463 : CollatzResearch.WordTrace tailWord_7150463 prefixEnd_7150463 3671624421190162514328125 := by
  unfold tailWord_7150463
  simp only [CollatzResearch.WordTrace]
  refine ⟨260798811094101227700664043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173865874062734151800442695 260798811094101227700664043)
  ·
    refine ⟨391198216641151841550996065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260798811094101227700664043 391198216641151841550996065)
    ·
      refine ⟨293398662480863881163247049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391198216641151841550996065 293398662480863881163247049)
      ·
        refine ⟨220048996860647910872435287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293398662480863881163247049 220048996860647910872435287)
        ·
          refine ⟨330073495290971866308652931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220048996860647910872435287 330073495290971866308652931)
          ·
            refine ⟨495110242936457799462979397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330073495290971866308652931 495110242936457799462979397)
            ·
              refine ⟨92833170550585837399308637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 495110242936457799462979397 92833170550585837399308637)
              ·
                refine ⟨34812438956469689024740739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92833170550585837399308637 34812438956469689024740739)
                ·
                  refine ⟨52218658434704533537111109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34812438956469689024740739 52218658434704533537111109)
                  ·
                    refine ⟨9790998456507100038208333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52218658434704533537111109 9790998456507100038208333)
                    ·
                      refine ⟨3671624421190162514328125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790998456507100038208333 3671624421190162514328125)
                      ·
                        rfl

theorem cell23_7150463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_7150463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150463 prefixEnd_7150463 := by exact prefixLift 7150463
  have htrace : WordTrace (prefixWord ++ tailWord_7150463) baseStart_7150463 baseEnd_7150463 := by
    simpa [prefixWord, tailWord_7150463, baseEnd_7150463] using wordTrace_append hprefix tailTrace_7150463
  have hstable : (prefixWord ++ tailWord_7150463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150463).length < 2 ^ (prefixWord ++ tailWord_7150463).sum := by decide
  have hdescent : baseEnd_7150463 < baseStart_7150463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150487 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 1, 4]
def baseStart_7150487 : Nat := 118140960795 + 7150487 * 2 ^ 59
def prefixEnd_7150487 : Nat := 4983230072969 + 3 ^ 40 * 7150487 * 2
def baseEnd_7150487 : Nat := 1223878914908623473476005

theorem tailTrace_7150487 : CollatzResearch.WordTrace tailWord_7150487 prefixEnd_7150487 1223878914908623473476005 := by
  unfold tailWord_7150487
  simp only [CollatzResearch.WordTrace]
  refine ⟨260799686446014279799537715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173866457630676186533025143 260799686446014279799537715)
  ·
    refine ⟨391199529669021419699306573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260799686446014279799537715 391199529669021419699306573)
    ·
      refine ⟨146699823625883032387239965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391199529669021419699306573 146699823625883032387239965)
      ·
        refine ⟨55012433859706137145214987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146699823625883032387239965 55012433859706137145214987)
        ·
          refine ⟨82518650789559205717822481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55012433859706137145214987 82518650789559205717822481)
          ·
            refine ⟨61888988092169404288366861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82518650789559205717822481 61888988092169404288366861)
            ·
              refine ⟨23208370534563526608137573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61888988092169404288366861 23208370534563526608137573)
              ·
                refine ⟨4351569475230661239025795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23208370534563526608137573 4351569475230661239025795)
                ·
                  refine ⟨6527354212845991858538693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351569475230661239025795 6527354212845991858538693)
                  ·
                    refine ⟨1223878914908623473476005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6527354212845991858538693 1223878914908623473476005)
                    ·
                      rfl

theorem cell23_7150487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_7150487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150487 prefixEnd_7150487 := by exact prefixLift 7150487
  have htrace : WordTrace (prefixWord ++ tailWord_7150487) baseStart_7150487 baseEnd_7150487 := by
    simpa [prefixWord, tailWord_7150487, baseEnd_7150487] using wordTrace_append hprefix tailTrace_7150487
  have hstable : (prefixWord ++ tailWord_7150487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150487).length < 2 ^ (prefixWord ++ tailWord_7150487).sum := by decide
  have hdescent : baseEnd_7150487 < baseStart_7150487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150567 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7150567 : Nat := 118140960795 + 7150567 * 2 ^ 59
def prefixEnd_7150567 : Nat := 4983230072969 + 3 ^ 40 * 7150567 * 2
def baseEnd_7150567 : Nat := 3671677823178230107427647

theorem tailTrace_7150567 : CollatzResearch.WordTrace tailWord_7150567 prefixEnd_7150567 3671677823178230107427647 := by
  unfold tailWord_7150567
  simp only [CollatzResearch.WordTrace]
  refine ⟨260802604285724453462449955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173868402857149635641633303 260802604285724453462449955)
  ·
    refine ⟨391203906428586680193674933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260802604285724453462449955 391203906428586680193674933)
    ·
      refine ⟨36675366227680001268157025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391203906428586680193674933 36675366227680001268157025)
      ·
        refine ⟨27506524670760000951117769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36675366227680001268157025 27506524670760000951117769)
        ·
          refine ⟨20629893503070000713338327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27506524670760000951117769 20629893503070000713338327)
          ·
            refine ⟨30944840254605001070007491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20629893503070000713338327 30944840254605001070007491)
            ·
              refine ⟨46417260381907501605011237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30944840254605001070007491 46417260381907501605011237)
              ·
                refine ⟨8703236321607656550939607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46417260381907501605011237 8703236321607656550939607)
                ·
                  refine ⟨13054854482411484826409411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703236321607656550939607 13054854482411484826409411)
                  ·
                    refine ⟨19582281723617227239614117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13054854482411484826409411 19582281723617227239614117)
                    ·
                      refine ⟨3671677823178230107427647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19582281723617227239614117 3671677823178230107427647)
                      ·
                        rfl

theorem cell23_7150567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7150567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150567 prefixEnd_7150567 := by exact prefixLift 7150567
  have htrace : WordTrace (prefixWord ++ tailWord_7150567) baseStart_7150567 baseEnd_7150567 := by
    simpa [prefixWord, tailWord_7150567, baseEnd_7150567] using wordTrace_append hprefix tailTrace_7150567
  have hstable : (prefixWord ++ tailWord_7150567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150567).length < 2 ^ (prefixWord ++ tailWord_7150567).sum := by decide
  have hdescent : baseEnd_7150567 < baseStart_7150567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150621 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_7150621 : Nat := 118140960795 + 7150621 * 2 ^ 59
def prefixEnd_7150621 : Nat := 4983230072969 + 3 ^ 40 * 7150621 * 2
def baseEnd_7150621 : Nat := 3671705551133572896152399

theorem tailTrace_7150621 : CollatzResearch.WordTrace tailWord_7150621 prefixEnd_7150621 3671705551133572896152399 := by
  unfold tailWord_7150621
  simp only [CollatzResearch.WordTrace]
  refine ⟨260804573827528820684915717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173869715885019213789943811 260804573827528820684915717)
  ·
    refine ⟨48900857592661653878421697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260804573827528820684915717 48900857592661653878421697)
    ·
      refine ⟨36675643194496240408816273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48900857592661653878421697 36675643194496240408816273)
      ·
        refine ⟨27506732395872180306612205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36675643194496240408816273 27506732395872180306612205)
        ·
          refine ⟨10315024648452067614979577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27506732395872180306612205 10315024648452067614979577)
          ·
            refine ⟨7736268486339050711234683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10315024648452067614979577 7736268486339050711234683)
            ·
              refine ⟨11604402729508576066852025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736268486339050711234683 11604402729508576066852025)
              ·
                refine ⟨8703302047131432050139019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11604402729508576066852025 8703302047131432050139019)
                ·
                  refine ⟨13054953070697148075208529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703302047131432050139019 13054953070697148075208529)
                  ·
                    refine ⟨9791214803022861056406397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13054953070697148075208529 9791214803022861056406397)
                    ·
                      refine ⟨3671705551133572896152399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9791214803022861056406397 3671705551133572896152399)
                      ·
                        rfl

theorem cell23_7150621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_7150621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150621 prefixEnd_7150621 := by exact prefixLift 7150621
  have htrace : WordTrace (prefixWord ++ tailWord_7150621) baseStart_7150621 baseEnd_7150621 := by
    simpa [prefixWord, tailWord_7150621, baseEnd_7150621] using wordTrace_append hprefix tailTrace_7150621
  have hstable : (prefixWord ++ tailWord_7150621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150621).length < 2 ^ (prefixWord ++ tailWord_7150621).sum := by decide
  have hdescent : baseEnd_7150621 < baseStart_7150621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150634 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7150634 : Nat := 118140960795 + 7150634 * 2 ^ 59
def prefixEnd_7150634 : Nat := 4983230072969 + 3 ^ 40 * 7150634 * 2
def baseEnd_7150634 : Nat := 3671712226382081345289839

theorem tailTrace_7150634 : CollatzResearch.WordTrace tailWord_7150634 prefixEnd_7150634 3671712226382081345289839 := by
  unfold tailWord_7150634
  simp only [CollatzResearch.WordTrace]
  refine ⟨65201261994120430976284739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173870031984321149270092637 65201261994120430976284739)
  ·
    refine ⟨97801892991180646464427109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65201261994120430976284739 97801892991180646464427109)
    ·
      refine ⟨18337854935846371212080083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97801892991180646464427109 18337854935846371212080083)
      ·
        refine ⟨27506782403769556818120125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18337854935846371212080083 27506782403769556818120125)
        ·
          refine ⟨10315043401413583806795047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27506782403769556818120125 10315043401413583806795047)
          ·
            refine ⟨15472565102120375710192571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10315043401413583806795047 15472565102120375710192571)
            ·
              refine ⟨23208847653180563565288857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15472565102120375710192571 23208847653180563565288857)
              ·
                refine ⟨17406635739885422673966643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23208847653180563565288857 17406635739885422673966643)
                ·
                  refine ⟨26109953609828134010949965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17406635739885422673966643 26109953609828134010949965)
                  ·
                    refine ⟨9791232603685550254106237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26109953609828134010949965 9791232603685550254106237)
                    ·
                      refine ⟨3671712226382081345289839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9791232603685550254106237 3671712226382081345289839)
                      ·
                        rfl

theorem cell23_7150634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7150634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150634 prefixEnd_7150634 := by exact prefixLift 7150634
  have htrace : WordTrace (prefixWord ++ tailWord_7150634) baseStart_7150634 baseEnd_7150634 := by
    simpa [prefixWord, tailWord_7150634, baseEnd_7150634] using wordTrace_append hprefix tailTrace_7150634
  have hstable : (prefixWord ++ tailWord_7150634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150634).length < 2 ^ (prefixWord ++ tailWord_7150634).sum := by decide
  have hdescent : baseEnd_7150634 < baseStart_7150634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150674 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_7150674 : Nat := 118140960795 + 7150674 * 2 ^ 59
def prefixEnd_7150674 : Nat := 4983230072969 + 3 ^ 40 * 7150674 * 2
def baseEnd_7150674 : Nat := 3671732765608261188789655

theorem tailTrace_7150674 : CollatzResearch.WordTrace tailWord_7150674 prefixEnd_7150674 3671732765608261188789655 := by
  unfold tailWord_7150674
  simp only [CollatzResearch.WordTrace]
  refine ⟨65201626724084202684148769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173871004597557873824396717 65201626724084202684148769)
  ·
    refine ⟨48901220043063152013111577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65201626724084202684148769 48901220043063152013111577)
    ·
      refine ⟨36675915032297364009833683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48901220043063152013111577 36675915032297364009833683)
      ·
        refine ⟨55013872548446046014750525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36675915032297364009833683 55013872548446046014750525)
        ·
          refine ⟨20630202205667267255531447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55013872548446046014750525 20630202205667267255531447)
          ·
            refine ⟨30945303308500900883297171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20630202205667267255531447 30945303308500900883297171)
            ·
              refine ⟨46417954962751351324945757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30945303308500900883297171 46417954962751351324945757)
              ·
                refine ⟨17406733111031756746854659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46417954962751351324945757 17406733111031756746854659)
                ·
                  refine ⟨26110099666547635120281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17406733111031756746854659 26110099666547635120281989)
                  ·
                    refine ⟨4895643687477681585052873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26110099666547635120281989 4895643687477681585052873)
                    ·
                      refine ⟨3671732765608261188789655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895643687477681585052873 3671732765608261188789655)
                      ·
                        rfl

theorem cell23_7150674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_7150674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150674 prefixEnd_7150674 := by exact prefixLift 7150674
  have htrace : WordTrace (prefixWord ++ tailWord_7150674) baseStart_7150674 baseEnd_7150674 := by
    simpa [prefixWord, tailWord_7150674, baseEnd_7150674] using wordTrace_append hprefix tailTrace_7150674
  have hstable : (prefixWord ++ tailWord_7150674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150674).length < 2 ^ (prefixWord ++ tailWord_7150674).sum := by decide
  have hdescent : baseEnd_7150674 < baseStart_7150674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150680 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 7]
def baseStart_7150680 : Nat := 118140960795 + 7150680 * 2 ^ 59
def prefixEnd_7150680 : Nat := 4983230072969 + 3 ^ 40 * 7150680 * 2
def baseEnd_7150680 : Nat := 407970649610243129479403

theorem tailTrace_7150680 : CollatzResearch.WordTrace tailWord_7150680 prefixEnd_7150680 407970649610243129479403 := by
  unfold tailWord_7150680
  simp only [CollatzResearch.WordTrace]
  refine ⟨130403362867157536880656747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173871150489543382507542329 130403362867157536880656747)
  ·
    refine ⟨195605044300736305320985121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130403362867157536880656747 195605044300736305320985121)
    ·
      refine ⟨146703783225552228990738841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195605044300736305320985121 146703783225552228990738841)
      ·
        refine ⟨110027837419164171743054131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146703783225552228990738841 110027837419164171743054131)
        ·
          refine ⟨165041756128746257614581197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110027837419164171743054131 165041756128746257614581197)
          ·
            refine ⟨61890658548279846605467949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165041756128746257614581197 61890658548279846605467949)
            ·
              refine ⟨23208996955604942477050481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61890658548279846605467949 23208996955604942477050481)
              ·
                refine ⟨17406747716703706857787861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23208996955604942477050481 17406747716703706857787861)
                ·
                  refine ⟨407970649610243129479403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17406747716703706857787861 407970649610243129479403)
                  ·
                    rfl

theorem cell23_7150680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_7150680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150680 prefixEnd_7150680 := by exact prefixLift 7150680
  have htrace : WordTrace (prefixWord ++ tailWord_7150680) baseStart_7150680 baseEnd_7150680 := by
    simpa [prefixWord, tailWord_7150680, baseEnd_7150680] using wordTrace_append hprefix tailTrace_7150680
  have hstable : (prefixWord ++ tailWord_7150680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150680).length < 2 ^ (prefixWord ++ tailWord_7150680).sum := by decide
  have hdescent : baseEnd_7150680 < baseStart_7150680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150697 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 5]
def baseStart_7150697 : Nat := 118140960795 + 7150697 * 2 ^ 59
def prefixEnd_7150697 : Nat := 4983230072969 + 3 ^ 40 * 7150697 * 2
def baseEnd_7150697 : Nat := 407971619518146066533561

theorem tailTrace_7150697 : CollatzResearch.WordTrace tailWord_7150697 prefixEnd_7150697 407971619518146066533561 := by
  unfold tailWord_7150697
  simp only [CollatzResearch.WordTrace]
  refine ⟨260807345775253485664682345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173871563850168990443121563 260807345775253485664682345)
  ·
    refine ⟨195605509331440114248511759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260807345775253485664682345 195605509331440114248511759)
    ·
      refine ⟨293408263997160171372767639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195605509331440114248511759 293408263997160171372767639)
      ·
        refine ⟨440112395995740257059151459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293408263997160171372767639 440112395995740257059151459)
        ·
          refine ⟨660168593993610385588727189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440112395995740257059151459 660168593993610385588727189)
          ·
            refine ⟨30945402843450486824471587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 660168593993610385588727189 30945402843450486824471587)
            ·
              refine ⟨46418104265175730236707381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30945402843450486824471587 46418104265175730236707381)
              ·
                refine ⟨4351697274860224709691317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46418104265175730236707381 4351697274860224709691317)
                ·
                  refine ⟨407971619518146066533561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4351697274860224709691317 407971619518146066533561)
                  ·
                    rfl

theorem cell23_7150697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 5].length) (baseStart_7150697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150697 prefixEnd_7150697 := by exact prefixLift 7150697
  have htrace : WordTrace (prefixWord ++ tailWord_7150697) baseStart_7150697 baseEnd_7150697 := by
    simpa [prefixWord, tailWord_7150697, baseEnd_7150697] using wordTrace_append hprefix tailTrace_7150697
  have hstable : (prefixWord ++ tailWord_7150697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150697).length < 2 ^ (prefixWord ++ tailWord_7150697).sum := by decide
  have hdescent : baseEnd_7150697 < baseStart_7150697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150720 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_7150720 : Nat := 118140960795 + 7150720 * 2 ^ 59
def prefixEnd_7150720 : Nat := 4983230072969 + 3 ^ 40 * 7150720 * 2
def baseEnd_7150720 : Nat := 3671756385718368008814443

theorem tailTrace_7150720 : CollatzResearch.WordTrace tailWord_7150720 prefixEnd_7150720 3671756385718368008814443 := by
  unfold tailWord_7150720
  simp only [CollatzResearch.WordTrace]
  refine ⟨130404092327085080296384807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173872123102780107061846409 130404092327085080296384807)
  ·
    refine ⟨195606138490627620444577211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130404092327085080296384807 195606138490627620444577211)
    ·
      refine ⟨293409207735941430666865817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195606138490627620444577211 293409207735941430666865817)
      ·
        refine ⟨220056905801956073000149363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293409207735941430666865817 220056905801956073000149363)
        ·
          refine ⟨330085358702934109500224045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220056905801956073000149363 330085358702934109500224045)
          ·
            refine ⟨123782009513600291062584017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330085358702934109500224045 123782009513600291062584017)
            ·
              refine ⟨92836507135200218296938013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123782009513600291062584017 92836507135200218296938013)
              ·
                refine ⟨34813690175700081861351755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92836507135200218296938013 34813690175700081861351755)
                ·
                  refine ⟨52220535263550122792027633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34813690175700081861351755 52220535263550122792027633)
                  ·
                    refine ⟨39165401447662592094020725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52220535263550122792027633 39165401447662592094020725)
                    ·
                      refine ⟨3671756385718368008814443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39165401447662592094020725 3671756385718368008814443)
                      ·
                        rfl

theorem cell23_7150720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_7150720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150720 prefixEnd_7150720 := by exact prefixLift 7150720
  have htrace : WordTrace (prefixWord ++ tailWord_7150720) baseStart_7150720 baseEnd_7150720 := by
    simpa [prefixWord, tailWord_7150720, baseEnd_7150720] using wordTrace_append hprefix tailTrace_7150720
  have hstable : (prefixWord ++ tailWord_7150720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150720).length < 2 ^ (prefixWord ++ tailWord_7150720).sum := by decide
  have hdescent : baseEnd_7150720 < baseStart_7150720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150747 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 6, 4, 2]
def baseStart_7150747 : Nat := 118140960795 + 7150747 * 2 ^ 59
def prefixEnd_7150747 : Nat := 4983230072969 + 3 ^ 40 * 7150747 * 2
def baseEnd_7150747 : Nat := 3671770249696039403176819

theorem tailTrace_7150747 : CollatzResearch.WordTrace tailWord_7150747 prefixEnd_7150747 3671770249696039403176819 := by
  unfold tailWord_7150747
  simp only [CollatzResearch.WordTrace]
  refine ⟨260809169425072344204002495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173872779616714896136001663 260809169425072344204002495)
  ·
    refine ⟨391213754137608516306003743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260809169425072344204002495 391213754137608516306003743)
    ·
      refine ⟨586820631206412774459005615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391213754137608516306003743 586820631206412774459005615)
      ·
        refine ⟨880230946809619161688508423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586820631206412774459005615 880230946809619161688508423)
        ·
          refine ⟨1320346420214428742532762635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880230946809619161688508423 1320346420214428742532762635)
          ·
            refine ⟨1980519630321643113799143953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320346420214428742532762635 1980519630321643113799143953)
            ·
              refine ⟨1485389722741232335349357965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980519630321643113799143953 1485389722741232335349357965)
              ·
                refine ⟨557021146027962125756009237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1485389722741232335349357965 557021146027962125756009237)
                ·
                  refine ⟨26110366220060724644812933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557021146027962125756009237 26110366220060724644812933)
                  ·
                    refine ⟨4895693666261385870902425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26110366220060724644812933 4895693666261385870902425)
                    ·
                      refine ⟨3671770249696039403176819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895693666261385870902425 3671770249696039403176819)
                      ·
                        rfl

theorem cell23_7150747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4, 2].length) (baseStart_7150747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150747 prefixEnd_7150747 := by exact prefixLift 7150747
  have htrace : WordTrace (prefixWord ++ tailWord_7150747) baseStart_7150747 baseEnd_7150747 := by
    simpa [prefixWord, tailWord_7150747, baseEnd_7150747] using wordTrace_append hprefix tailTrace_7150747
  have hstable : (prefixWord ++ tailWord_7150747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150747).length < 2 ^ (prefixWord ++ tailWord_7150747).sum := by decide
  have hdescent : baseEnd_7150747 < baseStart_7150747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150767 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_7150767 : Nat := 118140960795 + 7150767 * 2 ^ 59
def prefixEnd_7150767 : Nat := 4983230072969 + 3 ^ 40 * 7150767 * 2
def baseEnd_7150767 : Nat := 3671780519309129324926727

theorem tailTrace_7150767 : CollatzResearch.WordTrace tailWord_7150767 prefixEnd_7150767 3671780519309129324926727 := by
  unfold tailWord_7150767
  simp only [CollatzResearch.WordTrace]
  refine ⟨260809898884999887619730555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173873265923333258413153703 260809898884999887619730555)
  ·
    refine ⟨391214848327499831429595833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260809898884999887619730555 391214848327499831429595833)
    ·
      refine ⟨293411136245624873572196875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391214848327499831429595833 293411136245624873572196875)
      ·
        refine ⟨440116704368437310358295313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293411136245624873572196875 440116704368437310358295313)
        ·
          refine ⟨330087528276327982768721485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440116704368437310358295313 330087528276327982768721485)
          ·
            refine ⟨123782823103622993538270557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330087528276327982768721485 123782823103622993538270557)
            ·
              refine ⟨46418558663858622576851459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123782823103622993538270557 46418558663858622576851459)
              ·
                refine ⟨69627837995787933865277189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46418558663858622576851459 69627837995787933865277189)
                ·
                  refine ⟨13055219624210237599739473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69627837995787933865277189 13055219624210237599739473)
                  ·
                    refine ⟨9791414718157678199804605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13055219624210237599739473 9791414718157678199804605)
                    ·
                      refine ⟨3671780519309129324926727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9791414718157678199804605 3671780519309129324926727)
                      ·
                        rfl

theorem cell23_7150767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_7150767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150767 prefixEnd_7150767 := by exact prefixLift 7150767
  have htrace : WordTrace (prefixWord ++ tailWord_7150767) baseStart_7150767 baseEnd_7150767 := by
    simpa [prefixWord, tailWord_7150767, baseEnd_7150767] using wordTrace_append hprefix tailTrace_7150767
  have hstable : (prefixWord ++ tailWord_7150767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150767).length < 2 ^ (prefixWord ++ tailWord_7150767).sum := by decide
  have hdescent : baseEnd_7150767 < baseStart_7150767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150847 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 1, 6]
def baseStart_7150847 : Nat := 118140960795 + 7150847 * 2 ^ 59
def prefixEnd_7150847 : Nat := 4983230072969 + 3 ^ 40 * 7150847 * 2
def baseEnd_7150847 : Nat := 1223940532587163003975453

theorem tailTrace_7150847 : CollatzResearch.WordTrace tailWord_7150847 prefixEnd_7150847 1223940532587163003975453 := by
  unfold tailWord_7150847
  simp only [CollatzResearch.WordTrace]
  refine ⟨260812816724710061282642795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173875211149806707521761863 260812816724710061282642795)
  ·
    refine ⟨391219225087065091923964193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260812816724710061282642795 391219225087065091923964193)
    ·
      refine ⟨293414418815298818942973145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391219225087065091923964193 293414418815298818942973145)
      ·
        refine ⟨220060814111474114207229859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293414418815298818942973145 220060814111474114207229859)
        ·
          refine ⟨330091221167211171310844789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220060814111474114207229859 330091221167211171310844789)
          ·
            refine ⟨30946051984426047310391699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330091221167211171310844789 30946051984426047310391699)
            ·
              refine ⟨46419077976639070965587549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30946051984426047310391699 46419077976639070965587549)
              ·
                refine ⟨17407154241239651612095331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46419077976639070965587549 17407154241239651612095331)
                ·
                  refine ⟨26110731361859477418142997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17407154241239651612095331 26110731361859477418142997)
                  ·
                    refine ⟨1223940532587163003975453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26110731361859477418142997 1223940532587163003975453)
                    ·
                      rfl

theorem cell23_7150847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_7150847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150847 prefixEnd_7150847 := by exact prefixLift 7150847
  have htrace : WordTrace (prefixWord ++ tailWord_7150847) baseStart_7150847 baseEnd_7150847 := by
    simpa [prefixWord, tailWord_7150847, baseEnd_7150847] using wordTrace_append hprefix tailTrace_7150847
  have hstable : (prefixWord ++ tailWord_7150847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150847).length < 2 ^ (prefixWord ++ tailWord_7150847).sum := by decide
  have hdescent : baseEnd_7150847 < baseStart_7150847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150871 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 5, 2, 2]
def baseStart_7150871 : Nat := 118140960795 + 7150871 * 2 ^ 59
def prefixEnd_7150871 : Nat := 4983230072969 + 3 ^ 40 * 7150871 * 2
def baseEnd_7150871 : Nat := 3671833921297196918026249

theorem tailTrace_7150871 : CollatzResearch.WordTrace tailWord_7150871 prefixEnd_7150871 3671833921297196918026249 := by
  unfold tailWord_7150871
  simp only [CollatzResearch.WordTrace]
  refine ⟨260813692076623113381516467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173875794717748742254344311 260813692076623113381516467)
  ·
    refine ⟨391220538114934670072274701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260813692076623113381516467 391220538114934670072274701)
    ·
      refine ⟨146707701793100501277103013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391220538114934670072274701 146707701793100501277103013)
      ·
        refine ⟨27507694086206343989456815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146707701793100501277103013 27507694086206343989456815)
        ·
          refine ⟨41261541129309515984185223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27507694086206343989456815 41261541129309515984185223)
          ·
            refine ⟨61892311693964273976277835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41261541129309515984185223 61892311693964273976277835)
            ·
              refine ⟨92838467540946410964416753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61892311693964273976277835 92838467540946410964416753)
              ·
                refine ⟨69628850655709808223312565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92838467540946410964416753 69628850655709808223312565)
                ·
                  refine ⟨6527704748972794520935553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69628850655709808223312565 6527704748972794520935553)
                  ·
                    refine ⟨4895778561729595890701665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6527704748972794520935553 4895778561729595890701665)
                    ·
                      refine ⟨3671833921297196918026249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895778561729595890701665 3671833921297196918026249)
                      ·
                        rfl

theorem cell23_7150871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_7150871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150871 prefixEnd_7150871 := by exact prefixLift 7150871
  have htrace : WordTrace (prefixWord ++ tailWord_7150871) baseStart_7150871 baseEnd_7150871 := by
    simpa [prefixWord, tailWord_7150871, baseEnd_7150871] using wordTrace_append hprefix tailTrace_7150871
  have hstable : (prefixWord ++ tailWord_7150871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150871).length < 2 ^ (prefixWord ++ tailWord_7150871).sum := by decide
  have hdescent : baseEnd_7150871 < baseStart_7150871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150888 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_7150888 : Nat := 118140960795 + 7150888 * 2 ^ 59
def prefixEnd_7150888 : Nat := 4983230072969 + 3 ^ 40 * 7150888 * 2
def baseEnd_7150888 : Nat := 3671842650468323351513671

theorem tailTrace_7150888 : CollatzResearch.WordTrace tailWord_7150888 prefixEnd_7150888 3671842650468323351513671 := by
  unfold tailWord_7150888
  simp only [CollatzResearch.WordTrace]
  refine ⟨130407156058780762642442659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173876208078374350189923545 130407156058780762642442659)
  ·
    refine ⟨195610734088171143963663989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130407156058780762642442659 195610734088171143963663989)
    ·
      refine ⟨18338506320766044746593499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195610734088171143963663989 18338506320766044746593499)
      ·
        refine ⟨27507759481149067119890249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18338506320766044746593499 27507759481149067119890249)
        ·
          refine ⟨20630819610861800339917687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27507759481149067119890249 20630819610861800339917687)
          ·
            refine ⟨30946229416292700509876531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20630819610861800339917687 30946229416292700509876531)
            ·
              refine ⟨46419344124439050764814797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30946229416292700509876531 46419344124439050764814797)
              ·
                refine ⟨17407254046664644036805549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46419344124439050764814797 17407254046664644036805549)
                ·
                  refine ⟨6527720267499241513802081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17407254046664644036805549 6527720267499241513802081)
                  ·
                    refine ⟨4895790200624431135351561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6527720267499241513802081 4895790200624431135351561)
                    ·
                      refine ⟨3671842650468323351513671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895790200624431135351561 3671842650468323351513671)
                      ·
                        rfl

theorem cell23_7150888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_7150888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150888 prefixEnd_7150888 := by exact prefixLift 7150888
  have htrace : WordTrace (prefixWord ++ tailWord_7150888) baseStart_7150888 baseEnd_7150888 := by
    simpa [prefixWord, tailWord_7150888, baseEnd_7150888] using wordTrace_append hprefix tailTrace_7150888
  have hstable : (prefixWord ++ tailWord_7150888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150888).length < 2 ^ (prefixWord ++ tailWord_7150888).sum := by decide
  have hdescent : baseEnd_7150888 < baseStart_7150888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150898 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_7150898 : Nat := 118140960795 + 7150898 * 2 ^ 59
def prefixEnd_7150898 : Nat := 4983230072969 + 3 ^ 40 * 7150898 * 2
def baseEnd_7150898 : Nat := 1223949261758289437462875

theorem tailTrace_7150898 : CollatzResearch.WordTrace tailWord_7150898 prefixEnd_7150898 1223949261758289437462875 := by
  unfold tailWord_7150898
  simp only [CollatzResearch.WordTrace]
  refine ⟨65203669211881324248187337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173876451231683531328499565 65203669211881324248187337)
  ·
    refine ⟨48902751908910993186140503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65203669211881324248187337 48902751908910993186140503)
    ·
      refine ⟨73354127863366489779210755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48902751908910993186140503 73354127863366489779210755)
      ·
        refine ⟨110031191795049734668816133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73354127863366489779210755 110031191795049734668816133)
        ·
          refine ⟨20630848461571825250403025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110031191795049734668816133 20630848461571825250403025)
          ·
            refine ⟨15473136346178868937802269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20630848461571825250403025 15473136346178868937802269)
            ·
              refine ⟨5802426129817075851675851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15473136346178868937802269 5802426129817075851675851)
              ·
                refine ⟨8703639194725613777513777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802426129817075851675851 8703639194725613777513777)
                ·
                  refine ⟨6527729396044210333135333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703639194725613777513777 6527729396044210333135333)
                  ·
                    refine ⟨1223949261758289437462875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6527729396044210333135333 1223949261758289437462875)
                    ·
                      rfl

theorem cell23_7150898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_7150898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150898 prefixEnd_7150898 := by exact prefixLift 7150898
  have htrace : WordTrace (prefixWord ++ tailWord_7150898) baseStart_7150898 baseEnd_7150898 := by
    simpa [prefixWord, tailWord_7150898, baseEnd_7150898] using wordTrace_append hprefix tailTrace_7150898
  have hstable : (prefixWord ++ tailWord_7150898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150898).length < 2 ^ (prefixWord ++ tailWord_7150898).sum := by decide
  have hdescent : baseEnd_7150898 < baseStart_7150898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150901 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_7150901 : Nat := 118140960795 + 7150901 * 2 ^ 59
def prefixEnd_7150901 : Nat := 4983230072969 + 3 ^ 40 * 7150901 * 2
def baseEnd_7150901 : Nat := 3671849325716831800651111

theorem tailTrace_7150901 : CollatzResearch.WordTrace tailWord_7150901 prefixEnd_7150901 3671849325716831800651111 := by
  unfold tailWord_7150901
  simp only [CollatzResearch.WordTrace]
  refine ⟨260814786266514428505108557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173876524177676285670072371 260814786266514428505108557)
  ·
    refine ⟨97805544849942910689415709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260814786266514428505108557 97805544849942910689415709)
    ·
      refine ⟨36677079318728591508530891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97805544849942910689415709 36677079318728591508530891)
      ·
        refine ⟨55015618978092887262796337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36677079318728591508530891 55015618978092887262796337)
        ·
          refine ⟨41261714233569665447097253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55015618978092887262796337 41261714233569665447097253)
          ·
            refine ⟨7736571418794312271330735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41261714233569665447097253 7736571418794312271330735)
            ·
              refine ⟨11604857128191468406996103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736571418794312271330735 11604857128191468406996103)
              ·
                refine ⟨17407285692287202610494155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11604857128191468406996103 17407285692287202610494155)
                ·
                  refine ⟨26110928538430803915741233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17407285692287202610494155 26110928538430803915741233)
                  ·
                    refine ⟨19583196403823102936805925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26110928538430803915741233 19583196403823102936805925)
                    ·
                      refine ⟨3671849325716831800651111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19583196403823102936805925 3671849325716831800651111)
                      ·
                        rfl

theorem cell23_7150901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_7150901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150901 prefixEnd_7150901 := by exact prefixLift 7150901
  have htrace : WordTrace (prefixWord ++ tailWord_7150901) baseStart_7150901 baseEnd_7150901 := by
    simpa [prefixWord, tailWord_7150901, baseEnd_7150901] using wordTrace_append hprefix tailTrace_7150901
  have hstable : (prefixWord ++ tailWord_7150901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150901).length < 2 ^ (prefixWord ++ tailWord_7150901).sum := by decide
  have hdescent : baseEnd_7150901 < baseStart_7150901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150931 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 1, 3, 2]
def baseStart_7150931 : Nat := 118140960795 + 7150931 * 2 ^ 59
def prefixEnd_7150931 : Nat := 4983230072969 + 3 ^ 40 * 7150931 * 2
def baseEnd_7150931 : Nat := 3671864730136466683275973

theorem tailTrace_7150931 : CollatzResearch.WordTrace tailWord_7150931 prefixEnd_7150931 3671864730136466683275973 := by
  unfold tailWord_7150931
  simp only [CollatzResearch.WordTrace]
  refine ⟨260815880456405743628700647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173877253637603829085800431 260815880456405743628700647)
  ·
    refine ⟨391223820684608615443050971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260815880456405743628700647 391223820684608615443050971)
    ·
      refine ⟨586835731026912923164576457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391223820684608615443050971 586835731026912923164576457)
      ·
        refine ⟨440126798270184692373432343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586835731026912923164576457 440126798270184692373432343)
        ·
          refine ⟨660190197405277038560148515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440126798270184692373432343 660190197405277038560148515)
          ·
            refine ⟨990285296107915557840222773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660190197405277038560148515 990285296107915557840222773)
            ·
              refine ⟨92839246510117083547520885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 990285296107915557840222773 92839246510117083547520885)
              ·
                refine ⟨8703679360323476582580083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92839246510117083547520885 8703679360323476582580083)
                ·
                  refine ⟨13055519040485214873870125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703679360323476582580083 13055519040485214873870125)
                  ·
                    refine ⟨4895819640181955577701297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13055519040485214873870125 4895819640181955577701297)
                    ·
                      refine ⟨3671864730136466683275973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895819640181955577701297 3671864730136466683275973)
                      ·
                        rfl

theorem cell23_7150931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 3, 2].length) (baseStart_7150931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150931 prefixEnd_7150931 := by exact prefixLift 7150931
  have htrace : WordTrace (prefixWord ++ tailWord_7150931) baseStart_7150931 baseEnd_7150931 := by
    simpa [prefixWord, tailWord_7150931, baseEnd_7150931] using wordTrace_append hprefix tailTrace_7150931
  have hstable : (prefixWord ++ tailWord_7150931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150931).length < 2 ^ (prefixWord ++ tailWord_7150931).sum := by decide
  have hdescent : baseEnd_7150931 < baseStart_7150931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150937 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_7150937 : Nat := 118140960795 + 7150937 * 2 ^ 59
def prefixEnd_7150937 : Nat := 4983230072969 + 3 ^ 40 * 7150937 * 2
def baseEnd_7150937 : Nat := 1223955937006797886600315

theorem tailTrace_7150937 : CollatzResearch.WordTrace tailWord_7150937 prefixEnd_7150937 1223955937006797886600315 := by
  unfold tailWord_7150937
  simp only [CollatzResearch.WordTrace]
  refine ⟨260816099294384006653419065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173877399529589337768946043 260816099294384006653419065)
  ·
    refine ⟨195612074470788004990064299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260816099294384006653419065 195612074470788004990064299)
    ·
      refine ⟨293418111706182007485096449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195612074470788004990064299 293418111706182007485096449)
      ·
        refine ⟨220063583779636505613822337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293418111706182007485096449 220063583779636505613822337)
        ·
          refine ⟨165047687834727379210366753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220063583779636505613822337 165047687834727379210366753)
          ·
            refine ⟨123785765876045534407775065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165047687834727379210366753 123785765876045534407775065)
            ·
              refine ⟨92839324407034150805831299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123785765876045534407775065 92839324407034150805831299)
              ·
                refine ⟨139258986610551226208746949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92839324407034150805831299 139258986610551226208746949)
                ·
                  refine ⟨26111059989478354914140053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139258986610551226208746949 26111059989478354914140053)
                  ·
                    refine ⟨1223955937006797886600315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26111059989478354914140053 1223955937006797886600315)
                    ·
                      rfl

theorem cell23_7150937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_7150937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150937 prefixEnd_7150937 := by exact prefixLift 7150937
  have htrace : WordTrace (prefixWord ++ tailWord_7150937) baseStart_7150937 baseEnd_7150937 := by
    simpa [prefixWord, tailWord_7150937, baseEnd_7150937] using wordTrace_append hprefix tailTrace_7150937
  have hstable : (prefixWord ++ tailWord_7150937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150937).length < 2 ^ (prefixWord ++ tailWord_7150937).sum := by decide
  have hdescent : baseEnd_7150937 < baseStart_7150937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150967 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 9]
def baseStart_7150967 : Nat := 118140960795 + 7150967 * 2 ^ 59
def prefixEnd_7150967 : Nat := 4983230072969 + 3 ^ 40 * 7150967 * 2
def baseEnd_7150967 : Nat := 407987023937780949158423

theorem tailTrace_7150967 : CollatzResearch.WordTrace tailWord_7150967 prefixEnd_7150967 407987023937780949158423 := by
  unfold tailWord_7150967
  simp only [CollatzResearch.WordTrace]
  refine ⟨260817193484275321777011155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173878128989516881184674103 260817193484275321777011155)
  ·
    refine ⟨391225790226412982665516733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260817193484275321777011155 391225790226412982665516733)
    ·
      refine ⟨146709671334904868499568775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391225790226412982665516733 146709671334904868499568775)
      ·
        refine ⟨220064507002357302749353163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146709671334904868499568775 220064507002357302749353163)
        ·
          refine ⟨330096760503535954124029745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220064507002357302749353163 330096760503535954124029745)
          ·
            refine ⟨247572570377651965593022309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330096760503535954124029745 247572570377651965593022309)
            ·
              refine ⟨46419856945809743548691683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247572570377651965593022309 46419856945809743548691683)
              ·
                refine ⟨69629785418714615323037525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46419856945809743548691683 69629785418714615323037525)
                ·
                  refine ⟨407987023937780949158423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69629785418714615323037525 407987023937780949158423)
                  ·
                    rfl

theorem cell23_7150967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 9].length) (baseStart_7150967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150967 prefixEnd_7150967 := by exact prefixLift 7150967
  have htrace : WordTrace (prefixWord ++ tailWord_7150967) baseStart_7150967 baseEnd_7150967 := by
    simpa [prefixWord, tailWord_7150967, baseEnd_7150967] using wordTrace_append hprefix tailTrace_7150967
  have hstable : (prefixWord ++ tailWord_7150967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150967).length < 2 ^ (prefixWord ++ tailWord_7150967).sum := by decide
  have hdescent : baseEnd_7150967 < baseStart_7150967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151001 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 5]
def baseStart_7151001 : Nat := 118140960795 + 7151001 * 2 ^ 59
def prefixEnd_7151001 : Nat := 4983230072969 + 3 ^ 40 * 7151001 * 2
def baseEnd_7151001 : Nat := 407988963753586823266739

theorem tailTrace_7151001 : CollatzResearch.WordTrace tailWord_7151001 prefixEnd_7151001 407988963753586823266739 := by
  unfold tailWord_7151001
  simp only [CollatzResearch.WordTrace]
  refine ⟨260818433566152145583748857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173878955710768097055832571 260818433566152145583748857)
  ·
    refine ⟨195613825174614109187811643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260818433566152145583748857 195613825174614109187811643)
    ·
      refine ⟨293420737761921163781717465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195613825174614109187811643 293420737761921163781717465)
      ·
        refine ⟨220065553321440872836288099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293420737761921163781717465 220065553321440872836288099)
        ·
          refine ⟨330098329982161309254432149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220065553321440872836288099 330098329982161309254432149)
          ·
            refine ⟨15473359217913811371301507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 330098329982161309254432149 15473359217913811371301507)
            ·
              refine ⟨23210038826870717056952261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15473359217913811371301507 23210038826870717056952261)
              ·
                refine ⟨4351882280038259448178549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23210038826870717056952261 4351882280038259448178549)
                ·
                  refine ⟨407988963753586823266739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4351882280038259448178549 407988963753586823266739)
                  ·
                    rfl

theorem cell23_7151001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 5].length) (baseStart_7151001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151001 prefixEnd_7151001 := by exact prefixLift 7151001
  have htrace : WordTrace (prefixWord ++ tailWord_7151001) baseStart_7151001 baseEnd_7151001 := by
    simpa [prefixWord, tailWord_7151001, baseEnd_7151001] using wordTrace_append hprefix tailTrace_7151001
  have hstable : (prefixWord ++ tailWord_7151001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151001).length < 2 ^ (prefixWord ++ tailWord_7151001).sum := by decide
  have hdescent : baseEnd_7151001 < baseStart_7151001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151051 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 2, 4, 2]
def baseStart_7151051 : Nat := 118140960795 + 7151051 * 2 ^ 59
def prefixEnd_7151051 : Nat := 4983230072969 + 3 ^ 40 * 7151051 * 2
def baseEnd_7151051 : Nat := 3671926347815006213775421

theorem tailTrace_7151051 : CollatzResearch.WordTrace tailWord_7151051 prefixEnd_7151051 3671926347815006213775421 := by
  unfold tailWord_7151051
  simp only [CollatzResearch.WordTrace]
  refine ⟨260820257215971004123069007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173880171477314002748712671 260820257215971004123069007)
  ·
    refine ⟨391230385823956506184603511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260820257215971004123069007 391230385823956506184603511)
    ·
      refine ⟨586845578735934759276905267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391230385823956506184603511 586845578735934759276905267)
      ·
        refine ⟨880268368103902138915357901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586845578735934759276905267 880268368103902138915357901)
        ·
          refine ⟨330100638038963302093259213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 880268368103902138915357901 330100638038963302093259213)
          ·
            refine ⟨123787739264611238284972205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330100638038963302093259213 123787739264611238284972205)
            ·
              refine ⟨46420402224229214356864577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123787739264611238284972205 46420402224229214356864577)
              ·
                refine ⟨34815301668171910767648433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46420402224229214356864577 34815301668171910767648433)
                ·
                  refine ⟨26111476251128933075736325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34815301668171910767648433 26111476251128933075736325)
                  ·
                    refine ⟨4895901797086674951700561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26111476251128933075736325 4895901797086674951700561)
                    ·
                      refine ⟨3671926347815006213775421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895901797086674951700561 3671926347815006213775421)
                      ·
                        rfl

theorem cell23_7151051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4, 2].length) (baseStart_7151051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151051 prefixEnd_7151051 := by exact prefixLift 7151051
  have htrace : WordTrace (prefixWord ++ tailWord_7151051) baseStart_7151051 baseEnd_7151051 := by
    simpa [prefixWord, tailWord_7151051, baseEnd_7151051] using wordTrace_append hprefix tailTrace_7151051
  have hstable : (prefixWord ++ tailWord_7151051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151051).length < 2 ^ (prefixWord ++ tailWord_7151051).sum := by decide
  have hdescent : baseEnd_7151051 < baseStart_7151051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151054 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_7151054 : Nat := 118140960795 + 7151054 * 2 ^ 59
def prefixEnd_7151054 : Nat := 4983230072969 + 3 ^ 40 * 7151054 * 2
def baseEnd_7151054 : Nat := 3671927888256969702037907

theorem tailTrace_7151054 : CollatzResearch.WordTrace tailWord_7151054 prefixEnd_7151054 3671927888256969702037907 := by
  unfold tailWord_7151054
  simp only [CollatzResearch.WordTrace]
  refine ⟨32602545829370016954428527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173880244423306757090285477 32602545829370016954428527)
  ·
    refine ⟨48903818744055025431642791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32602545829370016954428527 48903818744055025431642791)
    ·
      refine ⟨73355728116082538147464187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48903818744055025431642791 73355728116082538147464187)
      ·
        refine ⟨110033592174123807221196281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73355728116082538147464187 110033592174123807221196281)
        ·
          refine ⟨82525194130592855415897211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110033592174123807221196281 82525194130592855415897211)
          ·
            refine ⟨123787791195889283123845817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82525194130592855415897211 123787791195889283123845817)
            ·
              refine ⟨92840843396916962342884363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123787791195889283123845817 92840843396916962342884363)
              ·
                refine ⟨139261265095375443514326545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92840843396916962342884363 139261265095375443514326545)
                ·
                  refine ⟨104445948821531582635744909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139261265095375443514326545 104445948821531582635744909)
                  ·
                    refine ⟨39167230808074343488404341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104445948821531582635744909 39167230808074343488404341)
                    ·
                      refine ⟨3671927888256969702037907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39167230808074343488404341 3671927888256969702037907)
                      ·
                        rfl

theorem cell23_7151054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_7151054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151054 prefixEnd_7151054 := by exact prefixLift 7151054
  have htrace : WordTrace (prefixWord ++ tailWord_7151054) baseStart_7151054 baseEnd_7151054 := by
    simpa [prefixWord, tailWord_7151054, baseEnd_7151054] using wordTrace_append hprefix tailTrace_7151054
  have hstable : (prefixWord ++ tailWord_7151054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151054).length < 2 ^ (prefixWord ++ tailWord_7151054).sum := by decide
  have hdescent : baseEnd_7151054 < baseStart_7151054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151138 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7151138 : Nat := 118140960795 + 7151138 * 2 ^ 59
def prefixEnd_7151138 : Nat := 4983230072969 + 3 ^ 40 * 7151138 * 2
def baseEnd_7151138 : Nat := 1223990340210649124462507

theorem tailTrace_7151138 : CollatzResearch.WordTrace tailWord_7151138 prefixEnd_7151138 1223990340210649124462507 := by
  unfold tailWord_7151138
  simp only [CollatzResearch.WordTrace]
  refine ⟨65205857591663954495371517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173882286911103878654324045 65205857591663954495371517)
  ·
    refine ⟨24452196596873982935764319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65205857591663954495371517 24452196596873982935764319)
    ·
      refine ⟨36678294895310974403646479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24452196596873982935764319 36678294895310974403646479)
      ·
        refine ⟨55017442342966461605469719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36678294895310974403646479 55017442342966461605469719)
        ·
          refine ⟨82526163514449692408204579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55017442342966461605469719 82526163514449692408204579)
          ·
            refine ⟨123789245271674538612306869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82526163514449692408204579 123789245271674538612306869)
            ·
              refine ⟨11605241744219487994903769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123789245271674538612306869 11605241744219487994903769)
              ·
                refine ⟨8703931308164615996177827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11605241744219487994903769 8703931308164615996177827)
                ·
                  refine ⟨13055896962246923994266741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8703931308164615996177827 13055896962246923994266741)
                  ·
                    refine ⟨1223990340210649124462507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13055896962246923994266741 1223990340210649124462507)
                    ·
                      rfl

theorem cell23_7151138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7151138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151138 prefixEnd_7151138 := by exact prefixLift 7151138
  have htrace : WordTrace (prefixWord ++ tailWord_7151138) baseStart_7151138 baseEnd_7151138 := by
    simpa [prefixWord, tailWord_7151138, baseEnd_7151138] using wordTrace_append hprefix tailTrace_7151138
  have hstable : (prefixWord ++ tailWord_7151138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151138).length < 2 ^ (prefixWord ++ tailWord_7151138).sum := by decide
  have hdescent : baseEnd_7151138 < baseStart_7151138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151164 : List Nat := [2, 2, 2, 2, 15]
def baseStart_7151164 : Nat := 118140960795 + 7151164 * 2 ^ 59
def prefixEnd_7151164 : Nat := 4983230072969 + 3 ^ 40 * 7151164 * 2
def baseEnd_7151164 : Nat := 5037015598256466764969

theorem tailTrace_7151164 : CollatzResearch.WordTrace tailWord_7151164 prefixEnd_7151164 5037015598256466764969 := by
  unfold tailWord_7151164
  simp only [CollatzResearch.WordTrace]
  refine ⟨130412189332280812210966273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173882919109707749614621697 130412189332280812210966273)
  ·
    refine ⟨97809141999210609158224705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130412189332280812210966273 97809141999210609158224705)
    ·
      refine ⟨73356856499407956868668529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97809141999210609158224705 73356856499407956868668529)
      ·
        refine ⟨55017642374555967651501397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73356856499407956868668529 55017642374555967651501397)
        ·
          refine ⟨5037015598256466764969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 55017642374555967651501397 5037015598256466764969)
          ·
            rfl

theorem cell23_7151164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 15].length) (baseStart_7151164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151164 prefixEnd_7151164 := by exact prefixLift 7151164
  have htrace : WordTrace (prefixWord ++ tailWord_7151164) baseStart_7151164 baseEnd_7151164 := by
    simpa [prefixWord, tailWord_7151164, baseEnd_7151164] using wordTrace_append hprefix tailTrace_7151164
  have hstable : (prefixWord ++ tailWord_7151164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151164).length < 2 ^ (prefixWord ++ tailWord_7151164).sum := by decide
  have hdescent : baseEnd_7151164 < baseStart_7151164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151188 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_7151188 : Nat := 118140960795 + 7151188 * 2 ^ 59
def prefixEnd_7151188 : Nat := 4983230072969 + 3 ^ 40 * 7151188 * 2
def baseEnd_7151188 : Nat := 3671996694664672177762291

theorem tailTrace_7151188 : CollatzResearch.WordTrace tailWord_7151188 prefixEnd_7151188 3671996694664672177762291 := by
  unfold tailWord_7151188
  simp only [CollatzResearch.WordTrace]
  refine ⟨130412627008237338260403109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173883502677649784347204145 130412627008237338260403109)
  ·
    refine ⟨24452367564044500923825583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130412627008237338260403109 24452367564044500923825583)
    ·
      refine ⟨36678551346066751385738375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24452367564044500923825583 36678551346066751385738375)
      ·
        refine ⟨55017827019100127078607563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36678551346066751385738375 55017827019100127078607563)
        ·
          refine ⟨82526740528650190617911345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55017827019100127078607563 82526740528650190617911345)
          ·
            refine ⟨61895055396487642963433509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82526740528650190617911345 61895055396487642963433509)
            ·
              refine ⟨11605322886841433055643783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61895055396487642963433509 11605322886841433055643783)
              ·
                refine ⟨17407984330262149583465675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11605322886841433055643783 17407984330262149583465675)
                ·
                  refine ⟨26111976495393224375198513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17407984330262149583465675 26111976495393224375198513)
                  ·
                    refine ⟨19583982371544918281398885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26111976495393224375198513 19583982371544918281398885)
                    ·
                      refine ⟨3671996694664672177762291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19583982371544918281398885 3671996694664672177762291)
                      ·
                        rfl

theorem cell23_7151188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_7151188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151188 prefixEnd_7151188 := by exact prefixLift 7151188
  have htrace : WordTrace (prefixWord ++ tailWord_7151188) baseStart_7151188 baseEnd_7151188 := by
    simpa [prefixWord, tailWord_7151188, baseEnd_7151188] using wordTrace_append hprefix tailTrace_7151188
  have hstable : (prefixWord ++ tailWord_7151188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151188).length < 2 ^ (prefixWord ++ tailWord_7151188).sum := by decide
  have hdescent : baseEnd_7151188 < baseStart_7151188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151241 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_7151241 : Nat := 118140960795 + 7151241 * 2 ^ 59
def prefixEnd_7151241 : Nat := 4983230072969 + 3 ^ 40 * 7151241 * 2
def baseEnd_7151241 : Nat := 1224007969713120156799849

theorem tailTrace_7151241 : CollatzResearch.WordTrace tailWord_7151241 prefixEnd_7151241 1224007969713120156799849 := by
  unfold tailWord_7151241
  simp only [CollatzResearch.WordTrace]
  refine ⟨260827187085282666572485577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173884791390188444381657051 260827187085282666572485577)
  ·
    refine ⟨195620390313961999929364183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260827187085282666572485577 195620390313961999929364183)
    ·
      refine ⟨293430585470942999894046275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195620390313961999929364183 293430585470942999894046275)
      ·
        refine ⟨440145878206414499841069413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293430585470942999894046275 440145878206414499841069413)
        ·
          refine ⟨82527352163702718720200515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440145878206414499841069413 82527352163702718720200515)
          ·
            refine ⟨123791028245554078080300773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82527352163702718720200515 123791028245554078080300773)
            ·
              refine ⟨23210817796041389640056395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123791028245554078080300773 23210817796041389640056395)
              ·
                refine ⟨34816226694062084460084593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23210817796041389640056395 34816226694062084460084593)
                ·
                  refine ⟨26112170020546563345063445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34816226694062084460084593 26112170020546563345063445)
                  ·
                    refine ⟨1224007969713120156799849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26112170020546563345063445 1224007969713120156799849)
                    ·
                      rfl

theorem cell23_7151241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_7151241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151241 prefixEnd_7151241 := by exact prefixLift 7151241
  have htrace : WordTrace (prefixWord ++ tailWord_7151241) baseStart_7151241 baseEnd_7151241 := by
    simpa [prefixWord, tailWord_7151241, baseEnd_7151241] using wordTrace_append hprefix tailTrace_7151241
  have hstable : (prefixWord ++ tailWord_7151241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151241).length < 2 ^ (prefixWord ++ tailWord_7151241).sum := by decide
  have hdescent : baseEnd_7151241 < baseStart_7151241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151268 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_7151268 : Nat := 118140960795 + 7151268 * 2 ^ 59
def prefixEnd_7151268 : Nat := 4983230072969 + 3 ^ 40 * 7151268 * 2
def baseEnd_7151268 : Nat := 3672037773117031864761923

theorem tailTrace_7151268 : CollatzResearch.WordTrace tailWord_7151268 prefixEnd_7151268 3672037773117031864761923 := by
  unfold tailWord_7151268
  simp only [CollatzResearch.WordTrace]
  refine ⟨130414085928092425091859229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173885447904123233455812305 130414085928092425091859229)
  ·
    refine ⟨48905282223034659409447211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130414085928092425091859229 48905282223034659409447211)
    ·
      refine ⟨73357923334551989114170817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48905282223034659409447211 73357923334551989114170817)
      ·
        refine ⟨55018442500913991835628113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73357923334551989114170817 55018442500913991835628113)
        ·
          refine ⟨41263831875685493876721085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55018442500913991835628113 41263831875685493876721085)
          ·
            refine ⟨15473936953382060203770407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41263831875685493876721085 15473936953382060203770407)
            ·
              refine ⟨23210905430073090305655611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15473936953382060203770407 23210905430073090305655611)
              ·
                refine ⟨34816358145109635458483417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23210905430073090305655611 34816358145109635458483417)
                ·
                  refine ⟨26112268608832226593862563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34816358145109635458483417 26112268608832226593862563)
                  ·
                    refine ⟨39168402913248339890793845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26112268608832226593862563 39168402913248339890793845)
                    ·
                      refine ⟨3672037773117031864761923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39168402913248339890793845 3672037773117031864761923)
                      ·
                        rfl

theorem cell23_7151268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_7151268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151268 prefixEnd_7151268 := by exact prefixLift 7151268
  have htrace : WordTrace (prefixWord ++ tailWord_7151268) baseStart_7151268 baseEnd_7151268 := by
    simpa [prefixWord, tailWord_7151268, baseEnd_7151268] using wordTrace_append hprefix tailTrace_7151268
  have hstable : (prefixWord ++ tailWord_7151268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151268).length < 2 ^ (prefixWord ++ tailWord_7151268).sum := by decide
  have hdescent : baseEnd_7151268 < baseStart_7151268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151288 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 5]
def baseStart_7151288 : Nat := 118140960795 + 7151288 * 2 ^ 59
def prefixEnd_7151288 : Nat := 4983230072969 + 3 ^ 40 * 7151288 * 2
def baseEnd_7151288 : Nat := 408005338081124642945759

theorem tailTrace_7151288 : CollatzResearch.WordTrace tailWord_7151288 prefixEnd_7151288 408005338081124642945759 := by
  unfold tailWord_7151288
  simp only [CollatzResearch.WordTrace]
  refine ⟨130414450658056196799723259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173885934210741595732964345 130414450658056196799723259)
  ·
    refine ⟨195621675987084295199584889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130414450658056196799723259 195621675987084295199584889)
    ·
      refine ⟨146716256990313221399688667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195621675987084295199584889 146716256990313221399688667)
      ·
        refine ⟨220074385485469832099533001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146716256990313221399688667 220074385485469832099533001)
        ·
          refine ⟨165055789114102374074649751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220074385485469832099533001 165055789114102374074649751)
          ·
            refine ⟨247583683671153561111974627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165055789114102374074649751 247583683671153561111974627)
            ·
              refine ⟨371375525506730341667961941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247583683671153561111974627 371375525506730341667961941)
              ·
                refine ⟨4352056939531996191421429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 371375525506730341667961941 4352056939531996191421429)
                ·
                  refine ⟨408005338081124642945759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352056939531996191421429 408005338081124642945759)
                  ·
                    rfl

theorem cell23_7151288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 5].length) (baseStart_7151288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151288 prefixEnd_7151288 := by exact prefixLift 7151288
  have htrace : WordTrace (prefixWord ++ tailWord_7151288) baseStart_7151288 baseEnd_7151288 := by
    simpa [prefixWord, tailWord_7151288, baseEnd_7151288] using wordTrace_append hprefix tailTrace_7151288
  have hstable : (prefixWord ++ tailWord_7151288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151288).length < 2 ^ (prefixWord ++ tailWord_7151288).sum := by decide
  have hdescent : baseEnd_7151288 < baseStart_7151288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151302 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7151302 : Nat := 118140960795 + 7151302 * 2 ^ 59
def prefixEnd_7151302 : Nat := 4983230072969 + 3 ^ 40 * 7151302 * 2
def baseEnd_7151302 : Nat := 3672055231459284731736767

theorem tailTrace_7151302 : CollatzResearch.WordTrace tailWord_7151302 prefixEnd_7151302 3672055231459284731736767 := by
  unfold tailWord_7151302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150919123064427312201755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173886274625374449326970773 8150919123064427312201755)
  ·
    refine ⟨12226378684596640968302633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150919123064427312201755 12226378684596640968302633)
    ·
      refine ⟨9169784013447480726226975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12226378684596640968302633 9169784013447480726226975)
      ·
        refine ⟨13754676020171221089340463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9169784013447480726226975 13754676020171221089340463)
        ·
          refine ⟨20632014030256831634010695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13754676020171221089340463 20632014030256831634010695)
          ·
            refine ⟨30948021045385247451016043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20632014030256831634010695 30948021045385247451016043)
            ·
              refine ⟨46422031568077871176524065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30948021045385247451016043 46422031568077871176524065)
              ·
                refine ⟨34816523676058403382393049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46422031568077871176524065 34816523676058403382393049)
                ·
                  refine ⟨26112392757043802536794787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34816523676058403382393049 26112392757043802536794787)
                  ·
                    refine ⟨39168589135565703805192181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26112392757043802536794787 39168589135565703805192181)
                    ·
                      refine ⟨3672055231459284731736767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39168589135565703805192181 3672055231459284731736767)
                      ·
                        rfl

theorem cell23_7151302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7151302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151302 prefixEnd_7151302 := by exact prefixLift 7151302
  have htrace : WordTrace (prefixWord ++ tailWord_7151302) baseStart_7151302 baseEnd_7151302 := by
    simpa [prefixWord, tailWord_7151302, baseEnd_7151302] using wordTrace_append hprefix tailTrace_7151302
  have hstable : (prefixWord ++ tailWord_7151302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151302).length < 2 ^ (prefixWord ++ tailWord_7151302).sum := by decide
  have hdescent : baseEnd_7151302 < baseStart_7151302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151373 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7151373 : Nat := 118140960795 + 7151373 * 2 ^ 59
def prefixEnd_7151373 : Nat := 4983230072969 + 3 ^ 40 * 7151373 * 2
def baseEnd_7151373 : Nat := 408010187620639328216549

theorem tailTrace_7151373 : CollatzResearch.WordTrace tailWord_7151373 prefixEnd_7151373 408010187620639328216549 := by
  unfold tailWord_7151373
  simp only [CollatzResearch.WordTrace]
  refine ⟨260832001520804453116290773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173888001013869635410860515 260832001520804453116290773)
  ·
    refine ⟨6113250035643854369913065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 260832001520804453116290773 6113250035643854369913065)
    ·
      refine ⟨4584937526732890777434799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6113250035643854369913065 4584937526732890777434799)
      ·
        refine ⟨6877406290099336166152199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584937526732890777434799 6877406290099336166152199)
        ·
          refine ⟨10316109435149004249228299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877406290099336166152199 10316109435149004249228299)
          ·
            refine ⟨15474164152723506373842449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316109435149004249228299 15474164152723506373842449)
            ·
              refine ⟨11605623114542629780381837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15474164152723506373842449 11605623114542629780381837)
              ·
                refine ⟨4352108667953486167643189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11605623114542629780381837 4352108667953486167643189)
                ·
                  refine ⟨408010187620639328216549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352108667953486167643189 408010187620639328216549)
                  ·
                    rfl

theorem cell23_7151373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7151373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151373 prefixEnd_7151373 := by exact prefixLift 7151373
  have htrace : WordTrace (prefixWord ++ tailWord_7151373) baseStart_7151373 baseEnd_7151373 := by
    simpa [prefixWord, tailWord_7151373, baseEnd_7151373] using wordTrace_append hprefix tailTrace_7151373
  have hstable : (prefixWord ++ tailWord_7151373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151373).length < 2 ^ (prefixWord ++ tailWord_7151373).sum := by decide
  have hdescent : baseEnd_7151373 < baseStart_7151373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151415 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 6, 3, 2]
def baseStart_7151415 : Nat := 118140960795 + 7151415 * 2 ^ 59
def prefixEnd_7151415 : Nat := 4983230072969 + 3 ^ 40 * 7151415 * 2
def baseEnd_7151415 : Nat := 3672113254773242789623747

theorem tailTrace_7151415 : CollatzResearch.WordTrace tailWord_7151415 prefixEnd_7151415 3672113254773242789623747 := by
  unfold tailWord_7151415
  simp only [CollatzResearch.WordTrace]
  refine ⟨260833533386652294289319699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173889022257768196192879799 260833533386652294289319699)
  ·
    refine ⟨391250300079978441433979549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260833533386652294289319699 391250300079978441433979549)
    ·
      refine ⟨146718862529991915537742331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391250300079978441433979549 146718862529991915537742331)
      ·
        refine ⟨220078293794987873306613497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146718862529991915537742331 220078293794987873306613497)
        ·
          refine ⟨165058720346240904979960123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220078293794987873306613497 165058720346240904979960123)
          ·
            refine ⟨247588080519361357469940185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165058720346240904979960123 247588080519361357469940185)
            ·
              refine ⟨185691060389521018102455139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247588080519361357469940185 185691060389521018102455139)
              ·
                refine ⟨278536590584281527153682709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185691060389521018102455139 278536590584281527153682709)
                ·
                  refine ⟨13056402683638196585328877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 278536590584281527153682709 13056402683638196585328877)
                  ·
                    refine ⟨4896151006364323719498329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13056402683638196585328877 4896151006364323719498329)
                    ·
                      refine ⟨3672113254773242789623747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896151006364323719498329 3672113254773242789623747)
                      ·
                        rfl

theorem cell23_7151415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_7151415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151415 prefixEnd_7151415 := by exact prefixLift 7151415
  have htrace : WordTrace (prefixWord ++ tailWord_7151415) baseStart_7151415 baseEnd_7151415 := by
    simpa [prefixWord, tailWord_7151415, baseEnd_7151415] using wordTrace_append hprefix tailTrace_7151415
  have hstable : (prefixWord ++ tailWord_7151415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151415).length < 2 ^ (prefixWord ++ tailWord_7151415).sum := by decide
  have hdescent : baseEnd_7151415 < baseStart_7151415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151455 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 4, 4]
def baseStart_7151455 : Nat := 118140960795 + 7151455 * 2 ^ 59
def prefixEnd_7151455 : Nat := 4983230072969 + 3 ^ 40 * 7151455 * 2
def baseEnd_7151455 : Nat := 1224044597999807544374521

theorem tailTrace_7151455 : CollatzResearch.WordTrace tailWord_7151455 prefixEnd_7151455 1224044597999807544374521 := by
  unfold tailWord_7151455
  simp only [CollatzResearch.WordTrace]
  refine ⟨260834992306507381120775819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173889994871004920747183879 260834992306507381120775819)
  ·
    refine ⟨391252488459761071681163729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260834992306507381120775819 391252488459761071681163729)
    ·
      refine ⟨293439366344820803760872797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391252488459761071681163729 293439366344820803760872797)
      ·
        refine ⟨110039762379307801410327299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293439366344820803760872797 110039762379307801410327299)
        ·
          refine ⟨165059643568961702115490949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110039762379307801410327299 165059643568961702115490949)
          ·
            refine ⟨30948683169180319146654553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165059643568961702115490949 30948683169180319146654553)
            ·
              refine ⟨23211512376885239359990915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30948683169180319146654553 23211512376885239359990915)
              ·
                refine ⟨34817268565327859039986373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23211512376885239359990915 34817268565327859039986373)
                ·
                  refine ⟨6528237855998973569997445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34817268565327859039986373 6528237855998973569997445)
                  ·
                    refine ⟨1224044597999807544374521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6528237855998973569997445 1224044597999807544374521)
                    ·
                      rfl

theorem cell23_7151455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_7151455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151455 prefixEnd_7151455 := by exact prefixLift 7151455
  have htrace : WordTrace (prefixWord ++ tailWord_7151455) baseStart_7151455 baseEnd_7151455 := by
    simpa [prefixWord, tailWord_7151455, baseEnd_7151455] using wordTrace_append hprefix tailTrace_7151455
  have hstable : (prefixWord ++ tailWord_7151455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151455).length < 2 ^ (prefixWord ++ tailWord_7151455).sum := by decide
  have hdescent : baseEnd_7151455 < baseStart_7151455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151456 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 1, 1, 3]
def baseStart_7151456 : Nat := 118140960795 + 7151456 * 2 ^ 59
def prefixEnd_7151456 : Nat := 4983230072969 + 3 ^ 40 * 7151456 * 2
def baseEnd_7151456 : Nat := 3672134307480077129211059

theorem tailTrace_7151456 : CollatzResearch.WordTrace tailWord_7151456 prefixEnd_7151456 3672134307480077129211059 := by
  unfold tailWord_7151456
  simp only [CollatzResearch.WordTrace]
  refine ⟨130417514389751879145781111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173890019186335838861041481 130417514389751879145781111)
  ·
    refine ⟨195626271584627818718671667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130417514389751879145781111 195626271584627818718671667)
    ·
      refine ⟨293439407376941728078007501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195626271584627818718671667 293439407376941728078007501)
      ·
        refine ⟨110039777766353148029252813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293439407376941728078007501 110039777766353148029252813)
        ·
          refine ⟨41264916662382430510969805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110039777766353148029252813 41264916662382430510969805)
          ·
            refine ⟨15474343748393411441613677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41264916662382430510969805 15474343748393411441613677)
            ·
              refine ⟨5802878905647529290605129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15474343748393411441613677 5802878905647529290605129)
              ·
                refine ⟨4352159179235646967953847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802878905647529290605129 4352159179235646967953847)
                ·
                  refine ⟨6528238768853470451930771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4352159179235646967953847 6528238768853470451930771)
                  ·
                    refine ⟨9792358153280205677896157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6528238768853470451930771 9792358153280205677896157)
                    ·
                      refine ⟨3672134307480077129211059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9792358153280205677896157 3672134307480077129211059)
                      ·
                        rfl

theorem cell23_7151456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_7151456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151456 prefixEnd_7151456 := by exact prefixLift 7151456
  have htrace : WordTrace (prefixWord ++ tailWord_7151456) baseStart_7151456 baseEnd_7151456 := by
    simpa [prefixWord, tailWord_7151456, baseEnd_7151456] using wordTrace_append hprefix tailTrace_7151456
  have hstable : (prefixWord ++ tailWord_7151456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151456).length < 2 ^ (prefixWord ++ tailWord_7151456).sum := by decide
  have hdescent : baseEnd_7151456 < baseStart_7151456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151468 : List Nat := [2, 2, 1, 1, 4, 2, 1, 10]
def baseStart_7151468 : Nat := 118140960795 + 7151468 * 2 ^ 59
def prefixEnd_7151468 : Nat := 4983230072969 + 3 ^ 40 * 7151468 * 2
def baseEnd_7151468 : Nat := 136005202564738188231889

theorem tailTrace_7151468 : CollatzResearch.WordTrace tailWord_7151468 prefixEnd_7151468 136005202564738188231889 := by
  unfold tailWord_7151468
  simp only [CollatzResearch.WordTrace]
  refine ⟨130417733227730142170499529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173890310970306856227332705 130417733227730142170499529)
  ·
    refine ⟨97813299920797606627874647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130417733227730142170499529 97813299920797606627874647)
    ·
      refine ⟨146719949881196409941811971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97813299920797606627874647 146719949881196409941811971)
      ·
        refine ⟨220079924821794614912717957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146719949881196409941811971 220079924821794614912717957)
        ·
          refine ⟨41264985904086490296134617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220079924821794614912717957 41264985904086490296134617)
          ·
            refine ⟨30948739428064867722100963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41264985904086490296134617 30948739428064867722100963)
            ·
              refine ⟨46423109142097301583151445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30948739428064867722100963 46423109142097301583151445)
              ·
                refine ⟨136005202564738188231889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46423109142097301583151445 136005202564738188231889)
                ·
                  rfl

theorem cell23_7151468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 10].length) (baseStart_7151468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151468 prefixEnd_7151468 := by exact prefixLift 7151468
  have htrace : WordTrace (prefixWord ++ tailWord_7151468) baseStart_7151468 baseEnd_7151468 := by
    simpa [prefixWord, tailWord_7151468, baseEnd_7151468] using wordTrace_append hprefix tailTrace_7151468
  have hstable : (prefixWord ++ tailWord_7151468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151468).length < 2 ^ (prefixWord ++ tailWord_7151468).sum := by decide
  have hdescent : baseEnd_7151468 < baseStart_7151468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151482 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_7151482 : Nat := 118140960795 + 7151482 * 2 ^ 59
def prefixEnd_7151482 : Nat := 4983230072969 + 3 ^ 40 * 7151482 * 2
def baseEnd_7151482 : Nat := 3672147657977094027485939

theorem tailTrace_7151482 : CollatzResearch.WordTrace tailWord_7151482 prefixEnd_7151482 3672147657977094027485939 := by
  unfold tailWord_7151482
  simp only [CollatzResearch.WordTrace]
  refine ⟨65208994269352391183002175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173890651384939709821339133 65208994269352391183002175)
  ·
    refine ⟨97813491404028586774503263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65208994269352391183002175 97813491404028586774503263)
    ·
      refine ⟨146720237106042880161754895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97813491404028586774503263 146720237106042880161754895)
      ·
        refine ⟨220080355659064320242632343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146720237106042880161754895 220080355659064320242632343)
        ·
          refine ⟨330120533488596480363948515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220080355659064320242632343 330120533488596480363948515)
          ·
            refine ⟨495180800232894720545922773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330120533488596480363948515 495180800232894720545922773)
            ·
              refine ⟨11605800005458470012795065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 495180800232894720545922773 11605800005458470012795065)
              ·
                refine ⟨8704350004093852509596299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11605800005458470012795065 8704350004093852509596299)
                ·
                  refine ⟨13056525006140778764394449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8704350004093852509596299 13056525006140778764394449)
                  ·
                    refine ⟨9792393754605584073295837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13056525006140778764394449 9792393754605584073295837)
                    ·
                      refine ⟨3672147657977094027485939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9792393754605584073295837 3672147657977094027485939)
                      ·
                        rfl

theorem cell23_7151482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_7151482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151482 prefixEnd_7151482 := by exact prefixLift 7151482
  have htrace : WordTrace (prefixWord ++ tailWord_7151482) baseStart_7151482 baseEnd_7151482 := by
    simpa [prefixWord, tailWord_7151482, baseEnd_7151482] using wordTrace_append hprefix tailTrace_7151482
  have hstable : (prefixWord ++ tailWord_7151482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151482).length < 2 ^ (prefixWord ++ tailWord_7151482).sum := by decide
  have hdescent : baseEnd_7151482 < baseStart_7151482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151502 : List Nat := [4, 1, 1, 5, 2, 10]
def baseStart_7151502 : Nat := 118140960795 + 7151502 * 2 ^ 59
def prefixEnd_7151502 : Nat := 4983230072969 + 3 ^ 40 * 7151502 * 2
def baseEnd_7151502 : Nat := 15111761018889645881629

theorem tailTrace_7151502 : CollatzResearch.WordTrace tailWord_7151502 prefixEnd_7151502 15111761018889645881629 := by
  unfold tailWord_7151502
  simp only [CollatzResearch.WordTrace]
  refine ⟨32604588317167138518467095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173891137691558072098491173 32604588317167138518467095)
  ·
    refine ⟨48906882475750707777700643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32604588317167138518467095 48906882475750707777700643)
    ·
      refine ⟨73360323713626061666550965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48906882475750707777700643 73360323713626061666550965)
      ·
        refine ⟨6877530348152443281239153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73360323713626061666550965 6877530348152443281239153)
        ·
          refine ⟨5158147761114332460929365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877530348152443281239153 5158147761114332460929365)
          ·
            refine ⟨15111761018889645881629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5158147761114332460929365 15111761018889645881629)
            ·
              rfl

theorem cell23_7151502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 10].length) (baseStart_7151502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151502 prefixEnd_7151502 := by exact prefixLift 7151502
  have htrace : WordTrace (prefixWord ++ tailWord_7151502) baseStart_7151502 baseEnd_7151502 := by
    simpa [prefixWord, tailWord_7151502, baseEnd_7151502] using wordTrace_append hprefix tailTrace_7151502
  have hstable : (prefixWord ++ tailWord_7151502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151502).length < 2 ^ (prefixWord ++ tailWord_7151502).sum := by decide
  have hdescent : baseEnd_7151502 < baseStart_7151502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151552 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 1, 4, 2]
def baseStart_7151552 : Nat := 118140960795 + 7151552 * 2 ^ 59
def prefixEnd_7151552 : Nat := 4983230072969 + 3 ^ 40 * 7151552 * 2
def baseEnd_7151552 : Nat := 3672183601622908753610617

theorem tailTrace_7151552 : CollatzResearch.WordTrace tailWord_7151552 prefixEnd_7151552 3672183601622908753610617 := by
  unfold tailWord_7151552
  simp only [CollatzResearch.WordTrace]
  refine ⟨130419265093577983343528455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173892353458103977791371273 130419265093577983343528455)
  ·
    refine ⟨195628897640366975015292683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130419265093577983343528455 195628897640366975015292683)
    ·
      refine ⟨293443346460550462522939025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195628897640366975015292683 293443346460550462522939025)
      ·
        refine ⟨220082509845412846892204269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293443346460550462522939025 220082509845412846892204269)
        ·
          refine ⟨82530941192029817584576601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220082509845412846892204269 82530941192029817584576601)
          ·
            refine ⟨61898205894022363188432451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82530941192029817584576601 61898205894022363188432451)
            ·
              refine ⟨92847308841033544782648677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61898205894022363188432451 92847308841033544782648677)
              ·
                refine ⟨17408870407693789646746627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92847308841033544782648677 17408870407693789646746627)
                ·
                  refine ⟨26113305611540684470119941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17408870407693789646746627 26113305611540684470119941)
                  ·
                    refine ⟨4896244802163878338147489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26113305611540684470119941 4896244802163878338147489)
                    ·
                      refine ⟨3672183601622908753610617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896244802163878338147489 3672183601622908753610617)
                      ·
                        rfl

theorem cell23_7151552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_7151552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151552 prefixEnd_7151552 := by exact prefixLift 7151552
  have htrace : WordTrace (prefixWord ++ tailWord_7151552) baseStart_7151552 baseEnd_7151552 := by
    simpa [prefixWord, tailWord_7151552, baseEnd_7151552] using wordTrace_append hprefix tailTrace_7151552
  have hstable : (prefixWord ++ tailWord_7151552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151552).length < 2 ^ (prefixWord ++ tailWord_7151552).sum := by decide
  have hdescent : baseEnd_7151552 < baseStart_7151552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151569 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 2, 2, 2]
def baseStart_7151569 : Nat := 118140960795 + 7151569 * 2 ^ 59
def prefixEnd_7151569 : Nat := 4983230072969 + 3 ^ 40 * 7151569 * 2
def baseEnd_7151569 : Nat := 3672192330794035187098039

theorem tailTrace_7151569 : CollatzResearch.WordTrace tailWord_7151569 prefixEnd_7151569 3672192330794035187098039 := by
  unfold tailWord_7151569
  simp only [CollatzResearch.WordTrace]
  refine ⟨260839150228094378590425761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173892766818729585726950507 260839150228094378590425761)
  ·
    refine ⟨195629362671070783942819321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260839150228094378590425761 195629362671070783942819321)
    ·
      refine ⟨146722022003303087957114491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195629362671070783942819321 146722022003303087957114491)
      ·
        refine ⟨220083033004954631935671737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146722022003303087957114491 220083033004954631935671737)
        ·
          refine ⟨165062274753715973951753803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220083033004954631935671737 165062274753715973951753803)
          ·
            refine ⟨247593412130573960927630705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165062274753715973951753803 247593412130573960927630705)
            ·
              refine ⟨185695059097930470695723029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247593412130573960927630705 185695059097930470695723029)
              ·
                refine ⟨8704455895215490813862017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185695059097930470695723029 8704455895215490813862017)
                ·
                  refine ⟨6528341921411618110396513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8704455895215490813862017 6528341921411618110396513)
                  ·
                    refine ⟨4896256441058713582797385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6528341921411618110396513 4896256441058713582797385)
                    ·
                      refine ⟨3672192330794035187098039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896256441058713582797385 3672192330794035187098039)
                      ·
                        rfl

theorem cell23_7151569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_7151569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151569 prefixEnd_7151569 := by exact prefixLift 7151569
  have htrace : WordTrace (prefixWord ++ tailWord_7151569) baseStart_7151569 baseEnd_7151569 := by
    simpa [prefixWord, tailWord_7151569, baseEnd_7151569] using wordTrace_append hprefix tailTrace_7151569
  have hstable : (prefixWord ++ tailWord_7151569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151569).length < 2 ^ (prefixWord ++ tailWord_7151569).sum := by decide
  have hdescent : baseEnd_7151569 < baseStart_7151569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151575 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 7]
def baseStart_7151575 : Nat := 118140960795 + 7151575 * 2 ^ 59
def prefixEnd_7151575 : Nat := 4983230072969 + 3 ^ 40 * 7151575 * 2
def baseEnd_7151575 : Nat := 408021712408662462624779

theorem tailTrace_7151575 : CollatzResearch.WordTrace tailWord_7151575 prefixEnd_7151575 408021712408662462624779 := by
  unfold tailWord_7151575
  simp only [CollatzResearch.WordTrace]
  refine ⟨260839369066072641615144179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173892912710715094410096119 260839369066072641615144179)
  ·
    refine ⟨391259053599108962422716269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260839369066072641615144179 391259053599108962422716269)
    ·
      refine ⟨146722145099665860908518601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391259053599108962422716269 146722145099665860908518601)
      ·
        refine ⟨110041608824749395681388951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146722145099665860908518601 110041608824749395681388951)
        ·
          refine ⟨165062413237124093522083427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110041608824749395681388951 165062413237124093522083427)
          ·
            refine ⟨247593619855686140283125141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165062413237124093522083427 247593619855686140283125141)
            ·
              refine ⟨11605950930735287825771491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247593619855686140283125141 11605950930735287825771491)
              ·
                refine ⟨17408926396102931738657237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11605950930735287825771491 17408926396102931738657237)
                ·
                  refine ⟨408021712408662462624779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17408926396102931738657237 408021712408662462624779)
                  ·
                    rfl

theorem cell23_7151575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 7].length) (baseStart_7151575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151575 prefixEnd_7151575 := by exact prefixLift 7151575
  have htrace : WordTrace (prefixWord ++ tailWord_7151575) baseStart_7151575 baseEnd_7151575 := by
    simpa [prefixWord, tailWord_7151575, baseEnd_7151575] using wordTrace_append hprefix tailTrace_7151575
  have hstable : (prefixWord ++ tailWord_7151575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151575).length < 2 ^ (prefixWord ++ tailWord_7151575).sum := by decide
  have hdescent : baseEnd_7151575 < baseStart_7151575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151580 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7151580 : Nat := 118140960795 + 7151580 * 2 ^ 59
def prefixEnd_7151580 : Nat := 4983230072969 + 3 ^ 40 * 7151580 * 2
def baseEnd_7151580 : Nat := 3672197979081234644060489

theorem tailTrace_7151580 : CollatzResearch.WordTrace tailWord_7151580 prefixEnd_7151580 3672197979081234644060489 := by
  unfold tailWord_7151580
  simp only [CollatzResearch.WordTrace]
  refine ⟨130419775715527263734538097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173893034287369684979384129 130419775715527263734538097)
  ·
    refine ⟨97814831786645447800903573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130419775715527263734538097 97814831786645447800903573)
    ·
      refine ⟨4585070239999005365667355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97814831786645447800903573 4585070239999005365667355)
      ·
        refine ⟨6877605359998508048501033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4585070239999005365667355 6877605359998508048501033)
        ·
          refine ⟨5158204019998881036375775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877605359998508048501033 5158204019998881036375775)
          ·
            refine ⟨7737306029998321554563663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158204019998881036375775 7737306029998321554563663)
            ·
              refine ⟨11605959044997482331845495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737306029998321554563663 11605959044997482331845495)
              ·
                refine ⟨17408938567496223497768243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11605959044997482331845495 17408938567496223497768243)
                ·
                  refine ⟨26113407851244335246652365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17408938567496223497768243 26113407851244335246652365)
                  ·
                    refine ⟨9792527944216625717494637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26113407851244335246652365 9792527944216625717494637)
                    ·
                      refine ⟨3672197979081234644060489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9792527944216625717494637 3672197979081234644060489)
                      ·
                        rfl

theorem cell23_7151580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7151580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151580 prefixEnd_7151580 := by exact prefixLift 7151580
  have htrace : WordTrace (prefixWord ++ tailWord_7151580) baseStart_7151580 baseEnd_7151580 := by
    simpa [prefixWord, tailWord_7151580, baseEnd_7151580] using wordTrace_append hprefix tailTrace_7151580
  have hstable : (prefixWord ++ tailWord_7151580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151580).length < 2 ^ (prefixWord ++ tailWord_7151580).sum := by decide
  have hdescent : baseEnd_7151580 < baseStart_7151580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151609 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 5]
def baseStart_7151609 : Nat := 118140960795 + 7151609 * 2 ^ 59
def prefixEnd_7151609 : Nat := 4983230072969 + 3 ^ 40 * 7151609 * 2
def baseEnd_7151609 : Nat := 408023652224468336733095

theorem tailTrace_7151609 : CollatzResearch.WordTrace tailWord_7151609 prefixEnd_7151609 408023652224468336733095 := by
  unfold tailWord_7151609
  simp only [CollatzResearch.WordTrace]
  refine ⟨260840609147949465421881881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173893739431966310281254587 260840609147949465421881881)
  ·
    refine ⟨195630456860962099066411411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260840609147949465421881881 195630456860962099066411411)
    ·
      refine ⟨293445685291443148599617117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195630456860962099066411411 293445685291443148599617117)
      ·
        refine ⟨110042131984291180724856419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293445685291443148599617117 110042131984291180724856419)
        ·
          refine ⟨165063197976436771087284629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110042131984291180724856419 165063197976436771087284629)
          ·
            refine ⟨7737337405145473644716467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165063197976436771087284629 7737337405145473644716467)
            ·
              refine ⟨11606006107718210467074701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737337405145473644716467 11606006107718210467074701)
              ·
                refine ⟨4352252290394328925153013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11606006107718210467074701 4352252290394328925153013)
                ·
                  refine ⟨408023652224468336733095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352252290394328925153013 408023652224468336733095)
                  ·
                    rfl

theorem cell23_7151609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 5].length) (baseStart_7151609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151609 prefixEnd_7151609 := by exact prefixLift 7151609
  have htrace : WordTrace (prefixWord ++ tailWord_7151609) baseStart_7151609 baseEnd_7151609 := by
    simpa [prefixWord, tailWord_7151609, baseEnd_7151609] using wordTrace_append hprefix tailTrace_7151609
  have hstable : (prefixWord ++ tailWord_7151609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151609).length < 2 ^ (prefixWord ++ tailWord_7151609).sum := by decide
  have hdescent : baseEnd_7151609 < baseStart_7151609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151626 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_7151626 : Nat := 118140960795 + 7151626 * 2 ^ 59
def prefixEnd_7151626 : Nat := 4983230072969 + 3 ^ 40 * 7151626 * 2
def baseEnd_7151626 : Nat := 408024622132371273787253

theorem tailTrace_7151626 : CollatzResearch.WordTrace tailWord_7151626 prefixEnd_7151626 408024622132371273787253 := by
  unfold tailWord_7151626
  simp only [CollatzResearch.WordTrace]
  refine ⟨65210307297221969331312683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173894152792591918216833821 65210307297221969331312683)
  ·
    refine ⟨97815460945832953996969025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65210307297221969331312683 97815460945832953996969025)
    ·
      refine ⟨73361595709374715497726769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97815460945832953996969025 73361595709374715497726769)
      ·
        refine ⟨55021196782031036623295077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73361595709374715497726769 55021196782031036623295077)
        ·
          refine ⟨10316474396630819366867827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55021196782031036623295077 10316474396630819366867827)
          ·
            refine ⟨15474711594946229050301741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316474396630819366867827 15474711594946229050301741)
            ·
              refine ⟨5803016848104835893863153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15474711594946229050301741 5803016848104835893863153)
              ·
                refine ⟨4352262636078626920397365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803016848104835893863153 4352262636078626920397365)
                ·
                  refine ⟨408024622132371273787253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352262636078626920397365 408024622132371273787253)
                  ·
                    rfl

theorem cell23_7151626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_7151626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151626 prefixEnd_7151626 := by exact prefixLift 7151626
  have htrace : WordTrace (prefixWord ++ tailWord_7151626) baseStart_7151626 baseEnd_7151626 := by
    simpa [prefixWord, tailWord_7151626, baseEnd_7151626] using wordTrace_append hprefix tailTrace_7151626
  have hstable : (prefixWord ++ tailWord_7151626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151626).length < 2 ^ (prefixWord ++ tailWord_7151626).sum := by decide
  have hdescent : baseEnd_7151626 < baseStart_7151626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151656 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 2, 5]
def baseStart_7151656 : Nat := 118140960795 + 7151656 * 2 ^ 59
def prefixEnd_7151656 : Nat := 4983230072969 + 3 ^ 40 * 7151656 * 2
def baseEnd_7151656 : Nat := 1224079001203658782236713

theorem tailTrace_7151656 : CollatzResearch.WordTrace tailWord_7151656 prefixEnd_7151656 1224079001203658782236713 := by
  unfold tailWord_7151656
  simp only [CollatzResearch.WordTrace]
  refine ⟨130421161689389596224421411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173894882252519461632561881 130421161689389596224421411)
  ·
    refine ⟨195631742534084394336632117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130421161689389596224421411 195631742534084394336632117)
    ·
      refine ⟨18340475862570411969059261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195631742534084394336632117 18340475862570411969059261)
      ·
        refine ⟨6877678448463904488397223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18340475862570411969059261 6877678448463904488397223)
        ·
          refine ⟨10316517672695856732595835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877678448463904488397223 10316517672695856732595835)
          ·
            refine ⟨15474776509043785098893753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316517672695856732595835 15474776509043785098893753)
            ·
              refine ⟨11606082381782838824170315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15474776509043785098893753 11606082381782838824170315)
              ·
                refine ⟨17409123572674258236255473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11606082381782838824170315 17409123572674258236255473)
                ·
                  refine ⟨13056842679505693677191605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17409123572674258236255473 13056842679505693677191605)
                  ·
                    refine ⟨1224079001203658782236713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13056842679505693677191605 1224079001203658782236713)
                    ·
                      rfl

theorem cell23_7151656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_7151656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151656 prefixEnd_7151656 := by exact prefixLift 7151656
  have htrace : WordTrace (prefixWord ++ tailWord_7151656) baseStart_7151656 baseEnd_7151656 := by
    simpa [prefixWord, tailWord_7151656, baseEnd_7151656] using wordTrace_append hprefix tailTrace_7151656
  have hstable : (prefixWord ++ tailWord_7151656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151656).length < 2 ^ (prefixWord ++ tailWord_7151656).sum := by decide
  have hdescent : baseEnd_7151656 < baseStart_7151656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151685 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_7151685 : Nat := 118140960795 + 7151685 * 2 ^ 59
def prefixEnd_7151685 : Nat := 4983230072969 + 3 ^ 40 * 7151685 * 2
def baseEnd_7151685 : Nat := 3672251894549956733247505

theorem tailTrace_7151685 : CollatzResearch.WordTrace tailWord_7151685 prefixEnd_7151685 3672251894549956733247505 := by
  unfold tailWord_7151685
  simp only [CollatzResearch.WordTrace]
  refine ⟨260843381095674130401648509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173895587397116086934432339 260843381095674130401648509)
  ·
    refine ⟨97816267910877798900618191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260843381095674130401648509 97816267910877798900618191)
    ·
      refine ⟨146724401866316698350927287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97816267910877798900618191 146724401866316698350927287)
      ·
        refine ⟨220086602799475047526390931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146724401866316698350927287 220086602799475047526390931)
        ·
          refine ⟨330129904199212571289586397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220086602799475047526390931 330129904199212571289586397)
          ·
            refine ⟨123798714074704714233594899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330129904199212571289586397 123798714074704714233594899)
            ·
              refine ⟨185698071112057071350392349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123798714074704714233594899 185698071112057071350392349)
              ·
                refine ⟨69636776667021401756397131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185698071112057071350392349 69636776667021401756397131)
                ·
                  refine ⟨104455165000532102634595697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69636776667021401756397131 104455165000532102634595697)
                  ·
                    refine ⟨78341373750399076975946773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104455165000532102634595697 78341373750399076975946773)
                    ·
                      refine ⟨3672251894549956733247505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78341373750399076975946773 3672251894549956733247505)
                      ·
                        rfl

theorem cell23_7151685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_7151685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151685 prefixEnd_7151685 := by exact prefixLift 7151685
  have htrace : WordTrace (prefixWord ++ tailWord_7151685) baseStart_7151685 baseEnd_7151685 := by
    simpa [prefixWord, tailWord_7151685, baseEnd_7151685] using wordTrace_append hprefix tailTrace_7151685
  have hstable : (prefixWord ++ tailWord_7151685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151685).length < 2 ^ (prefixWord ++ tailWord_7151685).sum := by decide
  have hdescent : baseEnd_7151685 < baseStart_7151685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151686 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_7151686 : Nat := 118140960795 + 7151686 * 2 ^ 59
def prefixEnd_7151686 : Nat := 4983230072969 + 3 ^ 40 * 7151686 * 2
def baseEnd_7151686 : Nat := 1224084136010203743111667

theorem tailTrace_7151686 : CollatzResearch.WordTrace tailWord_7151686 prefixEnd_7151686 1224084136010203743111667 := by
  unfold tailWord_7151686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151356799020953361638591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173895611712447005048289941 8151356799020953361638591)
  ·
    refine ⟨12227035198531430042457887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8151356799020953361638591 12227035198531430042457887)
    ·
      refine ⟨18340552797797145063686831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12227035198531430042457887 18340552797797145063686831)
      ·
        refine ⟨27510829196695717595530247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18340552797797145063686831 27510829196695717595530247)
        ·
          refine ⟨41266243795043576393295371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27510829196695717595530247 41266243795043576393295371)
          ·
            refine ⟨61899365692565364589943057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41266243795043576393295371 61899365692565364589943057)
            ·
              refine ⟨46424524269424023442457293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61899365692565364589943057 46424524269424023442457293)
              ·
                refine ⟨17409196601034008790921485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46424524269424023442457293 17409196601034008790921485)
                ·
                  refine ⟨6528448725387753296595557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17409196601034008790921485 6528448725387753296595557)
                  ·
                    refine ⟨1224084136010203743111667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6528448725387753296595557 1224084136010203743111667)
                    ·
                      rfl

theorem cell23_7151686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_7151686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151686 prefixEnd_7151686 := by exact prefixLift 7151686
  have htrace : WordTrace (prefixWord ++ tailWord_7151686) baseStart_7151686 baseEnd_7151686 := by
    simpa [prefixWord, tailWord_7151686, baseEnd_7151686] using wordTrace_append hprefix tailTrace_7151686
  have hstable : (prefixWord ++ tailWord_7151686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151686).length < 2 ^ (prefixWord ++ tailWord_7151686).sum := by decide
  have hdescent : baseEnd_7151686 < baseStart_7151686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151705 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_7151705 : Nat := 118140960795 + 7151705 * 2 ^ 59
def prefixEnd_7151705 : Nat := 4983230072969 + 3 ^ 40 * 7151705 * 2
def baseEnd_7151705 : Nat := 3672262164163046654997413

theorem tailTrace_7151705 : CollatzResearch.WordTrace tailWord_7151705 prefixEnd_7151705 3672262164163046654997413 := by
  unfold tailWord_7151705
  simp only [CollatzResearch.WordTrace]
  refine ⟨260844110555601673817376569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173896073703734449211584379 260844110555601673817376569)
  ·
    refine ⟨195633082916701255363032427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260844110555601673817376569 195633082916701255363032427)
    ·
      refine ⟨293449624375051883044548641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195633082916701255363032427 293449624375051883044548641)
      ·
        refine ⟨220087218281288912283411481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293449624375051883044548641 220087218281288912283411481)
        ·
          refine ⟨165065413710966684212558611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220087218281288912283411481 165065413710966684212558611)
          ·
            refine ⟨247598120566450026318837917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165065413710966684212558611 247598120566450026318837917)
            ·
              refine ⟨92849295212418759869564219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247598120566450026318837917 92849295212418759869564219)
              ·
                refine ⟨139273942818628139804346329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92849295212418759869564219 139273942818628139804346329)
                ·
                  refine ⟨104455457113971104853259747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139273942818628139804346329 104455457113971104853259747)
                  ·
                    refine ⟨156683185670956657279889621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104455457113971104853259747 156683185670956657279889621)
                    ·
                      refine ⟨3672262164163046654997413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156683185670956657279889621 3672262164163046654997413)
                      ·
                        rfl

theorem cell23_7151705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_7151705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151705 prefixEnd_7151705 := by exact prefixLift 7151705
  have htrace : WordTrace (prefixWord ++ tailWord_7151705) baseStart_7151705 baseEnd_7151705 := by
    simpa [prefixWord, tailWord_7151705, baseEnd_7151705] using wordTrace_append hprefix tailTrace_7151705
  have hstable : (prefixWord ++ tailWord_7151705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151705).length < 2 ^ (prefixWord ++ tailWord_7151705).sum := by decide
  have hdescent : baseEnd_7151705 < baseStart_7151705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151710 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7151710 : Nat := 118140960795 + 7151710 * 2 ^ 59
def prefixEnd_7151710 : Nat := 4983230072969 + 3 ^ 40 * 7151710 * 2
def baseEnd_7151710 : Nat := 3672264731566319135434891

theorem tailTrace_7151710 : CollatzResearch.WordTrace tailWord_7151710 prefixEnd_7151710 3672264731566319135434891 := by
  unfold tailWord_7151710
  simp only [CollatzResearch.WordTrace]
  refine ⟨32605536615072944958913573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173896195280389039780872389 32605536615072944958913573)
  ·
    refine ⟨6113538115326177179796295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32605536615072944958913573 6113538115326177179796295)
    ·
      refine ⟨9170307172989265769694443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113538115326177179796295 9170307172989265769694443)
      ·
        refine ⟨13755460759483898654541665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170307172989265769694443 13755460759483898654541665)
        ·
          refine ⟨10316595569612923990906249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13755460759483898654541665 10316595569612923990906249)
          ·
            refine ⟨7737446677209692993179687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10316595569612923990906249 7737446677209692993179687)
            ·
              refine ⟨11606170015814539489769531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737446677209692993179687 11606170015814539489769531)
              ·
                refine ⟨17409255023721809234654297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11606170015814539489769531 17409255023721809234654297)
                ·
                  refine ⟨13056941267791356925990723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17409255023721809234654297 13056941267791356925990723)
                  ·
                    refine ⟨19585411901687035388986085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13056941267791356925990723 19585411901687035388986085)
                    ·
                      refine ⟨3672264731566319135434891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19585411901687035388986085 3672264731566319135434891)
                      ·
                        rfl

theorem cell23_7151710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7151710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151710 prefixEnd_7151710 := by exact prefixLift 7151710
  have htrace : WordTrace (prefixWord ++ tailWord_7151710) baseStart_7151710 baseEnd_7151710 := by
    simpa [prefixWord, tailWord_7151710, baseEnd_7151710] using wordTrace_append hprefix tailTrace_7151710
  have hstable : (prefixWord ++ tailWord_7151710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151710).length < 2 ^ (prefixWord ++ tailWord_7151710).sum := by decide
  have hdescent : baseEnd_7151710 < baseStart_7151710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151712 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_7151712 : Nat := 118140960795 + 7151712 * 2 ^ 59
def prefixEnd_7151712 : Nat := 4983230072969 + 3 ^ 40 * 7151712 * 2
def baseEnd_7151712 : Nat := 1224088586175876042536627

theorem tailTrace_7151712 : CollatzResearch.WordTrace tailWord_7151712 prefixEnd_7151712 1224088586175876042536627 := by
  unfold tailWord_7151712
  simp only [CollatzResearch.WordTrace]
  refine ⟨130422182933288157006440695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173896243911050876008587593 130422182933288157006440695)
  ·
    refine ⟨195633274399932235509661043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130422182933288157006440695 195633274399932235509661043)
    ·
      refine ⟨293449911599898353264491565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195633274399932235509661043 293449911599898353264491565)
      ·
        refine ⟨110043716849961882474184337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293449911599898353264491565 110043716849961882474184337)
        ·
          refine ⟨82532787637471411855638253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110043716849961882474184337 82532787637471411855638253)
          ·
            refine ⟨30949795364051779445864345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82532787637471411855638253 30949795364051779445864345)
            ·
              refine ⟨23212346523038834584398259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30949795364051779445864345 23212346523038834584398259)
              ·
                refine ⟨34818519784558251876597389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23212346523038834584398259 34818519784558251876597389)
                ·
                  refine ⟨13056944919209344453724021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34818519784558251876597389 13056944919209344453724021)
                  ·
                    refine ⟨1224088586175876042536627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13056944919209344453724021 1224088586175876042536627)
                    ·
                      rfl

theorem cell23_7151712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_7151712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151712 prefixEnd_7151712 := by exact prefixLift 7151712
  have htrace : WordTrace (prefixWord ++ tailWord_7151712) baseStart_7151712 baseEnd_7151712 := by
    simpa [prefixWord, tailWord_7151712, baseEnd_7151712] using wordTrace_append hprefix tailTrace_7151712
  have hstable : (prefixWord ++ tailWord_7151712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151712).length < 2 ^ (prefixWord ++ tailWord_7151712).sum := by decide
  have hdescent : baseEnd_7151712 < baseStart_7151712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151719 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_7151719 : Nat := 118140960795 + 7151719 * 2 ^ 59
def prefixEnd_7151719 : Nat := 4983230072969 + 3 ^ 40 * 7151719 * 2
def baseEnd_7151719 : Nat := 3672269352892209600222349

theorem tailTrace_7151719 : CollatzResearch.WordTrace tailWord_7151719 prefixEnd_7151719 3672269352892209600222349 := by
  unfold tailWord_7151719
  simp only [CollatzResearch.WordTrace]
  refine ⟨260844621177550954208386211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173896414118367302805590807 260844621177550954208386211)
  ·
    refine ⟨391266931766326431312579317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260844621177550954208386211 391266931766326431312579317)
    ·
      refine ⟨36681274853093102935554311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391266931766326431312579317 36681274853093102935554311)
      ·
        refine ⟨55021912279639654403331467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36681274853093102935554311 55021912279639654403331467)
        ·
          refine ⟨82532868419459481604997201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55021912279639654403331467 82532868419459481604997201)
          ·
            refine ⟨61899651314594611203747901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82532868419459481604997201 61899651314594611203747901)
            ·
              refine ⟨23212369242972979201405463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61899651314594611203747901 23212369242972979201405463)
              ·
                refine ⟨34818553864459468802108195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23212369242972979201405463 34818553864459468802108195)
                ·
                  refine ⟨52227830796689203203162293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34818553864459468802108195 52227830796689203203162293)
                  ·
                    refine ⟨4896359137189612800296465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52227830796689203203162293 4896359137189612800296465)
                    ·
                      refine ⟨3672269352892209600222349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896359137189612800296465 3672269352892209600222349)
                      ·
                        rfl

theorem cell23_7151719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_7151719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151719 prefixEnd_7151719 := by exact prefixLift 7151719
  have htrace : WordTrace (prefixWord ++ tailWord_7151719) baseStart_7151719 baseEnd_7151719 := by
    simpa [prefixWord, tailWord_7151719, baseEnd_7151719] using wordTrace_append hprefix tailTrace_7151719
  have hstable : (prefixWord ++ tailWord_7151719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151719).length < 2 ^ (prefixWord ++ tailWord_7151719).sum := by decide
  have hdescent : baseEnd_7151719 < baseStart_7151719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151772 : List Nat := [2, 2, 3, 2, 1, 1, 3, 9]
def baseStart_7151772 : Nat := 118140960795 + 7151772 * 2 ^ 59
def prefixEnd_7151772 : Nat := 4983230072969 + 3 ^ 40 * 7151772 * 2
def baseEnd_7151772 : Nat := 136010983976551773809615

theorem tailTrace_7151772 : CollatzResearch.WordTrace tailWord_7151772 prefixEnd_7151772 136010983976551773809615 := by
  unfold tailWord_7151772
  simp only [CollatzResearch.WordTrace]
  refine ⟨130423277123179472130032785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173897702830905962840043713 130423277123179472130032785)
  ·
    refine ⟨97817457842384604097524589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130423277123179472130032785 97817457842384604097524589)
    ·
      refine ⟨36681546690894226536571721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97817457842384604097524589 36681546690894226536571721)
      ·
        refine ⟨27511160018170669902428791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36681546690894226536571721 27511160018170669902428791)
        ·
          refine ⟨41266740027256004853643187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27511160018170669902428791 41266740027256004853643187)
          ·
            refine ⟨61900110040884007280464781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41266740027256004853643187 61900110040884007280464781)
            ·
              refine ⟨23212541265331502730174293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61900110040884007280464781 23212541265331502730174293)
              ·
                refine ⟨136010983976551773809615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23212541265331502730174293 136010983976551773809615)
                ·
                  rfl

theorem cell23_7151772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 9].length) (baseStart_7151772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151772 prefixEnd_7151772 := by exact prefixLift 7151772
  have htrace : WordTrace (prefixWord ++ tailWord_7151772) baseStart_7151772 baseEnd_7151772 := by
    simpa [prefixWord, tailWord_7151772, baseEnd_7151772] using wordTrace_append hprefix tailTrace_7151772
  have hstable : (prefixWord ++ tailWord_7151772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151772).length < 2 ^ (prefixWord ++ tailWord_7151772).sum := by decide
  have hdescent : baseEnd_7151772 < baseStart_7151772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151789 : List Nat := [1, 5, 2, 1, 2, 3, 9]
def baseStart_7151789 : Nat := 118140960795 + 7151789 * 2 ^ 59
def prefixEnd_7151789 : Nat := 4983230072969 + 3 ^ 40 * 7151789 * 2
def baseEnd_7151789 : Nat := 45337102426395362053667

theorem tailTrace_7151789 : CollatzResearch.WordTrace tailWord_7151789 prefixEnd_7151789 45337102426395362053667 := by
  unfold tailWord_7151789
  simp only [CollatzResearch.WordTrace]
  refine ⟨260847174287297356163434421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173898116191531570775622947 260847174287297356163434421)
  ·
    refine ⟨24454422589434127140321977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260847174287297356163434421 24454422589434127140321977)
    ·
      refine ⟨18340816942075595355241483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24454422589434127140321977 18340816942075595355241483)
      ·
        refine ⟨27511225413113393032862225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18340816942075595355241483 27511225413113393032862225)
        ·
          refine ⟨20633419059835044774646669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27511225413113393032862225 20633419059835044774646669)
          ·
            refine ⟨7737532147438141790492501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20633419059835044774646669 7737532147438141790492501)
            ·
              refine ⟨45337102426395362053667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7737532147438141790492501 45337102426395362053667)
              ·
                rfl

theorem cell23_7151789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 9].length) (baseStart_7151789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151789 prefixEnd_7151789 := by exact prefixLift 7151789
  have htrace : WordTrace (prefixWord ++ tailWord_7151789) baseStart_7151789 baseEnd_7151789 := by
    simpa [prefixWord, tailWord_7151789, baseEnd_7151789] using wordTrace_append hprefix tailTrace_7151789
  have hstable : (prefixWord ++ tailWord_7151789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151789).length < 2 ^ (prefixWord ++ tailWord_7151789).sum := by decide
  have hdescent : baseEnd_7151789 < baseStart_7151789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151800 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 1, 2, 2]
def baseStart_7151800 : Nat := 118140960795 + 7151800 * 2 ^ 59
def prefixEnd_7151800 : Nat := 4983230072969 + 3 ^ 40 * 7151800 * 2
def baseEnd_7151800 : Nat := 3672310944825223783309477

theorem tailTrace_7151800 : CollatzResearch.WordTrace tailWord_7151800 prefixEnd_7151800 3672310944825223783309477 := by
  unfold tailWord_7151800
  simp only [CollatzResearch.WordTrace]
  refine ⟨130423787745128752521042427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173898383660171670028056569 130423787745128752521042427)
  ·
    refine ⟨195635681617693128781563641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130423787745128752521042427 195635681617693128781563641)
    ·
      refine ⟨146726761213269846586172731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195635681617693128781563641 146726761213269846586172731)
      ·
        refine ⟨220090141819904769879259097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146726761213269846586172731 220090141819904769879259097)
        ·
          refine ⟨165067606364928577409444323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220090141819904769879259097 165067606364928577409444323)
          ·
            refine ⟨247601409547392866114166485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165067606364928577409444323 247601409547392866114166485)
            ·
              refine ⟨5803158036267020299550777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 247601409547392866114166485 5803158036267020299550777)
              ·
                refine ⟨4352368527200265224663083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803158036267020299550777 4352368527200265224663083)
                ·
                  refine ⟨6528552790800397836994625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4352368527200265224663083 6528552790800397836994625)
                  ·
                    refine ⟨4896414593100298377745969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6528552790800397836994625 4896414593100298377745969)
                    ·
                      refine ⟨3672310944825223783309477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896414593100298377745969 3672310944825223783309477)
                      ·
                        rfl

theorem cell23_7151800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_7151800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151800 prefixEnd_7151800 := by exact prefixLift 7151800
  have htrace : WordTrace (prefixWord ++ tailWord_7151800) baseStart_7151800 baseEnd_7151800 := by
    simpa [prefixWord, tailWord_7151800, baseEnd_7151800] using wordTrace_append hprefix tailTrace_7151800
  have hstable : (prefixWord ++ tailWord_7151800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151800).length < 2 ^ (prefixWord ++ tailWord_7151800).sum := by decide
  have hdescent : baseEnd_7151800 < baseStart_7151800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151810 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7151810 : Nat := 118140960795 + 7151810 * 2 ^ 59
def prefixEnd_7151810 : Nat := 4983230072969 + 3 ^ 40 * 7151810 * 2
def baseEnd_7151810 : Nat := 1224105359877256248061477

theorem tailTrace_7151810 : CollatzResearch.WordTrace tailWord_7151810 prefixEnd_7151810 1224105359877256248061477 := by
  unfold tailWord_7151810
  simp only [CollatzResearch.WordTrace]
  refine ⟨65211985055055319187487221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173898626813480851166632589 65211985055055319187487221)
  ·
    refine ⟨6113623598911436173826927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65211985055055319187487221 6113623598911436173826927)
    ·
      refine ⟨9170435398367154260740391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113623598911436173826927 9170435398367154260740391)
      ·
        refine ⟨13755653097550731391110587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170435398367154260740391 13755653097550731391110587)
        ·
          refine ⟨20633479646326097086665881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13755653097550731391110587 20633479646326097086665881)
          ·
            refine ⟨15475109734744572814999411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20633479646326097086665881 15475109734744572814999411)
            ·
              refine ⟨23212664602116859222499117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15475109734744572814999411 23212664602116859222499117)
              ·
                refine ⟨8704749225793822208437169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23212664602116859222499117 8704749225793822208437169)
                ·
                  refine ⟨6528561919345366656327877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8704749225793822208437169 6528561919345366656327877)
                  ·
                    refine ⟨1224105359877256248061477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6528561919345366656327877 1224105359877256248061477)
                    ·
                      rfl

theorem cell23_7151810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7151810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151810 prefixEnd_7151810 := by exact prefixLift 7151810
  have htrace : WordTrace (prefixWord ++ tailWord_7151810) baseStart_7151810 baseEnd_7151810 := by
    simpa [prefixWord, tailWord_7151810, baseEnd_7151810] using wordTrace_append hprefix tailTrace_7151810
  have hstable : (prefixWord ++ tailWord_7151810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151810).length < 2 ^ (prefixWord ++ tailWord_7151810).sum := by decide
  have hdescent : baseEnd_7151810 < baseStart_7151810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151820 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7151820 : Nat := 118140960795 + 7151820 * 2 ^ 59
def prefixEnd_7151820 : Nat := 4983230072969 + 3 ^ 40 * 7151820 * 2
def baseEnd_7151820 : Nat := 3672321214438313705059385

theorem tailTrace_7151820 : CollatzResearch.WordTrace tailWord_7151820 prefixEnd_7151820 3672321214438313705059385 := by
  unfold tailWord_7151820
  simp only [CollatzResearch.WordTrace]
  refine ⟨130424152475092524228906457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173898869966790032305208609 130424152475092524228906457)
  ·
    refine ⟨97818114356319393171679843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130424152475092524228906457 97818114356319393171679843)
    ·
      refine ⟨146727171534479089757519765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97818114356319393171679843 146727171534479089757519765)
      ·
        refine ⟨6877836165678707332383739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146727171534479089757519765 6877836165678707332383739)
        ·
          refine ⟨10316754248518060998575609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877836165678707332383739 10316754248518060998575609)
          ·
            refine ⟨7737565686388545748931707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10316754248518060998575609 7737565686388545748931707)
            ·
              refine ⟨11606348529582818623397561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737565686388545748931707 11606348529582818623397561)
              ·
                refine ⟨8704761397187113967548171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11606348529582818623397561 8704761397187113967548171)
                ·
                  refine ⟨13057142095780670951322257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8704761397187113967548171 13057142095780670951322257)
                  ·
                    refine ⟨9792856571835503213491693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13057142095780670951322257 9792856571835503213491693)
                    ·
                      refine ⟨3672321214438313705059385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9792856571835503213491693 3672321214438313705059385)
                      ·
                        rfl

theorem cell23_7151820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7151820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151820 prefixEnd_7151820 := by exact prefixLift 7151820
  have htrace : WordTrace (prefixWord ++ tailWord_7151820) baseStart_7151820 baseEnd_7151820 := by
    simpa [prefixWord, tailWord_7151820, baseEnd_7151820] using wordTrace_append hprefix tailTrace_7151820
  have hstable : (prefixWord ++ tailWord_7151820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151820).length < 2 ^ (prefixWord ++ tailWord_7151820).sum := by decide
  have hdescent : baseEnd_7151820 < baseStart_7151820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151856 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 4, 2, 2]
def baseStart_7151856 : Nat := 118140960795 + 7151856 * 2 ^ 59
def prefixEnd_7151856 : Nat := 4983230072969 + 3 ^ 40 * 7151856 * 2
def baseEnd_7151856 : Nat := 3672339699741875564209219

theorem tailTrace_7151856 : CollatzResearch.WordTrace tailWord_7151856 prefixEnd_7151856 3672339699741875564209219 := by
  unfold tailWord_7151856
  simp only [CollatzResearch.WordTrace]
  refine ⟨130424808989027313303061711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173899745318703084404082281 130424808989027313303061711)
  ·
    refine ⟨195637213483540969954592567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130424808989027313303061711 195637213483540969954592567)
    ·
      refine ⟨293455820225311454931888851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195637213483540969954592567 293455820225311454931888851)
      ·
        refine ⟨440183730337967182397833277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293455820225311454931888851 440183730337967182397833277)
        ·
          refine ⟨165068898876737693399187479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440183730337967182397833277 165068898876737693399187479)
          ·
            refine ⟨247603348315106540098781219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165068898876737693399187479 247603348315106540098781219)
            ·
              refine ⟨371405022472659810148171829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247603348315106540098781219 371405022472659810148171829)
              ·
                refine ⟨34819220856811857201391109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 371405022472659810148171829 34819220856811857201391109)
                ·
                  refine ⟨6528603910652223225260833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34819220856811857201391109 6528603910652223225260833)
                  ·
                    refine ⟨4896452932989167418945625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6528603910652223225260833 4896452932989167418945625)
                    ·
                      refine ⟨3672339699741875564209219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896452932989167418945625 3672339699741875564209219)
                      ·
                        rfl

theorem cell23_7151856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 2, 2].length) (baseStart_7151856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151856 prefixEnd_7151856 := by exact prefixLift 7151856
  have htrace : WordTrace (prefixWord ++ tailWord_7151856) baseStart_7151856 baseEnd_7151856 := by
    simpa [prefixWord, tailWord_7151856, baseEnd_7151856] using wordTrace_append hprefix tailTrace_7151856
  have hstable : (prefixWord ++ tailWord_7151856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151856).length < 2 ^ (prefixWord ++ tailWord_7151856).sum := by decide
  have hdescent : baseEnd_7151856 < baseStart_7151856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151873 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_7151873 : Nat := 118140960795 + 7151873 * 2 ^ 59
def prefixEnd_7151873 : Nat := 4983230072969 + 3 ^ 40 * 7151873 * 2
def baseEnd_7151873 : Nat := 3672348428913001997696641

theorem tailTrace_7151873 : CollatzResearch.WordTrace tailWord_7151873 prefixEnd_7151873 3672348428913001997696641 := by
  unfold tailWord_7151873
  simp only [CollatzResearch.WordTrace]
  refine ⟨260850238018993038509492273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173900158679328692339661515 260850238018993038509492273)
  ·
    refine ⟨195637678514244778882119205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260850238018993038509492273 195637678514244778882119205)
    ·
      refine ⟨36682064721420896040397351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195637678514244778882119205 36682064721420896040397351)
      ·
        refine ⟨55023097082131344060596027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36682064721420896040397351 55023097082131344060596027)
        ·
          refine ⟨82534645623197016090894041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55023097082131344060596027 82534645623197016090894041)
          ·
            refine ⟨61900984217397762068170531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82534645623197016090894041 61900984217397762068170531)
            ·
              refine ⟨92851476326096643102255797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61900984217397762068170531 92851476326096643102255797)
              ·
                refine ⟨8704825905571560290836481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92851476326096643102255797 8704825905571560290836481)
                ·
                  refine ⟨6528619429178670218127361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8704825905571560290836481 6528619429178670218127361)
                  ·
                    refine ⟨4896464571884002663595521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6528619429178670218127361 4896464571884002663595521)
                    ·
                      refine ⟨3672348428913001997696641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896464571884002663595521 3672348428913001997696641)
                      ·
                        rfl

theorem cell23_7151873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_7151873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151873 prefixEnd_7151873 := by exact prefixLift 7151873
  have htrace : WordTrace (prefixWord ++ tailWord_7151873) baseStart_7151873 baseEnd_7151873 := by
    simpa [prefixWord, tailWord_7151873, baseEnd_7151873] using wordTrace_append hprefix tailTrace_7151873
  have hstable : (prefixWord ++ tailWord_7151873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151873).length < 2 ^ (prefixWord ++ tailWord_7151873).sum := by decide
  have hdescent : baseEnd_7151873 < baseStart_7151873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151896 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 5]
def baseStart_7151896 : Nat := 118140960795 + 7151896 * 2 ^ 59
def prefixEnd_7151896 : Nat := 4983230072969 + 3 ^ 40 * 7151896 * 2
def baseEnd_7151896 : Nat := 408040026552006156412115

theorem tailTrace_7151896 : CollatzResearch.WordTrace tailWord_7151896 prefixEnd_7151896 408040026552006156412115 := by
  unfold tailWord_7151896
  simp only [CollatzResearch.WordTrace]
  refine ⟨130425538448954856718789771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173900717931939808958386361 130425538448954856718789771)
  ·
    refine ⟨195638307673432285078184657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130425538448954856718789771 195638307673432285078184657)
    ·
      refine ⟨146728730755074213808638493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195638307673432285078184657 146728730755074213808638493)
      ·
        refine ⟨55023274033152830178239435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146728730755074213808638493 55023274033152830178239435)
        ·
          refine ⟨82534911049729245267359153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55023274033152830178239435 82534911049729245267359153)
          ·
            refine ⟨61901183287296933950519365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82534911049729245267359153 61901183287296933950519365)
            ·
              refine ⟨11606471866368175115722381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61901183287296933950519365 11606471866368175115722381)
              ·
                refine ⟨4352426949888065668395893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11606471866368175115722381 4352426949888065668395893)
                ·
                  refine ⟨408040026552006156412115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352426949888065668395893 408040026552006156412115)
                  ·
                    rfl

theorem cell23_7151896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 5].length) (baseStart_7151896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151896 prefixEnd_7151896 := by exact prefixLift 7151896
  have htrace : WordTrace (prefixWord ++ tailWord_7151896) baseStart_7151896 baseEnd_7151896 := by
    simpa [prefixWord, tailWord_7151896, baseEnd_7151896] using wordTrace_append hprefix tailTrace_7151896
  have hstable : (prefixWord ++ tailWord_7151896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151896).length < 2 ^ (prefixWord ++ tailWord_7151896).sum := by decide
  have hdescent : baseEnd_7151896 < baseStart_7151896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151906 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_7151906 : Nat := 118140960795 + 7151906 * 2 ^ 59
def prefixEnd_7151906 : Nat := 4983230072969 + 3 ^ 40 * 7151906 * 2
def baseEnd_7151906 : Nat := 3672365373774600368583989

theorem tailTrace_7151906 : CollatzResearch.WordTrace tailWord_7151906 prefixEnd_7151906 3672365373774600368583989 := by
  unfold tailWord_7151906
  simp only [CollatzResearch.WordTrace]
  refine ⟨65212860406968371286360893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173900961085248990096962381 65212860406968371286360893)
  ·
    refine ⟨24454822652613139232385335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65212860406968371286360893 24454822652613139232385335)
    ·
      refine ⟨36682233978919708848578003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24454822652613139232385335 36682233978919708848578003)
      ·
        refine ⟨55023350968379563272867005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36682233978919708848578003 55023350968379563272867005)
        ·
          refine ⟨20633756613142336227325127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55023350968379563272867005 20633756613142336227325127)
          ·
            refine ⟨30950634919713504340987691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20633756613142336227325127 30950634919713504340987691)
            ·
              refine ⟨46425952379570256511481537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30950634919713504340987691 46425952379570256511481537)
              ·
                refine ⟨34819464284677692383611153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46425952379570256511481537 34819464284677692383611153)
                ·
                  refine ⟨26114598213508269287708365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34819464284677692383611153 26114598213508269287708365)
                  ·
                    refine ⟨9792974330065600982890637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26114598213508269287708365 9792974330065600982890637)
                    ·
                      refine ⟨3672365373774600368583989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9792974330065600982890637 3672365373774600368583989)
                      ·
                        rfl

theorem cell23_7151906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_7151906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151906 prefixEnd_7151906 := by exact prefixLift 7151906
  have htrace : WordTrace (prefixWord ++ tailWord_7151906) baseStart_7151906 baseEnd_7151906 := by
    simpa [prefixWord, tailWord_7151906, baseEnd_7151906] using wordTrace_append hprefix tailTrace_7151906
  have hstable : (prefixWord ++ tailWord_7151906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151906).length < 2 ^ (prefixWord ++ tailWord_7151906).sum := by decide
  have hdescent : baseEnd_7151906 < baseStart_7151906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151973 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_7151973 : Nat := 118140960795 + 7151973 * 2 ^ 59
def prefixEnd_7151973 : Nat := 4983230072969 + 3 ^ 40 * 7151973 * 2
def baseEnd_7151973 : Nat := 1224133258992817202148727

theorem tailTrace_7151973 : CollatzResearch.WordTrace tailWord_7151973 prefixEnd_7151973 1224133258992817202148727 := by
  unfold tailWord_7151973
  simp only [CollatzResearch.WordTrace]
  refine ⟨260853885318630755588132573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173902590212420503725421715 260853885318630755588132573)
  ·
    refine ⟨97820206994486533345549715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260853885318630755588132573 97820206994486533345549715)
    ·
      refine ⟨146730310491729800018324573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97820206994486533345549715 146730310491729800018324573)
      ·
        refine ⟨55023866434398675006871715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146730310491729800018324573 55023866434398675006871715)
        ·
          refine ⟨82535799651598012510307573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55023866434398675006871715 82535799651598012510307573)
          ·
            refine ⟨7737731217337313672841335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82535799651598012510307573 7737731217337313672841335)
            ·
              refine ⟨11606596826005970509262003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737731217337313672841335 11606596826005970509262003)
              ·
                refine ⟨17409895239008955763893005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11606596826005970509262003 17409895239008955763893005)
                ·
                  refine ⟨6528710714628358411459877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17409895239008955763893005 6528710714628358411459877)
                  ·
                    refine ⟨1224133258992817202148727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6528710714628358411459877 1224133258992817202148727)
                    ·
                      rfl

theorem cell23_7151973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_7151973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151973 prefixEnd_7151973 := by exact prefixLift 7151973
  have htrace : WordTrace (prefixWord ++ tailWord_7151973) baseStart_7151973 baseEnd_7151973 := by
    simpa [prefixWord, tailWord_7151973, baseEnd_7151973] using wordTrace_append hprefix tailTrace_7151973
  have hstable : (prefixWord ++ tailWord_7151973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151973).length < 2 ^ (prefixWord ++ tailWord_7151973).sum := by decide
  have hdescent : baseEnd_7151973 < baseStart_7151973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151986 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_7151986 : Nat := 118140960795 + 7151986 * 2 ^ 59
def prefixEnd_7151986 : Nat := 4983230072969 + 3 ^ 40 * 7151986 * 2
def baseEnd_7151986 : Nat := 408045161358551117287069

theorem tailTrace_7151986 : CollatzResearch.WordTrace tailWord_7151986 prefixEnd_7151986 408045161358551117287069 := by
  unfold tailWord_7151986
  simp only [CollatzResearch.WordTrace]
  refine ⟨65213589866895914702088953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173902906311722439205570541 65213589866895914702088953)
  ·
    refine ⟨48910192400171936026566715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65213589866895914702088953 48910192400171936026566715)
    ·
      refine ⟨73365288600257904039850073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48910192400171936026566715 73365288600257904039850073)
      ·
        refine ⟨55023966450193428029887555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73365288600257904039850073 55023966450193428029887555)
        ·
          refine ⟨82535949675290142044831333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55023966450193428029887555 82535949675290142044831333)
          ·
            refine ⟨15475490564116901633405875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82535949675290142044831333 15475490564116901633405875)
            ·
              refine ⟨23213235846175352450108813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15475490564116901633405875 23213235846175352450108813)
              ·
                refine ⟨8704963442315757168790805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23213235846175352450108813 8704963442315757168790805)
                ·
                  refine ⟨408045161358551117287069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8704963442315757168790805 408045161358551117287069)
                  ·
                    rfl

theorem cell23_7151986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_7151986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151986 prefixEnd_7151986 := by exact prefixLift 7151986
  have htrace : WordTrace (prefixWord ++ tailWord_7151986) baseStart_7151986 baseEnd_7151986 := by
    simpa [prefixWord, tailWord_7151986, baseEnd_7151986] using wordTrace_append hprefix tailTrace_7151986
  have hstable : (prefixWord ++ tailWord_7151986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151986).length < 2 ^ (prefixWord ++ tailWord_7151986).sum := by decide
  have hdescent : baseEnd_7151986 < baseStart_7151986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7151999 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 3, 5]
def baseStart_7151999 : Nat := 118140960795 + 7151999 * 2 ^ 59
def prefixEnd_7151999 : Nat := 4983230072969 + 3 ^ 40 * 7151999 * 2
def baseEnd_7151999 : Nat := 1224137709158489501573687

theorem tailTrace_7151999 : CollatzResearch.WordTrace tailWord_7151999 prefixEnd_7151999 1224137709158489501573687 := by
  unfold tailWord_7151999
  simp only [CollatzResearch.WordTrace]
  refine ⟨260854833616536562028579051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173903222411024374685719367 260854833616536562028579051)
  ·
    refine ⟨391282250424804843042868577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260854833616536562028579051 391282250424804843042868577)
    ·
      refine ⟨293461687818603632282151433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391282250424804843042868577 293461687818603632282151433)
      ·
        refine ⟨220096265863952724211613575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293461687818603632282151433 220096265863952724211613575)
        ·
          refine ⟨330144398795929086317420363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220096265863952724211613575 330144398795929086317420363)
          ·
            refine ⟨495216598193893629476130545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330144398795929086317420363 495216598193893629476130545)
            ·
              refine ⟨371412448645420222107097909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495216598193893629476130545 371412448645420222107097909)
              ·
                refine ⟨34819917060508145822540429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 371412448645420222107097909 34819917060508145822540429)
                ·
                  refine ⟨13057468897690554683452661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34819917060508145822540429 13057468897690554683452661)
                  ·
                    refine ⟨1224137709158489501573687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13057468897690554683452661 1224137709158489501573687)
                    ·
                      rfl

theorem cell23_7151999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_7151999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7151999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7151999 prefixEnd_7151999 := by exact prefixLift 7151999
  have htrace : WordTrace (prefixWord ++ tailWord_7151999) baseStart_7151999 baseEnd_7151999 := by
    simpa [prefixWord, tailWord_7151999, baseEnd_7151999] using wordTrace_append hprefix tailTrace_7151999
  have hstable : (prefixWord ++ tailWord_7151999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7151999).length < 2 ^ (prefixWord ++ tailWord_7151999).sum := by decide
  have hdescent : baseEnd_7151999 < baseStart_7151999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7151999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152023 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 2, 3, 2]
def baseStart_7152023 : Nat := 118140960795 + 7152023 * 2 ^ 59
def prefixEnd_7152023 : Nat := 4983230072969 + 3 ^ 40 * 7152023 * 2
def baseEnd_7152023 : Nat := 3672425451011176410820951

theorem tailTrace_7152023 : CollatzResearch.WordTrace tailWord_7152023 prefixEnd_7152023 3672425451011176410820951 := by
  unfold tailWord_7152023
  simp only [CollatzResearch.WordTrace]
  refine ⟨260855708968449614127452723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173903805978966409418301815 260855708968449614127452723)
  ·
    refine ⟨391283563452674421191179085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260855708968449614127452723 391283563452674421191179085)
    ·
      refine ⟨146731336294752907946692157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391283563452674421191179085 146731336294752907946692157)
      ·
        refine ⟨55024251110532340480009559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146731336294752907946692157 55024251110532340480009559)
        ·
          refine ⟨82536376665798510720014339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55024251110532340480009559 82536376665798510720014339)
          ·
            refine ⟨123804564998697766080021509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82536376665798510720014339 123804564998697766080021509)
            ·
              refine ⟨23213355937255831140004033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123804564998697766080021509 23213355937255831140004033)
              ·
                refine ⟨17410016952941873355003025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23213355937255831140004033 17410016952941873355003025)
                ·
                  refine ⟨13057512714706405016252269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17410016952941873355003025 13057512714706405016252269)
                  ·
                    refine ⟨4896567268014901881094601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13057512714706405016252269 4896567268014901881094601)
                    ·
                      refine ⟨3672425451011176410820951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896567268014901881094601 3672425451011176410820951)
                      ·
                        rfl

theorem cell23_7152023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_7152023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152023 prefixEnd_7152023 := by exact prefixLift 7152023
  have htrace : WordTrace (prefixWord ++ tailWord_7152023) baseStart_7152023 baseEnd_7152023 := by
    simpa [prefixWord, tailWord_7152023, baseEnd_7152023] using wordTrace_append hprefix tailTrace_7152023
  have hstable : (prefixWord ++ tailWord_7152023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152023).length < 2 ^ (prefixWord ++ tailWord_7152023).sum := by decide
  have hdescent : baseEnd_7152023 < baseStart_7152023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152036 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_7152036 : Nat := 118140960795 + 7152036 * 2 ^ 59
def prefixEnd_7152036 : Nat := 4983230072969 + 3 ^ 40 * 7152036 * 2
def baseEnd_7152036 : Nat := 3672432126259684859958391

theorem tailTrace_7152036 : CollatzResearch.WordTrace tailWord_7152036 prefixEnd_7152036 3672432126259684859958391 := by
  unfold tailWord_7152036
  simp only [CollatzResearch.WordTrace]
  refine ⟨130428091558701258673837981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173904122078268344898450641 130428091558701258673837981)
  ·
    refine ⟨48910534334512972002689243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130428091558701258673837981 48910534334512972002689243)
    ·
      refine ⟨73365801501769458004033865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48910534334512972002689243 73365801501769458004033865)
      ·
        refine ⟨55024351126327093503025399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73365801501769458004033865 55024351126327093503025399)
        ·
          refine ⟨82536526689490640254538099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55024351126327093503025399 82536526689490640254538099)
          ·
            refine ⟨123804790034235960381807149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82536526689490640254538099 123804790034235960381807149)
            ·
              refine ⟨46426796262838485143177681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123804790034235960381807149 46426796262838485143177681)
              ·
                refine ⟨34820097197128863857383261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46426796262838485143177681 34820097197128863857383261)
                ·
                  refine ⟨13057536448923323946518723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34820097197128863857383261 13057536448923323946518723)
                  ·
                    refine ⟨19586304673384985919778085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13057536448923323946518723 19586304673384985919778085)
                    ·
                      refine ⟨3672432126259684859958391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19586304673384985919778085 3672432126259684859958391)
                      ·
                        rfl

theorem cell23_7152036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_7152036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152036 prefixEnd_7152036 := by exact prefixLift 7152036
  have htrace : WordTrace (prefixWord ++ tailWord_7152036) baseStart_7152036 baseEnd_7152036 := by
    simpa [prefixWord, tailWord_7152036, baseEnd_7152036] using wordTrace_append hprefix tailTrace_7152036
  have hstable : (prefixWord ++ tailWord_7152036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152036).length < 2 ^ (prefixWord ++ tailWord_7152036).sum := by decide
  have hdescent : baseEnd_7152036 < baseStart_7152036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152076 : List Nat := [2, 2, 1, 4, 3, 1, 10]
def baseStart_7152076 : Nat := 118140960795 + 7152076 * 2 ^ 59
def prefixEnd_7152076 : Nat := 4983230072969 + 3 ^ 40 * 7152076 * 2
def baseEnd_7152076 : Nat := 45338921796121786462447

theorem tailTrace_7152076 : CollatzResearch.WordTrace tailWord_7152076 prefixEnd_7152076 45338921796121786462447 := by
  unfold tailWord_7152076
  simp only [CollatzResearch.WordTrace]
  refine ⟨130428821018628802089566041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173905094691505069452754721 130428821018628802089566041)
  ·
    refine ⟨97821615763971601567174531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130428821018628802089566041 97821615763971601567174531)
    ·
      refine ⟨146732423645957402350761797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97821615763971601567174531 146732423645957402350761797)
      ·
        refine ⟨27512329433617012940767837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146732423645957402350761797 27512329433617012940767837)
        ·
          refine ⟨10317123537606379852787939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27512329433617012940767837 10317123537606379852787939)
          ·
            refine ⟨15475685306409569779181909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10317123537606379852787939 15475685306409569779181909)
            ·
              refine ⟨45338921796121786462447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15475685306409569779181909 45338921796121786462447)
              ·
                rfl

theorem cell23_7152076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 10].length) (baseStart_7152076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152076 prefixEnd_7152076 := by exact prefixLift 7152076
  have htrace : WordTrace (prefixWord ++ tailWord_7152076) baseStart_7152076 baseEnd_7152076 := by
    simpa [prefixWord, tailWord_7152076, baseEnd_7152076] using wordTrace_append hprefix tailTrace_7152076
  have hstable : (prefixWord ++ tailWord_7152076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152076).length < 2 ^ (prefixWord ++ tailWord_7152076).sum := by decide
  have hdescent : baseEnd_7152076 < baseStart_7152076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152079 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_7152079 : Nat := 118140960795 + 7152079 * 2 ^ 59
def prefixEnd_7152079 : Nat := 4983230072969 + 3 ^ 40 * 7152079 * 2
def baseEnd_7152079 : Nat := 3672454205927828191720693

theorem tailTrace_7152079 : CollatzResearch.WordTrace tailWord_7152079 prefixEnd_7152079 3672454205927828191720693 := by
  unfold tailWord_7152079
  simp only [CollatzResearch.WordTrace]
  refine ⟨260857751456246735691491291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173905167637497823794327527 260857751456246735691491291)
  ·
    refine ⟨391286627184370103537236937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260857751456246735691491291 391286627184370103537236937)
    ·
      refine ⟨293464970388277577652927703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391286627184370103537236937 293464970388277577652927703)
      ·
        refine ⟨440197455582416366479391555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293464970388277577652927703 440197455582416366479391555)
        ·
          refine ⟨660296183373624549719087333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440197455582416366479391555 660296183373624549719087333)
          ·
            refine ⟨123805534382554603072328875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 660296183373624549719087333 123805534382554603072328875)
            ·
              refine ⟨185708301573831904608493313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123805534382554603072328875 185708301573831904608493313)
              ·
                refine ⟨139281226180373928456369985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185708301573831904608493313 139281226180373928456369985)
                ·
                  refine ⟨104460919635280446342277489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139281226180373928456369985 104460919635280446342277489)
                  ·
                    refine ⟨78345689726460334756708117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104460919635280446342277489 78345689726460334756708117)
                    ·
                      refine ⟨3672454205927828191720693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78345689726460334756708117 3672454205927828191720693)
                      ·
                        rfl

theorem cell23_7152079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_7152079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152079 prefixEnd_7152079 := by exact prefixLift 7152079
  have htrace : WordTrace (prefixWord ++ tailWord_7152079) baseStart_7152079 baseEnd_7152079 := by
    simpa [prefixWord, tailWord_7152079, baseEnd_7152079] using wordTrace_append hprefix tailTrace_7152079
  have hstable : (prefixWord ++ tailWord_7152079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152079).length < 2 ^ (prefixWord ++ tailWord_7152079).sum := by decide
  have hdescent : baseEnd_7152079 < baseStart_7152079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152183 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 5]
def baseStart_7152183 : Nat := 118140960795 + 7152183 * 2 ^ 59
def prefixEnd_7152183 : Nat := 4983230072969 + 3 ^ 40 * 7152183 * 2
def baseEnd_7152183 : Nat := 408056400879543976091135

theorem tailTrace_7152183 : CollatzResearch.WordTrace tailWord_7152183 prefixEnd_7152183 408056400879543976091135 := by
  unfold tailWord_7152183
  simp only [CollatzResearch.WordTrace]
  refine ⟨260861544647869961453277203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173907696431913307635518135 260861544647869961453277203)
  ·
    refine ⟨391292316971804942179915805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260861544647869961453277203 391292316971804942179915805)
    ·
      refine ⟨146734618864426853317468427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391292316971804942179915805 146734618864426853317468427)
      ·
        refine ⟨220101928296640279976202641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146734618864426853317468427 220101928296640279976202641)
        ·
          refine ⟨165076446222480209982151981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220101928296640279976202641 165076446222480209982151981)
          ·
            refine ⟨61903667333430078743306993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165076446222480209982151981 61903667333430078743306993)
            ·
              refine ⟨46427750500072559057480245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61903667333430078743306993 46427750500072559057480245)
              ·
                refine ⟨4352601609381802411638773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46427750500072559057480245 4352601609381802411638773)
                ·
                  refine ⟨408056400879543976091135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352601609381802411638773 408056400879543976091135)
                  ·
                    rfl

theorem cell23_7152183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 5].length) (baseStart_7152183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152183 prefixEnd_7152183 := by exact prefixLift 7152183
  have htrace : WordTrace (prefixWord ++ tailWord_7152183) baseStart_7152183 baseEnd_7152183 := by
    simpa [prefixWord, tailWord_7152183, baseEnd_7152183] using wordTrace_append hprefix tailTrace_7152183
  have hstable : (prefixWord ++ tailWord_7152183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152183).length < 2 ^ (prefixWord ++ tailWord_7152183).sum := by decide
  have hdescent : baseEnd_7152183 < baseStart_7152183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152203 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 2, 5, 2]
def baseStart_7152203 : Nat := 118140960795 + 7152203 * 2 ^ 59
def prefixEnd_7152203 : Nat := 4983230072969 + 3 ^ 40 * 7152203 * 2
def baseEnd_7152203 : Nat := 3672517877528985706570123

theorem tailTrace_7152203 : CollatzResearch.WordTrace tailWord_7152203 prefixEnd_7152203 3672517877528985706570123 := by
  unfold tailWord_7152203
  simp only [CollatzResearch.WordTrace]
  refine ⟨260862274107797504869005263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173908182738531669912670175 260862274107797504869005263)
  ·
    refine ⟨391293411161696257303507895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260862274107797504869005263 391293411161696257303507895)
    ·
      refine ⟨586940116742544385955261843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391293411161696257303507895 586940116742544385955261843)
      ·
        refine ⟨880410175113816578932892765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586940116742544385955261843 880410175113816578932892765)
        ·
          refine ⟨330153815667681217099834787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 880410175113816578932892765 330153815667681217099834787)
          ·
            refine ⟨495230723501521825649752181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330153815667681217099834787 495230723501521825649752181)
            ·
              refine ⟨46427880328267671154664267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495230723501521825649752181 46427880328267671154664267)
              ·
                refine ⟨69641820492401506731996401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46427880328267671154664267 69641820492401506731996401)
                ·
                  refine ⟨52231365369301130048997301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69641820492401506731996401 52231365369301130048997301)
                  ·
                    refine ⟨4896690503371980942093497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52231365369301130048997301 4896690503371980942093497)
                    ·
                      refine ⟨3672517877528985706570123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896690503371980942093497 3672517877528985706570123)
                      ·
                        rfl

theorem cell23_7152203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5, 2].length) (baseStart_7152203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152203 prefixEnd_7152203 := by exact prefixLift 7152203
  have htrace : WordTrace (prefixWord ++ tailWord_7152203) baseStart_7152203 baseEnd_7152203 := by
    simpa [prefixWord, tailWord_7152203, baseEnd_7152203] using wordTrace_append hprefix tailTrace_7152203
  have hstable : (prefixWord ++ tailWord_7152203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152203).length < 2 ^ (prefixWord ++ tailWord_7152203).sum := by decide
  have hdescent : baseEnd_7152203 < baseStart_7152203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152233 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 6, 2]
def baseStart_7152233 : Nat := 118140960795 + 7152233 * 2 ^ 59
def prefixEnd_7152233 : Nat := 4983230072969 + 3 ^ 40 * 7152233 * 2
def baseEnd_7152233 : Nat := 3672533281948620589194985

theorem tailTrace_7152233 : CollatzResearch.WordTrace tailWord_7152233 prefixEnd_7152233 3672533281948620589194985 := by
  unfold tailWord_7152233
  simp only [CollatzResearch.WordTrace]
  refine ⟨260863368297688819992597353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173908912198459213328398235 260863368297688819992597353)
  ·
    refine ⟨195647526223266614994448015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260863368297688819992597353 195647526223266614994448015)
    ·
      refine ⟨293471289334899922491672023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195647526223266614994448015 293471289334899922491672023)
      ·
        refine ⟨440206934002349883737508035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293471289334899922491672023 440206934002349883737508035)
        ·
          refine ⟨660310401003524825606262053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440206934002349883737508035 660310401003524825606262053)
          ·
            refine ⟨123808200188160904801174135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 660310401003524825606262053 123808200188160904801174135)
            ·
              refine ⟨185712300282241357201761203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123808200188160904801174135 185712300282241357201761203)
              ·
                refine ⟨278568450423362035802641805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185712300282241357201761203 278568450423362035802641805)
                ·
                  refine ⟨104463168908760763425990677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278568450423362035802641805 104463168908760763425990677)
                  ·
                    refine ⟨4896711042598160785593313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104463168908760763425990677 4896711042598160785593313)
                    ·
                      refine ⟨3672533281948620589194985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896711042598160785593313 3672533281948620589194985)
                      ·
                        rfl

theorem cell23_7152233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 6, 2].length) (baseStart_7152233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152233 prefixEnd_7152233 := by exact prefixLift 7152233
  have htrace : WordTrace (prefixWord ++ tailWord_7152233) baseStart_7152233 baseEnd_7152233 := by
    simpa [prefixWord, tailWord_7152233, baseEnd_7152233] using wordTrace_append hprefix tailTrace_7152233
  have hstable : (prefixWord ++ tailWord_7152233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152233).length < 2 ^ (prefixWord ++ tailWord_7152233).sum := by decide
  have hdescent : baseEnd_7152233 < baseStart_7152233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152260 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_7152260 : Nat := 118140960795 + 7152260 * 2 ^ 59
def prefixEnd_7152260 : Nat := 4983230072969 + 3 ^ 40 * 7152260 * 2
def baseEnd_7152260 : Nat := 1224182381975430661185787

theorem tailTrace_7152260 : CollatzResearch.WordTrace tailWord_7152260 prefixEnd_7152260 1224182381975430661185787 := by
  unfold tailWord_7152260
  simp only [CollatzResearch.WordTrace]
  refine ⟨130432176534295501801915117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173909568712394002402553489 130432176534295501801915117)
  ·
    refine ⟨48912066200360813175718169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130432176534295501801915117 48912066200360813175718169)
    ·
      refine ⟨36684049650270609881788627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48912066200360813175718169 36684049650270609881788627)
      ·
        refine ⟨55026074475405914822682941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36684049650270609881788627 55026074475405914822682941)
        ·
          refine ⟨20634777928277218058506103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55026074475405914822682941 20634777928277218058506103)
          ·
            refine ⟨30952166892415827087759155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20634777928277218058506103 30952166892415827087759155)
            ·
              refine ⟨46428250338623740631638733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30952166892415827087759155 46428250338623740631638733)
              ·
                refine ⟨17410593876983902736864525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46428250338623740631638733 17410593876983902736864525)
                ·
                  refine ⟨6528972703868963526324197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17410593876983902736864525 6528972703868963526324197)
                  ·
                    refine ⟨1224182381975430661185787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6528972703868963526324197 1224182381975430661185787)
                    ·
                      rfl

theorem cell23_7152260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_7152260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152260 prefixEnd_7152260 := by exact prefixLift 7152260
  have htrace : WordTrace (prefixWord ++ tailWord_7152260) baseStart_7152260 baseEnd_7152260 := by
    simpa [prefixWord, tailWord_7152260, baseEnd_7152260] using wordTrace_append hprefix tailTrace_7152260
  have hstable : (prefixWord ++ tailWord_7152260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152260).length < 2 ^ (prefixWord ++ tailWord_7152260).sum := by decide
  have hdescent : baseEnd_7152260 < baseStart_7152260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152317 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_7152317 : Nat := 118140960795 + 7152317 * 2 ^ 59
def prefixEnd_7152317 : Nat := 4983230072969 + 3 ^ 40 * 7152317 * 2
def baseEnd_7152317 : Nat := 3672576414323598260544599

theorem tailTrace_7152317 : CollatzResearch.WordTrace tailWord_7152317 prefixEnd_7152317 3672576414323598260544599 := by
  unfold tailWord_7152317
  simp only [CollatzResearch.WordTrace]
  refine ⟨260866432029384502338655205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173910954686256334892436803 260866432029384502338655205)
  ·
    refine ⟨48912456005509594188497851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260866432029384502338655205 48912456005509594188497851)
    ·
      refine ⟨73368684008264391282746777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48912456005509594188497851 73368684008264391282746777)
      ·
        refine ⟨55026513006198293462060083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73368684008264391282746777 55026513006198293462060083)
        ·
          refine ⟨82539769509297440193090125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55026513006198293462060083 82539769509297440193090125)
          ·
            refine ⟨30952413565986540072408797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82539769509297440193090125 30952413565986540072408797)
            ·
              refine ⟨11607155087244952527153299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30952413565986540072408797 11607155087244952527153299)
              ·
                refine ⟨17410732630867428790729949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11607155087244952527153299 17410732630867428790729949)
                ·
                  refine ⟨6529024736575285796523731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17410732630867428790729949 6529024736575285796523731)
                  ·
                    refine ⟨9793537104862928694785597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6529024736575285796523731 9793537104862928694785597)
                    ·
                      refine ⟨3672576414323598260544599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9793537104862928694785597 3672576414323598260544599)
                      ·
                        rfl

theorem cell23_7152317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_7152317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152317 prefixEnd_7152317 := by exact prefixLift 7152317
  have htrace : WordTrace (prefixWord ++ tailWord_7152317) baseStart_7152317 baseEnd_7152317 := by
    simpa [prefixWord, tailWord_7152317, baseEnd_7152317] using wordTrace_append hprefix tailTrace_7152317
  have hstable : (prefixWord ++ tailWord_7152317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152317).length < 2 ^ (prefixWord ++ tailWord_7152317).sum := by decide
  have hdescent : baseEnd_7152317 < baseStart_7152317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152367 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 2, 4]
def baseStart_7152367 : Nat := 118140960795 + 7152367 * 2 ^ 59
def prefixEnd_7152367 : Nat := 4983230072969 + 3 ^ 40 * 7152367 * 2
def baseEnd_7152367 : Nat := 1224200696118774354973123

theorem tailTrace_7152367 : CollatzResearch.WordTrace tailWord_7152367 prefixEnd_7152367 1224200696118774354973123 := by
  unfold tailWord_7152367
  simp only [CollatzResearch.WordTrace]
  refine ⟨260868255679203360877975355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173912170452802240585316903 260868255679203360877975355)
  ·
    refine ⟨391302383518805041316963033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260868255679203360877975355 391302383518805041316963033)
    ·
      refine ⟨293476787639103780987722275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391302383518805041316963033 293476787639103780987722275)
      ·
        refine ⟨440215181458655671481583413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293476787639103780987722275 440215181458655671481583413)
        ·
          refine ⟨41270173261748969201398445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 440215181458655671481583413 41270173261748969201398445)
          ·
            refine ⟨15476314973155863450524417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41270173261748969201398445 15476314973155863450524417)
            ·
              refine ⟨11607236229866897587893313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15476314973155863450524417 11607236229866897587893313)
              ·
                refine ⟨8705427172400173190919985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11607236229866897587893313 8705427172400173190919985)
                ·
                  refine ⟨6529070379300129893189989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705427172400173190919985 6529070379300129893189989)
                  ·
                    refine ⟨1224200696118774354973123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6529070379300129893189989 1224200696118774354973123)
                    ·
                      rfl

theorem cell23_7152367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_7152367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152367 prefixEnd_7152367 := by exact prefixLift 7152367
  have htrace : WordTrace (prefixWord ++ tailWord_7152367) baseStart_7152367 baseEnd_7152367 := by
    simpa [prefixWord, tailWord_7152367, baseEnd_7152367] using wordTrace_append hprefix tailTrace_7152367
  have hstable : (prefixWord ++ tailWord_7152367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152367).length < 2 ^ (prefixWord ++ tailWord_7152367).sum := by decide
  have hdescent : baseEnd_7152367 < baseStart_7152367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152374 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_7152374 : Nat := 118140960795 + 7152374 * 2 ^ 59
def prefixEnd_7152374 : Nat := 4983230072969 + 3 ^ 40 * 7152374 * 2
def baseEnd_7152374 : Nat := 3672605682720904537531837

theorem tailTrace_7152374 : CollatzResearch.WordTrace tailWord_7152374 prefixEnd_7152374 3672605682720904537531837 := by
  unfold tailWord_7152374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304281936886125067092511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173912340660118667382320117 16304281936886125067092511)
  ·
    refine ⟨24456422905329187600638767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16304281936886125067092511 24456422905329187600638767)
    ·
      refine ⟨36684634357993781400958151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24456422905329187600638767 36684634357993781400958151)
      ·
        refine ⟨55026951536990672101437227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36684634357993781400958151 55026951536990672101437227)
        ·
          refine ⟨82540427305486008152155841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55026951536990672101437227 82540427305486008152155841)
          ·
            refine ⟨61905320479114506114116881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82540427305486008152155841 61905320479114506114116881)
            ·
              refine ⟨46428990359335879585587661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61905320479114506114116881 46428990359335879585587661)
              ·
                refine ⟨17410871384750954844595373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46428990359335879585587661 17410871384750954844595373)
                ·
                  refine ⟨6529076769281608066723265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17410871384750954844595373 6529076769281608066723265)
                  ·
                    refine ⟨4896807576961206050042449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6529076769281608066723265 4896807576961206050042449)
                    ·
                      refine ⟨3672605682720904537531837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896807576961206050042449 3672605682720904537531837)
                      ·
                        rfl

theorem cell23_7152374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_7152374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152374 prefixEnd_7152374 := by exact prefixLift 7152374
  have htrace : WordTrace (prefixWord ++ tailWord_7152374) baseStart_7152374 baseEnd_7152374 := by
    simpa [prefixWord, tailWord_7152374, baseEnd_7152374] using wordTrace_append hprefix tailTrace_7152374
  have hstable : (prefixWord ++ tailWord_7152374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152374).length < 2 ^ (prefixWord ++ tailWord_7152374).sum := by decide
  have hdescent : baseEnd_7152374 < baseStart_7152374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152380 : List Nat := [2, 2, 2, 1, 3, 4, 1, 8]
def baseStart_7152380 : Nat := 118140960795 + 7152380 * 2 ^ 59
def prefixEnd_7152380 : Nat := 4983230072969 + 3 ^ 40 * 7152380 * 2
def baseEnd_7152380 : Nat := 136022546800178944965067

theorem tailTrace_7152380 : CollatzResearch.WordTrace tailWord_7152380 prefixEnd_7152380 136022546800178944965067 := by
  unfold tailWord_7152380
  simp only [CollatzResearch.WordTrace]
  refine ⟨130434364914078132049099297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173912486552104176065465729 130434364914078132049099297)
  ·
    refine ⟨97825773685558599036824473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130434364914078132049099297 97825773685558599036824473)
    ·
      refine ⟨73369330264168949277618355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97825773685558599036824473 73369330264168949277618355)
      ·
        refine ⟨110053995396253423916427533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73369330264168949277618355 110053995396253423916427533)
        ·
          refine ⟨41270248273595033968660325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110053995396253423916427533 41270248273595033968660325)
          ·
            refine ⟨7738171551299068869123811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41270248273595033968660325 7738171551299068869123811)
            ·
              refine ⟨11607257326948603303685717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738171551299068869123811 11607257326948603303685717)
              ·
                refine ⟨136022546800178944965067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11607257326948603303685717 136022546800178944965067)
                ·
                  rfl

theorem cell23_7152380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 8].length) (baseStart_7152380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152380 prefixEnd_7152380 := by exact prefixLift 7152380
  have htrace : WordTrace (prefixWord ++ tailWord_7152380) baseStart_7152380 baseEnd_7152380 := by
    simpa [prefixWord, tailWord_7152380, baseEnd_7152380] using wordTrace_append hprefix tailTrace_7152380
  have hstable : (prefixWord ++ tailWord_7152380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152380).length < 2 ^ (prefixWord ++ tailWord_7152380).sum := by decide
  have hdescent : baseEnd_7152380 < baseStart_7152380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152403 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_7152403 : Nat := 118140960795 + 7152403 * 2 ^ 59
def prefixEnd_7152403 : Nat := 4983230072969 + 3 ^ 40 * 7152403 * 2
def baseEnd_7152403 : Nat := 3672620573659884924069203

theorem tailTrace_7152403 : CollatzResearch.WordTrace tailWord_7152403 prefixEnd_7152403 3672620573659884924069203 := by
  unfold tailWord_7152403
  simp only [CollatzResearch.WordTrace]
  refine ⟨260869568707072939026285863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173913045804715292684190575 260869568707072939026285863)
  ·
    refine ⟨391304353060609408539428795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260869568707072939026285863 391304353060609408539428795)
    ·
      refine ⟨586956529590914112809143193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391304353060609408539428795 586956529590914112809143193)
      ·
        refine ⟨440217397193185584606857395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586956529590914112809143193 440217397193185584606857395)
        ·
          refine ⟨660326095789778376910286093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440217397193185584606857395 660326095789778376910286093)
          ·
            refine ⟨247622285921166891341357285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660326095789778376910286093 247622285921166891341357285)
            ·
              refine ⟨46429178610218792126504491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247622285921166891341357285 46429178610218792126504491)
              ·
                refine ⟨69643767915328188189756737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46429178610218792126504491 69643767915328188189756737)
                ·
                  refine ⟨52232825936496141142317553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69643767915328188189756737 52232825936496141142317553)
                  ·
                    refine ⟨39174619452372105856738165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52232825936496141142317553 39174619452372105856738165)
                    ·
                      refine ⟨3672620573659884924069203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39174619452372105856738165 3672620573659884924069203)
                      ·
                        rfl

theorem cell23_7152403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_7152403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152403 prefixEnd_7152403 := by exact prefixLift 7152403
  have htrace : WordTrace (prefixWord ++ tailWord_7152403) baseStart_7152403 baseEnd_7152403 := by
    simpa [prefixWord, tailWord_7152403, baseEnd_7152403] using wordTrace_append hprefix tailTrace_7152403
  have hstable : (prefixWord ++ tailWord_7152403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152403).length < 2 ^ (prefixWord ++ tailWord_7152403).sum := by decide
  have hdescent : baseEnd_7152403 < baseStart_7152403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152453 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 9]
def baseStart_7152453 : Nat := 118140960795 + 7152453 * 2 ^ 59
def prefixEnd_7152453 : Nat := 4983230072969 + 3 ^ 40 * 7152453 * 2
def baseEnd_7152453 : Nat := 408071805299178858715997

theorem tailTrace_7152453 : CollatzResearch.WordTrace tailWord_7152453 prefixEnd_7152453 408071805299178858715997 := by
  unfold tailWord_7152453
  simp only [CollatzResearch.WordTrace]
  refine ⟨260871392356891797565606013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173914261571261198377070675 260871392356891797565606013)
  ·
    refine ⟨97826772133834424087102255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260871392356891797565606013 97826772133834424087102255)
    ·
      refine ⟨146740158200751636130653383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97826772133834424087102255 146740158200751636130653383)
      ·
        refine ⟨220110237301127454195980075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146740158200751636130653383 220110237301127454195980075)
        ·
          refine ⟨330165355951691181293970113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220110237301127454195980075 330165355951691181293970113)
          ·
            refine ⟨247624016963768385970477585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330165355951691181293970113 247624016963768385970477585)
            ·
              refine ⟨185718012722826289477858189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247624016963768385970477585 185718012722826289477858189)
              ·
                refine ⟨69644254771059858554196821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185718012722826289477858189 69644254771059858554196821)
                ·
                  refine ⟨408071805299178858715997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69644254771059858554196821 408071805299178858715997)
                  ·
                    rfl

theorem cell23_7152453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_7152453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152453 prefixEnd_7152453 := by exact prefixLift 7152453
  have htrace : WordTrace (prefixWord ++ tailWord_7152453) baseStart_7152453 baseEnd_7152453 := by
    simpa [prefixWord, tailWord_7152453, baseEnd_7152453] using wordTrace_append hprefix tailTrace_7152453
  have hstable : (prefixWord ++ tailWord_7152453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152453).length < 2 ^ (prefixWord ++ tailWord_7152453).sum := by decide
  have hdescent : baseEnd_7152453 < baseStart_7152453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152487 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 7]
def baseStart_7152487 : Nat := 118140960795 + 7152487 * 2 ^ 59
def prefixEnd_7152487 : Nat := 4983230072969 + 3 ^ 40 * 7152487 * 2
def baseEnd_7152487 : Nat := 408073745114984732824313

theorem tailTrace_7152487 : CollatzResearch.WordTrace tailWord_7152487 prefixEnd_7152487 408073745114984732824313 := by
  unfold tailWord_7152487
  simp only [CollatzResearch.WordTrace]
  refine ⟨260872632438768621372343715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173915088292512414248229143 260872632438768621372343715)
  ·
    refine ⟨391308948658152932058515573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260872632438768621372343715 391308948658152932058515573)
    ·
      refine ⟨36685213936701837380485835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391308948658152932058515573 36685213936701837380485835)
      ·
        refine ⟨55027820905052756070728753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36685213936701837380485835 55027820905052756070728753)
        ·
          refine ⟨41270865678789567053046565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55027820905052756070728753 41270865678789567053046565)
          ·
            refine ⟨7738287314773043822446231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41270865678789567053046565 7738287314773043822446231)
            ·
              refine ⟨11607430972159565733669347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738287314773043822446231 11607430972159565733669347)
              ·
                refine ⟨17411146458239348600504021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11607430972159565733669347 17411146458239348600504021)
                ·
                  refine ⟨408073745114984732824313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17411146458239348600504021 408073745114984732824313)
                  ·
                    rfl

theorem cell23_7152487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 7].length) (baseStart_7152487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152487 prefixEnd_7152487 := by exact prefixLift 7152487
  have htrace : WordTrace (prefixWord ++ tailWord_7152487) baseStart_7152487 baseEnd_7152487 := by
    simpa [prefixWord, tailWord_7152487, baseEnd_7152487] using wordTrace_append hprefix tailTrace_7152487
  have hstable : (prefixWord ++ tailWord_7152487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152487).length < 2 ^ (prefixWord ++ tailWord_7152487).sum := by decide
  have hdescent : baseEnd_7152487 < baseStart_7152487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152517 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_7152517 : Nat := 118140960795 + 7152517 * 2 ^ 59
def prefixEnd_7152517 : Nat := 4983230072969 + 3 ^ 40 * 7152517 * 2
def baseEnd_7152517 : Nat := 1224226370151499159347893

theorem tailTrace_7152517 : CollatzResearch.WordTrace tailWord_7152517 prefixEnd_7152517 1224226370151499159347893 := by
  unfold tailWord_7152517
  simp only [CollatzResearch.WordTrace]
  refine ⟨260873726628659936495935805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173915817752439957663957203 260873726628659936495935805)
  ·
    refine ⟨97827647485747476185975927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260873726628659936495935805 97827647485747476185975927)
    ·
      refine ⟨146741471228621214278963891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97827647485747476185975927 146741471228621214278963891)
      ·
        refine ⟨220112206842931821418445837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146741471228621214278963891 220112206842931821418445837)
        ·
          refine ⟨82542077566099433031917189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220112206842931821418445837 82542077566099433031917189)
          ·
            refine ⟨15476639543643643693484473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82542077566099433031917189 15476639543643643693484473)
            ·
              refine ⟨11607479657732732770113355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15476639543643643693484473 11607479657732732770113355)
              ·
                refine ⟨17411219486599099155170033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11607479657732732770113355 17411219486599099155170033)
                ·
                  refine ⟨13058414614949324366377525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17411219486599099155170033 13058414614949324366377525)
                  ·
                    refine ⟨1224226370151499159347893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13058414614949324366377525 1224226370151499159347893)
                    ·
                      rfl

theorem cell23_7152517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_7152517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152517 prefixEnd_7152517 := by exact prefixLift 7152517
  have htrace : WordTrace (prefixWord ++ tailWord_7152517) baseStart_7152517 baseEnd_7152517 := by
    simpa [prefixWord, tailWord_7152517, baseEnd_7152517] using wordTrace_append hprefix tailTrace_7152517
  have hstable : (prefixWord ++ tailWord_7152517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152517).length < 2 ^ (prefixWord ++ tailWord_7152517).sum := by decide
  have hdescent : baseEnd_7152517 < baseStart_7152517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152537 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 2, 4, 2]
def baseStart_7152537 : Nat := 118140960795 + 7152537 * 2 ^ 59
def prefixEnd_7152537 : Nat := 4983230072969 + 3 ^ 40 * 7152537 * 2
def baseEnd_7152537 : Nat := 3672689380067587399793587

theorem tailTrace_7152537 : CollatzResearch.WordTrace tailWord_7152537 prefixEnd_7152537 3672689380067587399793587 := by
  unfold tailWord_7152537
  simp only [CollatzResearch.WordTrace]
  refine ⟨260874456088587479911663865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173916304059058319941109243 260874456088587479911663865)
  ·
    refine ⟨195655842066440609933747899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260874456088587479911663865 195655842066440609933747899)
    ·
      refine ⟨293483763099660914900621849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195655842066440609933747899 293483763099660914900621849)
      ·
        refine ⟨220112822324745686175466387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293483763099660914900621849 220112822324745686175466387)
        ·
          refine ⟨330169233487118529263199581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220112822324745686175466387 330169233487118529263199581)
          ·
            refine ⟨123813462557669448473699843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330169233487118529263199581 123813462557669448473699843)
            ·
              refine ⟨185720193836504172710549765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123813462557669448473699843 185720193836504172710549765)
              ·
                refine ⟨34822536344344532383228081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185720193836504172710549765 34822536344344532383228081)
                ·
                  refine ⟨26116902258258399287421061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34822536344344532383228081 26116902258258399287421061)
                  ·
                    refine ⟨4896919173423449866391449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26116902258258399287421061 4896919173423449866391449)
                    ·
                      refine ⟨3672689380067587399793587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4896919173423449866391449 3672689380067587399793587)
                      ·
                        rfl

theorem cell23_7152537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_7152537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152537 prefixEnd_7152537 := by exact prefixLift 7152537
  have htrace : WordTrace (prefixWord ++ tailWord_7152537) baseStart_7152537 baseEnd_7152537 := by
    simpa [prefixWord, tailWord_7152537, baseEnd_7152537] using wordTrace_append hprefix tailTrace_7152537
  have hstable : (prefixWord ++ tailWord_7152537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152537).length < 2 ^ (prefixWord ++ tailWord_7152537).sum := by decide
  have hdescent : baseEnd_7152537 < baseStart_7152537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152538 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_7152538 : Nat := 118140960795 + 7152538 * 2 ^ 59
def prefixEnd_7152538 : Nat := 4983230072969 + 3 ^ 40 * 7152538 * 2
def baseEnd_7152538 : Nat := 408076654838693543986787

theorem tailTrace_7152538 : CollatzResearch.WordTrace tailWord_7152538 prefixEnd_7152538 408076654838693543986787 := by
  unfold tailWord_7152538
  simp only [CollatzResearch.WordTrace]
  refine ⟨65218623140395964270612567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173916328374389238054966845 65218623140395964270612567)
  ·
    refine ⟨97827934710593946405918851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65218623140395964270612567 97827934710593946405918851)
    ·
      refine ⟨146741902065890919608878277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97827934710593946405918851 146741902065890919608878277)
      ·
        refine ⟨27514106637354547426664677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146741902065890919608878277 27514106637354547426664677)
        ·
          refine ⟨5158894994503977642499627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27514106637354547426664677 5158894994503977642499627)
          ·
            refine ⟨7738342491755966463749441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158894994503977642499627 7738342491755966463749441)
            ·
              refine ⟨5803756868816974847812081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7738342491755966463749441 5803756868816974847812081)
              ·
                refine ⟨4352817651612731135859061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803756868816974847812081 4352817651612731135859061)
                ·
                  refine ⟨408076654838693543986787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352817651612731135859061 408076654838693543986787)
                  ·
                    rfl

theorem cell23_7152538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_7152538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152538 prefixEnd_7152538 := by exact prefixLift 7152538
  have htrace : WordTrace (prefixWord ++ tailWord_7152538) baseStart_7152538 baseEnd_7152538 := by
    simpa [prefixWord, tailWord_7152538, baseEnd_7152538] using wordTrace_append hprefix tailTrace_7152538
  have hstable : (prefixWord ++ tailWord_7152538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152538).length < 2 ^ (prefixWord ++ tailWord_7152538).sum := by decide
  have hdescent : baseEnd_7152538 < baseStart_7152538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152594 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_7152594 : Nat := 118140960795 + 7152594 * 2 ^ 59
def prefixEnd_7152594 : Nat := 4983230072969 + 3 ^ 40 * 7152594 * 2
def baseEnd_7152594 : Nat := 408079849829432630753425

theorem tailTrace_7152594 : CollatzResearch.WordTrace tailWord_7152594 prefixEnd_7152594 408079849829432630753425 := by
  unfold tailWord_7152594
  simp only [CollatzResearch.WordTrace]
  refine ⟨65219133762345244661622209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173917690032920652430992557 65219133762345244661622209)
  ·
    refine ⟨48914350321758933496216657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65219133762345244661622209 48914350321758933496216657)
    ·
      refine ⟨36685762741319200122162493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48914350321758933496216657 36685762741319200122162493)
      ·
        refine ⟨13757161027994700045810935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36685762741319200122162493 13757161027994700045810935)
        ·
          refine ⟨20635741541992050068716403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757161027994700045810935 20635741541992050068716403)
          ·
            refine ⟨30953612312988075103074605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20635741541992050068716403 30953612312988075103074605)
            ·
              refine ⟨11607604617370528163652977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30953612312988075103074605 11607604617370528163652977)
              ·
                refine ⟨8705703463027896122739733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11607604617370528163652977 8705703463027896122739733)
                ·
                  refine ⟨408079849829432630753425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8705703463027896122739733 408079849829432630753425)
                  ·
                    rfl

theorem cell23_7152594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_7152594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152594 prefixEnd_7152594 := by exact prefixLift 7152594
  have htrace : WordTrace (prefixWord ++ tailWord_7152594) baseStart_7152594 baseEnd_7152594 := by
    simpa [prefixWord, tailWord_7152594, baseEnd_7152594] using wordTrace_append hprefix tailTrace_7152594
  have hstable : (prefixWord ++ tailWord_7152594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152594).length < 2 ^ (prefixWord ++ tailWord_7152594).sum := by decide
  have hdescent : baseEnd_7152594 < baseStart_7152594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152598 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_7152598 : Nat := 118140960795 + 7152598 * 2 ^ 59
def prefixEnd_7152598 : Nat := 4983230072969 + 3 ^ 40 * 7152598 * 2
def baseEnd_7152598 : Nat := 1224240234129170553710269

theorem tailTrace_7152598 : CollatzResearch.WordTrace tailWord_7152598 prefixEnd_7152598 1224240234129170553710269 := by
  unfold tailWord_7152598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304792558835405458102153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173917787294244324886422965 16304792558835405458102153)
  ·
    refine ⟨12228594419126554093576615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16304792558835405458102153 12228594419126554093576615)
    ·
      refine ⟨18342891628689831140364923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12228594419126554093576615 18342891628689831140364923)
      ·
        refine ⟨27514337443034746710547385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18342891628689831140364923 27514337443034746710547385)
        ·
          refine ⟨20635753082276060032910539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27514337443034746710547385 20635753082276060032910539)
          ·
            refine ⟨30953629623414090049365809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20635753082276060032910539 30953629623414090049365809)
            ·
              refine ⟨23215222217560567537024357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30953629623414090049365809 23215222217560567537024357)
              ·
                refine ⟨4352854165792606413192067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23215222217560567537024357 4352854165792606413192067)
                ·
                  refine ⟨6529281248688909619788101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4352854165792606413192067 6529281248688909619788101)
                  ·
                    refine ⟨1224240234129170553710269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6529281248688909619788101 1224240234129170553710269)
                    ·
                      rfl

theorem cell23_7152598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_7152598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152598 prefixEnd_7152598 := by exact prefixLift 7152598
  have htrace : WordTrace (prefixWord ++ tailWord_7152598) baseStart_7152598 baseEnd_7152598 := by
    simpa [prefixWord, tailWord_7152598, baseEnd_7152598] using wordTrace_append hprefix tailTrace_7152598
  have hstable : (prefixWord ++ tailWord_7152598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152598).length < 2 ^ (prefixWord ++ tailWord_7152598).sum := by decide
  have hdescent : baseEnd_7152598 < baseStart_7152598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152654 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_7152654 : Nat := 118140960795 + 7152654 * 2 ^ 59
def prefixEnd_7152654 : Nat := 4983230072969 + 3 ^ 40 * 7152654 * 2
def baseEnd_7152654 : Nat := 1224249819101387814010183

theorem tailTrace_7152654 : CollatzResearch.WordTrace tailWord_7152654 prefixEnd_7152654 1224249819101387814010183 := by
  unfold tailWord_7152654
  simp only [CollatzResearch.WordTrace]
  refine ⟨32609840428645451111709127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173919148952775739262448677 32609840428645451111709127)
  ·
    refine ⟨48914760642968176667563691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32609840428645451111709127 48914760642968176667563691)
    ·
      refine ⟨73372140964452265001345537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48914760642968176667563691 73372140964452265001345537)
      ·
        refine ⟨55029105723339198751009153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73372140964452265001345537 55029105723339198751009153)
        ·
          refine ⟨41271829292504399063256865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55029105723339198751009153 41271829292504399063256865)
          ·
            refine ⟨30953871969378299297442649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41271829292504399063256865 30953871969378299297442649)
            ·
              refine ⟨23215403977033724473081987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30953871969378299297442649 23215403977033724473081987)
              ·
                refine ⟨34823105965550586709622981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23215403977033724473081987 34823105965550586709622981)
                ·
                  refine ⟨6529332368540735008054309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34823105965550586709622981 6529332368540735008054309)
                  ·
                    refine ⟨1224249819101387814010183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6529332368540735008054309 1224249819101387814010183)
                    ·
                      rfl

theorem cell23_7152654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_7152654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152654 prefixEnd_7152654 := by exact prefixLift 7152654
  have htrace : WordTrace (prefixWord ++ tailWord_7152654) baseStart_7152654 baseEnd_7152654 := by
    simpa [prefixWord, tailWord_7152654, baseEnd_7152654] using wordTrace_append hprefix tailTrace_7152654
  have hstable : (prefixWord ++ tailWord_7152654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152654).length < 2 ^ (prefixWord ++ tailWord_7152654).sum := by decide
  have hdescent : baseEnd_7152654 < baseStart_7152654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152671 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 2, 4]
def baseStart_7152671 : Nat := 118140960795 + 7152671 * 2 ^ 59
def prefixEnd_7152671 : Nat := 4983230072969 + 3 ^ 40 * 7152671 * 2
def baseEnd_7152671 : Nat := 1224252728825096625172657

theorem tailTrace_7152671 : CollatzResearch.WordTrace tailWord_7152671 prefixEnd_7152671 1224252728825096625172657 := by
  unfold tailWord_7152671
  simp only [CollatzResearch.WordTrace]
  refine ⟨260879343470102020797041867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173919562313401347198027911 260879343470102020797041867)
  ·
    refine ⟨391319015205153031195562801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260879343470102020797041867 391319015205153031195562801)
    ·
      refine ⟨293489261403864773396672101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391319015205153031195562801 293489261403864773396672101)
      ·
        refine ⟨55029236513224645011876019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293489261403864773396672101 55029236513224645011876019)
        ·
          refine ⟨82543854769836967517814029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55029236513224645011876019 82543854769836967517814029)
          ·
            refine ⟨30953945538688862819180261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82543854769836967517814029 30953945538688862819180261)
            ·
              refine ⟨5803864788504161778596299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30953945538688862819180261 5803864788504161778596299)
              ·
                refine ⟨8705797182756242667894449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5803864788504161778596299 8705797182756242667894449)
                ·
                  refine ⟨6529347887067182000920837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705797182756242667894449 6529347887067182000920837)
                  ·
                    refine ⟨1224252728825096625172657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6529347887067182000920837 1224252728825096625172657)
                    ·
                      rfl

theorem cell23_7152671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 4].length) (baseStart_7152671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152671 prefixEnd_7152671 := by exact prefixLift 7152671
  have htrace : WordTrace (prefixWord ++ tailWord_7152671) baseStart_7152671 baseEnd_7152671 := by
    simpa [prefixWord, tailWord_7152671, baseEnd_7152671] using wordTrace_append hprefix tailTrace_7152671
  have hstable : (prefixWord ++ tailWord_7152671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152671).length < 2 ^ (prefixWord ++ tailWord_7152671).sum := by decide
  have hdescent : baseEnd_7152671 < baseStart_7152671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152711 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_7152711 : Nat := 118140960795 + 7152711 * 2 ^ 59
def prefixEnd_7152711 : Nat := 4983230072969 + 3 ^ 40 * 7152711 * 2
def baseEnd_7152711 : Nat := 3672778725701469719017787

theorem tailTrace_7152711 : CollatzResearch.WordTrace tailWord_7152711 prefixEnd_7152711 3672778725701469719017787 := by
  unfold tailWord_7152711
  simp only [CollatzResearch.WordTrace]
  refine ⟨260880802389957107628497987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173920534926638071752331991 260880802389957107628497987)
  ·
    refine ⟨391321203584935661442746981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260880802389957107628497987 391321203584935661442746981)
    ·
      refine ⟨73372725672175436520515059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391321203584935661442746981 73372725672175436520515059)
      ·
        refine ⟨110059088508263154780772589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73372725672175436520515059 110059088508263154780772589)
        ·
          refine ⟨41272158190598683042789721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110059088508263154780772589 41272158190598683042789721)
          ·
            refine ⟨30954118642949012282092291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41272158190598683042789721 30954118642949012282092291)
            ·
              refine ⟨46431177964423518423138437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30954118642949012282092291 46431177964423518423138437)
              ·
                refine ⟨8705845868329409704338457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46431177964423518423138437 8705845868329409704338457)
                ·
                  refine ⟨6529384401247057278253843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705845868329409704338457 6529384401247057278253843)
                  ·
                    refine ⟨9794076601870585917380765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6529384401247057278253843 9794076601870585917380765)
                    ·
                      refine ⟨3672778725701469719017787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9794076601870585917380765 3672778725701469719017787)
                      ·
                        rfl

theorem cell23_7152711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_7152711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152711 prefixEnd_7152711 := by exact prefixLift 7152711
  have htrace : WordTrace (prefixWord ++ tailWord_7152711) baseStart_7152711 baseEnd_7152711 := by
    simpa [prefixWord, tailWord_7152711, baseEnd_7152711] using wordTrace_append hprefix tailTrace_7152711
  have hstable : (prefixWord ++ tailWord_7152711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152711).length < 2 ^ (prefixWord ++ tailWord_7152711).sum := by decide
  have hdescent : baseEnd_7152711 < baseStart_7152711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152737 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_7152737 : Nat := 118140960795 + 7152737 * 2 ^ 59
def prefixEnd_7152737 : Nat := 4983230072969 + 3 ^ 40 * 7152737 * 2
def baseEnd_7152737 : Nat := 3672792076198486617292667

theorem tailTrace_7152737 : CollatzResearch.WordTrace tailWord_7152737 prefixEnd_7152737 3672792076198486617292667 := by
  unfold tailWord_7152737
  simp only [CollatzResearch.WordTrace]
  refine ⟨260881750687862914068944465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173921167125241942712629643 260881750687862914068944465)
  ·
    refine ⟨195661313015897185551708349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260881750687862914068944465 195661313015897185551708349)
    ·
      refine ⟨73372992380961444581890631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195661313015897185551708349 73372992380961444581890631)
      ·
        refine ⟨110059488571442166872835947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73372992380961444581890631 110059488571442166872835947)
        ·
          refine ⟨165089232857163250309253921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110059488571442166872835947 165089232857163250309253921)
          ·
            refine ⟨123816924642872437731940441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165089232857163250309253921 123816924642872437731940441)
            ·
              refine ⟨92862693482154328298955331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123816924642872437731940441 92862693482154328298955331)
              ·
                refine ⟨139294040223231492448432997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92862693482154328298955331 139294040223231492448432997)
                ·
                  refine ⟨26117632541855904834081187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139294040223231492448432997 26117632541855904834081187)
                  ·
                    refine ⟨39176448812783857251121781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26117632541855904834081187 39176448812783857251121781)
                    ·
                      refine ⟨3672792076198486617292667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39176448812783857251121781 3672792076198486617292667)
                      ·
                        rfl

theorem cell23_7152737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_7152737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152737 prefixEnd_7152737 := by exact prefixLift 7152737
  have htrace : WordTrace (prefixWord ++ tailWord_7152737) baseStart_7152737 baseEnd_7152737 := by
    simpa [prefixWord, tailWord_7152737, baseEnd_7152737] using wordTrace_append hprefix tailTrace_7152737
  have hstable : (prefixWord ++ tailWord_7152737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152737).length < 2 ^ (prefixWord ++ tailWord_7152737).sum := by decide
  have hdescent : baseEnd_7152737 < baseStart_7152737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152738 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7152738 : Nat := 118140960795 + 7152738 * 2 ^ 59
def prefixEnd_7152738 : Nat := 4983230072969 + 3 ^ 40 * 7152738 * 2
def baseEnd_7152738 : Nat := 3672792589679141113380163

theorem tailTrace_7152738 : CollatzResearch.WordTrace tailWord_7152738 prefixEnd_7152738 3672792589679141113380163 := by
  unfold tailWord_7152738
  simp only [CollatzResearch.WordTrace]
  refine ⟨65220446790214822809932717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173921191440572860826487245 65220446790214822809932717)
  ·
    refine ⟨24457667546330558553724769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65220446790214822809932717 24457667546330558553724769)
    ·
      refine ⟨18343250659747918915293577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24457667546330558553724769 18343250659747918915293577)
      ·
        refine ⟨13757437994810939186470183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18343250659747918915293577 13757437994810939186470183)
        ·
          refine ⟨20636156992216408779705275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757437994810939186470183 20636156992216408779705275)
          ·
            refine ⟨30954235488324613169557913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20636156992216408779705275 30954235488324613169557913)
            ·
              refine ⟨23215676616243459877168435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30954235488324613169557913 23215676616243459877168435)
              ·
                refine ⟨34823514924365189815752653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23215676616243459877168435 34823514924365189815752653)
                ·
                  refine ⟨13058818096636946180907245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34823514924365189815752653 13058818096636946180907245)
                  ·
                    refine ⟨4897056786238854817840217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13058818096636946180907245 4897056786238854817840217)
                    ·
                      refine ⟨3672792589679141113380163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897056786238854817840217 3672792589679141113380163)
                      ·
                        rfl

theorem cell23_7152738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7152738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152738 prefixEnd_7152738 := by exact prefixLift 7152738
  have htrace : WordTrace (prefixWord ++ tailWord_7152738) baseStart_7152738 baseEnd_7152738 := by
    simpa [prefixWord, tailWord_7152738, baseEnd_7152738] using wordTrace_append hprefix tailTrace_7152738
  have hstable : (prefixWord ++ tailWord_7152738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152738).length < 2 ^ (prefixWord ++ tailWord_7152738).sum := by decide
  have hdescent : baseEnd_7152738 < baseStart_7152738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152751 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 4, 2, 2]
def baseStart_7152751 : Nat := 118140960795 + 7152751 * 2 ^ 59
def prefixEnd_7152751 : Nat := 4983230072969 + 3 ^ 40 * 7152751 * 2
def baseEnd_7152751 : Nat := 3672799264927649562517603

theorem tailTrace_7152751 : CollatzResearch.WordTrace tailWord_7152751 prefixEnd_7152751 3672799264927649562517603 := by
  unfold tailWord_7152751
  simp only [CollatzResearch.WordTrace]
  refine ⟨260882261309812194459954107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173921507539874796306636071 260882261309812194459954107)
  ·
    refine ⟨391323391964718291689931161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260882261309812194459954107 391323391964718291689931161)
    ·
      refine ⟨293492543973538718767448371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391323391964718291689931161 293492543973538718767448371)
      ·
        refine ⟨440238815960308078151172557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293492543973538718767448371 440238815960308078151172557)
        ·
          refine ⟨165089555985115529306689709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440238815960308078151172557 165089555985115529306689709)
          ·
            refine ⟨61908583494418323490008641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165089555985115529306689709 61908583494418323490008641)
            ·
              refine ⟨46431437620813742617506481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61908583494418323490008641 46431437620813742617506481)
              ·
                refine ⟨34823578215610306963129861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46431437620813742617506481 34823578215610306963129861)
                ·
                  refine ⟨6529420915426932555586849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34823578215610306963129861 6529420915426932555586849)
                  ·
                    refine ⟨4897065686570199416690137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6529420915426932555586849 4897065686570199416690137)
                    ·
                      refine ⟨3672799264927649562517603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897065686570199416690137 3672799264927649562517603)
                      ·
                        rfl

theorem cell23_7152751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 2, 2].length) (baseStart_7152751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152751 prefixEnd_7152751 := by exact prefixLift 7152751
  have htrace : WordTrace (prefixWord ++ tailWord_7152751) baseStart_7152751 baseEnd_7152751 := by
    simpa [prefixWord, tailWord_7152751, baseEnd_7152751] using wordTrace_append hprefix tailTrace_7152751
  have hstable : (prefixWord ++ tailWord_7152751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152751).length < 2 ^ (prefixWord ++ tailWord_7152751).sum := by decide
  have hdescent : baseEnd_7152751 < baseStart_7152751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152768 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 2, 2, 2]
def baseStart_7152768 : Nat := 118140960795 + 7152768 * 2 ^ 59
def prefixEnd_7152768 : Nat := 4983230072969 + 3 ^ 40 * 7152768 * 2
def baseEnd_7152768 : Nat := 3672807994098775996005025

theorem tailTrace_7152768 : CollatzResearch.WordTrace tailWord_7152768 prefixEnd_7152768 3672807994098775996005025 := by
  unfold tailWord_7152768
  simp only [CollatzResearch.WordTrace]
  refine ⟨130441440675375303181661479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173921920900500404242215305 130441440675375303181661479)
  ·
    refine ⟨195662161013062954772492219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130441440675375303181661479 195662161013062954772492219)
    ·
      refine ⟨293493241519594432158738329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195662161013062954772492219 293493241519594432158738329)
      ·
        refine ⟨220119931139695824119053747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293493241519594432158738329 220119931139695824119053747)
        ·
          refine ⟨330179896709543736178580621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220119931139695824119053747 330179896709543736178580621)
          ·
            refine ⟨123817461266078901066967733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330179896709543736178580621 123817461266078901066967733)
            ·
              refine ⟨11607886993694896975028225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123817461266078901066967733 11607886993694896975028225)
              ·
                refine ⟨8705915245271172731271169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11607886993694896975028225 8705915245271172731271169)
                ·
                  refine ⟨6529436433953379548453377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705915245271172731271169 6529436433953379548453377)
                  ·
                    refine ⟨4897077325465034661340033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6529436433953379548453377 4897077325465034661340033)
                    ·
                      refine ⟨3672807994098775996005025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897077325465034661340033 3672807994098775996005025)
                      ·
                        rfl

theorem cell23_7152768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_7152768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152768 prefixEnd_7152768 := by exact prefixLift 7152768
  have htrace : WordTrace (prefixWord ++ tailWord_7152768) baseStart_7152768 baseEnd_7152768 := by
    simpa [prefixWord, tailWord_7152768, baseEnd_7152768] using wordTrace_append hprefix tailTrace_7152768
  have hstable : (prefixWord ++ tailWord_7152768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152768).length < 2 ^ (prefixWord ++ tailWord_7152768).sum := by decide
  have hdescent : baseEnd_7152768 < baseStart_7152768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152787 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 1, 7]
def baseStart_7152787 : Nat := 118140960795 + 7152787 * 2 ^ 59
def prefixEnd_7152787 : Nat := 4983230072969 + 3 ^ 40 * 7152787 * 2
def baseEnd_7152787 : Nat := 1224272583410403807222479

theorem tailTrace_7152787 : CollatzResearch.WordTrace tailWord_7152787 prefixEnd_7152787 1224272583410403807222479 := by
  unfold tailWord_7152787
  simp only [CollatzResearch.WordTrace]
  refine ⟨260883574337681772608264615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173922382891787848405509743 260883574337681772608264615)
  ·
    refine ⟨391325361506522658912396923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260883574337681772608264615 391325361506522658912396923)
    ·
      refine ⟨586988042259783988368595385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391325361506522658912396923 586988042259783988368595385)
      ·
        refine ⟨440241031694837991276446539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586988042259783988368595385 440241031694837991276446539)
        ·
          refine ⟨660361547542256986914669809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440241031694837991276446539 660361547542256986914669809)
          ·
            refine ⟨495271160656692740186002357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660361547542256986914669809 495271160656692740186002357)
            ·
              refine ⟨46431671311564944392437721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495271160656692740186002357 46431671311564944392437721)
              ·
                refine ⟨34823753483673708294328291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46431671311564944392437721 34823753483673708294328291)
                ·
                  refine ⟨52235630225510562441492437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34823753483673708294328291 52235630225510562441492437)
                  ·
                    refine ⟨1224272583410403807222479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52235630225510562441492437 1224272583410403807222479)
                    ·
                      rfl

theorem cell23_7152787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 7].length) (baseStart_7152787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152787 prefixEnd_7152787 := by exact prefixLift 7152787
  have htrace : WordTrace (prefixWord ++ tailWord_7152787) baseStart_7152787 baseEnd_7152787 := by
    simpa [prefixWord, tailWord_7152787, baseEnd_7152787] using wordTrace_append hprefix tailTrace_7152787
  have hstable : (prefixWord ++ tailWord_7152787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152787).length < 2 ^ (prefixWord ++ tailWord_7152787).sum := by decide
  have hdescent : baseEnd_7152787 < baseStart_7152787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152804 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_7152804 : Nat := 118140960795 + 7152804 * 2 ^ 59
def prefixEnd_7152804 : Nat := 4983230072969 + 3 ^ 40 * 7152804 * 2
def baseEnd_7152804 : Nat := 1224275493134112618384953

theorem tailTrace_7152804 : CollatzResearch.WordTrace tailWord_7152804 prefixEnd_7152804 1224275493134112618384953 := by
  unfold tailWord_7152804
  simp only [CollatzResearch.WordTrace]
  refine ⟨130442097189310092255816733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173922796252413456341088977 130442097189310092255816733)
  ·
    refine ⟨48915786445991284595931275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130442097189310092255816733 48915786445991284595931275)
    ·
      refine ⟨73373679668986926893896913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48915786445991284595931275 73373679668986926893896913)
      ·
        refine ⟨55030259751740195170422685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73373679668986926893896913 55030259751740195170422685)
        ·
          refine ⟨20636347406902573188908507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55030259751740195170422685 20636347406902573188908507)
          ·
            refine ⟨30954521110353859783362761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20636347406902573188908507 30954521110353859783362761)
            ·
              refine ⟨23215890832765394837522071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30954521110353859783362761 23215890832765394837522071)
              ·
                refine ⟨34823836249148092256283107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23215890832765394837522071 34823836249148092256283107)
                ·
                  refine ⟨52235754373722138384424661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34823836249148092256283107 52235754373722138384424661)
                  ·
                    refine ⟨1224275493134112618384953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52235754373722138384424661 1224275493134112618384953)
                    ·
                      rfl

theorem cell23_7152804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_7152804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152804 prefixEnd_7152804 := by exact prefixLift 7152804
  have htrace : WordTrace (prefixWord ++ tailWord_7152804) baseStart_7152804 baseEnd_7152804 := by
    simpa [prefixWord, tailWord_7152804, baseEnd_7152804] using wordTrace_append hprefix tailTrace_7152804
  have hstable : (prefixWord ++ tailWord_7152804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152804).length < 2 ^ (prefixWord ++ tailWord_7152804).sum := by decide
  have hdescent : baseEnd_7152804 < baseStart_7152804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152827 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_7152827 : Nat := 118140960795 + 7152827 * 2 ^ 59
def prefixEnd_7152827 : Nat := 4983230072969 + 3 ^ 40 * 7152827 * 2
def baseEnd_7152827 : Nat := 3672838289457391265167253

theorem tailTrace_7152827 : CollatzResearch.WordTrace tailWord_7152827 prefixEnd_7152827 3672838289457391265167253 := by
  unfold tailWord_7152827
  simp only [CollatzResearch.WordTrace]
  refine ⟨260885033257536859439720735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173923355505024572959813823 260885033257536859439720735)
  ·
    refine ⟨391327549886305289159581103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260885033257536859439720735 391327549886305289159581103)
    ·
      refine ⟨586991324829457933739371655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391327549886305289159581103 586991324829457933739371655)
      ·
        refine ⟨880486987244186900609057483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586991324829457933739371655 880486987244186900609057483)
        ·
          refine ⟨1320730480866280350913586225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880486987244186900609057483 1320730480866280350913586225)
          ·
            refine ⟨990547860649710263185189669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320730480866280350913586225 990547860649710263185189669)
            ·
              refine ⟨185727723871820674347223063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 990547860649710263185189669 185727723871820674347223063)
              ·
                refine ⟨278591585807731011520834595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185727723871820674347223063 278591585807731011520834595)
                ·
                  refine ⟨417887378711596517281251893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278591585807731011520834595 417887378711596517281251893)
                  ·
                    refine ⟨39176941754212173495117365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 417887378711596517281251893 39176941754212173495117365)
                    ·
                      refine ⟨3672838289457391265167253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39176941754212173495117365 3672838289457391265167253)
                      ·
                        rfl

theorem cell23_7152827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_7152827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152827 prefixEnd_7152827 := by exact prefixLift 7152827
  have htrace : WordTrace (prefixWord ++ tailWord_7152827) baseStart_7152827 baseEnd_7152827 := by
    simpa [prefixWord, tailWord_7152827, baseEnd_7152827] using wordTrace_append hprefix tailTrace_7152827
  have hstable : (prefixWord ++ tailWord_7152827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152827).length < 2 ^ (prefixWord ++ tailWord_7152827).sum := by decide
  have hdescent : baseEnd_7152827 < baseStart_7152827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152847 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 10]
def baseStart_7152847 : Nat := 118140960795 + 7152847 * 2 ^ 59
def prefixEnd_7152847 : Nat := 4983230072969 + 3 ^ 40 * 7152847 * 2
def baseEnd_7152847 : Nat := 408094284341164576324129

theorem tailTrace_7152847 : CollatzResearch.WordTrace tailWord_7152847 prefixEnd_7152847 408094284341164576324129 := by
  unfold tailWord_7152847
  simp only [CollatzResearch.WordTrace]
  refine ⟨260885762717464402855448795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173923841811642935236965863 260885762717464402855448795)
  ·
    refine ⟨391328644076196604283173193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260885762717464402855448795 391328644076196604283173193)
    ·
      refine ⟨293496483057147453212379895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391328644076196604283173193 293496483057147453212379895)
      ·
        refine ⟨440244724585721179818569843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293496483057147453212379895 440244724585721179818569843)
        ·
          refine ⟨660367086878581769727854765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440244724585721179818569843 660367086878581769727854765)
          ·
            refine ⟨247637657579468163647945537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660367086878581769727854765 247637657579468163647945537)
            ·
              refine ⟨185728243184601122735959153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247637657579468163647945537 185728243184601122735959153)
              ·
                refine ⟨139296182388450842051969365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185728243184601122735959153 139296182388450842051969365)
                ·
                  refine ⟨408094284341164576324129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 139296182388450842051969365 408094284341164576324129)
                  ·
                    rfl

theorem cell23_7152847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 10].length) (baseStart_7152847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152847 prefixEnd_7152847 := by exact prefixLift 7152847
  have htrace : WordTrace (prefixWord ++ tailWord_7152847) baseStart_7152847 baseEnd_7152847 := by
    simpa [prefixWord, tailWord_7152847, baseEnd_7152847] using wordTrace_append hprefix tailTrace_7152847
  have hstable : (prefixWord ++ tailWord_7152847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152847).length < 2 ^ (prefixWord ++ tailWord_7152847).sum := by decide
  have hdescent : baseEnd_7152847 < baseStart_7152847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152901 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 1, 5, 2]
def baseStart_7152901 : Nat := 118140960795 + 7152901 * 2 ^ 59
def prefixEnd_7152901 : Nat := 4983230072969 + 3 ^ 40 * 7152901 * 2
def baseEnd_7152901 : Nat := 3672876287025823975641913

theorem tailTrace_7152901 : CollatzResearch.WordTrace tailWord_7152901 prefixEnd_7152901 3672876287025823975641913 := by
  unfold tailWord_7152901
  simp only [CollatzResearch.WordTrace]
  refine ⟨260887732259268770077914557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173925154839512513385276371 260887732259268770077914557)
  ·
    refine ⟨97832899597225788779217959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260887732259268770077914557 97832899597225788779217959)
    ·
      refine ⟨146749349395838683168826939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97832899597225788779217959 146749349395838683168826939)
      ·
        refine ⟨220124024093758024753240409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146749349395838683168826939 220124024093758024753240409)
        ·
          refine ⟨165093018070318518564930307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220124024093758024753240409 165093018070318518564930307)
          ·
            refine ⟨247639527105477777847395461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165093018070318518564930307 247639527105477777847395461)
            ·
              refine ⟨46432411332277083346386649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247639527105477777847395461 46432411332277083346386649)
              ·
                refine ⟨34824308499207812509789987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46432411332277083346386649 34824308499207812509789987)
                ·
                  refine ⟨52236462748811718764684981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34824308499207812509789987 52236462748811718764684981)
                  ·
                    refine ⟨4897168382701098634189217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52236462748811718764684981 4897168382701098634189217)
                    ·
                      refine ⟨3672876287025823975641913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897168382701098634189217 3672876287025823975641913)
                      ·
                        rfl

theorem cell23_7152901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_7152901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152901 prefixEnd_7152901 := by exact prefixLift 7152901
  have htrace : WordTrace (prefixWord ++ tailWord_7152901) baseStart_7152901 baseEnd_7152901 := by
    simpa [prefixWord, tailWord_7152901, baseEnd_7152901] using wordTrace_append hprefix tailTrace_7152901
  have hstable : (prefixWord ++ tailWord_7152901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152901).length < 2 ^ (prefixWord ++ tailWord_7152901).sum := by decide
  have hdescent : baseEnd_7152901 < baseStart_7152901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152908 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_7152908 : Nat := 118140960795 + 7152908 * 2 ^ 59
def prefixEnd_7152908 : Nat := 4983230072969 + 3 ^ 40 * 7152908 * 2
def baseEnd_7152908 : Nat := 3672879881390405448254381

theorem tailTrace_7152908 : CollatzResearch.WordTrace tailWord_7152908 prefixEnd_7152908 3672879881390405448254381 := by
  unfold tailWord_7152908
  simp only [CollatzResearch.WordTrace]
  refine ⟨130443993785121705136709689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173925325046828940182279585 130443993785121705136709689)
  ·
    refine ⟨97832995338841278852532267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130443993785121705136709689 97832995338841278852532267)
    ·
      refine ⟨146749493008261918278798401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97832995338841278852532267 146749493008261918278798401)
      ·
        refine ⟨110062119756196438709098801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146749493008261918278798401 110062119756196438709098801)
        ·
          refine ⟨82546589817147329031824101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110062119756196438709098801 82546589817147329031824101)
          ·
            refine ⟨15477485590715124193467019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82546589817147329031824101 15477485590715124193467019)
            ·
              refine ⟨23216228386072686290200529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15477485590715124193467019 23216228386072686290200529)
              ·
                refine ⟨17412171289554514717650397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23216228386072686290200529 17412171289554514717650397)
                ·
                  refine ⟨6529564233582943019118899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17412171289554514717650397 6529564233582943019118899)
                  ·
                    refine ⟨9794346350374414528678349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6529564233582943019118899 9794346350374414528678349)
                    ·
                      refine ⟨3672879881390405448254381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9794346350374414528678349 3672879881390405448254381)
                      ·
                        rfl

theorem cell23_7152908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_7152908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152908 prefixEnd_7152908 := by exact prefixLift 7152908
  have htrace : WordTrace (prefixWord ++ tailWord_7152908) baseStart_7152908 baseEnd_7152908 := by
    simpa [prefixWord, tailWord_7152908, baseEnd_7152908] using wordTrace_append hprefix tailTrace_7152908
  have hstable : (prefixWord ++ tailWord_7152908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152908).length < 2 ^ (prefixWord ++ tailWord_7152908).sum := by decide
  have hdescent : baseEnd_7152908 < baseStart_7152908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152928 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 1, 5]
def baseStart_7152928 : Nat := 118140960795 + 7152928 * 2 ^ 59
def prefixEnd_7152928 : Nat := 4983230072969 + 3 ^ 40 * 7152928 * 2
def baseEnd_7152928 : Nat := 1224296717001165123334763

theorem tailTrace_7152928 : CollatzResearch.WordTrace tailWord_7152928 prefixEnd_7152928 1224296717001165123334763 := by
  unfold tailWord_7152928
  simp only [CollatzResearch.WordTrace]
  refine ⟨130444358515085476844573719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173925811353447302459431625 130444358515085476844573719)
  ·
    refine ⟨195666537772628215266860579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130444358515085476844573719 195666537772628215266860579)
    ·
      refine ⟨293499806658942322900290869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195666537772628215266860579 293499806658942322900290869)
      ·
        refine ⟨27515606874275842771902269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293499806658942322900290869 27515606874275842771902269)
        ·
          refine ⟨10318352577853441039463351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27515606874275842771902269 10318352577853441039463351)
          ·
            refine ⟨15477528866780161559195027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10318352577853441039463351 15477528866780161559195027)
            ·
              refine ⟨23216293300170242338792541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15477528866780161559195027 23216293300170242338792541)
              ·
                refine ⟨8706109987563840877047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23216293300170242338792541 8706109987563840877047203)
                ·
                  refine ⟨13059164981345761315570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8706109987563840877047203 13059164981345761315570805)
                  ·
                    refine ⟨1224296717001165123334763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13059164981345761315570805 1224296717001165123334763)
                    ·
                      rfl

theorem cell23_7152928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_7152928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152928 prefixEnd_7152928 := by exact prefixLift 7152928
  have htrace : WordTrace (prefixWord ++ tailWord_7152928) baseStart_7152928 baseEnd_7152928 := by
    simpa [prefixWord, tailWord_7152928, baseEnd_7152928] using wordTrace_append hprefix tailTrace_7152928
  have hstable : (prefixWord ++ tailWord_7152928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152928).length < 2 ^ (prefixWord ++ tailWord_7152928).sum := by decide
  have hdescent : baseEnd_7152928 < baseStart_7152928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152944 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_7152944 : Nat := 118140960795 + 7152944 * 2 ^ 59
def prefixEnd_7152944 : Nat := 4983230072969 + 3 ^ 40 * 7152944 * 2
def baseEnd_7152944 : Nat := 3672898366693967307404215

theorem tailTrace_7152944 : CollatzResearch.WordTrace tailWord_7152944 prefixEnd_7152944 3672898366693967307404215 := by
  unfold tailWord_7152944
  simp only [CollatzResearch.WordTrace]
  refine ⟨130444650299056494210864943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173926200398741992281153257 130444650299056494210864943)
  ·
    refine ⟨195666975448584741316297415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130444650299056494210864943 195666975448584741316297415)
    ·
      refine ⟨293500463172877111974446123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195666975448584741316297415 293500463172877111974446123)
      ·
        refine ⟨440250694759315667961669185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293500463172877111974446123 440250694759315667961669185)
        ·
          refine ⟨330188021069486750971251889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440250694759315667961669185 330188021069486750971251889)
          ·
            refine ⟨247641015802115063228438917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330188021069486750971251889 247641015802115063228438917)
            ·
              refine ⟨46432690462896574355332297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247641015802115063228438917 46432690462896574355332297)
              ·
                refine ⟨34824517847172430766499223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46432690462896574355332297 34824517847172430766499223)
                ·
                  refine ⟨52236776770758646149748835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34824517847172430766499223 52236776770758646149748835)
                  ·
                    refine ⟨78355165156137969224623253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52236776770758646149748835 78355165156137969224623253)
                    ·
                      refine ⟨3672898366693967307404215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78355165156137969224623253 3672898366693967307404215)
                      ·
                        rfl

theorem cell23_7152944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_7152944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152944 prefixEnd_7152944 := by exact prefixLift 7152944
  have htrace : WordTrace (prefixWord ++ tailWord_7152944) baseStart_7152944 baseEnd_7152944 := by
    simpa [prefixWord, tailWord_7152944, baseEnd_7152944] using wordTrace_append hprefix tailTrace_7152944
  have hstable : (prefixWord ++ tailWord_7152944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152944).length < 2 ^ (prefixWord ++ tailWord_7152944).sum := by decide
  have hdescent : baseEnd_7152944 < baseStart_7152944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152954 : List Nat := [3, 1, 1, 1, 4, 1, 2, 10]
def baseStart_7152954 : Nat := 118140960795 + 7152954 * 2 ^ 59
def prefixEnd_7152954 : Nat := 4983230072969 + 3 ^ 40 * 7152954 * 2
def baseEnd_7152954 : Nat := 136033463018537491417747

theorem tailTrace_7152954 : CollatzResearch.WordTrace tailWord_7152954 prefixEnd_7152954 136033463018537491417747 := by
  unfold tailWord_7152954
  simp only [CollatzResearch.WordTrace]
  refine ⟨65222416332019190032398479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173926443552051173419729277 65222416332019190032398479)
  ·
    refine ⟨97833624498028785048597719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65222416332019190032398479 97833624498028785048597719)
    ·
      refine ⟨146750436747043177572896579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97833624498028785048597719 146750436747043177572896579)
      ·
        refine ⟨220125655120564766359344869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146750436747043177572896579 220125655120564766359344869)
        ·
          refine ⟨41273560335105893692377163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220125655120564766359344869 41273560335105893692377163)
          ·
            refine ⟨61910340502658840538565745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41273560335105893692377163 61910340502658840538565745)
            ·
              refine ⟨46432755376994130403924309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61910340502658840538565745 46432755376994130403924309)
              ·
                refine ⟨136033463018537491417747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46432755376994130403924309 136033463018537491417747)
                ·
                  rfl

theorem cell23_7152954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_7152954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152954 prefixEnd_7152954 := by exact prefixLift 7152954
  have htrace : WordTrace (prefixWord ++ tailWord_7152954) baseStart_7152954 baseEnd_7152954 := by
    simpa [prefixWord, tailWord_7152954, baseEnd_7152954] using wordTrace_append hprefix tailTrace_7152954
  have hstable : (prefixWord ++ tailWord_7152954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152954).length < 2 ^ (prefixWord ++ tailWord_7152954).sum := by decide
  have hdescent : baseEnd_7152954 < baseStart_7152954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7152999 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_7152999 : Nat := 118140960795 + 7152999 * 2 ^ 59
def prefixEnd_7152999 : Nat := 4983230072969 + 3 ^ 40 * 7152999 * 2
def baseEnd_7152999 : Nat := 3672926608129964592216463

theorem tailTrace_7152999 : CollatzResearch.WordTrace tailWord_7152999 prefixEnd_7152999 3672926608129964592216463 := by
  unfold tailWord_7152999
  simp only [CollatzResearch.WordTrace]
  refine ⟨260891306612913732814982051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173927537741942488543321367 260891306612913732814982051)
  ·
    refine ⟨391336959919370599222473077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260891306612913732814982051 391336959919370599222473077)
    ·
      refine ⟨36687839992440993677106851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391336959919370599222473077 36687839992440993677106851)
      ·
        refine ⟨55031759988661490515660277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36687839992440993677106851 55031759988661490515660277)
        ·
          refine ⟨5159227498937014735843151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55031759988661490515660277 5159227498937014735843151)
          ·
            refine ⟨7738841248405522103764727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159227498937014735843151 7738841248405522103764727)
            ·
              refine ⟨11608261872608283155647091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738841248405522103764727 11608261872608283155647091)
              ·
                refine ⟨17412392808912424733470637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11608261872608283155647091 17412392808912424733470637)
                ·
                  refine ⟨6529647303342159275051489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17412392808912424733470637 6529647303342159275051489)
                  ·
                    refine ⟨4897235477506619456288617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6529647303342159275051489 4897235477506619456288617)
                    ·
                      refine ⟨3672926608129964592216463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897235477506619456288617 3672926608129964592216463)
                      ·
                        rfl

theorem cell23_7152999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_7152999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7152999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7152999 prefixEnd_7152999 := by exact prefixLift 7152999
  have htrace : WordTrace (prefixWord ++ tailWord_7152999) baseStart_7152999 baseEnd_7152999 := by
    simpa [prefixWord, tailWord_7152999, baseEnd_7152999] using wordTrace_append hprefix tailTrace_7152999
  have hstable : (prefixWord ++ tailWord_7152999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7152999).length < 2 ^ (prefixWord ++ tailWord_7152999).sum := by decide
  have hdescent : baseEnd_7152999 < baseStart_7152999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7152999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153008 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 3, 3, 2]
def baseStart_7153008 : Nat := 118140960795 + 7153008 * 2 ^ 59
def prefixEnd_7153008 : Nat := 4983230072969 + 3 ^ 40 * 7153008 * 2
def baseEnd_7153008 : Nat := 3672931229455855057003921

theorem tailTrace_7153008 : CollatzResearch.WordTrace tailWord_7153008 prefixEnd_7153008 3672931229455855057003921 := by
  unfold tailWord_7153008
  simp only [CollatzResearch.WordTrace]
  refine ⟨130445817434940563676029839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173927756579920751568039785 130445817434940563676029839)
  ·
    refine ⟨195668726152410845514044759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130445817434940563676029839 195668726152410845514044759)
    ·
      refine ⟨293503089228616268271067139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195668726152410845514044759 293503089228616268271067139)
      ·
        refine ⟨440254633842924402406600709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293503089228616268271067139 440254633842924402406600709)
        ·
          refine ⟨82547743845548325451237633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440254633842924402406600709 82547743845548325451237633)
          ·
            refine ⟨61910807884161244088428225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82547743845548325451237633 61910807884161244088428225)
            ·
              refine ⟨46433105913120933066321169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61910807884161244088428225 46433105913120933066321169)
              ·
                refine ⟨34824829434840699799740877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46433105913120933066321169 34824829434840699799740877)
                ·
                  refine ⟨13059311038065262424902829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34824829434840699799740877 13059311038065262424902829)
                  ·
                    refine ⟨4897241639274473409338561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13059311038065262424902829 4897241639274473409338561)
                    ·
                      refine ⟨3672931229455855057003921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897241639274473409338561 3672931229455855057003921)
                      ·
                        rfl

theorem cell23_7153008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 3, 2].length) (baseStart_7153008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153008 prefixEnd_7153008 := by exact prefixLift 7153008
  have htrace : WordTrace (prefixWord ++ tailWord_7153008) baseStart_7153008 baseEnd_7153008 := by
    simpa [prefixWord, tailWord_7153008, baseEnd_7153008] using wordTrace_append hprefix tailTrace_7153008
  have hstable : (prefixWord ++ tailWord_7153008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153008).length < 2 ^ (prefixWord ++ tailWord_7153008).sum := by decide
  have hdescent : baseEnd_7153008 < baseStart_7153008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153058 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_7153058 : Nat := 118140960795 + 7153058 * 2 ^ 59
def prefixEnd_7153058 : Nat := 4983230072969 + 3 ^ 40 * 7153058 * 2
def baseEnd_7153058 : Nat := 3672956903488579861378691

theorem tailTrace_7153058 : CollatzResearch.WordTrace tailWord_7153058 prefixEnd_7153058 3672956903488579861378691 := by
  unfold tailWord_7153058
  simp only [CollatzResearch.WordTrace]
  refine ⟨65223364629924996472844957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173928972346466657260919885 65223364629924996472844957)
  ·
    refine ⟨24458761736221873677316859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65223364629924996472844957 24458761736221873677316859)
    ·
      refine ⟨36688142604332810515975289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24458761736221873677316859 36688142604332810515975289)
      ·
        refine ⟨27516106953249607886981467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36688142604332810515975289 27516106953249607886981467)
        ·
          refine ⟨41274160429874411830472201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27516106953249607886981467 41274160429874411830472201)
          ·
            refine ⟨30955620322405808872854151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41274160429874411830472201 30955620322405808872854151)
            ·
              refine ⟨46433430483608713309281227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30955620322405808872854151 46433430483608713309281227)
              ·
                refine ⟨69650145725413069963921841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46433430483608713309281227 69650145725413069963921841)
                ·
                  refine ⟨52237609294059802472941381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69650145725413069963921841 52237609294059802472941381)
                  ·
                    refine ⟨9794551742636212963676509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52237609294059802472941381 9794551742636212963676509)
                    ·
                      refine ⟨3672956903488579861378691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9794551742636212963676509 3672956903488579861378691)
                      ·
                        rfl

theorem cell23_7153058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_7153058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153058 prefixEnd_7153058 := by exact prefixLift 7153058
  have htrace : WordTrace (prefixWord ++ tailWord_7153058) baseStart_7153058 baseEnd_7153058 := by
    simpa [prefixWord, tailWord_7153058, baseEnd_7153058] using wordTrace_append hprefix tailTrace_7153058
  have hstable : (prefixWord ++ tailWord_7153058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153058).length < 2 ^ (prefixWord ++ tailWord_7153058).sum := by decide
  have hdescent : baseEnd_7153058 < baseStart_7153058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153148 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_7153148 : Nat := 118140960795 + 7153148 * 2 ^ 59
def prefixEnd_7153148 : Nat := 4983230072969 + 3 ^ 40 * 7153148 * 2
def baseEnd_7153148 : Nat := 3673003116747484509253277

theorem tailTrace_7153148 : CollatzResearch.WordTrace tailWord_7153148 prefixEnd_7153148 3673003116747484509253277 := by
  unfold tailWord_7153148
  simp only [CollatzResearch.WordTrace]
  refine ⟨130448370544686965631078049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173931160726249287508104065 130448370544686965631078049)
  ·
    refine ⟨97836277908515224223308537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130448370544686965631078049 97836277908515224223308537)
    ·
      refine ⟨73377208431386418167481403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97836277908515224223308537 73377208431386418167481403)
      ·
        refine ⟨110065812647079627251222105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73377208431386418167481403 110065812647079627251222105)
        ·
          refine ⟨82549359485309720438416579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110065812647079627251222105 82549359485309720438416579)
          ·
            refine ⟨123824039227964580657624869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82549359485309720438416579 123824039227964580657624869)
            ·
              refine ⟨23217007355243358873304663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123824039227964580657624869 23217007355243358873304663)
              ·
                refine ⟨34825511032865038309956995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23217007355243358873304663 34825511032865038309956995)
                ·
                  refine ⟨52238266549297557464935493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34825511032865038309956995 52238266549297557464935493)
                  ·
                    refine ⟨9794674977993292024675405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52238266549297557464935493 9794674977993292024675405)
                    ·
                      refine ⟨3673003116747484509253277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9794674977993292024675405 3673003116747484509253277)
                      ·
                        rfl

theorem cell23_7153148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_7153148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153148 prefixEnd_7153148 := by exact prefixLift 7153148
  have htrace : WordTrace (prefixWord ++ tailWord_7153148) baseStart_7153148 baseEnd_7153148 := by
    simpa [prefixWord, tailWord_7153148, baseEnd_7153148] using wordTrace_append hprefix tailTrace_7153148
  have hstable : (prefixWord ++ tailWord_7153148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153148).length < 2 ^ (prefixWord ++ tailWord_7153148).sum := by decide
  have hdescent : baseEnd_7153148 < baseStart_7153148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153155 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 1, 4]
def baseStart_7153155 : Nat := 118140960795 + 7153155 * 2 ^ 59
def prefixEnd_7153155 : Nat := 4983230072969 + 3 ^ 40 * 7153155 * 2
def baseEnd_7153155 : Nat := 1224335570370688660621915

theorem tailTrace_7153155 : CollatzResearch.WordTrace tailWord_7153155 prefixEnd_7153155 1224335570370688660621915 := by
  unfold tailWord_7153155
  simp only [CollatzResearch.WordTrace]
  refine ⟨260896996400348571457660919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173931330933565714305107279 260896996400348571457660919)
  ·
    refine ⟨391345494600522857186491379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260896996400348571457660919 391345494600522857186491379)
    ·
      refine ⟨587018241900784285779737069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391345494600522857186491379 587018241900784285779737069)
      ·
        refine ⟨220131840712794107167401401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587018241900784285779737069 220131840712794107167401401)
        ·
          refine ⟨165098880534595580375551051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220131840712794107167401401 165098880534595580375551051)
          ·
            refine ⟨247648320801893370563326577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165098880534595580375551051 247648320801893370563326577)
            ·
              refine ⟨185736240601420027922494933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247648320801893370563326577 185736240601420027922494933)
              ·
                refine ⟨4353193139095781904433475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185736240601420027922494933 4353193139095781904433475)
                ·
                  refine ⟨6529789708643672856650213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353193139095781904433475 6529789708643672856650213)
                  ·
                    refine ⟨1224335570370688660621915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6529789708643672856650213 1224335570370688660621915)
                    ·
                      rfl

theorem cell23_7153155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 4].length) (baseStart_7153155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153155 prefixEnd_7153155 := by exact prefixLift 7153155
  have htrace : WordTrace (prefixWord ++ tailWord_7153155) baseStart_7153155 baseEnd_7153155 := by
    simpa [prefixWord, tailWord_7153155, baseEnd_7153155] using wordTrace_append hprefix tailTrace_7153155
  have hstable : (prefixWord ++ tailWord_7153155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153155).length < 2 ^ (prefixWord ++ tailWord_7153155).sum := by decide
  have hdescent : baseEnd_7153155 < baseStart_7153155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153185 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 6]
def baseStart_7153185 : Nat := 118140960795 + 7153185 * 2 ^ 59
def prefixEnd_7153185 : Nat := 4983230072969 + 3 ^ 40 * 7153185 * 2
def baseEnd_7153185 : Nat := 408113568392411207165623

theorem tailTrace_7153185 : CollatzResearch.WordTrace tailWord_7153185 prefixEnd_7153185 408113568392411207165623 := by
  unfold tailWord_7153185
  simp only [CollatzResearch.WordTrace]
  refine ⟨260898090590239886581253009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173932060393493257720835339 260898090590239886581253009)
  ·
    refine ⟨195673567942679914935939757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260898090590239886581253009 195673567942679914935939757)
    ·
      refine ⟨73377587978504968100977409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195673567942679914935939757 73377587978504968100977409)
      ·
        refine ⟨55033190983878726075733057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73377587978504968100977409 55033190983878726075733057)
        ·
          refine ⟨41274893237909044556799793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55033190983878726075733057 41274893237909044556799793)
          ·
            refine ⟨30956169928431783417599845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41274893237909044556799793 30956169928431783417599845)
            ·
              refine ⟨5804281861580959390799971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30956169928431783417599845 5804281861580959390799971)
              ·
                refine ⟨8706422792371439086199957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804281861580959390799971 8706422792371439086199957)
                ·
                  refine ⟨408113568392411207165623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8706422792371439086199957 408113568392411207165623)
                  ·
                    rfl

theorem cell23_7153185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 6].length) (baseStart_7153185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153185 prefixEnd_7153185 := by exact prefixLift 7153185
  have htrace : WordTrace (prefixWord ++ tailWord_7153185) baseStart_7153185 baseEnd_7153185 := by
    simpa [prefixWord, tailWord_7153185, baseEnd_7153185] using wordTrace_append hprefix tailTrace_7153185
  have hstable : (prefixWord ++ tailWord_7153185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153185).length < 2 ^ (prefixWord ++ tailWord_7153185).sum := by decide
  have hdescent : baseEnd_7153185 < baseStart_7153185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153252 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_7153252 : Nat := 118140960795 + 7153252 * 2 ^ 59
def prefixEnd_7153252 : Nat := 4983230072969 + 3 ^ 40 * 7153252 * 2
def baseEnd_7153252 : Nat := 3673056518735552102352799

theorem tailTrace_7153252 : CollatzResearch.WordTrace tailWord_7153252 prefixEnd_7153252 3673056518735552102352799 := by
  unfold tailWord_7153252
  simp only [CollatzResearch.WordTrace]
  refine ⟨130450267140498578511971005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173933689520664771349294673 130450267140498578511971005)
  ·
    refine ⟨48918850177686966941989127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130450267140498578511971005 48918850177686966941989127)
    ·
      refine ⟨73378275266530450412983691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48918850177686966941989127 73378275266530450412983691)
      ·
        refine ⟨110067412899795675619475537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73378275266530450412983691 110067412899795675619475537)
        ·
          refine ⟨82550559674846756714606653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110067412899795675619475537 82550559674846756714606653)
          ·
            refine ⟨30956459878067533767977495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82550559674846756714606653 30956459878067533767977495)
            ·
              refine ⟨46434689817101300651966243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30956459878067533767977495 46434689817101300651966243)
              ·
                refine ⟨69652034725651950977949365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46434689817101300651966243 69652034725651950977949365)
                ·
                  refine ⟨6529878255529870404182753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69652034725651950977949365 6529878255529870404182753)
                  ·
                    refine ⟨4897408691647402803137065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6529878255529870404182753 4897408691647402803137065)
                    ·
                      refine ⟨3673056518735552102352799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897408691647402803137065 3673056518735552102352799)
                      ·
                        rfl

theorem cell23_7153252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_7153252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153252 prefixEnd_7153252 := by exact prefixLift 7153252
  have htrace : WordTrace (prefixWord ++ tailWord_7153252) baseStart_7153252 baseEnd_7153252 := by
    simpa [prefixWord, tailWord_7153252, baseEnd_7153252] using wordTrace_append hprefix tailTrace_7153252
  have hstable : (prefixWord ++ tailWord_7153252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153252).length < 2 ^ (prefixWord ++ tailWord_7153252).sum := by decide
  have hdescent : baseEnd_7153252 < baseStart_7153252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153255 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_7153255 : Nat := 118140960795 + 7153255 * 2 ^ 59
def prefixEnd_7153255 : Nat := 4983230072969 + 3 ^ 40 * 7153255 * 2
def baseEnd_7153255 : Nat := 3673058059177515590615285

theorem tailTrace_7153255 : CollatzResearch.WordTrace tailWord_7153255 prefixEnd_7153255 3673058059177515590615285 := by
  unfold tailWord_7153255
  simp only [CollatzResearch.WordTrace]
  refine ⟨260900643699986288536301219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173933762466657525690867479 260900643699986288536301219)
  ·
    refine ⟨391350965549979432804451829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260900643699986288536301219 391350965549979432804451829)
    ·
      refine ⟨36689153020310571825417359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391350965549979432804451829 36689153020310571825417359)
      ·
        refine ⟨55033729530465857738126039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36689153020310571825417359 55033729530465857738126039)
        ·
          refine ⟨82550594295698786607189059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55033729530465857738126039 82550594295698786607189059)
          ·
            refine ⟨123825891443548179910783589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82550594295698786607189059 123825891443548179910783589)
            ·
              refine ⟨23217354645665283733271923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123825891443548179910783589 23217354645665283733271923)
              ·
                refine ⟨34826031968497925599907885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23217354645665283733271923 34826031968497925599907885)
                ·
                  refine ⟨13059761988186722099965457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34826031968497925599907885 13059761988186722099965457)
                  ·
                    refine ⟨9794821491140041574974093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13059761988186722099965457 9794821491140041574974093)
                    ·
                      refine ⟨3673058059177515590615285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9794821491140041574974093 3673058059177515590615285)
                      ·
                        rfl

theorem cell23_7153255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_7153255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153255 prefixEnd_7153255 := by exact prefixLift 7153255
  have htrace : WordTrace (prefixWord ++ tailWord_7153255) baseStart_7153255 baseEnd_7153255 := by
    simpa [prefixWord, tailWord_7153255, baseEnd_7153255] using wordTrace_append hprefix tailTrace_7153255
  have hstable : (prefixWord ++ tailWord_7153255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153255).length < 2 ^ (prefixWord ++ tailWord_7153255).sum := by decide
  have hdescent : baseEnd_7153255 < baseStart_7153255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153269 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7153269 : Nat := 118140960795 + 7153269 * 2 ^ 59
def prefixEnd_7153269 : Nat := 4983230072969 + 3 ^ 40 * 7153269 * 2
def baseEnd_7153269 : Nat := 3673065247906678535840221

theorem tailTrace_7153269 : CollatzResearch.WordTrace tailWord_7153269 prefixEnd_7153269 3673065247906678535840221 := by
  unfold tailWord_7153269
  simp only [CollatzResearch.WordTrace]
  refine ⟨260901154321935568927310861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173934102881290379284873907 260901154321935568927310861)
  ·
    refine ⟨97837932870725838347741573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260901154321935568927310861 97837932870725838347741573)
    ·
      refine ⟨18344612413261094690201545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97837932870725838347741573 18344612413261094690201545)
      ·
        refine ⟨13758459309945821017651159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18344612413261094690201545 13758459309945821017651159)
        ·
          refine ⟨20637688964918731526476739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13758459309945821017651159 20637688964918731526476739)
          ·
            refine ⟨30956533447378097289715109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20637688964918731526476739 30956533447378097289715109)
            ·
              refine ⟨5804350021383393241821583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30956533447378097289715109 5804350021383393241821583)
              ·
                refine ⟨8706525032075089862732375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804350021383393241821583 8706525032075089862732375)
                ·
                  refine ⟨13059787548112634794098563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8706525032075089862732375 13059787548112634794098563)
                  ·
                    refine ⟨19589681322168952191147845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13059787548112634794098563 19589681322168952191147845)
                    ·
                      refine ⟨3673065247906678535840221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19589681322168952191147845 3673065247906678535840221)
                      ·
                        rfl

theorem cell23_7153269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7153269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153269 prefixEnd_7153269 := by exact prefixLift 7153269
  have htrace : WordTrace (prefixWord ++ tailWord_7153269) baseStart_7153269 baseEnd_7153269 := by
    simpa [prefixWord, tailWord_7153269, baseEnd_7153269] using wordTrace_append hprefix tailTrace_7153269
  have hstable : (prefixWord ++ tailWord_7153269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153269).length < 2 ^ (prefixWord ++ tailWord_7153269).sum := by decide
  have hdescent : baseEnd_7153269 < baseStart_7153269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153328 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_7153328 : Nat := 118140960795 + 7153328 * 2 ^ 59
def prefixEnd_7153328 : Nat := 4983230072969 + 3 ^ 40 * 7153328 * 2
def baseEnd_7153328 : Nat := 3673095543265293805002449

theorem tailTrace_7153328 : CollatzResearch.WordTrace tailWord_7153328 prefixEnd_7153328 3673095543265293805002449 := by
  unfold tailWord_7153328
  simp only [CollatzResearch.WordTrace]
  refine ⟨130451653114360911001854319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173935537485814548002472425 130451653114360911001854319)
  ·
    refine ⟨195677479671541366502781479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130451653114360911001854319 195677479671541366502781479)
    ·
      refine ⟨293516219507312049754172219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195677479671541366502781479 293516219507312049754172219)
      ·
        refine ⟨440274329260968074631258329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293516219507312049754172219 440274329260968074631258329)
        ·
          refine ⟨330205746945726055973443747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440274329260968074631258329 330205746945726055973443747)
          ·
            refine ⟨495308620418589083960165621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330205746945726055973443747 495308620418589083960165621)
            ·
              refine ⟨46435183164242726621265527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495308620418589083960165621 46435183164242726621265527)
              ·
                refine ⟨69652774746364089931898291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46435183164242726621265527 69652774746364089931898291)
                ·
                  refine ⟨104479162119546134897847437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69652774746364089931898291 104479162119546134897847437)
                  ·
                    refine ⟨39179685794829800586692789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104479162119546134897847437 39179685794829800586692789)
                    ·
                      refine ⟨3673095543265293805002449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39179685794829800586692789 3673095543265293805002449)
                      ·
                        rfl

theorem cell23_7153328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_7153328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153328 prefixEnd_7153328 := by exact prefixLift 7153328
  have htrace : WordTrace (prefixWord ++ tailWord_7153328) baseStart_7153328 baseEnd_7153328 := by
    simpa [prefixWord, tailWord_7153328, baseEnd_7153328] using wordTrace_append hprefix tailTrace_7153328
  have hstable : (prefixWord ++ tailWord_7153328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153328).length < 2 ^ (prefixWord ++ tailWord_7153328).sum := by decide
  have hdescent : baseEnd_7153328 < baseStart_7153328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153395 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 2, 5]
def baseStart_7153395 : Nat := 118140960795 + 7153395 * 2 ^ 59
def prefixEnd_7153395 : Nat := 4983230072969 + 3 ^ 40 * 7153395 * 2
def baseEnd_7153395 : Nat := 1224376648823048347621547

theorem tailTrace_7153395 : CollatzResearch.WordTrace tailWord_7153395 prefixEnd_7153395 1224376648823048347621547 := by
  unfold tailWord_7153395
  simp only [CollatzResearch.WordTrace]
  refine ⟨260905749919479092446397639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173937166612986061630931759 260905749919479092446397639)
  ·
    refine ⟨391358624879218638669596459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260905749919479092446397639 391358624879218638669596459)
    ·
      refine ⟨587037937318827958004394689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391358624879218638669596459 587037937318827958004394689)
      ·
        refine ⟨440278452989120968503296017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587037937318827958004394689 440278452989120968503296017)
        ·
          refine ⟨330208839741840726377472013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440278452989120968503296017 330208839741840726377472013)
          ·
            refine ⟨123828314903190272391552005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330208839741840726377472013 123828314903190272391552005)
            ·
              refine ⟨23217809044348176073416001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123828314903190272391552005 23217809044348176073416001)
              ·
                refine ⟨17413356783261132055062001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23217809044348176073416001 17413356783261132055062001)
                ·
                  refine ⟨13060017587445849041296501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17413356783261132055062001 13060017587445849041296501)
                  ·
                    refine ⟨1224376648823048347621547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13060017587445849041296501 1224376648823048347621547)
                    ·
                      rfl

theorem cell23_7153395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 5].length) (baseStart_7153395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153395 prefixEnd_7153395 := by exact prefixLift 7153395
  have htrace : WordTrace (prefixWord ++ tailWord_7153395) baseStart_7153395 baseEnd_7153395 := by
    simpa [prefixWord, tailWord_7153395, baseEnd_7153395] using wordTrace_append hprefix tailTrace_7153395
  have hstable : (prefixWord ++ tailWord_7153395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153395).length < 2 ^ (prefixWord ++ tailWord_7153395).sum := by decide
  have hdescent : baseEnd_7153395 < baseStart_7153395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153432 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7153432 : Nat := 118140960795 + 7153432 * 2 ^ 59
def prefixEnd_7153432 : Nat := 4983230072969 + 3 ^ 40 * 7153432 * 2
def baseEnd_7153432 : Nat := 3673148945253361398101971

theorem tailTrace_7153432 : CollatzResearch.WordTrace tailWord_7153432 prefixEnd_7153432 3673148945253361398101971 := by
  unfold tailWord_7153432
  simp only [CollatzResearch.WordTrace]
  refine ⟨130453549710172523882747275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173938066280230031843663033 130453549710172523882747275)
  ·
    refine ⟨195680324565258785824120913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130453549710172523882747275 195680324565258785824120913)
    ·
      refine ⟨146760243423944089368090685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195680324565258785824120913 146760243423944089368090685)
      ·
        refine ⟨55035091283979033513034007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146760243423944089368090685 55035091283979033513034007)
        ·
          refine ⟨82552636925968550269551011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55035091283979033513034007 82552636925968550269551011)
          ·
            refine ⟨123828955388952825404326517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82552636925968550269551011 123828955388952825404326517)
            ·
              refine ⟨11608964567714327381655611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123828955388952825404326517 11608964567714327381655611)
              ·
                refine ⟨17413446851571491072483417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11608964567714327381655611 17413446851571491072483417)
                ·
                  refine ⟨13060085138678618304362563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17413446851571491072483417 13060085138678618304362563)
                  ·
                    refine ⟨19590127708017927456543845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13060085138678618304362563 19590127708017927456543845)
                    ·
                      refine ⟨3673148945253361398101971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19590127708017927456543845 3673148945253361398101971)
                      ·
                        rfl

theorem cell23_7153432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7153432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153432 prefixEnd_7153432 := by exact prefixLift 7153432
  have htrace : WordTrace (prefixWord ++ tailWord_7153432) baseStart_7153432 baseEnd_7153432 := by
    simpa [prefixWord, tailWord_7153432, baseEnd_7153432] using wordTrace_append hprefix tailTrace_7153432
  have hstable : (prefixWord ++ tailWord_7153432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153432).length < 2 ^ (prefixWord ++ tailWord_7153432).sum := by decide
  have hdescent : baseEnd_7153432 < baseStart_7153432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153435 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 3]
def baseStart_7153435 : Nat := 118140960795 + 7153435 * 2 ^ 59
def prefixEnd_7153435 : Nat := 4983230072969 + 3 ^ 40 * 7153435 * 2
def baseEnd_7153435 : Nat := 3673150485695324886364457

theorem tailTrace_7153435 : CollatzResearch.WordTrace tailWord_7153435 prefixEnd_7153435 3673150485695324886364457 := by
  unfold tailWord_7153435
  simp only [CollatzResearch.WordTrace]
  refine ⟨260907208839334179277853759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173938139226222786185235839 260907208839334179277853759)
  ·
    refine ⟨391360813259001268916780639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260907208839334179277853759 391360813259001268916780639)
    ·
      refine ⟨587041219888501903375170959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391360813259001268916780639 587041219888501903375170959)
      ·
        refine ⟨880561829832752855062756439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587041219888501903375170959 880561829832752855062756439)
        ·
          refine ⟨1320842744749129282594134659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880561829832752855062756439 1320842744749129282594134659)
          ·
            refine ⟨1981264117123693923891201989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320842744749129282594134659 1981264117123693923891201989)
            ·
              refine ⟨371487021960692610729600373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1981264117123693923891201989 371487021960692610729600373)
              ·
                refine ⟨34826908308814932255900035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 371487021960692610729600373 34826908308814932255900035)
                ·
                  refine ⟨52240362463222398383850053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34826908308814932255900035 52240362463222398383850053)
                  ·
                    refine ⟨9795067961854199696971885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52240362463222398383850053 9795067961854199696971885)
                    ·
                      refine ⟨3673150485695324886364457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795067961854199696971885 3673150485695324886364457)
                      ·
                        rfl

theorem cell23_7153435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 3].length) (baseStart_7153435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153435 prefixEnd_7153435 := by exact prefixLift 7153435
  have htrace : WordTrace (prefixWord ++ tailWord_7153435) baseStart_7153435 baseEnd_7153435 := by
    simpa [prefixWord, tailWord_7153435, baseEnd_7153435] using wordTrace_append hprefix tailTrace_7153435
  have hstable : (prefixWord ++ tailWord_7153435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153435).length < 2 ^ (prefixWord ++ tailWord_7153435).sum := by decide
  have hdescent : baseEnd_7153435 < baseStart_7153435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153442 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7153442 : Nat := 118140960795 + 7153442 * 2 ^ 59
def prefixEnd_7153442 : Nat := 4983230072969 + 3 ^ 40 * 7153442 * 2
def baseEnd_7153442 : Nat := 1224384693353302119658975

theorem tailTrace_7153442 : CollatzResearch.WordTrace tailWord_7153442 prefixEnd_7153442 1224384693353302119658975 := by
  unfold tailWord_7153442
  simp only [CollatzResearch.WordTrace]
  refine ⟨65226866037577204868339645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173938309433539212982239053 65226866037577204868339645)
  ·
    refine ⟨24460074764091451825627367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65226866037577204868339645 24460074764091451825627367)
    ·
      refine ⟨36690112146137177738441051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24460074764091451825627367 36690112146137177738441051)
      ·
        refine ⟨55035168219205766607661577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36690112146137177738441051 55035168219205766607661577)
        ·
          refine ⟨41276376164404324955746183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55035168219205766607661577 41276376164404324955746183)
          ·
            refine ⟨61914564246606487433619275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41276376164404324955746183 61914564246606487433619275)
            ·
              refine ⟨92871846369909731150428913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61914564246606487433619275 92871846369909731150428913)
              ·
                refine ⟨69653884777432298362821685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92871846369909731150428913 69653884777432298362821685)
                ·
                  refine ⟨6530051697884277971514533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69653884777432298362821685 6530051697884277971514533)
                  ·
                    refine ⟨1224384693353302119658975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530051697884277971514533 1224384693353302119658975)
                    ·
                      rfl

theorem cell23_7153442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7153442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153442 prefixEnd_7153442 := by exact prefixLift 7153442
  have htrace : WordTrace (prefixWord ++ tailWord_7153442) baseStart_7153442 baseEnd_7153442 := by
    simpa [prefixWord, tailWord_7153442, baseEnd_7153442] using wordTrace_append hprefix tailTrace_7153442
  have hstable : (prefixWord ++ tailWord_7153442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153442).length < 2 ^ (prefixWord ++ tailWord_7153442).sum := by decide
  have hdescent : baseEnd_7153442 < baseStart_7153442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153445 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_7153445 : Nat := 118140960795 + 7153445 * 2 ^ 59
def prefixEnd_7153445 : Nat := 4983230072969 + 3 ^ 40 * 7153445 * 2
def baseEnd_7153445 : Nat := 3673155620501869847239411

theorem tailTrace_7153445 : CollatzResearch.WordTrace tailWord_7153445 prefixEnd_7153445 3673155620501869847239411 := by
  unfold tailWord_7153445
  simp only [CollatzResearch.WordTrace]
  refine ⟨260907573569297950985717789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173938382379531967323811859 260907573569297950985717789)
  ·
    refine ⟨97840340088486731619644171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260907573569297950985717789 97840340088486731619644171)
    ·
      refine ⟨146760510132730097429466257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97840340088486731619644171 146760510132730097429466257)
      ·
        refine ⟨110070382599547573072099693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146760510132730097429466257 110070382599547573072099693)
        ·
          refine ⟨41276393474830339902037385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110070382599547573072099693 41276393474830339902037385)
          ·
            refine ⟨30957295106122754926528039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41276393474830339902037385 30957295106122754926528039)
            ·
              refine ⟨46435942659184132389792059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30957295106122754926528039 46435942659184132389792059)
              ·
                refine ⟨69653913988776198584688089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46435942659184132389792059 69653913988776198584688089)
                ·
                  refine ⟨52240435491582148938516067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69653913988776198584688089 52240435491582148938516067)
                  ·
                    refine ⟨78360653237373223407774101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52240435491582148938516067 78360653237373223407774101)
                    ·
                      refine ⟨3673155620501869847239411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78360653237373223407774101 3673155620501869847239411)
                      ·
                        rfl

theorem cell23_7153445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_7153445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153445 prefixEnd_7153445 := by exact prefixLift 7153445
  have htrace : WordTrace (prefixWord ++ tailWord_7153445) baseStart_7153445 baseEnd_7153445 := by
    simpa [prefixWord, tailWord_7153445, baseEnd_7153445] using wordTrace_append hprefix tailTrace_7153445
  have hstable : (prefixWord ++ tailWord_7153445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153445).length < 2 ^ (prefixWord ++ tailWord_7153445).sum := by decide
  have hdescent : baseEnd_7153445 < baseStart_7153445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153459 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 3, 4]
def baseStart_7153459 : Nat := 118140960795 + 7153459 * 2 ^ 59
def prefixEnd_7153459 : Nat := 4983230072969 + 3 ^ 40 * 7153459 * 2
def baseEnd_7153459 : Nat := 1224387603077010930821449

theorem tailTrace_7153459 : CollatzResearch.WordTrace tailWord_7153459 prefixEnd_7153459 1224387603077010930821449 := by
  unfold tailWord_7153459
  simp only [CollatzResearch.WordTrace]
  refine ⟨260908084191247231376727431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173938722794164820917818287 260908084191247231376727431)
  ·
    refine ⟨391362126286870847065091147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260908084191247231376727431 391362126286870847065091147)
    ·
      refine ⟨587043189430306270597636721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391362126286870847065091147 587043189430306270597636721)
      ·
        refine ⟨440282392072729702948227541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587043189430306270597636721 440282392072729702948227541)
        ·
          refine ⟨10319118564204602412849083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 440282392072729702948227541 10319118564204602412849083)
          ·
            refine ⟨15478677846306903619273625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319118564204602412849083 15478677846306903619273625)
            ·
              refine ⟨11609008384730177714455219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15478677846306903619273625 11609008384730177714455219)
              ·
                refine ⟨17413512577095266571682829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609008384730177714455219 17413512577095266571682829)
                ·
                  refine ⟨6530067216410724964381061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17413512577095266571682829 6530067216410724964381061)
                  ·
                    refine ⟨1224387603077010930821449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530067216410724964381061 1224387603077010930821449)
                    ·
                      rfl

theorem cell23_7153459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 4].length) (baseStart_7153459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153459 prefixEnd_7153459 := by exact prefixLift 7153459
  have htrace : WordTrace (prefixWord ++ tailWord_7153459) baseStart_7153459 baseEnd_7153459 := by
    simpa [prefixWord, tailWord_7153459, baseEnd_7153459] using wordTrace_append hprefix tailTrace_7153459
  have hstable : (prefixWord ++ tailWord_7153459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153459).length < 2 ^ (prefixWord ++ tailWord_7153459).sum := by decide
  have hdescent : baseEnd_7153459 < baseStart_7153459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153516 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_7153516 : Nat := 118140960795 + 7153516 * 2 ^ 59
def prefixEnd_7153516 : Nat := 4983230072969 + 3 ^ 40 * 7153516 * 2
def baseEnd_7153516 : Nat := 3673192077628339069451585

theorem tailTrace_7153516 : CollatzResearch.WordTrace tailWord_7153516 prefixEnd_7153516 3673192077628339069451585 := by
  unfold tailWord_7153516
  simp only [CollatzResearch.WordTrace]
  refine ⟨130455081576020365055776201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173940108768027153407701601 130455081576020365055776201)
  ·
    refine ⟨97841311182015273791832151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130455081576020365055776201 97841311182015273791832151)
    ·
      refine ⟨146761966773022910687748227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97841311182015273791832151 146761966773022910687748227)
      ·
        refine ⟨220142950159534366031622341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146761966773022910687748227 220142950159534366031622341)
        ·
          refine ⟨41276803154912693630929189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220142950159534366031622341 41276803154912693630929189)
          ·
            refine ⟨7739400591546130055799223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41276803154912693630929189 7739400591546130055799223)
            ·
              refine ⟨11609100887319195083698835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739400591546130055799223 11609100887319195083698835)
              ·
                refine ⟨17413651330978792625548253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609100887319195083698835 17413651330978792625548253)
                ·
                  refine ⟨6530119249117047234580595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17413651330978792625548253 6530119249117047234580595)
                  ·
                    refine ⟨9795178873675570851870893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530119249117047234580595 9795178873675570851870893)
                    ·
                      refine ⟨3673192077628339069451585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795178873675570851870893 3673192077628339069451585)
                      ·
                        rfl

theorem cell23_7153516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_7153516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153516 prefixEnd_7153516 := by exact prefixLift 7153516
  have htrace : WordTrace (prefixWord ++ tailWord_7153516) baseStart_7153516 baseEnd_7153516 := by
    simpa [prefixWord, tailWord_7153516, baseEnd_7153516] using wordTrace_append hprefix tailTrace_7153516
  have hstable : (prefixWord ++ tailWord_7153516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153516).length < 2 ^ (prefixWord ++ tailWord_7153516).sum := by decide
  have hdescent : baseEnd_7153516 < baseStart_7153516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153522 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7153522 : Nat := 118140960795 + 7153522 * 2 ^ 59
def prefixEnd_7153522 : Nat := 4983230072969 + 3 ^ 40 * 7153522 * 2
def baseEnd_7153522 : Nat := 3673195158512266045976557

theorem tailTrace_7153522 : CollatzResearch.WordTrace tailWord_7153522 prefixEnd_7153522 3673195158512266045976557 := by
  unfold tailWord_7153522
  simp only [CollatzResearch.WordTrace]
  refine ⟨65227595497504748284067705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173940254660012662090847213 65227595497504748284067705)
  ·
    refine ⟨48920696623128561213050779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65227595497504748284067705 48920696623128561213050779)
    ·
      refine ⟨73381044934692841819576169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48920696623128561213050779 73381044934692841819576169)
      ·
        refine ⟨55035783701019631364682127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73381044934692841819576169 55035783701019631364682127)
        ·
          refine ⟨82553675551529447047023191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55035783701019631364682127 82553675551529447047023191)
          ·
            refine ⟨123830513327294170570534787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82553675551529447047023191 123830513327294170570534787)
            ·
              refine ⟨185745769990941255855802181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123830513327294170570534787 185745769990941255855802181)
              ·
                refine ⟨34827331873301485472962909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185745769990941255855802181 34827331873301485472962909)
                ·
                  refine ⟨13060249452488057052361091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34827331873301485472962909 13060249452488057052361091)
                  ·
                    refine ⟨19590374178732085578541637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13060249452488057052361091 19590374178732085578541637)
                    ·
                      refine ⟨3673195158512266045976557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19590374178732085578541637 3673195158512266045976557)
                      ·
                        rfl

theorem cell23_7153522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7153522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153522 prefixEnd_7153522 := by exact prefixLift 7153522
  have htrace : WordTrace (prefixWord ++ tailWord_7153522) baseStart_7153522 baseEnd_7153522 := by
    simpa [prefixWord, tailWord_7153522, baseEnd_7153522] using wordTrace_append hprefix tailTrace_7153522
  have hstable : (prefixWord ++ tailWord_7153522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153522).length < 2 ^ (prefixWord ++ tailWord_7153522).sum := by decide
  have hdescent : baseEnd_7153522 < baseStart_7153522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153539 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 4]
def baseStart_7153539 : Nat := 118140960795 + 7153539 * 2 ^ 59
def prefixEnd_7153539 : Nat := 4983230072969 + 3 ^ 40 * 7153539 * 2
def baseEnd_7153539 : Nat := 3673203887683392479463979

theorem tailTrace_7153539 : CollatzResearch.WordTrace tailWord_7153539 prefixEnd_7153539 3673203887683392479463979 := by
  unfold tailWord_7153539
  simp only [CollatzResearch.WordTrace]
  refine ⟨260911002030957405039639671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173940668020638270026426447 260911002030957405039639671)
  ·
    refine ⟨391366503046436107559459507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260911002030957405039639671 391366503046436107559459507)
    ·
      refine ⟨587049754569654161339189261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391366503046436107559459507 587049754569654161339189261)
      ·
        refine ⟨220143657963620310502195973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587049754569654161339189261 220143657963620310502195973)
        ·
          refine ⟨41276935868178808219161745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220143657963620310502195973 41276935868178808219161745)
          ·
            refine ⟨30957701901134106164371309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41276935868178808219161745 30957701901134106164371309)
            ·
              refine ⟨11609138212925289811639241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30957701901134106164371309 11609138212925289811639241)
              ·
                refine ⟨8706853659693967358729431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609138212925289811639241 8706853659693967358729431)
                ·
                  refine ⟨13060280489540951038094147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8706853659693967358729431 13060280489540951038094147)
                  ·
                    refine ⟨19590420734311426557141221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13060280489540951038094147 19590420734311426557141221)
                    ·
                      refine ⟨3673203887683392479463979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19590420734311426557141221 3673203887683392479463979)
                      ·
                        rfl

theorem cell23_7153539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_7153539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153539 prefixEnd_7153539 := by exact prefixLift 7153539
  have htrace : WordTrace (prefixWord ++ tailWord_7153539) baseStart_7153539 baseEnd_7153539 := by
    simpa [prefixWord, tailWord_7153539, baseEnd_7153539] using wordTrace_append hprefix tailTrace_7153539
  have hstable : (prefixWord ++ tailWord_7153539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153539).length < 2 ^ (prefixWord ++ tailWord_7153539).sum := by decide
  have hdescent : baseEnd_7153539 < baseStart_7153539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153545 : List Nat := [1, 2, 1, 1, 5, 1, 1, 11]
def baseStart_7153545 : Nat := 118140960795 + 7153545 * 2 ^ 59
def prefixEnd_7153545 : Nat := 4983230072969 + 3 ^ 40 * 7153545 * 2
def baseEnd_7153545 : Nat := 136044702539530350221813

theorem tailTrace_7153545 : CollatzResearch.WordTrace tailWord_7153545 prefixEnd_7153545 136044702539530350221813 := by
  unfold tailWord_7153545
  simp only [CollatzResearch.WordTrace]
  refine ⟨260911220868935668064358089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173940813912623778709572059 260911220868935668064358089)
  ·
    refine ⟨195683415651701751048268567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260911220868935668064358089 195683415651701751048268567)
    ·
      refine ⟨293525123477552626572402851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195683415651701751048268567 293525123477552626572402851)
      ·
        refine ⟨440287685216328939858604277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293525123477552626572402851 440287685216328939858604277)
        ·
          refine ⟨41276970489030838111744151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 440287685216328939858604277 41276970489030838111744151)
          ·
            refine ⟨61915455733546257167616227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41276970489030838111744151 61915455733546257167616227)
            ·
              refine ⟨92873183600319385751424341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61915455733546257167616227 92873183600319385751424341)
              ·
                refine ⟨136044702539530350221813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92873183600319385751424341 136044702539530350221813)
                ·
                  rfl

theorem cell23_7153545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 11].length) (baseStart_7153545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153545 prefixEnd_7153545 := by exact prefixLift 7153545
  have htrace : WordTrace (prefixWord ++ tailWord_7153545) baseStart_7153545 baseEnd_7153545 := by
    simpa [prefixWord, tailWord_7153545, baseEnd_7153545] using wordTrace_append hprefix tailTrace_7153545
  have hstable : (prefixWord ++ tailWord_7153545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153545).length < 2 ^ (prefixWord ++ tailWord_7153545).sum := by decide
  have hdescent : baseEnd_7153545 < baseStart_7153545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153559 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_7153559 : Nat := 118140960795 + 7153559 * 2 ^ 59
def prefixEnd_7153559 : Nat := 4983230072969 + 3 ^ 40 * 7153559 * 2
def baseEnd_7153559 : Nat := 3673214157296482401213887

theorem tailTrace_7153559 : CollatzResearch.WordTrace tailWord_7153559 prefixEnd_7153559 3673214157296482401213887 := by
  unfold tailWord_7153559
  simp only [CollatzResearch.WordTrace]
  refine ⟨260911731490884948455367731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173941154327256632303578487 260911731490884948455367731)
  ·
    refine ⟨391367597236327422683051597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260911731490884948455367731 391367597236327422683051597)
    ·
      refine ⟨146762848963622783506144349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391367597236327422683051597 146762848963622783506144349)
      ·
        refine ⟨55036068361358543814804131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146762848963622783506144349 55036068361358543814804131)
        ·
          refine ⟨82554102542037815722206197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55036068361358543814804131 82554102542037815722206197)
          ·
            refine ⟨7739447113316045223956831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82554102542037815722206197 7739447113316045223956831)
            ·
              refine ⟨11609170669974067835935247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739447113316045223956831 11609170669974067835935247)
              ·
                refine ⟨17413756004961101753902871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609170669974067835935247 17413756004961101753902871)
                ·
                  refine ⟨26120634007441652630854307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17413756004961101753902871 26120634007441652630854307)
                  ·
                    refine ⟨39180951011162478946281461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26120634007441652630854307 39180951011162478946281461)
                    ·
                      refine ⟨3673214157296482401213887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39180951011162478946281461 3673214157296482401213887)
                      ·
                        rfl

theorem cell23_7153559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_7153559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153559 prefixEnd_7153559 := by exact prefixLift 7153559
  have htrace : WordTrace (prefixWord ++ tailWord_7153559) baseStart_7153559 baseEnd_7153559 := by
    simpa [prefixWord, tailWord_7153559, baseEnd_7153559] using wordTrace_append hprefix tailTrace_7153559
  have hstable : (prefixWord ++ tailWord_7153559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153559).length < 2 ^ (prefixWord ++ tailWord_7153559).sum := by decide
  have hdescent : baseEnd_7153559 < baseStart_7153559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153567 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 1, 1, 3]
def baseStart_7153567 : Nat := 118140960795 + 7153567 * 2 ^ 59
def prefixEnd_7153567 : Nat := 4983230072969 + 3 ^ 40 * 7153567 * 2
def baseEnd_7153567 : Nat := 3673218265141718369913851

theorem tailTrace_7153567 : CollatzResearch.WordTrace tailWord_7153567 prefixEnd_7153567 3673218265141718369913851 := by
  unfold tailWord_7153567
  simp only [CollatzResearch.WordTrace]
  refine ⟨260912023274855965821658955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173941348849903977214439303 260912023274855965821658955)
  ·
    refine ⟨391368034912283948732488433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260912023274855965821658955 391368034912283948732488433)
    ·
      refine ⟨293526026184212961549366325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391368034912283948732488433 293526026184212961549366325)
      ·
        refine ⟨27518064954769965145253093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293526026184212961549366325 27518064954769965145253093)
        ·
          refine ⟨5159637179019368464734955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27518064954769965145253093 5159637179019368464734955)
          ·
            refine ⟨7739455768529052697102433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159637179019368464734955 7739455768529052697102433)
            ·
              refine ⟨5804591826396789522826825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7739455768529052697102433 5804591826396789522826825)
              ·
                refine ⟨4353443869797592142120119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5804591826396789522826825 4353443869797592142120119)
                ·
                  refine ⟨6530165804696388213180179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353443869797592142120119 6530165804696388213180179)
                  ·
                    refine ⟨9795248707044582319770269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530165804696388213180179 9795248707044582319770269)
                    ·
                      refine ⟨3673218265141718369913851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795248707044582319770269 3673218265141718369913851)
                      ·
                        rfl

theorem cell23_7153567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_7153567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153567 prefixEnd_7153567 := by exact prefixLift 7153567
  have htrace : WordTrace (prefixWord ++ tailWord_7153567) baseStart_7153567 baseEnd_7153567 := by
    simpa [prefixWord, tailWord_7153567, baseEnd_7153567] using wordTrace_append hprefix tailTrace_7153567
  have hstable : (prefixWord ++ tailWord_7153567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153567).length < 2 ^ (prefixWord ++ tailWord_7153567).sum := by decide
  have hdescent : baseEnd_7153567 < baseStart_7153567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153589 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_7153589 : Nat := 118140960795 + 7153589 * 2 ^ 59
def prefixEnd_7153589 : Nat := 4983230072969 + 3 ^ 40 * 7153589 * 2
def baseEnd_7153589 : Nat := 3673229561716117283838749

theorem tailTrace_7153589 : CollatzResearch.WordTrace tailWord_7153589 prefixEnd_7153589 3673229561716117283838749 := by
  unfold tailWord_7153589
  simp only [CollatzResearch.WordTrace]
  refine ⟨260912825680776263578959821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173941883787184175719306547 260912825680776263578959821)
  ·
    refine ⟨97842309630291098842109933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260912825680776263578959821 97842309630291098842109933)
    ·
      refine ⟨36690866111359162065791225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97842309630291098842109933 36690866111359162065791225)
      ·
        refine ⟨27518149583519371549343419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36690866111359162065791225 27518149583519371549343419)
        ·
          refine ⟨41277224375279057324015129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27518149583519371549343419 41277224375279057324015129)
          ·
            refine ⟨30957918281459292993011347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41277224375279057324015129 30957918281459292993011347)
            ·
              refine ⟨46436877422188939489517021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30957918281459292993011347 46436877422188939489517021)
              ·
                refine ⟨17413829033320852308568883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46436877422188939489517021 17413829033320852308568883)
                ·
                  refine ⟨26120743549981278462853325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17413829033320852308568883 26120743549981278462853325)
                  ·
                    refine ⟨9795278831242979423569997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26120743549981278462853325 9795278831242979423569997)
                    ·
                      refine ⟨3673229561716117283838749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795278831242979423569997 3673229561716117283838749)
                      ·
                        rfl

theorem cell23_7153589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_7153589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153589 prefixEnd_7153589 := by exact prefixLift 7153589
  have htrace : WordTrace (prefixWord ++ tailWord_7153589) baseStart_7153589 baseEnd_7153589 := by
    simpa [prefixWord, tailWord_7153589, baseEnd_7153589] using wordTrace_append hprefix tailTrace_7153589
  have hstable : (prefixWord ++ tailWord_7153589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153589).length < 2 ^ (prefixWord ++ tailWord_7153589).sum := by decide
  have hdescent : baseEnd_7153589 < baseStart_7153589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153595 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_7153595 : Nat := 118140960795 + 7153595 * 2 ^ 59
def prefixEnd_7153595 : Nat := 4983230072969 + 3 ^ 40 * 7153595 * 2
def baseEnd_7153595 : Nat := 3673232642600044260363721

theorem tailTrace_7153595 : CollatzResearch.WordTrace tailWord_7153595 prefixEnd_7153595 3673232642600044260363721 := by
  unfold tailWord_7153595
  simp only [CollatzResearch.WordTrace]
  refine ⟨260913044518754526603678239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173942029679169684402452159 260913044518754526603678239)
  ·
    refine ⟨391369566778131789905517359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260913044518754526603678239 391369566778131789905517359)
    ·
      refine ⟨587054350167197684858276039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391369566778131789905517359 587054350167197684858276039)
      ·
        refine ⟨880581525250796527287414059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587054350167197684858276039 880581525250796527287414059)
        ·
          refine ⟨1320872287876194790931121089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880581525250796527287414059 1320872287876194790931121089)
          ·
            refine ⟨990654215907146093198340817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320872287876194790931121089 990654215907146093198340817)
            ·
              refine ⟨742990661930359569898755613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990654215907146093198340817 742990661930359569898755613)
              ·
                refine ⟨278621498223884838712033355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742990661930359569898755613 278621498223884838712033355)
                ·
                  refine ⟨417932247335827258068050033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278621498223884838712033355 417932247335827258068050033)
                  ·
                    refine ⟨313449185501870443551037525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417932247335827258068050033 313449185501870443551037525)
                    ·
                      refine ⟨3673232642600044260363721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 313449185501870443551037525 3673232642600044260363721)
                      ·
                        rfl

theorem cell23_7153595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_7153595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153595 prefixEnd_7153595 := by exact prefixLift 7153595
  have htrace : WordTrace (prefixWord ++ tailWord_7153595) baseStart_7153595 baseEnd_7153595 := by
    simpa [prefixWord, tailWord_7153595, baseEnd_7153595] using wordTrace_append hprefix tailTrace_7153595
  have hstable : (prefixWord ++ tailWord_7153595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153595).length < 2 ^ (prefixWord ++ tailWord_7153595).sum := by decide
  have hdescent : baseEnd_7153595 < baseStart_7153595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153596 : List Nat := [2, 2, 2, 5, 1, 1, 3, 7]
def baseStart_7153596 : Nat := 118140960795 + 7153596 * 2 ^ 59
def prefixEnd_7153596 : Nat := 4983230072969 + 3 ^ 40 * 7153596 * 2
def baseEnd_7153596 : Nat := 136045672447433287275971

theorem tailTrace_7153596 : CollatzResearch.WordTrace tailWord_7153596 prefixEnd_7153596 136045672447433287275971 := by
  unfold tailWord_7153596
  simp only [CollatzResearch.WordTrace]
  refine ⟨130456540495875451887232321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173942053994500602516309761 130456540495875451887232321)
  ·
    refine ⟨97842405371906588915424241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130456540495875451887232321 97842405371906588915424241)
    ·
      refine ⟨73381804028929941686568181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97842405371906588915424241 73381804028929941686568181)
      ·
        refine ⟨6879544127712182033115767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73381804028929941686568181 6879544127712182033115767)
        ·
          refine ⟨10319316191568273049673651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879544127712182033115767 10319316191568273049673651)
          ·
            refine ⟨15478974287352409574510477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319316191568273049673651 15478974287352409574510477)
            ·
              refine ⟨5804615357757153590441429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15478974287352409574510477 5804615357757153590441429)
              ·
                refine ⟨136045672447433287275971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5804615357757153590441429 136045672447433287275971)
                ·
                  rfl

theorem cell23_7153596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 7].length) (baseStart_7153596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153596 prefixEnd_7153596 := by exact prefixLift 7153596
  have htrace : WordTrace (prefixWord ++ tailWord_7153596) baseStart_7153596 baseEnd_7153596 := by
    simpa [prefixWord, tailWord_7153596, baseEnd_7153596] using wordTrace_append hprefix tailTrace_7153596
  have hstable : (prefixWord ++ tailWord_7153596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153596).length < 2 ^ (prefixWord ++ tailWord_7153596).sum := by decide
  have hdescent : baseEnd_7153596 < baseStart_7153596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153599 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 3, 3, 2]
def baseStart_7153599 : Nat := 118140960795 + 7153599 * 2 ^ 59
def prefixEnd_7153599 : Nat := 4983230072969 + 3 ^ 40 * 7153599 * 2
def baseEnd_7153599 : Nat := 3673234696522662244713703

theorem tailTrace_7153599 : CollatzResearch.WordTrace tailWord_7153599 prefixEnd_7153599 3673234696522662244713703 := by
  unfold tailWord_7153599
  simp only [CollatzResearch.WordTrace]
  refine ⟨260913190410740035286823851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173942126940493356857882567 260913190410740035286823851)
  ·
    refine ⟨391369785616110052930235777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260913190410740035286823851 391369785616110052930235777)
    ·
      refine ⟨293527339212082539697676833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391369785616110052930235777 293527339212082539697676833)
      ·
        refine ⟨220145504409061904773257625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293527339212082539697676833 220145504409061904773257625)
        ·
          refine ⟨165109128306796428579943219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220145504409061904773257625 165109128306796428579943219)
          ·
            refine ⟨247663692460194642869914829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165109128306796428579943219 247663692460194642869914829)
            ·
              refine ⟨92873884672572991076218061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247663692460194642869914829 92873884672572991076218061)
              ·
                refine ⟨34827706752214871653581773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92873884672572991076218061 34827706752214871653581773)
                ·
                  refine ⟨13060390032080576870093165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34827706752214871653581773 13060390032080576870093165)
                  ·
                    refine ⟨4897646262030216326284937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13060390032080576870093165 4897646262030216326284937)
                    ·
                      refine ⟨3673234696522662244713703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897646262030216326284937 3673234696522662244713703)
                      ·
                        rfl

theorem cell23_7153599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_7153599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153599 prefixEnd_7153599 := by exact prefixLift 7153599
  have htrace : WordTrace (prefixWord ++ tailWord_7153599) baseStart_7153599 baseEnd_7153599 := by
    simpa [prefixWord, tailWord_7153599, baseEnd_7153599] using wordTrace_append hprefix tailTrace_7153599
  have hstable : (prefixWord ++ tailWord_7153599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153599).length < 2 ^ (prefixWord ++ tailWord_7153599).sum := by decide
  have hdescent : baseEnd_7153599 < baseStart_7153599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153632 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_7153632 : Nat := 118140960795 + 7153632 * 2 ^ 59
def prefixEnd_7153632 : Nat := 4983230072969 + 3 ^ 40 * 7153632 * 2
def baseEnd_7153632 : Nat := 3673251641384260615601051

theorem tailTrace_7153632 : CollatzResearch.WordTrace tailWord_7153632 prefixEnd_7153632 3673251641384260615601051 := by
  unfold tailWord_7153632
  simp only [CollatzResearch.WordTrace]
  refine ⟨130457197009810240961387575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173942929346413654615183433 130457197009810240961387575)
  ·
    refine ⟨195685795514715361442081363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130457197009810240961387575 195685795514715361442081363)
    ·
      refine ⟨293528693272073042163122045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195685795514715361442081363 293528693272073042163122045)
      ·
        refine ⟨110073259977027390811170767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293528693272073042163122045 110073259977027390811170767)
        ·
          refine ⟨165109889965541086216756151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110073259977027390811170767 165109889965541086216756151)
          ·
            refine ⟨247664834948311629325134227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165109889965541086216756151 247664834948311629325134227)
            ·
              refine ⟨371497252422467443987701341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247664834948311629325134227 371497252422467443987701341)
              ·
                refine ⟨139311469658425291495388003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371497252422467443987701341 139311469658425291495388003)
                ·
                  refine ⟨208967204487637937243082005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139311469658425291495388003 208967204487637937243082005)
                  ·
                    refine ⟨9795337710358028308269469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208967204487637937243082005 9795337710358028308269469)
                    ·
                      refine ⟨3673251641384260615601051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795337710358028308269469 3673251641384260615601051)
                      ·
                        rfl

theorem cell23_7153632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_7153632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153632 prefixEnd_7153632 := by exact prefixLift 7153632
  have htrace : WordTrace (prefixWord ++ tailWord_7153632) baseStart_7153632 baseEnd_7153632 := by
    simpa [prefixWord, tailWord_7153632, baseEnd_7153632] using wordTrace_append hprefix tailTrace_7153632
  have hstable : (prefixWord ++ tailWord_7153632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153632).length < 2 ^ (prefixWord ++ tailWord_7153632).sum := by decide
  have hdescent : baseEnd_7153632 < baseStart_7153632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153689 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 2, 5, 2]
def baseStart_7153689 : Nat := 118140960795 + 7153689 * 2 ^ 59
def prefixEnd_7153689 : Nat := 4983230072969 + 3 ^ 40 * 7153689 * 2
def baseEnd_7153689 : Nat := 3673280909781566892588289

theorem tailTrace_7153689 : CollatzResearch.WordTrace tailWord_7153689 prefixEnd_7153689 3673280909781566892588289 := by
  unfold tailWord_7153689
  simp only [CollatzResearch.WordTrace]
  refine ⟨260916472980413980657600121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173944315320275987105066747 260916472980413980657600121)
  ·
    refine ⟨195687354735310485493200091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260916472980413980657600121 195687354735310485493200091)
    ·
      refine ⟨293531032102965728239800137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195687354735310485493200091 293531032102965728239800137)
      ·
        refine ⟨220148274077224296179850103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293531032102965728239800137 220148274077224296179850103)
        ·
          refine ⟨330222411115836444269775155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220148274077224296179850103 330222411115836444269775155)
          ·
            refine ⟨495333616673754666404662733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330222411115836444269775155 495333616673754666404662733)
            ·
              refine ⟨185750106252657999901748525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495333616673754666404662733 185750106252657999901748525)
              ·
                refine ⟨69656289844746749963155697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185750106252657999901748525 69656289844746749963155697)
                ·
                  refine ⟨52242217383560062472366773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69656289844746749963155697 52242217383560062472366773)
                  ·
                    refine ⟨4897707879708755856784385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52242217383560062472366773 4897707879708755856784385)
                    ·
                      refine ⟨3673280909781566892588289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897707879708755856784385 3673280909781566892588289)
                      ·
                        rfl

theorem cell23_7153689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_7153689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153689 prefixEnd_7153689 := by exact prefixLift 7153689
  have htrace : WordTrace (prefixWord ++ tailWord_7153689) baseStart_7153689 baseEnd_7153689 := by
    simpa [prefixWord, tailWord_7153689, baseEnd_7153689] using wordTrace_append hprefix tailTrace_7153689
  have hstable : (prefixWord ++ tailWord_7153689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153689).length < 2 ^ (prefixWord ++ tailWord_7153689).sum := by decide
  have hdescent : baseEnd_7153689 < baseStart_7153689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153697 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_7153697 : Nat := 118140960795 + 7153697 * 2 ^ 59
def prefixEnd_7153697 : Nat := 4983230072969 + 3 ^ 40 * 7153697 * 2
def baseEnd_7153697 : Nat := 3673285017626802861288253

theorem tailTrace_7153697 : CollatzResearch.WordTrace tailWord_7153697 prefixEnd_7153697 3673285017626802861288253 := by
  unfold tailWord_7153697
  simp only [CollatzResearch.WordTrace]
  refine ⟨260916764764384998023891345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173944509842923332015927563 260916764764384998023891345)
  ·
    refine ⟨195687573573288748517918509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260916764764384998023891345 195687573573288748517918509)
    ·
      refine ⟨73382840089983280694219441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195687573573288748517918509 73382840089983280694219441)
      ·
        refine ⟨55037130067487460520664581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73382840089983280694219441 55037130067487460520664581)
        ·
          refine ⟨10319461887653898847624609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55037130067487460520664581 10319461887653898847624609)
          ·
            refine ⟨7739596415740424135718457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10319461887653898847624609 7739596415740424135718457)
            ·
              refine ⟨5804697311805318101788843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7739596415740424135718457 5804697311805318101788843)
              ·
                refine ⟨8707045967707977152683265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804697311805318101788843 8707045967707977152683265)
                ·
                  refine ⟨6530284475780982864512449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707045967707977152683265 6530284475780982864512449)
                  ·
                    refine ⟨4897713356835737148384337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6530284475780982864512449 4897713356835737148384337)
                    ·
                      refine ⟨3673285017626802861288253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897713356835737148384337 3673285017626802861288253)
                      ·
                        rfl

theorem cell23_7153697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_7153697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153697 prefixEnd_7153697 := by exact prefixLift 7153697
  have htrace : WordTrace (prefixWord ++ tailWord_7153697) baseStart_7153697 baseEnd_7153697 := by
    simpa [prefixWord, tailWord_7153697, baseEnd_7153697] using wordTrace_append hprefix tailTrace_7153697
  have hstable : (prefixWord ++ tailWord_7153697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153697).length < 2 ^ (prefixWord ++ tailWord_7153697).sum := by decide
  have hdescent : baseEnd_7153697 < baseStart_7153697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153719 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_7153719 : Nat := 118140960795 + 7153719 * 2 ^ 59
def prefixEnd_7153719 : Nat := 4983230072969 + 3 ^ 40 * 7153719 * 2
def baseEnd_7153719 : Nat := 3673296314201201775213151

theorem tailTrace_7153719 : CollatzResearch.WordTrace tailWord_7153719 prefixEnd_7153719 3673296314201201775213151 := by
  unfold tailWord_7153719
  simp only [CollatzResearch.WordTrace]
  refine ⟨260917567170305295781192211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173945044780203530520794807 260917567170305295781192211)
  ·
    refine ⟨391376350755457943671788317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260917567170305295781192211 391376350755457943671788317)
    ·
      refine ⟨146766131533296728876920619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391376350755457943671788317 146766131533296728876920619)
      ·
        refine ⟨220149197299945093315380929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146766131533296728876920619 220149197299945093315380929)
        ·
          refine ⟨165111897974958819986535697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220149197299945093315380929 165111897974958819986535697)
          ·
            refine ⟨123833923481219114989901773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165111897974958819986535697 123833923481219114989901773)
            ·
              refine ⟨46437721305457168121213165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123833923481219114989901773 46437721305457168121213165)
              ·
                refine ⟨17414145489546438045454937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46437721305457168121213165 17414145489546438045454937)
                ·
                  refine ⟨13060609117159828534091203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17414145489546438045454937 13060609117159828534091203)
                  ·
                    refine ⟨19590913675739742801136805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13060609117159828534091203 19590913675739742801136805)
                    ·
                      refine ⟨3673296314201201775213151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19590913675739742801136805 3673296314201201775213151)
                      ·
                        rfl

theorem cell23_7153719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_7153719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153719 prefixEnd_7153719 := by exact prefixLift 7153719
  have htrace : WordTrace (prefixWord ++ tailWord_7153719) baseStart_7153719 baseEnd_7153719 := by
    simpa [prefixWord, tailWord_7153719, baseEnd_7153719] using wordTrace_append hprefix tailTrace_7153719
  have hstable : (prefixWord ++ tailWord_7153719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153719).length < 2 ^ (prefixWord ++ tailWord_7153719).sum := by decide
  have hdescent : baseEnd_7153719 < baseStart_7153719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153770 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7153770 : Nat := 118140960795 + 7153770 * 2 ^ 59
def prefixEnd_7153770 : Nat := 4983230072969 + 3 ^ 40 * 7153770 * 2
def baseEnd_7153770 : Nat := 3673322501714581075675417

theorem tailTrace_7153770 : CollatzResearch.WordTrace tailWord_7153770 prefixEnd_7153770 3673322501714581075675417 := by
  unfold tailWord_7153770
  simp only [CollatzResearch.WordTrace]
  refine ⟨65229856823280132872824691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173946284862080354327532509 65229856823280132872824691)
  ·
    refine ⟨97844785234920199309237037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65229856823280132872824691 97844785234920199309237037)
    ·
      refine ⟨36691794463095074740963889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97844785234920199309237037 36691794463095074740963889)
      ·
        refine ⟨27518845847321306055722917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36691794463095074740963889 27518845847321306055722917)
        ·
          refine ⟨5159783596372744885448047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27518845847321306055722917 5159783596372744885448047)
          ·
            refine ⟨7739675394559117328172071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159783596372744885448047 7739675394559117328172071)
            ·
              refine ⟨11609513091838675992258107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739675394559117328172071 11609513091838675992258107)
              ·
                refine ⟨17414269637758013988387161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609513091838675992258107 17414269637758013988387161)
                ·
                  refine ⟨13060702228318510491290371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17414269637758013988387161 13060702228318510491290371)
                  ·
                    refine ⟨19591053342477765736935557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13060702228318510491290371 19591053342477765736935557)
                    ·
                      refine ⟨3673322501714581075675417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19591053342477765736935557 3673322501714581075675417)
                      ·
                        rfl

theorem cell23_7153770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7153770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153770 prefixEnd_7153770 := by exact prefixLift 7153770
  have htrace : WordTrace (prefixWord ++ tailWord_7153770) baseStart_7153770 baseEnd_7153770 := by
    simpa [prefixWord, tailWord_7153770, baseEnd_7153770] using wordTrace_append hprefix tailTrace_7153770
  have hstable : (prefixWord ++ tailWord_7153770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153770).length < 2 ^ (prefixWord ++ tailWord_7153770).sum := by decide
  have hdescent : baseEnd_7153770 < baseStart_7153770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153793 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 6]
def baseStart_7153793 : Nat := 118140960795 + 7153793 * 2 ^ 59
def prefixEnd_7153793 : Nat := 4983230072969 + 3 ^ 40 * 7153793 * 2
def baseEnd_7153793 : Nat := 408148256863292720631979

theorem tailTrace_7153793 : CollatzResearch.WordTrace tailWord_7153793 prefixEnd_7153793 408148256863292720631979 := by
  unfold tailWord_7153793
  simp only [CollatzResearch.WordTrace]
  refine ⟨260920266172037206419386033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173946844114691470946257355 260920266172037206419386033)
  ·
    refine ⟨195690199629027904814539525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260920266172037206419386033 195690199629027904814539525)
    ·
      refine ⟨36691912430442732152726161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195690199629027904814539525 36691912430442732152726161)
      ·
        refine ⟨27518934322832049114544621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36691912430442732152726161 27518934322832049114544621)
        ·
          refine ⟨10319600371062018417954233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27518934322832049114544621 10319600371062018417954233)
          ·
            refine ⟨7739700278296513813465675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10319600371062018417954233 7739700278296513813465675)
            ·
              refine ⟨11609550417444770720198513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739700278296513813465675 11609550417444770720198513)
              ·
                refine ⟨8707162813083578040148885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609550417444770720198513 8707162813083578040148885)
                ·
                  refine ⟨408148256863292720631979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8707162813083578040148885 408148256863292720631979)
                  ·
                    rfl

theorem cell23_7153793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 6].length) (baseStart_7153793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153793 prefixEnd_7153793 := by exact prefixLift 7153793
  have htrace : WordTrace (prefixWord ++ tailWord_7153793) baseStart_7153793 baseEnd_7153793 := by
    simpa [prefixWord, tailWord_7153793, baseEnd_7153793] using wordTrace_append hprefix tailTrace_7153793
  have hstable : (prefixWord ++ tailWord_7153793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153793).length < 2 ^ (prefixWord ++ tailWord_7153793).sum := by decide
  have hdescent : baseEnd_7153793 < baseStart_7153793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153823 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 1, 5]
def baseStart_7153823 : Nat := 118140960795 + 7153823 * 2 ^ 59
def prefixEnd_7153823 : Nat := 4983230072969 + 3 ^ 40 * 7153823 * 2
def baseEnd_7153823 : Nat := 1224449905396423122770891

theorem tailTrace_7153823 : CollatzResearch.WordTrace tailWord_7153823 prefixEnd_7153823 1224449905396423122770891 := by
  unfold tailWord_7153823
  simp only [CollatzResearch.WordTrace]
  refine ⟨260921360361928521542978123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173947573574619014361985415 260921360361928521542978123)
  ·
    refine ⟨391382040542892782314467185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260921360361928521542978123 391382040542892782314467185)
    ·
      refine ⟨293536530407169586735850389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391382040542892782314467185 293536530407169586735850389)
      ·
        refine ⟨13759524862836074378242987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 293536530407169586735850389 13759524862836074378242987)
        ·
          refine ⟨20639287294254111567364481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13759524862836074378242987 20639287294254111567364481)
          ·
            refine ⟨15479465470690583675523361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20639287294254111567364481 15479465470690583675523361)
            ·
              refine ⟨11609599103017937756642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15479465470690583675523361 11609599103017937756642521)
              ·
                refine ⟨8707199327263453317481891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609599103017937756642521 8707199327263453317481891)
                ·
                  refine ⟨13060798990895179976222837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707199327263453317481891 13060798990895179976222837)
                  ·
                    refine ⟨1224449905396423122770891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13060798990895179976222837 1224449905396423122770891)
                    ·
                      rfl

theorem cell23_7153823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_7153823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153823 prefixEnd_7153823 := by exact prefixLift 7153823
  have htrace : WordTrace (prefixWord ++ tailWord_7153823) baseStart_7153823 baseEnd_7153823 := by
    simpa [prefixWord, tailWord_7153823, baseEnd_7153823] using wordTrace_append hprefix tailTrace_7153823
  have hstable : (prefixWord ++ tailWord_7153823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153823).length < 2 ^ (prefixWord ++ tailWord_7153823).sum := by decide
  have hdescent : baseEnd_7153823 < baseStart_7153823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153829 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_7153829 : Nat := 118140960795 + 7153829 * 2 ^ 59
def prefixEnd_7153829 : Nat := 4983230072969 + 3 ^ 40 * 7153829 * 2
def baseEnd_7153829 : Nat := 3673352797073196344837645

theorem tailTrace_7153829 : CollatzResearch.WordTrace tailWord_7153829 prefixEnd_7153829 3673352797073196344837645 := by
  unfold tailWord_7153829
  simp only [CollatzResearch.WordTrace]
  refine ⟨260921579199906784567696541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173947719466604523045131027 260921579199906784567696541)
  ·
    refine ⟨97845592199965044212886203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260921579199906784567696541 97845592199965044212886203)
    ·
      refine ⟨146768388299947566319329305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97845592199965044212886203 146768388299947566319329305)
      ·
        refine ⟨110076291224960674739496979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146768388299947566319329305 110076291224960674739496979)
        ·
          refine ⟨165114436837441012109245469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110076291224960674739496979 165114436837441012109245469)
          ·
            refine ⟨61917913814040379540967051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165114436837441012109245469 61917913814040379540967051)
            ·
              refine ⟨92876870721060569311450577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61917913814040379540967051 92876870721060569311450577)
              ·
                refine ⟨69657653040795426983587933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92876870721060569311450577 69657653040795426983587933)
                ·
                  refine ⟨26121619890298285118845475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69657653040795426983587933 26121619890298285118845475)
                  ·
                    refine ⟨39182429835447427678268213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26121619890298285118845475 39182429835447427678268213)
                    ·
                      refine ⟨3673352797073196344837645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39182429835447427678268213 3673352797073196344837645)
                      ·
                        rfl

theorem cell23_7153829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_7153829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153829 prefixEnd_7153829 := by exact prefixLift 7153829
  have htrace : WordTrace (prefixWord ++ tailWord_7153829) baseStart_7153829 baseEnd_7153829 := by
    simpa [prefixWord, tailWord_7153829, baseEnd_7153829] using wordTrace_append hprefix tailTrace_7153829
  have hstable : (prefixWord ++ tailWord_7153829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153829).length < 2 ^ (prefixWord ++ tailWord_7153829).sum := by decide
  have hdescent : baseEnd_7153829 < baseStart_7153829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153837 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7153837 : Nat := 118140960795 + 7153837 * 2 ^ 59
def prefixEnd_7153837 : Nat := 4983230072969 + 3 ^ 40 * 7153837 * 2
def baseEnd_7153837 : Nat := 3673356904918432313537609

theorem tailTrace_7153837 : CollatzResearch.WordTrace tailWord_7153837 prefixEnd_7153837 3673356904918432313537609 := by
  unfold tailWord_7153837
  simp only [CollatzResearch.WordTrace]
  refine ⟨260921870983877801933987765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173947913989251867955991843 260921870983877801933987765)
  ·
    refine ⟨24461425404738543931311353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260921870983877801933987765 24461425404738543931311353)
    ·
      refine ⟨18346069053553907948483515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24461425404738543931311353 18346069053553907948483515)
      ·
        refine ⟨27519103580330861922725273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18346069053553907948483515 27519103580330861922725273)
        ·
          refine ⟨20639327685248146442043955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27519103580330861922725273 20639327685248146442043955)
          ·
            refine ⟨30958991527872219663065933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20639327685248146442043955 30958991527872219663065933)
            ·
              refine ⟨11609621822952082373649725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30958991527872219663065933 11609621822952082373649725)
              ·
                refine ⟨4353608183607030890118647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11609621822952082373649725 4353608183607030890118647)
                ·
                  refine ⟨6530412275410546335177971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353608183607030890118647 6530412275410546335177971)
                  ·
                    refine ⟨9795618413115819502766957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530412275410546335177971 9795618413115819502766957)
                    ·
                      refine ⟨3673356904918432313537609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795618413115819502766957 3673356904918432313537609)
                      ·
                        rfl

theorem cell23_7153837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7153837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153837 prefixEnd_7153837 := by exact prefixLift 7153837
  have htrace : WordTrace (prefixWord ++ tailWord_7153837) baseStart_7153837 baseEnd_7153837 := by
    simpa [prefixWord, tailWord_7153837, baseEnd_7153837] using wordTrace_append hprefix tailTrace_7153837
  have hstable : (prefixWord ++ tailWord_7153837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153837).length < 2 ^ (prefixWord ++ tailWord_7153837).sum := by decide
  have hdescent : baseEnd_7153837 < baseStart_7153837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153839 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_7153839 : Nat := 118140960795 + 7153839 * 2 ^ 59
def prefixEnd_7153839 : Nat := 4983230072969 + 3 ^ 40 * 7153839 * 2
def baseEnd_7153839 : Nat := 3673357931879741305712599

theorem tailTrace_7153839 : CollatzResearch.WordTrace tailWord_7153839 prefixEnd_7153839 3673357931879741305712599 := by
  unfold tailWord_7153839
  simp only [CollatzResearch.WordTrace]
  refine ⟨260921943929870556275560571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173947962619913704183707047 260921943929870556275560571)
  ·
    refine ⟨391382915894805834413340857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260921943929870556275560571 391382915894805834413340857)
    ·
      refine ⟨293537186921104375810005643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391382915894805834413340857 293537186921104375810005643)
      ·
        refine ⟨440305780381656563715008465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293537186921104375810005643 440305780381656563715008465)
        ·
          refine ⟨330229335286242422786256349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440305780381656563715008465 330229335286242422786256349)
          ·
            refine ⟨123836000732340908544846131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330229335286242422786256349 123836000732340908544846131)
            ·
              refine ⟨185754001098511362817269197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123836000732340908544846131 185754001098511362817269197)
              ·
                refine ⟨69657750411941761056475949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185754001098511362817269197 69657750411941761056475949)
                ·
                  refine ⟨26121656404478160396178481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69657750411941761056475949 26121656404478160396178481)
                  ·
                    refine ⟨19591242303358620297133861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26121656404478160396178481 19591242303358620297133861)
                    ·
                      refine ⟨3673357931879741305712599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19591242303358620297133861 3673357931879741305712599)
                      ·
                        rfl

theorem cell23_7153839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_7153839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153839 prefixEnd_7153839 := by exact prefixLift 7153839
  have htrace : WordTrace (prefixWord ++ tailWord_7153839) baseStart_7153839 baseEnd_7153839 := by
    simpa [prefixWord, tailWord_7153839, baseEnd_7153839] using wordTrace_append hprefix tailTrace_7153839
  have hstable : (prefixWord ++ tailWord_7153839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153839).length < 2 ^ (prefixWord ++ tailWord_7153839).sum := by decide
  have hdescent : baseEnd_7153839 < baseStart_7153839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153854 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_7153854 : Nat := 118140960795 + 7153854 * 2 ^ 59
def prefixEnd_7153854 : Nat := 4983230072969 + 3 ^ 40 * 7153854 * 2
def baseEnd_7153854 : Nat := 3673365634089558747025031

theorem tailTrace_7153854 : CollatzResearch.WordTrace tailWord_7153854 prefixEnd_7153854 3673365634089558747025031 := by
  unfold tailWord_7153854
  simp only [CollatzResearch.WordTrace]
  refine ⟨32615311378102026729669577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173948327349877475891571077 32615311378102026729669577)
  ·
    refine ⟨24461483533576520047252183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32615311378102026729669577 24461483533576520047252183)
    ·
      refine ⟨36692225300364780070878275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24461483533576520047252183 36692225300364780070878275)
      ·
        refine ⟨55038337950547170106317413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36692225300364780070878275 55038337950547170106317413)
        ·
          refine ⟨10319688365727594394934515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55038337950547170106317413 10319688365727594394934515)
          ·
            refine ⟨15479532548591391592401773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319688365727594394934515 15479532548591391592401773)
            ·
              refine ⟨5804824705721771847150665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15479532548591391592401773 5804824705721771847150665)
              ·
                refine ⟨4353618529291328885362999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5804824705721771847150665 4353618529291328885362999)
                ·
                  refine ⟨6530427793936993328044499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353618529291328885362999 6530427793936993328044499)
                  ·
                    refine ⟨9795641690905489992066749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530427793936993328044499 9795641690905489992066749)
                    ·
                      refine ⟨3673365634089558747025031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795641690905489992066749 3673365634089558747025031)
                      ·
                        rfl

theorem cell23_7153854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_7153854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153854 prefixEnd_7153854 := by exact prefixLift 7153854
  have htrace : WordTrace (prefixWord ++ tailWord_7153854) baseStart_7153854 baseEnd_7153854 := by
    simpa [prefixWord, tailWord_7153854, baseEnd_7153854] using wordTrace_append hprefix tailTrace_7153854
  have hstable : (prefixWord ++ tailWord_7153854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153854).length < 2 ^ (prefixWord ++ tailWord_7153854).sum := by decide
  have hdescent : baseEnd_7153854 < baseStart_7153854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153870 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_7153870 : Nat := 118140960795 + 7153870 * 2 ^ 59
def prefixEnd_7153870 : Nat := 4983230072969 + 3 ^ 40 * 7153870 * 2
def baseEnd_7153870 : Nat := 1224457949926676894808319

theorem tailTrace_7153870 : CollatzResearch.WordTrace tailWord_7153870 prefixEnd_7153870 1224457949926676894808319 := by
  unfold tailWord_7153870
  simp only [CollatzResearch.WordTrace]
  refine ⟨32615384324094781071242383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173948716395172165713292709 32615384324094781071242383)
  ·
    refine ⟨48923076486142171606863575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32615384324094781071242383 48923076486142171606863575)
    ·
      refine ⟨73384614729213257410295363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48923076486142171606863575 73384614729213257410295363)
      ·
        refine ⟨110076922093819886115443045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73384614729213257410295363 110076922093819886115443045)
        ·
          refine ⟨20639422892591228646645571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110076922093819886115443045 20639422892591228646645571)
          ·
            refine ⟨30959134338886842969968357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20639422892591228646645571 30959134338886842969968357)
            ·
              refine ⟨5804837688541283056869067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30959134338886842969968357 5804837688541283056869067)
              ·
                refine ⟨8707256532811924585303601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804837688541283056869067 8707256532811924585303601)
                ·
                  refine ⟨6530442399608943438977701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707256532811924585303601 6530442399608943438977701)
                  ·
                    refine ⟨1224457949926676894808319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530442399608943438977701 1224457949926676894808319)
                    ·
                      rfl

theorem cell23_7153870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_7153870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153870 prefixEnd_7153870 := by exact prefixLift 7153870
  have htrace : WordTrace (prefixWord ++ tailWord_7153870) baseStart_7153870 baseEnd_7153870 := by
    simpa [prefixWord, tailWord_7153870, baseEnd_7153870] using wordTrace_append hprefix tailTrace_7153870
  have hstable : (prefixWord ++ tailWord_7153870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153870).length < 2 ^ (prefixWord ++ tailWord_7153870).sum := by decide
  have hdescent : baseEnd_7153870 < baseStart_7153870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153877 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7153877 : Nat := 118140960795 + 7153877 * 2 ^ 59
def prefixEnd_7153877 : Nat := 4983230072969 + 3 ^ 40 * 7153877 * 2
def baseEnd_7153877 : Nat := 3673377444144612157037425

theorem tailTrace_7153877 : CollatzResearch.WordTrace tailWord_7153877 prefixEnd_7153877 3673377444144612157037425 := by
  unfold tailWord_7153877
  simp only [CollatzResearch.WordTrace]
  refine ⟨260923329903732888765443885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173948886602488592510295923 260923329903732888765443885)
  ·
    refine ⟨97846248713899833287041457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260923329903732888765443885 97846248713899833287041457)
    ·
      refine ⟨73384686535424874965281093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97846248713899833287041457 73384686535424874965281093)
      ·
        refine ⟨13759628725392164055990205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73384686535424874965281093 13759628725392164055990205)
        ·
          refine ⟨5159860772022061520996327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13759628725392164055990205 5159860772022061520996327)
          ·
            refine ⟨7739791158033092281494491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159860772022061520996327 7739791158033092281494491)
            ·
              refine ⟨11609686737049638422241737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739791158033092281494491 11609686737049638422241737)
              ·
                refine ⟨8707265052787228816681303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609686737049638422241737 8707265052787228816681303)
                ·
                  refine ⟨13060897579180843225021955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707265052787228816681303 13060897579180843225021955)
                  ·
                    refine ⟨19591346368771264837532933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13060897579180843225021955 19591346368771264837532933)
                    ·
                      refine ⟨3673377444144612157037425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19591346368771264837532933 3673377444144612157037425)
                      ·
                        rfl

theorem cell23_7153877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7153877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153877 prefixEnd_7153877 := by exact prefixLift 7153877
  have htrace : WordTrace (prefixWord ++ tailWord_7153877) baseStart_7153877 baseEnd_7153877 := by
    simpa [prefixWord, tailWord_7153877, baseEnd_7153877] using wordTrace_append hprefix tailTrace_7153877
  have hstable : (prefixWord ++ tailWord_7153877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153877).length < 2 ^ (prefixWord ++ tailWord_7153877).sum := by decide
  have hdescent : baseEnd_7153877 < baseStart_7153877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153880 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_7153880 : Nat := 118140960795 + 7153880 * 2 ^ 59
def prefixEnd_7153880 : Nat := 4983230072969 + 3 ^ 40 * 7153880 * 2
def baseEnd_7153880 : Nat := 3673378984586575645299911

theorem tailTrace_7153880 : CollatzResearch.WordTrace tailWord_7153880 prefixEnd_7153880 3673378984586575645299911 := by
  unfold tailWord_7153880
  simp only [CollatzResearch.WordTrace]
  refine ⟨130461719661361010138901547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173948959548481346851868729 130461719661361010138901547)
  ·
    refine ⟨195692579492041515208352321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130461719661361010138901547 195692579492041515208352321)
    ·
      refine ⟨146769434619031136406264241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195692579492041515208352321 146769434619031136406264241)
      ·
        refine ⟨110077075964273352304698181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146769434619031136406264241 110077075964273352304698181)
        ·
          refine ⟨20639451743301253557130909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110077075964273352304698181 20639451743301253557130909)
          ·
            refine ⟨7739794403737970083924091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20639451743301253557130909 7739794403737970083924091)
            ·
              refine ⟨11609691605606955125886137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739794403737970083924091 11609691605606955125886137)
              ·
                refine ⟨8707268704205216344414603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609691605606955125886137 8707268704205216344414603)
                ·
                  refine ⟨13060903056307824516621905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707268704205216344414603 13060903056307824516621905)
                  ·
                    refine ⟨9795677292230868387466429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13060903056307824516621905 9795677292230868387466429)
                    ·
                      refine ⟨3673378984586575645299911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795677292230868387466429 3673378984586575645299911)
                      ·
                        rfl

theorem cell23_7153880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_7153880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153880 prefixEnd_7153880 := by exact prefixLift 7153880
  have htrace : WordTrace (prefixWord ++ tailWord_7153880) baseStart_7153880 baseEnd_7153880 := by
    simpa [prefixWord, tailWord_7153880, baseEnd_7153880] using wordTrace_append hprefix tailTrace_7153880
  have hstable : (prefixWord ++ tailWord_7153880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153880).length < 2 ^ (prefixWord ++ tailWord_7153880).sum := by decide
  have hdescent : baseEnd_7153880 < baseStart_7153880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153893 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_7153893 : Nat := 118140960795 + 7153893 * 2 ^ 59
def prefixEnd_7153893 : Nat := 4983230072969 + 3 ^ 40 * 7153893 * 2
def baseEnd_7153893 : Nat := 3673385659835084094437351

theorem tailTrace_7153893 : CollatzResearch.WordTrace tailWord_7153893 prefixEnd_7153893 3673385659835084094437351 := by
  unfold tailWord_7153893
  simp only [CollatzResearch.WordTrace]
  refine ⟨260923913471674923498026333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173949275647783282332017555 260923913471674923498026333)
  ·
    refine ⟨97846467551878096311759875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260923913471674923498026333 97846467551878096311759875)
    ·
      refine ⟨146769701327817144467639813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97846467551878096311759875 146769701327817144467639813)
      ·
        refine ⟨27519318998965714587682465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146769701327817144467639813 27519318998965714587682465)
        ·
          refine ⟨20639489249224285940761849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27519318998965714587682465 20639489249224285940761849)
          ·
            refine ⟨15479616936918214455571387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20639489249224285940761849 15479616936918214455571387)
            ·
              refine ⟨23219425405377321683357081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15479616936918214455571387 23219425405377321683357081)
              ·
                refine ⟨17414569054032991262517811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23219425405377321683357081 17414569054032991262517811)
                ·
                  refine ⟨26121853581049486893776717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17414569054032991262517811 26121853581049486893776717)
                  ·
                    refine ⟨9795695092893557585166269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26121853581049486893776717 9795695092893557585166269)
                    ·
                      refine ⟨3673385659835084094437351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795695092893557585166269 3673385659835084094437351)
                      ·
                        rfl

theorem cell23_7153893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_7153893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153893 prefixEnd_7153893 := by exact prefixLift 7153893
  have htrace : WordTrace (prefixWord ++ tailWord_7153893) baseStart_7153893 baseEnd_7153893 := by
    simpa [prefixWord, tailWord_7153893, baseEnd_7153893] using wordTrace_append hprefix tailTrace_7153893
  have hstable : (prefixWord ++ tailWord_7153893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153893).length < 2 ^ (prefixWord ++ tailWord_7153893).sum := by decide
  have hdescent : baseEnd_7153893 < baseStart_7153893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153910 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_7153910 : Nat := 118140960795 + 7153910 * 2 ^ 59
def prefixEnd_7153910 : Nat := 4983230072969 + 3 ^ 40 * 7153910 * 2
def baseEnd_7153910 : Nat := 3673394389006210527924773

theorem tailTrace_7153910 : CollatzResearch.WordTrace tailWord_7153910 prefixEnd_7153910 3673394389006210527924773 := by
  unfold tailWord_7153910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16307783344538333462587199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173949689008408890267596789 16307783344538333462587199)
  ·
    refine ⟨24461675016807500193880799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16307783344538333462587199 24461675016807500193880799)
    ·
      refine ⟨36692512525211250290821199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24461675016807500193880799 36692512525211250290821199)
      ·
        refine ⟨55038768787816875436231799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36692512525211250290821199 55038768787816875436231799)
        ·
          refine ⟨82558153181725313154347699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55038768787816875436231799 82558153181725313154347699)
          ·
            refine ⟨123837229772587969731521549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82558153181725313154347699 123837229772587969731521549)
            ·
              refine ⟨46438961164720488649320581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123837229772587969731521549 46438961164720488649320581)
              ·
                refine ⟨8707305218385091621747609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46438961164720488649320581 8707305218385091621747609)
                ·
                  refine ⟨6530478913788818716310707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707305218385091621747609 6530478913788818716310707)
                  ·
                    refine ⟨9795718370683228074466061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530478913788818716310707 9795718370683228074466061)
                    ·
                      refine ⟨3673394389006210527924773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795718370683228074466061 3673394389006210527924773)
                      ·
                        rfl

theorem cell23_7153910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_7153910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153910 prefixEnd_7153910 := by exact prefixLift 7153910
  have htrace : WordTrace (prefixWord ++ tailWord_7153910) baseStart_7153910 baseEnd_7153910 := by
    simpa [prefixWord, tailWord_7153910, baseEnd_7153910] using wordTrace_append hprefix tailTrace_7153910
  have hstable : (prefixWord ++ tailWord_7153910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153910).length < 2 ^ (prefixWord ++ tailWord_7153910).sum := by decide
  have hdescent : baseEnd_7153910 < baseStart_7153910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153916 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_7153916 : Nat := 118140960795 + 7153916 * 2 ^ 59
def prefixEnd_7153916 : Nat := 4983230072969 + 3 ^ 40 * 7153916 * 2
def baseEnd_7153916 : Nat := 3673397469890137504449745

theorem tailTrace_7153916 : CollatzResearch.WordTrace tailWord_7153916 prefixEnd_7153916 3673397469890137504449745 := by
  unfold tailWord_7153916
  simp only [CollatzResearch.WordTrace]
  refine ⟨130462376175295799213056801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173949834900394398950742401 130462376175295799213056801)
  ·
    refine ⟨97846782131471849409792601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130462376175295799213056801 97846782131471849409792601)
    ·
      refine ⟨73385086598603887057344451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97846782131471849409792601 73385086598603887057344451)
      ·
        refine ⟨110077629897905830586016677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73385086598603887057344451 110077629897905830586016677)
        ·
          refine ⟨20639555605857343234878127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110077629897905830586016677 20639555605857343234878127)
          ·
            refine ⟨30959333408786014852317191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20639555605857343234878127 30959333408786014852317191)
            ·
              refine ⟨46439000113179022278475787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30959333408786014852317191 46439000113179022278475787)
              ·
                refine ⟨69658500169768533417713681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46439000113179022278475787 69658500169768533417713681)
                ·
                  refine ⟨52243875127326400063285261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69658500169768533417713681 52243875127326400063285261)
                  ·
                    refine ⟨19591453172747400023731973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52243875127326400063285261 19591453172747400023731973)
                    ·
                      refine ⟨3673397469890137504449745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19591453172747400023731973 3673397469890137504449745)
                      ·
                        rfl

theorem cell23_7153916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_7153916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153916 prefixEnd_7153916 := by exact prefixLift 7153916
  have htrace : WordTrace (prefixWord ++ tailWord_7153916) baseStart_7153916 baseEnd_7153916 := by
    simpa [prefixWord, tailWord_7153916, baseEnd_7153916] using wordTrace_append hprefix tailTrace_7153916
  have hstable : (prefixWord ++ tailWord_7153916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153916).length < 2 ^ (prefixWord ++ tailWord_7153916).sum := by decide
  have hdescent : baseEnd_7153916 < baseStart_7153916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153954 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_7153954 : Nat := 118140960795 + 7153954 * 2 ^ 59
def prefixEnd_7153954 : Nat := 4983230072969 + 3 ^ 40 * 7153954 * 2
def baseEnd_7153954 : Nat := 3673416982155008355774571

theorem tailTrace_7153954 : CollatzResearch.WordTrace tailWord_7153954 prefixEnd_7153954 3673416982155008355774571 := by
  unfold tailWord_7153954
  simp only [CollatzResearch.WordTrace]
  refine ⟨65231534581113482728999229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173950758882969287277331277 65231534581113482728999229)
  ·
    refine ⟨24461825467917556023374711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65231534581113482728999229 24461825467917556023374711)
    ·
      refine ⟨36692738201876334035062067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24461825467917556023374711 36692738201876334035062067)
      ·
        refine ⟨55039107302814501052593101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36692738201876334035062067 55039107302814501052593101)
        ·
          refine ⟨20639665238555437894722413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55039107302814501052593101 20639665238555437894722413)
          ·
            refine ⟨7739874464458289210520905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20639665238555437894722413 7739874464458289210520905)
            ·
              refine ⟨5804905848343716907890679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7739874464458289210520905 5804905848343716907890679)
              ·
                refine ⟨8707358772515575361836019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804905848343716907890679 8707358772515575361836019)
                ·
                  refine ⟨13061038158773363042754029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707358772515575361836019 13061038158773363042754029)
                  ·
                    refine ⟨4897889309540011141032761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13061038158773363042754029 4897889309540011141032761)
                    ·
                      refine ⟨3673416982155008355774571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4897889309540011141032761 3673416982155008355774571)
                      ·
                        rfl

theorem cell23_7153954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_7153954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153954 prefixEnd_7153954 := by exact prefixLift 7153954
  have htrace : WordTrace (prefixWord ++ tailWord_7153954) baseStart_7153954 baseEnd_7153954 := by
    simpa [prefixWord, tailWord_7153954, baseEnd_7153954] using wordTrace_append hprefix tailTrace_7153954
  have hstable : (prefixWord ++ tailWord_7153954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153954).length < 2 ^ (prefixWord ++ tailWord_7153954).sum := by decide
  have hdescent : baseEnd_7153954 < baseStart_7153954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153973 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 5]
def baseStart_7153973 : Nat := 118140960795 + 7153973 * 2 ^ 59
def prefixEnd_7153973 : Nat := 4983230072969 + 3 ^ 40 * 7153973 * 2
def baseEnd_7153973 : Nat := 408158526476382642381887

theorem tailTrace_7153973 : CollatzResearch.WordTrace tailWord_7153973 prefixEnd_7153973 408158526476382642381887 := by
  unfold tailWord_7153973
  simp only [CollatzResearch.WordTrace]
  refine ⟨260926831311385097160938573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173951220874256731440625715 260926831311385097160938573)
  ·
    refine ⟨97847561741769411435351965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260926831311385097160938573 97847561741769411435351965)
    ·
      refine ⟨36692835653163529288256987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97847561741769411435351965 36692835653163529288256987)
      ·
        refine ⟨55039253479745293932385481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36692835653163529288256987 55039253479745293932385481)
        ·
          refine ⟨41279440109808970449289111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55039253479745293932385481 41279440109808970449289111)
          ·
            refine ⟨61919160164713455673933667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41279440109808970449289111 61919160164713455673933667)
            ·
              refine ⟨92878740247070183510900501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61919160164713455673933667 92878740247070183510900501)
              ·
                refine ⟨4353690949081414852073461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92878740247070183510900501 4353690949081414852073461)
                ·
                  refine ⟨408158526476382642381887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4353690949081414852073461 408158526476382642381887)
                  ·
                    rfl

theorem cell23_7153973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_7153973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7153973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7153973 prefixEnd_7153973 := by exact prefixLift 7153973
  have htrace : WordTrace (prefixWord ++ tailWord_7153973) baseStart_7153973 baseEnd_7153973 := by
    simpa [prefixWord, tailWord_7153973, baseEnd_7153973] using wordTrace_append hprefix tailTrace_7153973
  have hstable : (prefixWord ++ tailWord_7153973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153973).length < 2 ^ (prefixWord ++ tailWord_7153973).sum := by decide
  have hdescent : baseEnd_7153973 < baseStart_7153973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154023 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_7154023 : Nat := 118140960795 + 7154023 * 2 ^ 59
def prefixEnd_7154023 : Nat := 4983230072969 + 3 ^ 40 * 7154023 * 2
def baseEnd_7154023 : Nat := 3673452412320168585811753

theorem tailTrace_7154023 : CollatzResearch.WordTrace tailWord_7154023 prefixEnd_7154023 3673452412320168585811753 := by
  unfold tailWord_7154023
  simp only [CollatzResearch.WordTrace]
  refine ⟨260928654961203955700258723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173952436640802637133505815 260928654961203955700258723)
  ·
    refine ⟨391392982441805933550388085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260928654961203955700258723 391392982441805933550388085)
    ·
      refine ⟨36693092103919306270348883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391392982441805933550388085 36693092103919306270348883)
      ·
        refine ⟨55039638155878959405523325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36693092103919306270348883 55039638155878959405523325)
        ·
          refine ⟨20639864308454609777071247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55039638155878959405523325 20639864308454609777071247)
          ·
            refine ⟨30959796462681914665606871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20639864308454609777071247 30959796462681914665606871)
            ·
              refine ⟨46439694694022871998410307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30959796462681914665606871 46439694694022871998410307)
              ·
                refine ⟨69659542041034307997615461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46439694694022871998410307 69659542041034307997615461)
                ·
                  refine ⟨13061164132693932749552899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69659542041034307997615461 13061164132693932749552899)
                  ·
                    refine ⟨19591746199040899124329349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13061164132693932749552899 19591746199040899124329349)
                    ·
                      refine ⟨3673452412320168585811753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19591746199040899124329349 3673452412320168585811753)
                      ·
                        rfl

theorem cell23_7154023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_7154023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154023 prefixEnd_7154023 := by exact prefixLift 7154023
  have htrace : WordTrace (prefixWord ++ tailWord_7154023) baseStart_7154023 baseEnd_7154023 := by
    simpa [prefixWord, tailWord_7154023, baseEnd_7154023] using wordTrace_append hprefix tailTrace_7154023
  have hstable : (prefixWord ++ tailWord_7154023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154023).length < 2 ^ (prefixWord ++ tailWord_7154023).sum := by decide
  have hdescent : baseEnd_7154023 < baseStart_7154023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154060 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_7154060 : Nat := 118140960795 + 7154060 * 2 ^ 59
def prefixEnd_7154060 : Nat := 4983230072969 + 3 ^ 40 * 7154060 * 2
def baseEnd_7154060 : Nat := 3673471411104384941049083

theorem tailTrace_7154060 : CollatzResearch.WordTrace tailWord_7154060 prefixEnd_7154060 3673471411104384941049083 := by
  unfold tailWord_7154060
  simp only [CollatzResearch.WordTrace]
  refine ⟨130465002231034955509677817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173953336308046607346237089 130465002231034955509677817)
  ·
    refine ⟨97848751673276216632258363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130465002231034955509677817 97848751673276216632258363)
    ·
      refine ⟨146773127509914324948387545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97848751673276216632258363 146773127509914324948387545)
      ·
        refine ⟨110079845632435743711290659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146773127509914324948387545 110079845632435743711290659)
        ·
          refine ⟨165119768448653615566935989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110079845632435743711290659 165119768448653615566935989)
          ·
            refine ⟨15479978292061276459400249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165119768448653615566935989 15479978292061276459400249)
            ·
              refine ⟨11609983719045957344550187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15479978292061276459400249 11609983719045957344550187)
              ·
                refine ⟨17414975578568936016825281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609983719045957344550187 17414975578568936016825281)
                ·
                  refine ⟨13061231683926702012618961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17414975578568936016825281 13061231683926702012618961)
                  ·
                    refine ⟨9795923762945026509464221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13061231683926702012618961 9795923762945026509464221)
                    ·
                      refine ⟨3673471411104384941049083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9795923762945026509464221 3673471411104384941049083)
                      ·
                        rfl

theorem cell23_7154060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_7154060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154060 prefixEnd_7154060 := by exact prefixLift 7154060
  have htrace : WordTrace (prefixWord ++ tailWord_7154060) baseStart_7154060 baseEnd_7154060 := by
    simpa [prefixWord, tailWord_7154060, baseEnd_7154060] using wordTrace_append hprefix tailTrace_7154060
  have hstable : (prefixWord ++ tailWord_7154060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154060).length < 2 ^ (prefixWord ++ tailWord_7154060).sum := by decide
  have hdescent : baseEnd_7154060 < baseStart_7154060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154123 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 4, 4]
def baseStart_7154123 : Nat := 118140960795 + 7154123 * 2 ^ 59
def prefixEnd_7154123 : Nat := 4983230072969 + 3 ^ 40 * 7154123 * 2
def baseEnd_7154123 : Nat := 1224501253461872731520431

theorem tailTrace_7154123 : CollatzResearch.WordTrace tailWord_7154123 prefixEnd_7154123 1224501253461872731520431 := by
  unfold tailWord_7154123
  simp only [CollatzResearch.WordTrace]
  refine ⟨260932302260841672778899023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173954868173894448519266015 260932302260841672778899023)
  ·
    refine ⟨391398453391262509168348535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260932302260841672778899023 391398453391262509168348535)
    ·
      refine ⟨587097680086893763752522803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391398453391262509168348535 587097680086893763752522803)
      ·
        refine ⟨880646520130340645628784205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587097680086893763752522803 880646520130340645628784205)
        ·
          refine ⟨330242445048877742110794077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 880646520130340645628784205 330242445048877742110794077)
          ·
            refine ⟨123840916893329153291547779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330242445048877742110794077 123840916893329153291547779)
            ·
              refine ⟨185761375339993729937321669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123840916893329153291547779 185761375339993729937321669)
              ·
                refine ⟨34830257876248824363247813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185761375339993729937321669 34830257876248824363247813)
                ·
                  refine ⟨6530673351796654568108965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34830257876248824363247813 6530673351796654568108965)
                  ·
                    refine ⟨1224501253461872731520431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530673351796654568108965 1224501253461872731520431)
                    ·
                      rfl

theorem cell23_7154123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 4].length) (baseStart_7154123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154123 prefixEnd_7154123 := by exact prefixLift 7154123
  have htrace : WordTrace (prefixWord ++ tailWord_7154123) baseStart_7154123 baseEnd_7154123 := by
    simpa [prefixWord, tailWord_7154123, baseEnd_7154123] using wordTrace_append hprefix tailTrace_7154123
  have hstable : (prefixWord ++ tailWord_7154123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154123).length < 2 ^ (prefixWord ++ tailWord_7154123).sum := by decide
  have hdescent : baseEnd_7154123 < baseStart_7154123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154157 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_7154157 : Nat := 118140960795 + 7154157 * 2 ^ 59
def prefixEnd_7154157 : Nat := 4983230072969 + 3 ^ 40 * 7154157 * 2
def baseEnd_7154157 : Nat := 1224507072909290353845379

theorem tailTrace_7154157 : CollatzResearch.WordTrace tailWord_7154157 prefixEnd_7154157 1224507072909290353845379 := by
  unfold tailWord_7154157
  simp only [CollatzResearch.WordTrace]
  refine ⟨260933542342718496585636725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173955694895145664390424483 260933542342718496585636725)
  ·
    refine ⟨24462519594629859054903443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260933542342718496585636725 24462519594629859054903443)
    ·
      refine ⟨36693779391944788582355165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24462519594629859054903443 36693779391944788582355165)
      ·
        refine ⟨13760167271979295718383187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36693779391944788582355165 13760167271979295718383187)
        ·
          refine ⟨20640250907968943577574781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760167271979295718383187 20640250907968943577574781)
          ·
            refine ⟨7740094090488353841590543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20640250907968943577574781 7740094090488353841590543)
            ·
              refine ⟨11610141135732530762385815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740094090488353841590543 11610141135732530762385815)
              ·
                refine ⟨17415211703598796143578723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11610141135732530762385815 17415211703598796143578723)
                ·
                  refine ⟨26122817555398194215368085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17415211703598796143578723 26122817555398194215368085)
                  ·
                    refine ⟨1224507072909290353845379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26122817555398194215368085 1224507072909290353845379)
                    ·
                      rfl

theorem cell23_7154157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_7154157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154157 prefixEnd_7154157 := by exact prefixLift 7154157
  have htrace : WordTrace (prefixWord ++ tailWord_7154157) baseStart_7154157 baseEnd_7154157 := by
    simpa [prefixWord, tailWord_7154157, baseEnd_7154157] using wordTrace_append hprefix tailTrace_7154157
  have hstable : (prefixWord ++ tailWord_7154157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154157).length < 2 ^ (prefixWord ++ tailWord_7154157).sum := by decide
  have hdescent : baseEnd_7154157 < baseStart_7154157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154197 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_7154197 : Nat := 118140960795 + 7154197 * 2 ^ 59
def prefixEnd_7154197 : Nat := 4983230072969 + 3 ^ 40 * 7154197 * 2
def baseEnd_7154197 : Nat := 3673541757954050905035953

theorem tailTrace_7154197 : CollatzResearch.WordTrace tailWord_7154197 prefixEnd_7154197 3673541757954050905035953 := by
  unfold tailWord_7154197
  simp only [CollatzResearch.WordTrace]
  refine ⟨260935001262573583417092845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173956667508382388944728563 260935001262573583417092845)
  ·
    refine ⟨97850625473465093781409817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260935001262573583417092845 97850625473465093781409817)
    ·
      refine ⟨73387969105098820336057363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97850625473465093781409817 73387969105098820336057363)
      ·
        refine ⟨110081953657648230504086045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73387969105098820336057363 110081953657648230504086045)
        ·
          refine ⟨41280732621618086439032267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110081953657648230504086045 41280732621618086439032267)
          ·
            refine ⟨61921098932427129658548401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41280732621618086439032267 61921098932427129658548401)
            ·
              refine ⟨46440824199320347243911301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61921098932427129658548401 46440824199320347243911301)
              ·
                refine ⟨8707654537372565108233369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46440824199320347243911301 8707654537372565108233369)
                ·
                  refine ⟨6530740903029423831175027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707654537372565108233369 6530740903029423831175027)
                  ·
                    refine ⟨9796111354544135746762541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530740903029423831175027 9796111354544135746762541)
                    ·
                      refine ⟨3673541757954050905035953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9796111354544135746762541 3673541757954050905035953)
                      ·
                        rfl

theorem cell23_7154197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_7154197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154197 prefixEnd_7154197 := by exact prefixLift 7154197
  have htrace : WordTrace (prefixWord ++ tailWord_7154197) baseStart_7154197 baseEnd_7154197 := by
    simpa [prefixWord, tailWord_7154197, baseEnd_7154197] using wordTrace_append hprefix tailTrace_7154197
  have hstable : (prefixWord ++ tailWord_7154197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154197).length < 2 ^ (prefixWord ++ tailWord_7154197).sum := by decide
  have hdescent : baseEnd_7154197 < baseStart_7154197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154213 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_7154213 : Nat := 118140960795 + 7154213 * 2 ^ 59
def prefixEnd_7154213 : Nat := 4983230072969 + 3 ^ 40 * 7154213 * 2
def baseEnd_7154213 : Nat := 1224516657881507614145293

theorem tailTrace_7154213 : CollatzResearch.WordTrace tailWord_7154213 prefixEnd_7154213 1224516657881507614145293 := by
  unfold tailWord_7154213
  simp only [CollatzResearch.WordTrace]
  refine ⟨260935584830515618149675293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173957056553677078766450195 260935584830515618149675293)
  ·
    refine ⟨97850844311443356806128235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260935584830515618149675293 97850844311443356806128235)
    ·
      refine ⟨146776266467165035209192353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97850844311443356806128235 146776266467165035209192353)
      ·
        refine ⟨110082199850373776406894265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146776266467165035209192353 110082199850373776406894265)
        ·
          refine ⟨82561649887780332305170699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110082199850373776406894265 82561649887780332305170699)
          ·
            refine ⟨123842474831670498457756049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82561649887780332305170699 123842474831670498457756049)
            ·
              refine ⟨92881856123752873843317037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123842474831670498457756049 92881856123752873843317037)
              ·
                refine ⟨34830696046407327691243889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92881856123752873843317037 34830696046407327691243889)
                ·
                  refine ⟨26123022034805495768432917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34830696046407327691243889 26123022034805495768432917)
                  ·
                    refine ⟨1224516657881507614145293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26123022034805495768432917 1224516657881507614145293)
                    ·
                      rfl

theorem cell23_7154213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_7154213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154213 prefixEnd_7154213 := by exact prefixLift 7154213
  have htrace : WordTrace (prefixWord ++ tailWord_7154213) baseStart_7154213 baseEnd_7154213 := by
    simpa [prefixWord, tailWord_7154213, baseEnd_7154213] using wordTrace_append hprefix tailTrace_7154213
  have hstable : (prefixWord ++ tailWord_7154213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154213).length < 2 ^ (prefixWord ++ tailWord_7154213).sum := by decide
  have hdescent : baseEnd_7154213 < baseStart_7154213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154220 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 5, 4, 2]
def baseStart_7154220 : Nat := 118140960795 + 7154220 * 2 ^ 59
def prefixEnd_7154220 : Nat := 4983230072969 + 3 ^ 40 * 7154220 * 2
def baseEnd_7154220 : Nat := 3673553568009104315048347

theorem tailTrace_7154220 : CollatzResearch.WordTrace tailWord_7154220 prefixEnd_7154220 3673553568009104315048347 := by
  unfold tailWord_7154220
  simp only [CollatzResearch.WordTrace]
  refine ⟨130467920070745129172590057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173957226760993505563453409 130467920070745129172590057)
  ·
    refine ⟨97850940053058846879442543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130467920070745129172590057 97850940053058846879442543)
    ·
      refine ⟨146776410079588270319163815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97850940053058846879442543 146776410079588270319163815)
      ·
        refine ⟨220164615119382405478745723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146776410079588270319163815 220164615119382405478745723)
        ·
          refine ⟨330246922679073608218118585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220164615119382405478745723 330246922679073608218118585)
          ·
            refine ⟨247685192009305206163588939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330246922679073608218118585 247685192009305206163588939)
            ·
              refine ⟨371527788013957809245383409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247685192009305206163588939 371527788013957809245383409)
              ·
                refine ⟨278645841010468356934037557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371527788013957809245383409 278645841010468356934037557)
                ·
                  refine ⟨26123047594731408462566021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278645841010468356934037557 26123047594731408462566021)
                  ·
                    refine ⟨4898071424012139086731129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26123047594731408462566021 4898071424012139086731129)
                    ·
                      refine ⟨3673553568009104315048347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898071424012139086731129 3673553568009104315048347)
                      ·
                        rfl

theorem cell23_7154220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_7154220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154220 prefixEnd_7154220 := by exact prefixLift 7154220
  have htrace : WordTrace (prefixWord ++ tailWord_7154220) baseStart_7154220 baseEnd_7154220 := by
    simpa [prefixWord, tailWord_7154220, baseEnd_7154220] using wordTrace_append hprefix tailTrace_7154220
  have hstable : (prefixWord ++ tailWord_7154220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154220).length < 2 ^ (prefixWord ++ tailWord_7154220).sum := by decide
  have hdescent : baseEnd_7154220 < baseStart_7154220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154237 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_7154237 : Nat := 118140960795 + 7154237 * 2 ^ 59
def prefixEnd_7154237 : Nat := 4983230072969 + 3 ^ 40 * 7154237 * 2
def baseEnd_7154237 : Nat := 3673562297180230748535769

theorem tailTrace_7154237 : CollatzResearch.WordTrace tailWord_7154237 prefixEnd_7154237 3673562297180230748535769 := by
  unfold tailWord_7154237
  simp only [CollatzResearch.WordTrace]
  refine ⟨260936460182428670248548965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173957640121619113499032643 260936460182428670248548965)
  ·
    refine ⟨48925586284205375671602931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260936460182428670248548965 48925586284205375671602931)
    ·
      refine ⟨73388379426308063507404397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48925586284205375671602931 73388379426308063507404397)
      ·
        refine ⟨27520642284865523815276649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73388379426308063507404397 27520642284865523815276649)
        ·
          refine ⟨20640481713649142861457487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27520642284865523815276649 20640481713649142861457487)
          ·
            refine ⟨30960722570473714292186231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20640481713649142861457487 30960722570473714292186231)
            ·
              refine ⟨46441083855710571438279347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30960722570473714292186231 46441083855710571438279347)
              ·
                refine ⟨69661625783565857157419021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46441083855710571438279347 69661625783565857157419021)
                ·
                  refine ⟨26123109668837196434032133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69661625783565857157419021 26123109668837196434032133)
                  ·
                    refine ⟨4898083062906974331381025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26123109668837196434032133 4898083062906974331381025)
                    ·
                      refine ⟨3673562297180230748535769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898083062906974331381025 3673562297180230748535769)
                      ·
                        rfl

theorem cell23_7154237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_7154237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154237 prefixEnd_7154237 := by exact prefixLift 7154237
  have htrace : WordTrace (prefixWord ++ tailWord_7154237) baseStart_7154237 baseEnd_7154237 := by
    simpa [prefixWord, tailWord_7154237, baseEnd_7154237] using wordTrace_append hprefix tailTrace_7154237
  have hstable : (prefixWord ++ tailWord_7154237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154237).length < 2 ^ (prefixWord ++ tailWord_7154237).sum := by decide
  have hdescent : baseEnd_7154237 < baseStart_7154237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154241 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7154241 : Nat := 118140960795 + 7154241 * 2 ^ 59
def prefixEnd_7154241 : Nat := 4983230072969 + 3 ^ 40 * 7154241 * 2
def baseEnd_7154241 : Nat := 3673564351102848732885751

theorem tailTrace_7154241 : CollatzResearch.WordTrace tailWord_7154241 prefixEnd_7154241 3673564351102848732885751 := by
  unfold tailWord_7154241
  simp only [CollatzResearch.WordTrace]
  refine ⟨260936606074414178931694577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173957737382942785954463051 260936606074414178931694577)
  ·
    refine ⟨195702454555810634198770933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260936606074414178931694577 195702454555810634198770933)
    ·
      refine ⟨18347105114607246956134775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195702454555810634198770933 18347105114607246956134775)
      ·
        refine ⟨27520657671910870434202163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347105114607246956134775 27520657671910870434202163)
        ·
          refine ⟨41280986507866305651303245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27520657671910870434202163 41280986507866305651303245)
          ·
            refine ⟨15480369940449864619238717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41280986507866305651303245 15480369940449864619238717)
            ·
              refine ⟨5805138727668699232214519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15480369940449864619238717 5805138727668699232214519)
              ·
                refine ⟨8707708091503048848321779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805138727668699232214519 8707708091503048848321779)
                ·
                  refine ⟨13061562137254573272482669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707708091503048848321779 13061562137254573272482669)
                  ·
                    refine ⟨4898085801470464977181001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13061562137254573272482669 4898085801470464977181001)
                    ·
                      refine ⟨3673564351102848732885751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898085801470464977181001 3673564351102848732885751)
                      ·
                        rfl

theorem cell23_7154241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7154241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154241 prefixEnd_7154241 := by exact prefixLift 7154241
  have htrace : WordTrace (prefixWord ++ tailWord_7154241) baseStart_7154241 baseEnd_7154241 := by
    simpa [prefixWord, tailWord_7154241, baseEnd_7154241] using wordTrace_append hprefix tailTrace_7154241
  have hstable : (prefixWord ++ tailWord_7154241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154241).length < 2 ^ (prefixWord ++ tailWord_7154241).sum := by decide
  have hdescent : baseEnd_7154241 < baseStart_7154241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154254 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_7154254 : Nat := 118140960795 + 7154254 * 2 ^ 59
def prefixEnd_7154254 : Nat := 4983230072969 + 3 ^ 40 * 7154254 * 2
def baseEnd_7154254 : Nat := 3673571026351357182023191

theorem tailTrace_7154254 : CollatzResearch.WordTrace tailWord_7154254 prefixEnd_7154254 3673571026351357182023191 := by
  unfold tailWord_7154254
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617135027920885268989727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173958053482244721434611877 32617135027920885268989727)
  ·
    refine ⟨48925702541881327903484591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32617135027920885268989727 48925702541881327903484591)
    ·
      refine ⟨73388553812821991855226887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48925702541881327903484591 73388553812821991855226887)
      ·
        refine ⟨110082830719232987782840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73388553812821991855226887 110082830719232987782840331)
        ·
          refine ⟨165124246078849481674260497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110082830719232987782840331 165124246078849481674260497)
          ·
            refine ⟨123843184559137111255695373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165124246078849481674260497 123843184559137111255695373)
            ·
              refine ⟨46441194209676416720885765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123843184559137111255695373 46441194209676416720885765)
              ·
                refine ⟨8707723914314328135166081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46441194209676416720885765 8707723914314328135166081)
                ·
                  refine ⟨6530792935735746101374561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707723914314328135166081 6530792935735746101374561)
                  ·
                    refine ⟨4898094701801809576030921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6530792935735746101374561 4898094701801809576030921)
                    ·
                      refine ⟨3673571026351357182023191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898094701801809576030921 3673571026351357182023191)
                      ·
                        rfl

theorem cell23_7154254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_7154254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154254 prefixEnd_7154254 := by exact prefixLift 7154254
  have htrace : WordTrace (prefixWord ++ tailWord_7154254) baseStart_7154254 baseEnd_7154254 := by
    simpa [prefixWord, tailWord_7154254, baseEnd_7154254] using wordTrace_append hprefix tailTrace_7154254
  have hstable : (prefixWord ++ tailWord_7154254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154254).length < 2 ^ (prefixWord ++ tailWord_7154254).sum := by decide
  have hdescent : baseEnd_7154254 < baseStart_7154254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154283 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_7154283 : Nat := 118140960795 + 7154283 * 2 ^ 59
def prefixEnd_7154283 : Nat := 4983230072969 + 3 ^ 40 * 7154283 * 2
def baseEnd_7154283 : Nat := 3673585917290337568560557

theorem tailTrace_7154283 : CollatzResearch.WordTrace tailWord_7154283 prefixEnd_7154283 3673585917290337568560557 := by
  unfold tailWord_7154283
  simp only [CollatzResearch.WordTrace]
  refine ⟨260938137940262020104723503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173958758626841346736482335 260938137940262020104723503)
  ·
    refine ⟨391407206910393030157085255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260938137940262020104723503 391407206910393030157085255)
    ·
      refine ⟨587110810365589545235627883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391407206910393030157085255 587110810365589545235627883)
      ·
        refine ⟨880666215548384317853441825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587110810365589545235627883 880666215548384317853441825)
        ·
          refine ⟨660499661661288238390081369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880666215548384317853441825 660499661661288238390081369)
          ·
            refine ⟨495374746245966178792561027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660499661661288238390081369 495374746245966178792561027)
            ·
              refine ⟨743062119368949268188841541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495374746245966178792561027 743062119368949268188841541)
              ·
                refine ⟨139324147381677987785407789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743062119368949268188841541 139324147381677987785407789)
                ·
                  refine ⟨52246555268129245419527921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139324147381677987785407789 52246555268129245419527921)
                  ·
                    refine ⟨39184916451096934064645941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52246555268129245419527921 39184916451096934064645941)
                    ·
                      refine ⟨3673585917290337568560557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39184916451096934064645941 3673585917290337568560557)
                      ·
                        rfl

theorem cell23_7154283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_7154283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154283 prefixEnd_7154283 := by exact prefixLift 7154283
  have htrace : WordTrace (prefixWord ++ tailWord_7154283) baseStart_7154283 baseEnd_7154283 := by
    simpa [prefixWord, tailWord_7154283, baseEnd_7154283] using wordTrace_append hprefix tailTrace_7154283
  have hstable : (prefixWord ++ tailWord_7154283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154283).length < 2 ^ (prefixWord ++ tailWord_7154283).sum := by decide
  have hdescent : baseEnd_7154283 < baseStart_7154283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154327 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 2, 4, 2]
def baseStart_7154327 : Nat := 118140960795 + 7154327 * 2 ^ 59
def prefixEnd_7154327 : Nat := 4983230072969 + 3 ^ 40 * 7154327 * 2
def baseEnd_7154327 : Nat := 3673608510439135396410355

theorem tailTrace_7154327 : CollatzResearch.WordTrace tailWord_7154327 prefixEnd_7154327 3673608510439135396410355 := by
  unfold tailWord_7154327
  simp only [CollatzResearch.WordTrace]
  refine ⟨260939742752102615619325235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173959828501401743746216823 260939742752102615619325235)
  ·
    refine ⟨391409614128153923428987853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260939742752102615619325235 391409614128153923428987853)
    ·
      refine ⟨146778605298057721285870445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391409614128153923428987853 146778605298057721285870445)
      ·
        refine ⟨55041976986771645482201417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146778605298057721285870445 55041976986771645482201417)
        ·
          refine ⟨41281482740078734111651063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55041976986771645482201417 41281482740078734111651063)
          ·
            refine ⟨61922224110118101167476595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41281482740078734111651063 61922224110118101167476595)
            ·
              refine ⟨92883336165177151751214893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61922224110118101167476595 92883336165177151751214893)
              ·
                refine ⟨34831251061941431906705585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92883336165177151751214893 34831251061941431906705585)
                ·
                  refine ⟨26123438296456073930029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34831251061941431906705585 26123438296456073930029189)
                  ·
                    refine ⟨4898144680585513861880473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26123438296456073930029189 4898144680585513861880473)
                    ·
                      refine ⟨3673608510439135396410355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898144680585513861880473 3673608510439135396410355)
                      ·
                        rfl

theorem cell23_7154327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_7154327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154327 prefixEnd_7154327 := by exact prefixLift 7154327
  have htrace : WordTrace (prefixWord ++ tailWord_7154327) baseStart_7154327 baseEnd_7154327 := by
    simpa [prefixWord, tailWord_7154327, baseEnd_7154327] using wordTrace_append hprefix tailTrace_7154327
  have hstable : (prefixWord ++ tailWord_7154327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154327).length < 2 ^ (prefixWord ++ tailWord_7154327).sum := by decide
  have hdescent : baseEnd_7154327 < baseStart_7154327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154340 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_7154340 : Nat := 118140960795 + 7154340 * 2 ^ 59
def prefixEnd_7154340 : Nat := 4983230072969 + 3 ^ 40 * 7154340 * 2
def baseEnd_7154340 : Nat := 3673615185687643845547795

theorem tailTrace_7154340 : CollatzResearch.WordTrace tailWord_7154340 prefixEnd_7154340 3673615185687643845547795 := by
  unfold tailWord_7154340
  simp only [CollatzResearch.WordTrace]
  refine ⟨130470108450527759419774237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173960144600703679226365649 130470108450527759419774237)
  ·
    refine ⟨48926290668947909782415339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130470108450527759419774237 48926290668947909782415339)
    ·
      refine ⟨73389436003421864673623009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48926290668947909782415339 73389436003421864673623009)
      ·
        refine ⟨55042077002566398505217257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73389436003421864673623009 55042077002566398505217257)
        ·
          refine ⟨41281557751924798878912943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55042077002566398505217257 41281557751924798878912943)
          ·
            refine ⟨61922336627887198318369415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41281557751924798878912943 61922336627887198318369415)
            ·
              refine ⟨92883504941830797477554123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61922336627887198318369415 92883504941830797477554123)
              ·
                refine ⟨139325257412746196216331185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92883504941830797477554123 139325257412746196216331185)
                ·
                  refine ⟨104493943059559647162248389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139325257412746196216331185 104493943059559647162248389)
                  ·
                    refine ⟨19592614323667433842921573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104493943059559647162248389 19592614323667433842921573)
                    ·
                      refine ⟨3673615185687643845547795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19592614323667433842921573 3673615185687643845547795)
                      ·
                        rfl

theorem cell23_7154340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_7154340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154340 prefixEnd_7154340 := by exact prefixLift 7154340
  have htrace : WordTrace (prefixWord ++ tailWord_7154340) baseStart_7154340 baseEnd_7154340 := by
    simpa [prefixWord, tailWord_7154340, baseEnd_7154340] using wordTrace_append hprefix tailTrace_7154340
  have hstable : (prefixWord ++ tailWord_7154340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154340).length < 2 ^ (prefixWord ++ tailWord_7154340).sum := by decide
  have hdescent : baseEnd_7154340 < baseStart_7154340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154404 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_7154404 : Nat := 118140960795 + 7154404 * 2 ^ 59
def prefixEnd_7154404 : Nat := 4983230072969 + 3 ^ 40 * 7154404 * 2
def baseEnd_7154404 : Nat := 3673648048449531595147501

theorem tailTrace_7154404 : CollatzResearch.WordTrace tailWord_7154404 prefixEnd_7154404 3673648048449531595147501 := by
  unfold tailWord_7154404
  simp only [CollatzResearch.WordTrace]
  refine ⟨130471275586411828884939133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173961700781882438513252177 130471275586411828884939133)
  ·
    refine ⟨48926728344904435831852175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130471275586411828884939133 48926728344904435831852175)
    ·
      refine ⟨73390092517356653747778263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48926728344904435831852175 73390092517356653747778263)
      ·
        refine ⟨110085138776034980621667395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73390092517356653747778263 110085138776034980621667395)
        ·
          refine ⟨165127708164052470932501093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110085138776034980621667395 165127708164052470932501093)
          ·
            refine ⟨30961445280759838299843955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165127708164052470932501093 30961445280759838299843955)
            ·
              refine ⟨46442167921139757449765933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30961445280759838299843955 46442167921139757449765933)
              ·
                refine ⟨17415812970427409043662225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46442167921139757449765933 17415812970427409043662225)
                ·
                  refine ⟨13061859727820556782746669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17415812970427409043662225 13061859727820556782746669)
                  ·
                    refine ⟨4898197397932708793530001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13061859727820556782746669 4898197397932708793530001)
                    ·
                      refine ⟨3673648048449531595147501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898197397932708793530001 3673648048449531595147501)
                      ·
                        rfl

theorem cell23_7154404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_7154404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154404 prefixEnd_7154404 := by exact prefixLift 7154404
  have htrace : WordTrace (prefixWord ++ tailWord_7154404) baseStart_7154404 baseEnd_7154404 := by
    simpa [prefixWord, tailWord_7154404, baseEnd_7154404] using wordTrace_append hprefix tailTrace_7154404
  have hstable : (prefixWord ++ tailWord_7154404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154404).length < 2 ^ (prefixWord ++ tailWord_7154404).sum := by decide
  have hdescent : baseEnd_7154404 < baseStart_7154404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154428 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_7154428 : Nat := 118140960795 + 7154428 * 2 ^ 59
def prefixEnd_7154428 : Nat := 4983230072969 + 3 ^ 40 * 7154428 * 2
def baseEnd_7154428 : Nat := 3673660371985239501247391

theorem tailTrace_7154428 : CollatzResearch.WordTrace tailWord_7154428 prefixEnd_7154428 3673660371985239501247391 := by
  unfold tailWord_7154428
  simp only [CollatzResearch.WordTrace]
  refine ⟨130471713262368354934375969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173962284349824473245834625 130471713262368354934375969)
  ·
    refine ⟨97853784946776266200781977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130471713262368354934375969 97853784946776266200781977)
    ·
      refine ⟨73390338710082199650586483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97853784946776266200781977 73390338710082199650586483)
      ·
        refine ⟨110085508065123299475879725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73390338710082199650586483 110085508065123299475879725)
        ·
          refine ⟨41282065524421237303454897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110085508065123299475879725 41282065524421237303454897)
          ·
            refine ⟨30961549143315927977591173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41282065524421237303454897 30961549143315927977591173)
            ·
              refine ⟨5805290464371736495798345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30961549143315927977591173 5805290464371736495798345)
              ·
                refine ⟨4353967848278802371848759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5805290464371736495798345 4353967848278802371848759)
                ·
                  refine ⟨6530951772418203557773139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353967848278802371848759 6530951772418203557773139)
                  ·
                    refine ⟨9796427658627305336659709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6530951772418203557773139 9796427658627305336659709)
                    ·
                      refine ⟨3673660371985239501247391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9796427658627305336659709 3673660371985239501247391)
                      ·
                        rfl

theorem cell23_7154428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_7154428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154428 prefixEnd_7154428 := by exact prefixLift 7154428
  have htrace : WordTrace (prefixWord ++ tailWord_7154428) baseStart_7154428 baseEnd_7154428 := by
    simpa [prefixWord, tailWord_7154428, baseEnd_7154428] using wordTrace_append hprefix tailTrace_7154428
  have hstable : (prefixWord ++ tailWord_7154428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154428).length < 2 ^ (prefixWord ++ tailWord_7154428).sum := by decide
  have hdescent : baseEnd_7154428 < baseStart_7154428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154434 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7154434 : Nat := 118140960795 + 7154434 * 2 ^ 59
def prefixEnd_7154434 : Nat := 4983230072969 + 3 ^ 40 * 7154434 * 2
def baseEnd_7154434 : Nat := 3673663452869166477772363

theorem tailTrace_7154434 : CollatzResearch.WordTrace tailWord_7154434 prefixEnd_7154434 3673663452869166477772363 := by
  unfold tailWord_7154434
  simp only [CollatzResearch.WordTrace]
  refine ⟨65235911340678743223367589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173962430241809981928980237 65235911340678743223367589)
  ·
    refine ⟨12231733376377264354381423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65235911340678743223367589 12231733376377264354381423)
    ·
      refine ⟨18347600064565896531572135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12231733376377264354381423 18347600064565896531572135)
      ·
        refine ⟨27521400096848844797358203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347600064565896531572135 27521400096848844797358203)
        ·
          refine ⟨41282100145273267196037305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27521400096848844797358203 41282100145273267196037305)
          ·
            refine ⟨30961575108954950397027979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41282100145273267196037305 30961575108954950397027979)
            ·
              refine ⟨46442362663432425595541969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30961575108954950397027979 46442362663432425595541969)
              ·
                refine ⟨34831771997574319196656477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46442362663432425595541969 34831771997574319196656477)
                ·
                  refine ⟨13061914499090369698746179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34831771997574319196656477 13061914499090369698746179)
                  ·
                    refine ⟨19592871748635554548119269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13061914499090369698746179 19592871748635554548119269)
                    ·
                      refine ⟨3673663452869166477772363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19592871748635554548119269 3673663452869166477772363)
                      ·
                        rfl

theorem cell23_7154434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7154434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154434 prefixEnd_7154434 := by exact prefixLift 7154434
  have htrace : WordTrace (prefixWord ++ tailWord_7154434) baseStart_7154434 baseEnd_7154434 := by
    simpa [prefixWord, tailWord_7154434, baseEnd_7154434] using wordTrace_append hprefix tailTrace_7154434
  have hstable : (prefixWord ++ tailWord_7154434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154434).length < 2 ^ (prefixWord ++ tailWord_7154434).sum := by decide
  have hdescent : baseEnd_7154434 < baseStart_7154434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154447 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_7154447 : Nat := 118140960795 + 7154447 * 2 ^ 59
def prefixEnd_7154447 : Nat := 4983230072969 + 3 ^ 40 * 7154447 * 2
def baseEnd_7154447 : Nat := 3673670128117674926909803

theorem tailTrace_7154447 : CollatzResearch.WordTrace tailWord_7154447 prefixEnd_7154447 3673670128117674926909803 := by
  unfold tailWord_7154447
  simp only [CollatzResearch.WordTrace]
  refine ⟨260944119511667876113693595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173962746341111917409129063 260944119511667876113693595)
  ·
    refine ⟨391416179267501814170540393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260944119511667876113693595 391416179267501814170540393)
    ·
      refine ⟨293562134450626360627905295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391416179267501814170540393 293562134450626360627905295)
      ·
        refine ⟨440343201675939540941857943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293562134450626360627905295 440343201675939540941857943)
        ·
          refine ⟨660514802513909311412786915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440343201675939540941857943 660514802513909311412786915)
          ·
            refine ⟨990772203770863967119180373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660514802513909311412786915 990772203770863967119180373)
            ·
              refine ⟨11610611762939812114677895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 990772203770863967119180373 11610611762939812114677895)
              ·
                refine ⟨17415917644409718172016843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11610611762939812114677895 17415917644409718172016843)
                ·
                  refine ⟨26123876466614577258025265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17415917644409718172016843 26123876466614577258025265)
                  ·
                    refine ⟨19592907349960932943518949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26123876466614577258025265 19592907349960932943518949)
                    ·
                      refine ⟨3673670128117674926909803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19592907349960932943518949 3673670128117674926909803)
                      ·
                        rfl

theorem cell23_7154447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_7154447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154447 prefixEnd_7154447 := by exact prefixLift 7154447
  have htrace : WordTrace (prefixWord ++ tailWord_7154447) baseStart_7154447 baseEnd_7154447 := by
    simpa [prefixWord, tailWord_7154447, baseEnd_7154447] using wordTrace_append hprefix tailTrace_7154447
  have hstable : (prefixWord ++ tailWord_7154447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154447).length < 2 ^ (prefixWord ++ tailWord_7154447).sum := by decide
  have hdescent : baseEnd_7154447 < baseStart_7154447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154468 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_7154468 : Nat := 118140960795 + 7154468 * 2 ^ 59
def prefixEnd_7154468 : Nat := 4983230072969 + 3 ^ 40 * 7154468 * 2
def baseEnd_7154468 : Nat := 3673680911211419344747207

theorem tailTrace_7154468 : CollatzResearch.WordTrace tailWord_7154468 prefixEnd_7154468 3673680911211419344747207 := by
  unfold tailWord_7154468
  simp only [CollatzResearch.WordTrace]
  refine ⟨130472442722295898350104029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173963256963061197800138705 130472442722295898350104029)
  ·
    refine ⟨48927166020860961881289011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130472442722295898350104029 48927166020860961881289011)
    ·
      refine ⟨73390749031291442821933517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48927166020860961881289011 73390749031291442821933517)
      ·
        refine ⟨27521530886734291058225069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73390749031291442821933517 27521530886734291058225069)
        ·
          refine ⟨10320574082525359146834401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27521530886734291058225069 10320574082525359146834401)
          ·
            refine ⟨7740430561894019360125801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10320574082525359146834401 7740430561894019360125801)
            ·
              refine ⟨5805322921420514520094351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740430561894019360125801 5805322921420514520094351)
              ·
                refine ⟨8707984382130771780141527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805322921420514520094351 8707984382130771780141527)
                ·
                  refine ⟨13061976573196157670212291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8707984382130771780141527 13061976573196157670212291)
                  ·
                    refine ⟨19592964859794236505318437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13061976573196157670212291 19592964859794236505318437)
                    ·
                      refine ⟨3673680911211419344747207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19592964859794236505318437 3673680911211419344747207)
                      ·
                        rfl

theorem cell23_7154468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_7154468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154468 prefixEnd_7154468 := by exact prefixLift 7154468
  have htrace : WordTrace (prefixWord ++ tailWord_7154468) baseStart_7154468 baseEnd_7154468 := by
    simpa [prefixWord, tailWord_7154468, baseEnd_7154468] using wordTrace_append hprefix tailTrace_7154468
  have hstable : (prefixWord ++ tailWord_7154468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154468).length < 2 ^ (prefixWord ++ tailWord_7154468).sum := by decide
  have hdescent : baseEnd_7154468 < baseStart_7154468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154474 : List Nat := [3, 1, 4, 3, 1, 1, 10]
def baseStart_7154474 : Nat := 118140960795 + 7154474 * 2 ^ 59
def prefixEnd_7154474 : Nat := 4983230072969 + 3 ^ 40 * 7154474 * 2
def baseEnd_7154474 : Nat := 45354123359201806435459

theorem tailTrace_7154474 : CollatzResearch.WordTrace tailWord_7154474 prefixEnd_7154474 45354123359201806435459 := by
  unfold tailWord_7154474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65236276070642514931231619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173963402855046706483284317 65236276070642514931231619)
  ·
    refine ⟨97854414105963772396847429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65236276070642514931231619 97854414105963772396847429)
    ·
      refine ⟨18347702644868207324408893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97854414105963772396847429 18347702644868207324408893)
      ·
        refine ⟨6880388491825577746653335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18347702644868207324408893 6880388491825577746653335)
        ·
          refine ⟨10320582737738366619980003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6880388491825577746653335 10320582737738366619980003)
          ·
            refine ⟨15480874106607549929970005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10320582737738366619980003 15480874106607549929970005)
            ·
              refine ⟨45354123359201806435459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15480874106607549929970005 45354123359201806435459)
              ·
                rfl

theorem cell23_7154474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 10].length) (baseStart_7154474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154474 prefixEnd_7154474 := by exact prefixLift 7154474
  have htrace : WordTrace (prefixWord ++ tailWord_7154474) baseStart_7154474 baseEnd_7154474 := by
    simpa [prefixWord, tailWord_7154474, baseEnd_7154474] using wordTrace_append hprefix tailTrace_7154474
  have hstable : (prefixWord ++ tailWord_7154474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154474).length < 2 ^ (prefixWord ++ tailWord_7154474).sum := by decide
  have hdescent : baseEnd_7154474 < baseStart_7154474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154478 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_7154478 : Nat := 118140960795 + 7154478 * 2 ^ 59
def prefixEnd_7154478 : Nat := 4983230072969 + 3 ^ 40 * 7154478 * 2
def baseEnd_7154478 : Nat := 1224562015339321435207387

theorem tailTrace_7154478 : CollatzResearch.WordTrace tailWord_7154478 prefixEnd_7154478 1224562015339321435207387 := by
  unfold tailWord_7154478
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618156271819446051009011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173963500116370378938714725 32618156271819446051009011)
  ·
    refine ⟨48927234407729169076513517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32618156271819446051009011 48927234407729169076513517)
    ·
      refine ⟨18347712902898438403692569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48927234407729169076513517 18347712902898438403692569)
      ·
        refine ⟨13760784677173828802769427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18347712902898438403692569 13760784677173828802769427)
        ·
          refine ⟨20641177015760743204154141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760784677173828802769427 20641177015760743204154141)
          ·
            refine ⟨7740441380910278701557803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20641177015760743204154141 7740441380910278701557803)
            ·
              refine ⟨11610662071365418052336705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740441380910278701557803 11610662071365418052336705)
              ·
                refine ⟨8707996553524063539252529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11610662071365418052336705 8707996553524063539252529)
                ·
                  refine ⟨6530997415143047654439397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707996553524063539252529 6530997415143047654439397)
                  ·
                    refine ⟨1224562015339321435207387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530997415143047654439397 1224562015339321435207387)
                    ·
                      rfl

theorem cell23_7154478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_7154478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154478 prefixEnd_7154478 := by exact prefixLift 7154478
  have htrace : WordTrace (prefixWord ++ tailWord_7154478) baseStart_7154478 baseEnd_7154478 := by
    simpa [prefixWord, tailWord_7154478, baseEnd_7154478] using wordTrace_append hprefix tailTrace_7154478
  have hstable : (prefixWord ++ tailWord_7154478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154478).length < 2 ^ (prefixWord ++ tailWord_7154478).sum := by decide
  have hdescent : baseEnd_7154478 < baseStart_7154478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154527 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_7154527 : Nat := 118140960795 + 7154527 * 2 ^ 59
def prefixEnd_7154527 : Nat := 4983230072969 + 3 ^ 40 * 7154527 * 2
def baseEnd_7154527 : Nat := 3673711206570034613909435

theorem tailTrace_7154527 : CollatzResearch.WordTrace tailWord_7154527 prefixEnd_7154527 3673711206570034613909435 := by
  unfold tailWord_7154527
  simp only [CollatzResearch.WordTrace]
  refine ⟨260947037351378049776605835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173964691567585366517737223 260947037351378049776605835)
  ·
    refine ⟨391420556027067074664908753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260947037351378049776605835 391420556027067074664908753)
    ·
      refine ⟨293565417020300305998681565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391420556027067074664908753 293565417020300305998681565)
      ·
        refine ⟨110087031382612614749505587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293565417020300305998681565 110087031382612614749505587)
        ·
          refine ⟨165130547073918922124258381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110087031382612614749505587 165130547073918922124258381)
          ·
            refine ⟨61923955152719595796596893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165130547073918922124258381 61923955152719595796596893)
            ·
              refine ⟨23221483182269848423723835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61923955152719595796596893 23221483182269848423723835)
              ·
                refine ⟨34832224773404772635585753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23221483182269848423723835 34832224773404772635585753)
                ·
                  refine ⟨26124168580053579476689315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34832224773404772635585753 26124168580053579476689315)
                  ·
                    refine ⟨39186252870080369215033973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26124168580053579476689315 39186252870080369215033973)
                    ·
                      refine ⟨3673711206570034613909435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39186252870080369215033973 3673711206570034613909435)
                      ·
                        rfl

theorem cell23_7154527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_7154527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154527 prefixEnd_7154527 := by exact prefixLift 7154527
  have htrace : WordTrace (prefixWord ++ tailWord_7154527) baseStart_7154527 baseEnd_7154527 := by
    simpa [prefixWord, tailWord_7154527, baseEnd_7154527] using wordTrace_append hprefix tailTrace_7154527
  have hstable : (prefixWord ++ tailWord_7154527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154527).length < 2 ^ (prefixWord ++ tailWord_7154527).sum := by decide
  have hdescent : baseEnd_7154527 < baseStart_7154527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154547 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 7]
def baseStart_7154547 : Nat := 118140960795 + 7154547 * 2 ^ 59
def prefixEnd_7154547 : Nat := 4983230072969 + 3 ^ 40 * 7154547 * 2
def baseEnd_7154547 : Nat := 408191275131458281739927

theorem tailTrace_7154547 : CollatzResearch.WordTrace tailWord_7154547 prefixEnd_7154547 408191275131458281739927 := by
  unfold tailWord_7154547
  simp only [CollatzResearch.WordTrace]
  refine ⟨260947766811305593192333895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173965177874203728794889263 260947766811305593192333895)
  ·
    refine ⟨391421650216958389788500843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260947766811305593192333895 391421650216958389788500843)
    ·
      refine ⟨587132475325437584682751265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391421650216958389788500843 587132475325437584682751265)
      ·
        refine ⟨440349356494078188512063449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587132475325437584682751265 440349356494078188512063449)
        ·
          refine ⟨330262017370558641384047587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440349356494078188512063449 330262017370558641384047587)
          ·
            refine ⟨495393026055837962076071381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330262017370558641384047587 495393026055837962076071381)
            ·
              refine ⟨11610774048183702236157923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 495393026055837962076071381 11610774048183702236157923)
              ·
                refine ⟨17416161072275553354236885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11610774048183702236157923 17416161072275553354236885)
                ·
                  refine ⟨408191275131458281739927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17416161072275553354236885 408191275131458281739927)
                  ·
                    rfl

theorem cell23_7154547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 7].length) (baseStart_7154547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154547 prefixEnd_7154547 := by exact prefixLift 7154547
  have htrace : WordTrace (prefixWord ++ tailWord_7154547) baseStart_7154547 baseEnd_7154547 := by
    simpa [prefixWord, tailWord_7154547, baseEnd_7154547] using wordTrace_append hprefix tailTrace_7154547
  have hstable : (prefixWord ++ tailWord_7154547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154547).length < 2 ^ (prefixWord ++ tailWord_7154547).sum := by decide
  have hdescent : baseEnd_7154547 < baseStart_7154547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154597 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_7154597 : Nat := 118140960795 + 7154597 * 2 ^ 59
def prefixEnd_7154597 : Nat := 4983230072969 + 3 ^ 40 * 7154597 * 2
def baseEnd_7154597 : Nat := 3673747150215849340034113

theorem tailTrace_7154597 : CollatzResearch.WordTrace tailWord_7154597 prefixEnd_7154597 3673747150215849340034113 := by
  unfold tailWord_7154597
  simp only [CollatzResearch.WordTrace]
  refine ⟨260949590461124451731654045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173966393640749634487769363 260949590461124451731654045)
  ·
    refine ⟨97856096422921669399370267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260949590461124451731654045 97856096422921669399370267)
    ·
      refine ⟨146784144634382504099055401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97856096422921669399370267 146784144634382504099055401)
      ·
        refine ⟨110088108475786878074291551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146784144634382504099055401 110088108475786878074291551)
        ·
          refine ⟨165132162713680317111437327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110088108475786878074291551 165132162713680317111437327)
          ·
            refine ⟨247698244070520475667155991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165132162713680317111437327 247698244070520475667155991)
            ·
              refine ⟨371547366105780713500733987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247698244070520475667155991 371547366105780713500733987)
              ·
                refine ⟨557321049158671070251100981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371547366105780713500733987 557321049158671070251100981)
                ·
                  refine ⟨52248848358625412836040717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557321049158671070251100981 52248848358625412836040717)
                  ·
                    refine ⟨19593318134484529813515269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52248848358625412836040717 19593318134484529813515269)
                    ·
                      refine ⟨3673747150215849340034113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19593318134484529813515269 3673747150215849340034113)
                      ·
                        rfl

theorem cell23_7154597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_7154597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154597 prefixEnd_7154597 := by exact prefixLift 7154597
  have htrace : WordTrace (prefixWord ++ tailWord_7154597) baseStart_7154597 baseEnd_7154597 := by
    simpa [prefixWord, tailWord_7154597, baseEnd_7154597] using wordTrace_append hprefix tailTrace_7154597
  have hstable : (prefixWord ++ tailWord_7154597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154597).length < 2 ^ (prefixWord ++ tailWord_7154597).sum := by decide
  have hdescent : baseEnd_7154597 < baseStart_7154597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154624 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 5, 4]
def baseStart_7154624 : Nat := 118140960795 + 7154624 * 2 ^ 59
def prefixEnd_7154624 : Nat := 4983230072969 + 3 ^ 40 * 7154624 * 2
def baseEnd_7154624 : Nat := 1224587004731173578132163

theorem tailTrace_7154624 : CollatzResearch.WordTrace tailWord_7154624 prefixEnd_7154624 1224587004731173578132163 := by
  unfold tailWord_7154624
  simp only [CollatzResearch.WordTrace]
  refine ⟨130475287616013317671443463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173967050154684423561924617 130475287616013317671443463)
  ·
    refine ⟨195712931424019976507165195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130475287616013317671443463 195712931424019976507165195)
    ·
      refine ⟨293569397136029964760747793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195712931424019976507165195 293569397136029964760747793)
      ·
        refine ⟨220177047852022473570560845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293569397136029964760747793 220177047852022473570560845)
        ·
          refine ⟨82566392944508427588960317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220177047852022473570560845 82566392944508427588960317)
          ·
            refine ⟨30962397354190660345860119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82566392944508427588960317 30962397354190660345860119)
            ·
              refine ⟨46443596031285990518790179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30962397354190660345860119 46443596031285990518790179)
              ·
                refine ⟨69665394046928985778185269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46443596031285990518790179 69665394046928985778185269)
                ·
                  refine ⟨6531130691899592416704869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69665394046928985778185269 6531130691899592416704869)
                  ·
                    refine ⟨1224587004731173578132163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531130691899592416704869 1224587004731173578132163)
                    ·
                      rfl

theorem cell23_7154624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_7154624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154624 prefixEnd_7154624 := by exact prefixLift 7154624
  have htrace : WordTrace (prefixWord ++ tailWord_7154624) baseStart_7154624 baseEnd_7154624 := by
    simpa [prefixWord, tailWord_7154624, baseEnd_7154624] using wordTrace_append hprefix tailTrace_7154624
  have hstable : (prefixWord ++ tailWord_7154624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154624).length < 2 ^ (prefixWord ++ tailWord_7154624).sum := by decide
  have hdescent : baseEnd_7154624 < baseStart_7154624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154627 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4]
def baseStart_7154627 : Nat := 118140960795 + 7154627 * 2 ^ 59
def prefixEnd_7154627 : Nat := 4983230072969 + 3 ^ 40 * 7154627 * 2
def baseEnd_7154627 : Nat := 3673762554635484222658975

theorem tailTrace_7154627 : CollatzResearch.WordTrace tailWord_7154627 prefixEnd_7154627 3673762554635484222658975 := by
  unfold tailWord_7154627
  simp only [CollatzResearch.WordTrace]
  refine ⟨260950684651015766855246135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173967123100677177903497423 260950684651015766855246135)
  ·
    refine ⟨391426026976523650282869203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260950684651015766855246135 391426026976523650282869203)
    ·
      refine ⟨587139040464785475424303805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391426026976523650282869203 587139040464785475424303805)
      ·
        refine ⟨220177140174294553284113927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587139040464785475424303805 220177140174294553284113927)
        ·
          refine ⟨330265710261441829926170891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220177140174294553284113927 330265710261441829926170891)
          ·
            refine ⟨495398565392162744889256337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330265710261441829926170891 495398565392162744889256337)
            ·
              refine ⟨371548924044122058666942253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495398565392162744889256337 371548924044122058666942253)
              ·
                refine ⟨139330846516545772000103345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371548924044122058666942253 139330846516545772000103345)
                ·
                  refine ⟨104498134887409329000077509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139330846516545772000103345 104498134887409329000077509)
                  ·
                    refine ⟨19593400291389249187514533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104498134887409329000077509 19593400291389249187514533)
                    ·
                      refine ⟨3673762554635484222658975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19593400291389249187514533 3673762554635484222658975)
                      ·
                        rfl

theorem cell23_7154627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_7154627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154627 prefixEnd_7154627 := by exact prefixLift 7154627
  have htrace : WordTrace (prefixWord ++ tailWord_7154627) baseStart_7154627 baseEnd_7154627 := by
    simpa [prefixWord, tailWord_7154627, baseEnd_7154627] using wordTrace_append hprefix tailTrace_7154627
  have hstable : (prefixWord ++ tailWord_7154627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154627).length < 2 ^ (prefixWord ++ tailWord_7154627).sum := by decide
  have hdescent : baseEnd_7154627 < baseStart_7154627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154644 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7154644 : Nat := 118140960795 + 7154644 * 2 ^ 59
def prefixEnd_7154644 : Nat := 4983230072969 + 3 ^ 40 * 7154644 * 2
def baseEnd_7154644 : Nat := 3673771283806610656146397

theorem tailTrace_7154644 : CollatzResearch.WordTrace tailWord_7154644 prefixEnd_7154644 3673771283806610656146397 := by
  unfold tailWord_7154644
  simp only [CollatzResearch.WordTrace]
  refine ⟨130475652345977089379307493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173967536461302785839076657 130475652345977089379307493)
  ·
    refine ⟨24464184814870704258620155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130475652345977089379307493 24464184814870704258620155)
    ·
      refine ⟨36696277222306056387930233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24464184814870704258620155 36696277222306056387930233)
      ·
        refine ⟨27522207916729542290947675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36696277222306056387930233 27522207916729542290947675)
        ·
          refine ⟨41283311875094313436421513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27522207916729542290947675 41283311875094313436421513)
          ·
            refine ⟨30962483906320735077316135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41283311875094313436421513 30962483906320735077316135)
            ·
              refine ⟨46443725859481102615974203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30962483906320735077316135 46443725859481102615974203)
              ·
                refine ⟨69665588789221653923961305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46443725859481102615974203 69665588789221653923961305)
                ·
                  refine ⟨52249191591916240442970979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69665588789221653923961305 52249191591916240442970979)
                  ·
                    refine ⟨78373787387874360664456469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52249191591916240442970979 78373787387874360664456469)
                    ·
                      refine ⟨3673771283806610656146397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78373787387874360664456469 3673771283806610656146397)
                      ·
                        rfl

theorem cell23_7154644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7154644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154644 prefixEnd_7154644 := by exact prefixLift 7154644
  have htrace : WordTrace (prefixWord ++ tailWord_7154644) baseStart_7154644 baseEnd_7154644 := by
    simpa [prefixWord, tailWord_7154644, baseEnd_7154644] using wordTrace_append hprefix tailTrace_7154644
  have hstable : (prefixWord ++ tailWord_7154644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154644).length < 2 ^ (prefixWord ++ tailWord_7154644).sum := by decide
  have hdescent : baseEnd_7154644 < baseStart_7154644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154658 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7154658 : Nat := 118140960795 + 7154658 * 2 ^ 59
def prefixEnd_7154658 : Nat := 4983230072969 + 3 ^ 40 * 7154658 * 2
def baseEnd_7154658 : Nat := 1224592824178591200457111

theorem tailTrace_7154658 : CollatzResearch.WordTrace tailWord_7154658 prefixEnd_7154658 1224592824178591200457111 := by
  unfold tailWord_7154658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65237953828475864787406157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173967876875935639433083085 65237953828475864787406157)
  ·
    refine ⟨24464232685678449295277309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65237953828475864787406157 24464232685678449295277309)
    ·
      refine ⟨9174087257129418485728991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24464232685678449295277309 9174087257129418485728991)
      ·
        refine ⟨13761130885694127728593487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174087257129418485728991 13761130885694127728593487)
        ·
          refine ⟨20641696328541191592890231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761130885694127728593487 20641696328541191592890231)
          ·
            refine ⟨30962544492811787389335347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20641696328541191592890231 30962544492811787389335347)
            ·
              refine ⟨46443816739217681084003021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30962544492811787389335347 46443816739217681084003021)
              ·
                refine ⟨17416431277206630406501133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46443816739217681084003021 17416431277206630406501133)
                ·
                  refine ⟨6531161728952486402437925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17416431277206630406501133 6531161728952486402437925)
                  ·
                    refine ⟨1224592824178591200457111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531161728952486402437925 1224592824178591200457111)
                    ·
                      rfl

theorem cell23_7154658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7154658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154658 prefixEnd_7154658 := by exact prefixLift 7154658
  have htrace : WordTrace (prefixWord ++ tailWord_7154658) baseStart_7154658 baseEnd_7154658 := by
    simpa [prefixWord, tailWord_7154658, baseEnd_7154658] using wordTrace_append hprefix tailTrace_7154658
  have hstable : (prefixWord ++ tailWord_7154658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154658).length < 2 ^ (prefixWord ++ tailWord_7154658).sum := by decide
  have hdescent : baseEnd_7154658 < baseStart_7154658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154671 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 6]
def baseStart_7154671 : Nat := 118140960795 + 7154671 * 2 ^ 59
def prefixEnd_7154671 : Nat := 4983230072969 + 3 ^ 40 * 7154671 * 2
def baseEnd_7154671 : Nat := 408198349753809116723197

theorem tailTrace_7154671 : CollatzResearch.WordTrace tailWord_7154671 prefixEnd_7154671 408198349753809116723197 := by
  unfold tailWord_7154671
  simp only [CollatzResearch.WordTrace]
  refine ⟨260952289462856362369847867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173968192975237574913231911 260952289462856362369847867)
  ·
    refine ⟨391428434194284543554771801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260952289462856362369847867 391428434194284543554771801)
    ·
      refine ⟨293571325645713407666078851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391428434194284543554771801 293571325645713407666078851)
      ·
        refine ⟨440356988468570111499118277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293571325645713407666078851 440356988468570111499118277)
        ·
          refine ⟨82566935337856895906084677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440356988468570111499118277 82566935337856895906084677)
          ·
            refine ⟨15481300375848167982390877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82566935337856895906084677 15481300375848167982390877)
            ·
              refine ⟨5805487640943062993396579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15481300375848167982390877 5805487640943062993396579)
              ·
                refine ⟨8708231461414594490094869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805487640943062993396579 8708231461414594490094869)
                ·
                  refine ⟨408198349753809116723197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8708231461414594490094869 408198349753809116723197)
                  ·
                    rfl

theorem cell23_7154671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 6].length) (baseStart_7154671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154671 prefixEnd_7154671 := by exact prefixLift 7154671
  have htrace : WordTrace (prefixWord ++ tailWord_7154671) baseStart_7154671 baseEnd_7154671 := by
    simpa [prefixWord, tailWord_7154671, baseEnd_7154671] using wordTrace_append hprefix tailTrace_7154671
  have hstable : (prefixWord ++ tailWord_7154671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154671).length < 2 ^ (prefixWord ++ tailWord_7154671).sum := by decide
  have hdescent : baseEnd_7154671 < baseStart_7154671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154681 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 3]
def baseStart_7154681 : Nat := 118140960795 + 7154681 * 2 ^ 59
def prefixEnd_7154681 : Nat := 4983230072969 + 3 ^ 40 * 7154681 * 2
def baseEnd_7154681 : Nat := 3673790282590827011383727

theorem tailTrace_7154681 : CollatzResearch.WordTrace tailWord_7154681 prefixEnd_7154681 3673790282590827011383727 := by
  unfold tailWord_7154681
  simp only [CollatzResearch.WordTrace]
  refine ⟨260952654192820134077711897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173968436128546756051807931 260952654192820134077711897)
  ·
    refine ⟨195714490644615100558283923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260952654192820134077711897 195714490644615100558283923)
    ·
      refine ⟨293571735966922650837425885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195714490644615100558283923 293571735966922650837425885)
      ·
        refine ⟨110089400987595994064034707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293571735966922650837425885 110089400987595994064034707)
        ·
          refine ⟨165134101481393991096052061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110089400987595994064034707 165134101481393991096052061)
          ·
            refine ⟨61925288055522746661019523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165134101481393991096052061 61925288055522746661019523)
            ·
              refine ⟨92887932083284119991529285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61925288055522746661019523 92887932083284119991529285)
              ·
                refine ⟨17416487265615772498411741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92887932083284119991529285 17416487265615772498411741)
                ·
                  refine ⟨6531182724605914686904403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17416487265615772498411741 6531182724605914686904403)
                  ·
                    refine ⟨9796774086908872030356605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6531182724605914686904403 9796774086908872030356605)
                    ·
                      refine ⟨3673790282590827011383727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9796774086908872030356605 3673790282590827011383727)
                      ·
                        rfl

theorem cell23_7154681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_7154681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154681 prefixEnd_7154681 := by exact prefixLift 7154681
  have htrace : WordTrace (prefixWord ++ tailWord_7154681) baseStart_7154681 baseEnd_7154681 := by
    simpa [prefixWord, tailWord_7154681, baseEnd_7154681] using wordTrace_append hprefix tailTrace_7154681
  have hstable : (prefixWord ++ tailWord_7154681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154681).length < 2 ^ (prefixWord ++ tailWord_7154681).sum := by decide
  have hdescent : baseEnd_7154681 < baseStart_7154681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154731 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 2, 4]
def baseStart_7154731 : Nat := 118140960795 + 7154731 * 2 ^ 59
def prefixEnd_7154731 : Nat := 4983230072969 + 3 ^ 40 * 7154731 * 2
def baseEnd_7154731 : Nat := 1224605318874517271919499

theorem tailTrace_7154731 : CollatzResearch.WordTrace tailWord_7154731 prefixEnd_7154731 1224605318874517271919499 := by
  unfold tailWord_7154731
  simp only [CollatzResearch.WordTrace]
  refine ⟨260954477842638992617032047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173969651895092661744688031 260954477842638992617032047)
  ·
    refine ⟨391431716763958488925548071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260954477842638992617032047 391431716763958488925548071)
    ·
      refine ⟨587147575145937733388322107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391431716763958488925548071 587147575145937733388322107)
      ·
        refine ⟨880721362718906600082483161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587147575145937733388322107 880721362718906600082483161)
        ·
          refine ⟨660541022039179950061862371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880721362718906600082483161 660541022039179950061862371)
          ·
            refine ⟨990811533058769925092793557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660541022039179950061862371 990811533058769925092793557)
            ·
              refine ⟨23222145306064920119362349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 990811533058769925092793557 23222145306064920119362349)
              ·
                refine ⟨8708304489774345044760881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23222145306064920119362349 8708304489774345044760881)
                ·
                  refine ⟨6531228367330758783570661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8708304489774345044760881 6531228367330758783570661)
                  ·
                    refine ⟨1224605318874517271919499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531228367330758783570661 1224605318874517271919499)
                    ·
                      rfl

theorem cell23_7154731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 4].length) (baseStart_7154731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154731 prefixEnd_7154731 := by exact prefixLift 7154731
  have htrace : WordTrace (prefixWord ++ tailWord_7154731) baseStart_7154731 baseEnd_7154731 := by
    simpa [prefixWord, tailWord_7154731, baseEnd_7154731] using wordTrace_append hprefix tailTrace_7154731
  have hstable : (prefixWord ++ tailWord_7154731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154731).length < 2 ^ (prefixWord ++ tailWord_7154731).sum := by decide
  have hdescent : baseEnd_7154731 < baseStart_7154731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154738 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_7154738 : Nat := 118140960795 + 7154738 * 2 ^ 59
def prefixEnd_7154738 : Nat := 4983230072969 + 3 ^ 40 * 7154738 * 2
def baseEnd_7154738 : Nat := 3673819550988133288370965

theorem tailTrace_7154738 : CollatzResearch.WordTrace tailWord_7154738 prefixEnd_7154738 3673819550988133288370965 := by
  unfold tailWord_7154738
  simp only [CollatzResearch.WordTrace]
  refine ⟨65238683288403408203134217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173969822102409088541691245 65238683288403408203134217)
  ·
    refine ⟨48929012466302556152350663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65238683288403408203134217 48929012466302556152350663)
    ·
      refine ⟨73393518699453834228525995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48929012466302556152350663 73393518699453834228525995)
      ·
        refine ⟨110090278049180751342788993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73393518699453834228525995 110090278049180751342788993)
        ·
          refine ⟨82567708536885563507091745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110090278049180751342788993 82567708536885563507091745)
          ·
            refine ⟨61925781402664172630318809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82567708536885563507091745 61925781402664172630318809)
            ·
              refine ⟨46444336051998129472739107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61925781402664172630318809 46444336051998129472739107)
              ·
                refine ⟨69666504077997194209108661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46444336051998129472739107 69666504077997194209108661)
                ·
                  refine ⟨6531234757312236957103937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69666504077997194209108661 6531234757312236957103937)
                  ·
                    refine ⟨4898426067984177717827953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6531234757312236957103937 4898426067984177717827953)
                    ·
                      refine ⟨3673819550988133288370965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898426067984177717827953 3673819550988133288370965)
                      ·
                        rfl

theorem cell23_7154738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_7154738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154738 prefixEnd_7154738 := by exact prefixLift 7154738
  have htrace : WordTrace (prefixWord ++ tailWord_7154738) baseStart_7154738 baseEnd_7154738 := by
    simpa [prefixWord, tailWord_7154738, baseEnd_7154738] using wordTrace_append hprefix tailTrace_7154738
  have hstable : (prefixWord ++ tailWord_7154738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154738).length < 2 ^ (prefixWord ++ tailWord_7154738).sum := by decide
  have hdescent : baseEnd_7154738 < baseStart_7154738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154744 : List Nat := [2, 1, 2, 1, 5, 1, 2, 9]
def baseStart_7154744 : Nat := 118140960795 + 7154744 * 2 ^ 59
def prefixEnd_7154744 : Nat := 4983230072969 + 3 ^ 40 * 7154744 * 2
def baseEnd_7154744 : Nat := 136067504884150380181331

theorem tailTrace_7154744 : CollatzResearch.WordTrace tailWord_7154744 prefixEnd_7154744 136067504884150380181331 := by
  unfold tailWord_7154744
  simp only [CollatzResearch.WordTrace]
  refine ⟨130477475995795947918627643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173969967994394597224836857 130477475995795947918627643)
  ·
    refine ⟨195716213993693921877941465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130477475995795947918627643 195716213993693921877941465)
    ·
      refine ⟨146787160495270441408456099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195716213993693921877941465 146787160495270441408456099)
      ·
        refine ⟨220180740742905662112684149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146787160495270441408456099 220180740742905662112684149)
        ·
          refine ⟨20641944444647405823064139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220180740742905662112684149 20641944444647405823064139)
          ·
            refine ⟨30962916666971108734596209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20641944444647405823064139 30962916666971108734596209)
            ·
              refine ⟨23222187500228331550947157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30962916666971108734596209 23222187500228331550947157)
              ·
                refine ⟨136067504884150380181331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23222187500228331550947157 136067504884150380181331)
                ·
                  rfl

theorem cell23_7154744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 9].length) (baseStart_7154744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154744 prefixEnd_7154744 := by exact prefixLift 7154744
  have htrace : WordTrace (prefixWord ++ tailWord_7154744) baseStart_7154744 baseEnd_7154744 := by
    simpa [prefixWord, tailWord_7154744, baseEnd_7154744] using wordTrace_append hprefix tailTrace_7154744
  have hstable : (prefixWord ++ tailWord_7154744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154744).length < 2 ^ (prefixWord ++ tailWord_7154744).sum := by decide
  have hdescent : baseEnd_7154744 < baseStart_7154744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154755 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 1, 2, 2]
def baseStart_7154755 : Nat := 118140960795 + 7154755 * 2 ^ 59
def prefixEnd_7154755 : Nat := 4983230072969 + 3 ^ 40 * 7154755 * 2
def baseEnd_7154755 : Nat := 3673828280159259721858387

theorem tailTrace_7154755 : CollatzResearch.WordTrace tailWord_7154755 prefixEnd_7154755 3673828280159259721858387 := by
  unfold tailWord_7154755
  simp only [CollatzResearch.WordTrace]
  refine ⟨260955353194552044715905719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173970235463034696477270479 260955353194552044715905719)
  ·
    refine ⟨391433029791828067073858579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260955353194552044715905719 391433029791828067073858579)
    ·
      refine ⟨587149544687742100610787869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391433029791828067073858579 587149544687742100610787869)
      ·
        refine ⟨220181079257903287729045451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 587149544687742100610787869 220181079257903287729045451)
        ·
          refine ⟨330271618886854931593568177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220181079257903287729045451 330271618886854931593568177)
          ·
            refine ⟨247703714165141198695176133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330271618886854931593568177 247703714165141198695176133)
            ·
              refine ⟨46444446405963974755345525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247703714165141198695176133 46444446405963974755345525)
              ·
                refine ⟨4354166850559122633313643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46444446405963974755345525 4354166850559122633313643)
                ·
                  refine ⟨6531250275838683949970465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354166850559122633313643 6531250275838683949970465)
                  ·
                    refine ⟨4898437706879012962477849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6531250275838683949970465 4898437706879012962477849)
                    ·
                      refine ⟨3673828280159259721858387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898437706879012962477849 3673828280159259721858387)
                      ·
                        rfl

theorem cell23_7154755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_7154755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154755 prefixEnd_7154755 := by exact prefixLift 7154755
  have htrace : WordTrace (prefixWord ++ tailWord_7154755) baseStart_7154755 baseEnd_7154755 := by
    simpa [prefixWord, tailWord_7154755, baseEnd_7154755] using wordTrace_append hprefix tailTrace_7154755
  have hstable : (prefixWord ++ tailWord_7154755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154755).length < 2 ^ (prefixWord ++ tailWord_7154755).sum := by decide
  have hdescent : baseEnd_7154755 < baseStart_7154755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154765 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_7154765 : Nat := 118140960795 + 7154765 * 2 ^ 59
def prefixEnd_7154765 : Nat := 4983230072969 + 3 ^ 40 * 7154765 * 2
def baseEnd_7154765 : Nat := 1224611138321934894244447

theorem tailTrace_7154765 : CollatzResearch.WordTrace tailWord_7154765 prefixEnd_7154765 1224611138321934894244447 := by
  unfold tailWord_7154765
  simp only [CollatzResearch.WordTrace]
  refine ⟨260955717924515816423769749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173970478616343877615846499 260955717924515816423769749)
  ·
    refine ⟨12232299277711678894864207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260955717924515816423769749 12232299277711678894864207)
    ·
      refine ⟨18348448916567518342296311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12232299277711678894864207 18348448916567518342296311)
      ·
        refine ⟨27522673374851277513444467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18348448916567518342296311 27522673374851277513444467)
        ·
          refine ⟨41284010062276916270166701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27522673374851277513444467 41284010062276916270166701)
          ·
            refine ⟨15481503773353843601312513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41284010062276916270166701 15481503773353843601312513)
            ·
              refine ⟨11611127830015382700984385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15481503773353843601312513 11611127830015382700984385)
              ·
                refine ⟨8708345872511537025738289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11611127830015382700984385 8708345872511537025738289)
                ·
                  refine ⟨6531259404383652769303717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8708345872511537025738289 6531259404383652769303717)
                  ·
                    refine ⟨1224611138321934894244447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531259404383652769303717 1224611138321934894244447)
                    ·
                      rfl

theorem cell23_7154765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_7154765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154765 prefixEnd_7154765 := by exact prefixLift 7154765
  have htrace : WordTrace (prefixWord ++ tailWord_7154765) baseStart_7154765 baseEnd_7154765 := by
    simpa [prefixWord, tailWord_7154765, baseEnd_7154765] using wordTrace_append hprefix tailTrace_7154765
  have hstable : (prefixWord ++ tailWord_7154765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154765).length < 2 ^ (prefixWord ++ tailWord_7154765).sum := by decide
  have hdescent : baseEnd_7154765 < baseStart_7154765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154782 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_7154782 : Nat := 118140960795 + 7154782 * 2 ^ 59
def prefixEnd_7154782 : Nat := 4983230072969 + 3 ^ 40 * 7154782 * 2
def baseEnd_7154782 : Nat := 1224614048045643705406921

theorem tailTrace_7154782 : CollatzResearch.WordTrace tailWord_7154782 prefixEnd_7154782 1224614048045643705406921 := by
  unfold tailWord_7154782
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619542245681778540892325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173970891976969485551425733 32619542245681778540892325)
  ·
    refine ⟨6116164171065333476417311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32619542245681778540892325 6116164171065333476417311)
    ·
      refine ⟨9174246256598000214625967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116164171065333476417311 9174246256598000214625967)
      ·
        refine ⟨13761369384897000321938951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174246256598000214625967 13761369384897000321938951)
        ·
          refine ⟨20642054077345500482908427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761369384897000321938951 20642054077345500482908427)
          ·
            refine ⟨30963081116018250724362641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20642054077345500482908427 30963081116018250724362641)
            ·
              refine ⟨23222310837013688043271981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30963081116018250724362641 23222310837013688043271981)
              ·
                refine ⟨8708366563880133016226993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23222310837013688043271981 8708366563880133016226993)
                ·
                  refine ⟨6531274922910099762170245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8708366563880133016226993 6531274922910099762170245)
                  ·
                    refine ⟨1224614048045643705406921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531274922910099762170245 1224614048045643705406921)
                    ·
                      rfl

theorem cell23_7154782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_7154782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154782 prefixEnd_7154782 := by exact prefixLift 7154782
  have htrace : WordTrace (prefixWord ++ tailWord_7154782) baseStart_7154782 baseEnd_7154782 := by
    simpa [prefixWord, tailWord_7154782, baseEnd_7154782] using wordTrace_append hprefix tailTrace_7154782
  have hstable : (prefixWord ++ tailWord_7154782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154782).length < 2 ^ (prefixWord ++ tailWord_7154782).sum := by decide
  have hdescent : baseEnd_7154782 < baseStart_7154782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154938 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_7154938 : Nat := 118140960795 + 7154938 * 2 ^ 59
def prefixEnd_7154938 : Nat := 4983230072969 + 3 ^ 40 * 7154938 * 2
def baseEnd_7154938 : Nat := 3673922247119032505870045

theorem tailTrace_7154938 : CollatzResearch.WordTrace tailWord_7154938 prefixEnd_7154938 3673922247119032505870045 := by
  unfold tailWord_7154938
  simp only [CollatzResearch.WordTrace]
  refine ⟨65240506938222266742454367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173974685168592711313211645 65240506938222266742454367)
  ·
    refine ⟨97860760407333400113681551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65240506938222266742454367 97860760407333400113681551)
    ·
      refine ⟨146791140611000100170522327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97860760407333400113681551 146791140611000100170522327)
      ·
        refine ⟨220186710916500150255783491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146791140611000100170522327 220186710916500150255783491)
        ·
          refine ⟨330280066374750225383675237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220186710916500150255783491 330280066374750225383675237)
          ·
            refine ⟨61927512445265667259439107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330280066374750225383675237 61927512445265667259439107)
            ·
              refine ⟨92891268667898500889158661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61927512445265667259439107 92891268667898500889158661)
              ·
                refine ⟨17417112875230968916717249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92891268667898500889158661 17417112875230968916717249)
                ·
                  refine ⟨13062834656423226687537937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17417112875230968916717249 13062834656423226687537937)
                  ·
                    refine ⟨9797125992317420015653453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13062834656423226687537937 9797125992317420015653453)
                    ·
                      refine ⟨3673922247119032505870045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9797125992317420015653453 3673922247119032505870045)
                      ·
                        rfl

theorem cell23_7154938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_7154938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154938 prefixEnd_7154938 := by exact prefixLift 7154938
  have htrace : WordTrace (prefixWord ++ tailWord_7154938) baseStart_7154938 baseEnd_7154938 := by
    simpa [prefixWord, tailWord_7154938, baseEnd_7154938] using wordTrace_append hprefix tailTrace_7154938
  have hstable : (prefixWord ++ tailWord_7154938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154938).length < 2 ^ (prefixWord ++ tailWord_7154938).sum := by decide
  have hdescent : baseEnd_7154938 < baseStart_7154938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7154958 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_7154958 : Nat := 118140960795 + 7154958 * 2 ^ 59
def prefixEnd_7154958 : Nat := 4983230072969 + 3 ^ 40 * 7154958 * 2
def baseEnd_7154958 : Nat := 408214724081346936402217

theorem tailTrace_7154958 : CollatzResearch.WordTrace tailWord_7154958 prefixEnd_7154958 408214724081346936402217 := by
  unfold tailWord_7154958
  simp only [CollatzResearch.WordTrace]
  refine ⟨32620344651602076298193191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173975171475211073590363685 32620344651602076298193191)
  ·
    refine ⟨48930516977403114447289787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32620344651602076298193191 48930516977403114447289787)
    ·
      refine ⟨73395775466104671670934681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48930516977403114447289787 73395775466104671670934681)
      ·
        refine ⟨55046831599578503753201011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73395775466104671670934681 55046831599578503753201011)
        ·
          refine ⟨82570247399367755629801517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55046831599578503753201011 82570247399367755629801517)
          ·
            refine ⟨30963842774762908361175569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82570247399367755629801517 30963842774762908361175569)
            ·
              refine ⟨23222882081072181270881677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30963842774762908361175569 23222882081072181270881677)
              ·
                refine ⟨8708580780402067976580629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23222882081072181270881677 8708580780402067976580629)
                ·
                  refine ⟨408214724081346936402217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8708580780402067976580629 408214724081346936402217)
                  ·
                    rfl

theorem cell23_7154958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_7154958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7154958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7154958 prefixEnd_7154958 := by exact prefixLift 7154958
  have htrace : WordTrace (prefixWord ++ tailWord_7154958) baseStart_7154958 baseEnd_7154958 := by
    simpa [prefixWord, tailWord_7154958, baseEnd_7154958] using wordTrace_append hprefix tailTrace_7154958
  have hstable : (prefixWord ++ tailWord_7154958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7154958).length < 2 ^ (prefixWord ++ tailWord_7154958).sum := by decide
  have hdescent : baseEnd_7154958 < baseStart_7154958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7154958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155002 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3]
def baseStart_7155002 : Nat := 118140960795 + 7155002 * 2 ^ 59
def prefixEnd_7155002 : Nat := 4983230072969 + 3 ^ 40 * 7155002 * 2
def baseEnd_7155002 : Nat := 3673955109880920255469751

theorem tailTrace_7155002 : CollatzResearch.WordTrace tailWord_7155002 prefixEnd_7155002 3673955109880920255469751 := by
  unfold tailWord_7155002
  simp only [CollatzResearch.WordTrace]
  refine ⟨65241090506164301475036815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173976241349771470600098173 65241090506164301475036815)
  ·
    refine ⟨97861635759246452212555223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65241090506164301475036815 97861635759246452212555223)
    ·
      refine ⟨146792453638869678318832835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97861635759246452212555223 146792453638869678318832835)
      ·
        refine ⟨220188680458304517478249253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146792453638869678318832835 220188680458304517478249253)
        ·
          refine ⟨41285377585932097027171735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220188680458304517478249253 41285377585932097027171735)
          ·
            refine ⟨61928066378898145540757603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41285377585932097027171735 61928066378898145540757603)
            ·
              refine ⟨92892099568347218311136405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61928066378898145540757603 92892099568347218311136405)
              ·
                refine ⟨4354317167266275858334519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92892099568347218311136405 4354317167266275858334519)
                ·
                  refine ⟨6531475750899413787501779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354317167266275858334519 6531475750899413787501779)
                  ·
                    refine ⟨9797213626349120681252669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6531475750899413787501779 9797213626349120681252669)
                    ·
                      refine ⟨3673955109880920255469751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9797213626349120681252669 3673955109880920255469751)
                      ·
                        rfl

theorem cell23_7155002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_7155002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155002 prefixEnd_7155002 := by exact prefixLift 7155002
  have htrace : WordTrace (prefixWord ++ tailWord_7155002) baseStart_7155002 baseEnd_7155002 := by
    simpa [prefixWord, tailWord_7155002, baseEnd_7155002] using wordTrace_append hprefix tailTrace_7155002
  have hstable : (prefixWord ++ tailWord_7155002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155002).length < 2 ^ (prefixWord ++ tailWord_7155002).sum := by decide
  have hdescent : baseEnd_7155002 < baseStart_7155002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155012 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7155012 : Nat := 118140960795 + 7155012 * 2 ^ 59
def prefixEnd_7155012 : Nat := 4983230072969 + 3 ^ 40 * 7155012 * 2
def baseEnd_7155012 : Nat := 3673960244687465216344705

theorem tailTrace_7155012 : CollatzResearch.WordTrace tailWord_7155012 prefixEnd_7155012 3673960244687465216344705 := by
  unfold tailWord_7155012
  simp only [CollatzResearch.WordTrace]
  refine ⟨130482363377310488804005645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173976484503080651738674193 130482363377310488804005645)
  ·
    refine ⟨48930886266491433301502117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130482363377310488804005645 48930886266491433301502117)
    ·
      refine ⟨9174541174967143744031647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48930886266491433301502117 9174541174967143744031647)
      ·
        refine ⟨13761811762450715616047471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174541174967143744031647 13761811762450715616047471)
        ·
          refine ⟨20642717643676073424071207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13761811762450715616047471 20642717643676073424071207)
          ·
            refine ⟨30964076465514110136106811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20642717643676073424071207 30964076465514110136106811)
            ·
              refine ⟨46446114698271165204160217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30964076465514110136106811 46446114698271165204160217)
              ·
                refine ⟨34834586023703373903120163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46446114698271165204160217 34834586023703373903120163)
                ·
                  refine ⟨52251879035555060854680245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34834586023703373903120163 52251879035555060854680245)
                  ·
                    refine ⟨4898613659583286955126273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52251879035555060854680245 4898613659583286955126273)
                    ·
                      refine ⟨3673960244687465216344705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898613659583286955126273 3673960244687465216344705)
                      ·
                        rfl

theorem cell23_7155012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7155012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155012 prefixEnd_7155012 := by exact prefixLift 7155012
  have htrace : WordTrace (prefixWord ++ tailWord_7155012) baseStart_7155012 baseEnd_7155012 := by
    simpa [prefixWord, tailWord_7155012, baseEnd_7155012] using wordTrace_append hprefix tailTrace_7155012
  have hstable : (prefixWord ++ tailWord_7155012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155012).length < 2 ^ (prefixWord ++ tailWord_7155012).sum := by decide
  have hdescent : baseEnd_7155012 < baseStart_7155012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155025 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_7155025 : Nat := 118140960795 + 7155025 * 2 ^ 59
def prefixEnd_7155025 : Nat := 4983230072969 + 3 ^ 40 * 7155025 * 2
def baseEnd_7155025 : Nat := 3673966919935973665482145

theorem tailTrace_7155025 : CollatzResearch.WordTrace tailWord_7155025 prefixEnd_7155025 3673966919935973665482145 := by
  unfold tailWord_7155025
  simp only [CollatzResearch.WordTrace]
  refine ⟨260965200903573880828234529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173976800602382587218823019 260965200903573880828234529)
  ·
    refine ⟨195723900677680410621175897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260965200903573880828234529 195723900677680410621175897)
    ·
      refine ⟨146792925508260307965881923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195723900677680410621175897 146792925508260307965881923)
      ·
        refine ⟨220189388262390461948822885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146792925508260307965881923 220189388262390461948822885)
        ·
          refine ⟨41285510299198211615404291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220189388262390461948822885 41285510299198211615404291)
          ·
            refine ⟨61928265448797317423106437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41285510299198211615404291 61928265448797317423106437)
            ·
              refine ⟨11611549771649497016832457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61928265448797317423106437 11611549771649497016832457)
              ·
                refine ⟨8708662328737122762624343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11611549771649497016832457 8708662328737122762624343)
                ·
                  refine ⟨13062993493105684143936515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8708662328737122762624343 13062993493105684143936515)
                  ·
                    refine ⟨19594490239658526215904773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13062993493105684143936515 19594490239658526215904773)
                    ·
                      refine ⟨3673966919935973665482145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19594490239658526215904773 3673966919935973665482145)
                      ·
                        rfl

theorem cell23_7155025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_7155025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155025 prefixEnd_7155025 := by exact prefixLift 7155025
  have htrace : WordTrace (prefixWord ++ tailWord_7155025) baseStart_7155025 baseEnd_7155025 := by
    simpa [prefixWord, tailWord_7155025, baseEnd_7155025] using wordTrace_append hprefix tailTrace_7155025
  have hstable : (prefixWord ++ tailWord_7155025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155025).length < 2 ^ (prefixWord ++ tailWord_7155025).sum := by decide
  have hdescent : baseEnd_7155025 < baseStart_7155025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155028 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_7155028 : Nat := 118140960795 + 7155028 * 2 ^ 59
def prefixEnd_7155028 : Nat := 4983230072969 + 3 ^ 40 * 7155028 * 2
def baseEnd_7155028 : Nat := 3673968460377937153744631

theorem tailTrace_7155028 : CollatzResearch.WordTrace tailWord_7155028 prefixEnd_7155028 3673968460377937153744631 := by
  unfold tailWord_7155028
  simp only [CollatzResearch.WordTrace]
  refine ⟨130482655161281506170296869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173976873548375341560395825 130482655161281506170296869)
  ·
    refine ⟨24465497842740282406930663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130482655161281506170296869 24465497842740282406930663)
    ·
      refine ⟨36698246764110423610395995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24465497842740282406930663 36698246764110423610395995)
      ·
        refine ⟨55047370146165635415593993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36698246764110423610395995 55047370146165635415593993)
        ·
          refine ⟨41285527609624226561695495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55047370146165635415593993 41285527609624226561695495)
          ·
            refine ⟨61928291414436339842543243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41285527609624226561695495 61928291414436339842543243)
            ·
              refine ⟨92892437121654509763814865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61928291414436339842543243 92892437121654509763814865)
              ·
                refine ⟨69669327841240882322861149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92892437121654509763814865 69669327841240882322861149)
                ·
                  refine ⟨26125997940465330871072931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69669327841240882322861149 26125997940465330871072931)
                  ·
                    refine ⟨39188996910697996306609397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26125997940465330871072931 39188996910697996306609397)
                    ·
                      refine ⟨3673968460377937153744631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39188996910697996306609397 3673968460377937153744631)
                      ·
                        rfl

theorem cell23_7155028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_7155028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155028 prefixEnd_7155028 := by exact prefixLift 7155028
  have htrace : WordTrace (prefixWord ++ tailWord_7155028) baseStart_7155028 baseEnd_7155028 := by
    simpa [prefixWord, tailWord_7155028, baseEnd_7155028] using wordTrace_append hprefix tailTrace_7155028
  have hstable : (prefixWord ++ tailWord_7155028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155028).length < 2 ^ (prefixWord ++ tailWord_7155028).sum := by decide
  have hdescent : baseEnd_7155028 < baseStart_7155028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155030 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7155030 : Nat := 118140960795 + 7155030 * 2 ^ 59
def prefixEnd_7155030 : Nat := 4983230072969 + 3 ^ 40 * 7155030 * 2
def baseEnd_7155030 : Nat := 1224656495779748715306541

theorem tailTrace_7155030 : CollatzResearch.WordTrace tailWord_7155030 prefixEnd_7155030 1224656495779748715306541 := by
  unfold tailWord_7155030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16310336454284735417635409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173976922179037177788111029 16310336454284735417635409)
  ·
    refine ⟨12232752340713551563226557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16310336454284735417635409 12232752340713551563226557)
    ·
      refine ⟨4587282127767581836209959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12232752340713551563226557 4587282127767581836209959)
      ·
        refine ⟨6880923191651372754314939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587282127767581836209959 6880923191651372754314939)
        ·
          refine ⟨10321384787477059131472409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6880923191651372754314939 10321384787477059131472409)
          ·
            refine ⟨7741038590607794348604307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10321384787477059131472409 7741038590607794348604307)
            ·
              refine ⟨11611557885911691522906461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741038590607794348604307 11611557885911691522906461)
              ·
                refine ⟨4354334207216884321089923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11611557885911691522906461 4354334207216884321089923)
                ·
                  refine ⟨6531501310825326481634885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354334207216884321089923 6531501310825326481634885)
                  ·
                    refine ⟨1224656495779748715306541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531501310825326481634885 1224656495779748715306541)
                    ·
                      rfl

theorem cell23_7155030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7155030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155030 prefixEnd_7155030 := by exact prefixLift 7155030
  have htrace : WordTrace (prefixWord ++ tailWord_7155030) baseStart_7155030 baseEnd_7155030 := by
    simpa [prefixWord, tailWord_7155030, baseEnd_7155030] using wordTrace_append hprefix tailTrace_7155030
  have hstable : (prefixWord ++ tailWord_7155030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155030).length < 2 ^ (prefixWord ++ tailWord_7155030).sum := by decide
  have hdescent : baseEnd_7155030 < baseStart_7155030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155045 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_7155045 : Nat := 118140960795 + 7155045 * 2 ^ 59
def prefixEnd_7155045 : Nat := 4983230072969 + 3 ^ 40 * 7155045 * 2
def baseEnd_7155045 : Nat := 3673977189549063587232053

theorem tailTrace_7155045 : CollatzResearch.WordTrace tailWord_7155045 prefixEnd_7155045 3673977189549063587232053 := by
  unfold tailWord_7155045
  simp only [CollatzResearch.WordTrace]
  refine ⟨260965930363501424243962589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173977286909000949495975059 260965930363501424243962589)
  ·
    refine ⟨97862223886313034091485971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260965930363501424243962589 97862223886313034091485971)
    ·
      refine ⟨146793335829469551137228957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97862223886313034091485971 146793335829469551137228957)
      ·
        refine ⟨55047500936051081676460859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146793335829469551137228957 55047500936051081676460859)
        ·
          refine ⟨82571251404076622514691289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55047500936051081676460859 82571251404076622514691289)
          ·
            refine ⟨61928438553057466886018467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82571251404076622514691289 61928438553057466886018467)
            ·
              refine ⟨92892657829586200329027701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61928438553057466886018467 92892657829586200329027701)
              ·
                refine ⟨8708686671523706280846347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92892657829586200329027701 8708686671523706280846347)
                ·
                  refine ⟨13063030007285559421269521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8708686671523706280846347 13063030007285559421269521)
                  ·
                    refine ⟨9797272505464169565952141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13063030007285559421269521 9797272505464169565952141)
                    ·
                      refine ⟨3673977189549063587232053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9797272505464169565952141 3673977189549063587232053)
                      ·
                        rfl

theorem cell23_7155045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_7155045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155045 prefixEnd_7155045 := by exact prefixLift 7155045
  have htrace : WordTrace (prefixWord ++ tailWord_7155045) baseStart_7155045 baseEnd_7155045 := by
    simpa [prefixWord, tailWord_7155045, baseEnd_7155045] using wordTrace_append hprefix tailTrace_7155045
  have hstable : (prefixWord ++ tailWord_7155045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155045).length < 2 ^ (prefixWord ++ tailWord_7155045).sum := by decide
  have hdescent : baseEnd_7155045 < baseStart_7155045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155051 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_7155051 : Nat := 118140960795 + 7155051 * 2 ^ 59
def prefixEnd_7155051 : Nat := 4983230072969 + 3 ^ 40 * 7155051 * 2
def baseEnd_7155051 : Nat := 3673980270432990563757025

theorem tailTrace_7155051 : CollatzResearch.WordTrace tailWord_7155051 prefixEnd_7155051 3673980270432990563757025 := by
  unfold tailWord_7155051
  simp only [CollatzResearch.WordTrace]
  refine ⟨260966149201479687268681007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173977432800986458179120671 260966149201479687268681007)
  ·
    refine ⟨391449223802219530903021511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260966149201479687268681007 391449223802219530903021511)
    ·
      refine ⟨587173835703329296354532267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391449223802219530903021511 587173835703329296354532267)
      ·
        refine ⟨880760753554993944531798401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587173835703329296354532267 880760753554993944531798401)
        ·
          refine ⟨660570565166245458398848801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880760753554993944531798401 660570565166245458398848801)
          ·
            refine ⟨495427923874684093799136601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660570565166245458398848801 495427923874684093799136601)
            ·
              refine ⟨371570942906013070349352451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495427923874684093799136601 371570942906013070349352451)
              ·
                refine ⟨557356414359019605524028677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371570942906013070349352451 557356414359019605524028677)
                ·
                  refine ⟨104504327692316176035755377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557356414359019605524028677 104504327692316176035755377)
                  ·
                    refine ⟨78378245769237132026816533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104504327692316176035755377 78378245769237132026816533)
                    ·
                      refine ⟨3673980270432990563757025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78378245769237132026816533 3673980270432990563757025)
                      ·
                        rfl

theorem cell23_7155051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_7155051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155051 prefixEnd_7155051 := by exact prefixLift 7155051
  have htrace : WordTrace (prefixWord ++ tailWord_7155051) baseStart_7155051 baseEnd_7155051 := by
    simpa [prefixWord, tailWord_7155051, baseEnd_7155051] using wordTrace_append hprefix tailTrace_7155051
  have hstable : (prefixWord ++ tailWord_7155051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155051).length < 2 ^ (prefixWord ++ tailWord_7155051).sum := by decide
  have hdescent : baseEnd_7155051 < baseStart_7155051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155092 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_7155092 : Nat := 118140960795 + 7155092 * 2 ^ 59
def prefixEnd_7155092 : Nat := 4983230072969 + 3 ^ 40 * 7155092 * 2
def baseEnd_7155092 : Nat := 3674001323139824903344337

theorem tailTrace_7155092 : CollatzResearch.WordTrace tailWord_7155092 prefixEnd_7155092 3674001323139824903344337 := by
  unfold tailWord_7155092
  simp only [CollatzResearch.WordTrace]
  refine ⟨130483822297165575635461765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173978429729554100847282353 130483822297165575635461765)
  ·
    refine ⟨24465716680718545431649081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130483822297165575635461765 24465716680718545431649081)
    ·
      refine ⟨18349287510538909073736811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24465716680718545431649081 18349287510538909073736811)
      ·
        refine ⟨27523931265808363610605217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18349287510538909073736811 27523931265808363610605217)
        ·
          refine ⟨20642948449356272707953913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27523931265808363610605217 20642948449356272707953913)
          ·
            refine ⟨15482211337017204530965435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20642948449356272707953913 15482211337017204530965435)
            ·
              refine ⟨23223317005525806796448153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15482211337017204530965435 23223317005525806796448153)
              ·
                refine ⟨17417487754144355097336115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23223317005525806796448153 17417487754144355097336115)
                ·
                  refine ⟨26126231631216532646004173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17417487754144355097336115 26126231631216532646004173)
                  ·
                    refine ⟨9797336861706199742251565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26126231631216532646004173 9797336861706199742251565)
                    ·
                      refine ⟨3674001323139824903344337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9797336861706199742251565 3674001323139824903344337)
                      ·
                        rfl

theorem cell23_7155092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_7155092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155092 prefixEnd_7155092 := by exact prefixLift 7155092
  have htrace : WordTrace (prefixWord ++ tailWord_7155092) baseStart_7155092 baseEnd_7155092 := by
    simpa [prefixWord, tailWord_7155092, baseEnd_7155092] using wordTrace_append hprefix tailTrace_7155092
  have hstable : (prefixWord ++ tailWord_7155092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155092).length < 2 ^ (prefixWord ++ tailWord_7155092).sum := by decide
  have hdescent : baseEnd_7155092 < baseStart_7155092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155108 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_7155108 : Nat := 118140960795 + 7155108 * 2 ^ 59
def prefixEnd_7155108 : Nat := 4983230072969 + 3 ^ 40 * 7155108 * 2
def baseEnd_7155108 : Nat := 1224669846276765613581421

theorem tailTrace_7155108 : CollatzResearch.WordTrace tailWord_7155108 prefixEnd_7155108 1224669846276765613581421 := by
  unfold tailWord_7155108
  simp only [CollatzResearch.WordTrace]
  refine ⟨130484114081136593001752989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173978818774848790669003985 130484114081136593001752989)
  ·
    refine ⟨48931542780426222375657371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130484114081136593001752989 48931542780426222375657371)
    ·
      refine ⟨73397314170639333563486057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48931542780426222375657371 73397314170639333563486057)
      ·
        refine ⟨55047985627979500172614543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73397314170639333563486057 55047985627979500172614543)
        ·
          refine ⟨82571978441969250258921815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55047985627979500172614543 82571978441969250258921815)
          ·
            refine ⟨123857967662953875388382723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82571978441969250258921815 123857967662953875388382723)
            ·
              refine ⟨185786951494430813082574085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123857967662953875388382723 185786951494430813082574085)
              ·
                refine ⟨34835053405205777452982641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185786951494430813082574085 34835053405205777452982641)
                ·
                  refine ⟨26126290053904333089736981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34835053405205777452982641 26126290053904333089736981)
                  ·
                    refine ⟨1224669846276765613581421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26126290053904333089736981 1224669846276765613581421)
                    ·
                      rfl

theorem cell23_7155108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_7155108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155108 prefixEnd_7155108 := by exact prefixLift 7155108
  have htrace : WordTrace (prefixWord ++ tailWord_7155108) baseStart_7155108 baseEnd_7155108 := by
    simpa [prefixWord, tailWord_7155108, baseEnd_7155108] using wordTrace_append hprefix tailTrace_7155108
  have hstable : (prefixWord ++ tailWord_7155108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155108).length < 2 ^ (prefixWord ++ tailWord_7155108).sum := by decide
  have hdescent : baseEnd_7155108 < baseStart_7155108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155125 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_7155125 : Nat := 118140960795 + 7155125 * 2 ^ 59
def prefixEnd_7155125 : Nat := 4983230072969 + 3 ^ 40 * 7155125 * 2
def baseEnd_7155125 : Nat := 1224672756000474424743895

theorem tailTrace_7155125 : CollatzResearch.WordTrace tailWord_7155125 prefixEnd_7155125 1224672756000474424743895 := by
  unfold tailWord_7155125
  simp only [CollatzResearch.WordTrace]
  refine ⟨260968848203211597906874829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173979232135474398604583219 260968848203211597906874829)
  ·
    refine ⟨97863318076204349215078061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260968848203211597906874829 97863318076204349215078061)
    ·
      refine ⟨36698744278576630955654273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97863318076204349215078061 36698744278576630955654273)
      ·
        refine ⟨27524058208932473216740705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36698744278576630955654273 27524058208932473216740705)
        ·
          refine ⟨20643043656699354912555529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27524058208932473216740705 20643043656699354912555529)
          ·
            refine ⟨15482282742524516184416647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20643043656699354912555529 15482282742524516184416647)
            ·
              refine ⟨23223424113786774276624971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15482282742524516184416647 23223424113786774276624971)
              ·
                refine ⟨34835136170680161414937457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23223424113786774276624971 34835136170680161414937457)
                ·
                  refine ⟨26126352128010121061203093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34835136170680161414937457 26126352128010121061203093)
                  ·
                    refine ⟨1224672756000474424743895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26126352128010121061203093 1224672756000474424743895)
                    ·
                      rfl

theorem cell23_7155125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_7155125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155125 prefixEnd_7155125 := by exact prefixLift 7155125
  have htrace : WordTrace (prefixWord ++ tailWord_7155125) baseStart_7155125 baseEnd_7155125 := by
    simpa [prefixWord, tailWord_7155125, baseEnd_7155125] using wordTrace_append hprefix tailTrace_7155125
  have hstable : (prefixWord ++ tailWord_7155125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155125).length < 2 ^ (prefixWord ++ tailWord_7155125).sum := by decide
  have hdescent : baseEnd_7155125 < baseStart_7155125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155128 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_7155128 : Nat := 118140960795 + 7155128 * 2 ^ 59
def prefixEnd_7155128 : Nat := 4983230072969 + 3 ^ 40 * 7155128 * 2
def baseEnd_7155128 : Nat := 3674019808443386762494171

theorem tailTrace_7155128 : CollatzResearch.WordTrace tailWord_7155128 prefixEnd_7155128 3674019808443386762494171 := by
  unfold tailWord_7155128
  simp only [CollatzResearch.WordTrace]
  refine ⟨130484478811100364709617019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173979305081467152946156025 130484478811100364709617019)
  ·
    refine ⟨195726718216650547064425529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130484478811100364709617019 195726718216650547064425529)
    ·
      refine ⟨146795038662487910298319147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195726718216650547064425529 146795038662487910298319147)
      ·
        refine ⟨220192557993731865447478721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146795038662487910298319147 220192557993731865447478721)
        ·
          refine ⟨165144418495298899085609041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220192557993731865447478721 165144418495298899085609041)
          ·
            refine ⟨123858313871474174314206781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165144418495298899085609041 123858313871474174314206781)
            ·
              refine ⟨46446867701802815367827543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123858313871474174314206781 46446867701802815367827543)
              ·
                refine ⟨69670301552704223051741315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46446867701802815367827543 69670301552704223051741315)
                ·
                  refine ⟨104505452329056334577611973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69670301552704223051741315 104505452329056334577611973)
                  ·
                    refine ⟨19594772311698062733302245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104505452329056334577611973 19594772311698062733302245)
                    ·
                      refine ⟨3674019808443386762494171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19594772311698062733302245 3674019808443386762494171)
                      ·
                        rfl

theorem cell23_7155128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_7155128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155128 prefixEnd_7155128 := by exact prefixLift 7155128
  have htrace : WordTrace (prefixWord ++ tailWord_7155128) baseStart_7155128 baseEnd_7155128 := by
    simpa [prefixWord, tailWord_7155128, baseEnd_7155128] using wordTrace_append hprefix tailTrace_7155128
  have hstable : (prefixWord ++ tailWord_7155128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155128).length < 2 ^ (prefixWord ++ tailWord_7155128).sum := by decide
  have hdescent : baseEnd_7155128 < baseStart_7155128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155202 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7155202 : Nat := 118140960795 + 7155202 * 2 ^ 59
def prefixEnd_7155202 : Nat := 4983230072969 + 3 ^ 40 * 7155202 * 2
def baseEnd_7155202 : Nat := 1224685935337273157656277

theorem tailTrace_7155202 : CollatzResearch.WordTrace tailWord_7155202 prefixEnd_7155202 1224685935337273157656277 := by
  unfold tailWord_7155202
  simp only [CollatzResearch.WordTrace]
  refine ⟨65242914155983160014356965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173981104415955093371618573 65242914155983160014356965)
  ·
    refine ⟨12233046404246842502691931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65242914155983160014356965 12233046404246842502691931)
    ·
      refine ⟨18349569606370263754037897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233046404246842502691931 18349569606370263754037897)
      ·
        refine ⟨13762177204777697815528423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18349569606370263754037897 13762177204777697815528423)
        ·
          refine ⟨20643265807166546723292635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762177204777697815528423 20643265807166546723292635)
          ·
            refine ⟨30964898710749820084938953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20643265807166546723292635 30964898710749820084938953)
            ·
              refine ⟨23223674033062365063704215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30964898710749820084938953 23223674033062365063704215)
              ·
                refine ⟨34835511049593547595556323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23223674033062365063704215 34835511049593547595556323)
                ·
                  refine ⟨52253266574390321393334485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34835511049593547595556323 52253266574390321393334485)
                  ·
                    refine ⟨1224685935337273157656277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52253266574390321393334485 1224685935337273157656277)
                    ·
                      rfl

theorem cell23_7155202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7155202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155202 prefixEnd_7155202 := by exact prefixLift 7155202
  have htrace : WordTrace (prefixWord ++ tailWord_7155202) baseStart_7155202 baseEnd_7155202 := by
    simpa [prefixWord, tailWord_7155202, baseEnd_7155202] using wordTrace_append hprefix tailTrace_7155202
  have hstable : (prefixWord ++ tailWord_7155202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155202).length < 2 ^ (prefixWord ++ tailWord_7155202).sum := by decide
  have hdescent : baseEnd_7155202 < baseStart_7155202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155205 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_7155205 : Nat := 118140960795 + 7155205 * 2 ^ 59
def prefixEnd_7155205 : Nat := 4983230072969 + 3 ^ 40 * 7155205 * 2
def baseEnd_7155205 : Nat := 3674059346453782961231317

theorem tailTrace_7155205 : CollatzResearch.WordTrace tailWord_7155205 prefixEnd_7155205 3674059346453782961231317 := by
  unfold tailWord_7155205
  simp only [CollatzResearch.WordTrace]
  refine ⟨260971766042921771569787069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173981177361947847713191379 260971766042921771569787069)
  ·
    refine ⟨97864412266095664338670151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260971766042921771569787069 97864412266095664338670151)
    ·
      refine ⟨146796618399143496508005227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97864412266095664338670151 146796618399143496508005227)
      ·
        refine ⟨220194927598715244762007841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146796618399143496508005227 220194927598715244762007841)
        ·
          refine ⟨165146195699036433571505881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220194927598715244762007841 165146195699036433571505881)
          ·
            refine ⟨123859646774277325178629411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165146195699036433571505881 123859646774277325178629411)
            ·
              refine ⟨185789470161415987767944117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123859646774277325178629411 185789470161415987767944117)
              ·
                refine ⟨17417762827632748853244761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185789470161415987767944117 17417762827632748853244761)
                ·
                  refine ⟨13063322120724561639933571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17417762827632748853244761 13063322120724561639933571)
                  ·
                    refine ⟨19594983181086842459900357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13063322120724561639933571 19594983181086842459900357)
                    ·
                      refine ⟨3674059346453782961231317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19594983181086842459900357 3674059346453782961231317)
                      ·
                        rfl

theorem cell23_7155205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_7155205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155205 prefixEnd_7155205 := by exact prefixLift 7155205
  have htrace : WordTrace (prefixWord ++ tailWord_7155205) baseStart_7155205 baseEnd_7155205 := by
    simpa [prefixWord, tailWord_7155205, baseEnd_7155205] using wordTrace_append hprefix tailTrace_7155205
  have hstable : (prefixWord ++ tailWord_7155205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155205).length < 2 ^ (prefixWord ++ tailWord_7155205).sum := by decide
  have hdescent : baseEnd_7155205 < baseStart_7155205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155242 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7155242 : Nat := 118140960795 + 7155242 * 2 ^ 59
def prefixEnd_7155242 : Nat := 4983230072969 + 3 ^ 40 * 7155242 * 2
def baseEnd_7155242 : Nat := 3674078345237999316468647

theorem tailTrace_7155242 : CollatzResearch.WordTrace tailWord_7155242 prefixEnd_7155242 3674078345237999316468647 := by
  unfold tailWord_7155242
  simp only [CollatzResearch.WordTrace]
  refine ⟨65243278885946931722220995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173982077029191817925922653 65243278885946931722220995)
  ·
    refine ⟨97864918328920397583331493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65243278885946931722220995 97864918328920397583331493)
    ·
      refine ⟨18349672186672574546874655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97864918328920397583331493 18349672186672574546874655)
      ·
        refine ⟨27524508280008861820311983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18349672186672574546874655 27524508280008861820311983)
        ·
          refine ⟨41286762420013292730467975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27524508280008861820311983 41286762420013292730467975)
          ·
            refine ⟨61930143630019939095701963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41286762420013292730467975 61930143630019939095701963)
            ·
              refine ⟨92895215445029908643552945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61930143630019939095701963 92895215445029908643552945)
              ·
                refine ⟨69671411583772431482664709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92895215445029908643552945 69671411583772431482664709)
                ·
                  refine ⟨13063389671957330902999633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69671411583772431482664709 13063389671957330902999633)
                  ·
                    refine ⟨9797542253967998177249725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13063389671957330902999633 9797542253967998177249725)
                    ·
                      refine ⟨3674078345237999316468647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9797542253967998177249725 3674078345237999316468647)
                      ·
                        rfl

theorem cell23_7155242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7155242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155242 prefixEnd_7155242 := by exact prefixLift 7155242
  have htrace : WordTrace (prefixWord ++ tailWord_7155242) baseStart_7155242 baseEnd_7155242 := by
    simpa [prefixWord, tailWord_7155242, baseEnd_7155242] using wordTrace_append hprefix tailTrace_7155242
  have hstable : (prefixWord ++ tailWord_7155242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155242).length < 2 ^ (prefixWord ++ tailWord_7155242).sum := by decide
  have hdescent : baseEnd_7155242 < baseStart_7155242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155292 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7155292 : Nat := 118140960795 + 7155292 * 2 ^ 59
def prefixEnd_7155292 : Nat := 4983230072969 + 3 ^ 40 * 7155292 * 2
def baseEnd_7155292 : Nat := 1224701339756908040281139

theorem tailTrace_7155292 : CollatzResearch.WordTrace tailWord_7155292 prefixEnd_7155292 1224701339756908040281139 := by
  unfold tailWord_7155292
  simp only [CollatzResearch.WordTrace]
  refine ⟨130487469596803292714102065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173983292795737723618802753 130487469596803292714102065)
  ·
    refine ⟨97865602197602469535576549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130487469596803292714102065 97865602197602469535576549)
    ·
      refine ⟨18349800412050463037920603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97865602197602469535576549 18349800412050463037920603)
      ·
        refine ⟨27524700618075694556880905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18349800412050463037920603 27524700618075694556880905)
        ·
          refine ⟨20643525463556770917660679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27524700618075694556880905 20643525463556770917660679)
          ·
            refine ⟨30965288195335156376491019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20643525463556770917660679 30965288195335156376491019)
            ·
              refine ⟨46447932293002734564736529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30965288195335156376491019 46447932293002734564736529)
              ·
                refine ⟨34835949219752050923552397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46447932293002734564736529 34835949219752050923552397)
                ·
                  refine ⟨13063480957407019096332149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34835949219752050923552397 13063480957407019096332149)
                  ·
                    refine ⟨1224701339756908040281139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13063480957407019096332149 1224701339756908040281139)
                    ·
                      rfl

theorem cell23_7155292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7155292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155292 prefixEnd_7155292 := by exact prefixLift 7155292
  have htrace : WordTrace (prefixWord ++ tailWord_7155292) baseStart_7155292 baseEnd_7155292 := by
    simpa [prefixWord, tailWord_7155292, baseEnd_7155292] using wordTrace_append hprefix tailTrace_7155292
  have hstable : (prefixWord ++ tailWord_7155292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155292).length < 2 ^ (prefixWord ++ tailWord_7155292).sum := by decide
  have hdescent : baseEnd_7155292 < baseStart_7155292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155305 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_7155305 : Nat := 118140960795 + 7155305 * 2 ^ 59
def prefixEnd_7155305 : Nat := 4983230072969 + 3 ^ 40 * 7155305 * 2
def baseEnd_7155305 : Nat := 1224703564839744189993619

theorem tailTrace_7155305 : CollatzResearch.WordTrace tailWord_7155305 prefixEnd_7155305 1224703564839744189993619 := by
  unfold tailWord_7155305
  simp only [CollatzResearch.WordTrace]
  refine ⟨260975413342559488648427369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173983608895039659098951579 260975413342559488648427369)
  ·
    refine ⟨195731560006919616486320527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260975413342559488648427369 195731560006919616486320527)
    ·
      refine ⟨293597340010379424729480791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195731560006919616486320527 293597340010379424729480791)
      ·
        refine ⟨440396010015569137094221187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293597340010379424729480791 440396010015569137094221187)
        ·
          refine ⟨660594015023353705641331781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440396010015569137094221187 660594015023353705641331781)
          ·
            refine ⟨123861377816878819807749709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 660594015023353705641331781 123861377816878819807749709)
            ·
              refine ⟨46448016681329557427906141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123861377816878819807749709 46448016681329557427906141)
              ·
                refine ⟨17418006255498584035464803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46448016681329557427906141 17418006255498584035464803)
                ·
                  refine ⟨26127009383247876053197205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17418006255498584035464803 26127009383247876053197205)
                  ·
                    refine ⟨1224703564839744189993619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26127009383247876053197205 1224703564839744189993619)
                    ·
                      rfl

theorem cell23_7155305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_7155305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155305 prefixEnd_7155305 := by exact prefixLift 7155305
  have htrace : WordTrace (prefixWord ++ tailWord_7155305) baseStart_7155305 baseEnd_7155305 := by
    simpa [prefixWord, tailWord_7155305, baseEnd_7155305] using wordTrace_append hprefix tailTrace_7155305
  have hstable : (prefixWord ++ tailWord_7155305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155305).length < 2 ^ (prefixWord ++ tailWord_7155305).sum := by decide
  have hdescent : baseEnd_7155305 < baseStart_7155305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155312 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_7155312 : Nat := 118140960795 + 7155312 * 2 ^ 59
def prefixEnd_7155312 : Nat := 4983230072969 + 3 ^ 40 * 7155312 * 2
def baseEnd_7155312 : Nat := 3674114288883814042593325

theorem tailTrace_7155312 : CollatzResearch.WordTrace tailWord_7155312 prefixEnd_7155312 3674114288883814042593325 := by
  unfold tailWord_7155312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130487834326767064421966095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173983779102356085895954793 130487834326767064421966095)
  ·
    refine ⟨195731751490150596632949143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130487834326767064421966095 195731751490150596632949143)
    ·
      refine ⟨293597627235225894949423715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195731751490150596632949143 293597627235225894949423715)
      ·
        refine ⟨440396440852838842424135573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293597627235225894949423715 440396440852838842424135573)
        ·
          refine ⟨20643583164976820738631355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 440396440852838842424135573 20643583164976820738631355)
          ·
            refine ⟨30965374747465231107947033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20643583164976820738631355 30965374747465231107947033)
            ·
              refine ⟨23224031060598923330960275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30965374747465231107947033 23224031060598923330960275)
              ·
                refine ⟨34836046590898384996440413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23224031060598923330960275 34836046590898384996440413)
                ·
                  refine ⟨13063517471586894373665155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34836046590898384996440413 13063517471586894373665155)
                  ·
                    refine ⟨19595276207380341560497733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13063517471586894373665155 19595276207380341560497733)
                    ·
                      refine ⟨3674114288883814042593325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19595276207380341560497733 3674114288883814042593325)
                      ·
                        rfl

theorem cell23_7155312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_7155312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155312 prefixEnd_7155312 := by exact prefixLift 7155312
  have htrace : WordTrace (prefixWord ++ tailWord_7155312) baseStart_7155312 baseEnd_7155312 := by
    simpa [prefixWord, tailWord_7155312, baseEnd_7155312] using wordTrace_append hprefix tailTrace_7155312
  have hstable : (prefixWord ++ tailWord_7155312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155312).length < 2 ^ (prefixWord ++ tailWord_7155312).sum := by decide
  have hdescent : baseEnd_7155312 < baseStart_7155312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155329 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_7155329 : Nat := 118140960795 + 7155329 * 2 ^ 59
def prefixEnd_7155329 : Nat := 4983230072969 + 3 ^ 40 * 7155329 * 2
def baseEnd_7155329 : Nat := 3674123018054940476080747

theorem tailTrace_7155329 : CollatzResearch.WordTrace tailWord_7155329 prefixEnd_7155329 3674123018054940476080747 := by
  unfold tailWord_7155329
  simp only [CollatzResearch.WordTrace]
  refine ⟨260976288694472540747301041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173984192462981693831534027 260976288694472540747301041)
  ·
    refine ⟨195732216520854405560475781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260976288694472540747301041 195732216520854405560475781)
    ·
      refine ⟨36699790597660201042589209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195732216520854405560475781 36699790597660201042589209)
      ·
        refine ⟨27524842948245150781941907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36699790597660201042589209 27524842948245150781941907)
        ·
          refine ⟨41287264422367726172912861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27524842948245150781941907 41287264422367726172912861)
          ·
            refine ⟨15482724158387897314842323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41287264422367726172912861 15482724158387897314842323)
            ·
              refine ⟨23224086237581845972263485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15482724158387897314842323 23224086237581845972263485)
              ·
                refine ⟨8709032339093192239598807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23224086237581845972263485 8709032339093192239598807)
                ·
                  refine ⟨13063548508639788359398211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8709032339093192239598807 13063548508639788359398211)
                  ·
                    refine ⟨19595322762959682539097317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13063548508639788359398211 19595322762959682539097317)
                    ·
                      refine ⟨3674123018054940476080747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19595322762959682539097317 3674123018054940476080747)
                      ·
                        rfl

theorem cell23_7155329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_7155329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155329 prefixEnd_7155329 := by exact prefixLift 7155329
  have htrace : WordTrace (prefixWord ++ tailWord_7155329) baseStart_7155329 baseEnd_7155329 := by
    simpa [prefixWord, tailWord_7155329, baseEnd_7155329] using wordTrace_append hprefix tailTrace_7155329
  have hstable : (prefixWord ++ tailWord_7155329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155329).length < 2 ^ (prefixWord ++ tailWord_7155329).sum := by decide
  have hdescent : baseEnd_7155329 < baseStart_7155329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155335 : List Nat := [1, 1, 4, 2, 1, 4, 10]
def baseStart_7155335 : Nat := 118140960795 + 7155335 * 2 ^ 59
def prefixEnd_7155335 : Nat := 4983230072969 + 3 ^ 40 * 7155335 * 2
def baseEnd_7155335 : Nat := 45359581468381079661799

theorem tailTrace_7155335 : CollatzResearch.WordTrace tailWord_7155335 prefixEnd_7155335 45359581468381079661799 := by
  unfold tailWord_7155335
  simp only [CollatzResearch.WordTrace]
  refine ⟨260976507532450803772019459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173984338354967202514679639 260976507532450803772019459)
  ·
    refine ⟨391464761298676205658029189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260976507532450803772019459 391464761298676205658029189)
    ·
      refine ⟨73399642743501788560880473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391464761298676205658029189 73399642743501788560880473)
      ·
        refine ⟨55049732057626341420660355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73399642743501788560880473 55049732057626341420660355)
        ·
          refine ⟨82574598086439512130990533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55049732057626341420660355 82574598086439512130990533)
          ·
            refine ⟨15482737141207408524560725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82574598086439512130990533 15482737141207408524560725)
            ·
              refine ⟨45359581468381079661799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15482737141207408524560725 45359581468381079661799)
              ·
                rfl

theorem cell23_7155335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 10].length) (baseStart_7155335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155335 prefixEnd_7155335 := by exact prefixLift 7155335
  have htrace : WordTrace (prefixWord ++ tailWord_7155335) baseStart_7155335 baseEnd_7155335 := by
    simpa [prefixWord, tailWord_7155335, baseEnd_7155335] using wordTrace_append hprefix tailTrace_7155335
  have hstable : (prefixWord ++ tailWord_7155335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155335).length < 2 ^ (prefixWord ++ tailWord_7155335).sum := by decide
  have hdescent : baseEnd_7155335 < baseStart_7155335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155356 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_7155356 : Nat := 118140960795 + 7155356 * 2 ^ 59
def prefixEnd_7155356 : Nat := 4983230072969 + 3 ^ 40 * 7155356 * 2
def baseEnd_7155356 : Nat := 1224712294010870623481041

theorem tailTrace_7155356 : CollatzResearch.WordTrace tailWord_7155356 prefixEnd_7155356 1224712294010870623481041 := by
  unfold tailWord_7155356
  simp only [CollatzResearch.WordTrace]
  refine ⟨130488636732687362179266961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173984848976916482905689281 130488636732687362179266961)
  ·
    refine ⟨97866477549515521634450221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130488636732687362179266961 97866477549515521634450221)
    ·
      refine ⟨36699929081068320612918833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97866477549515521634450221 36699929081068320612918833)
      ·
        refine ⟨27524946810801240459689125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36699929081068320612918833 27524946810801240459689125)
        ·
          refine ⟨5160927527025232586191711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27524946810801240459689125 5160927527025232586191711)
          ·
            refine ⟨7741391290537848879287567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160927527025232586191711 7741391290537848879287567)
            ·
              refine ⟨11612086935806773318931351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741391290537848879287567 11612086935806773318931351)
              ·
                refine ⟨17418130403710159978397027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612086935806773318931351 17418130403710159978397027)
                ·
                  refine ⟨26127195605565239967595541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17418130403710159978397027 26127195605565239967595541)
                  ·
                    refine ⟨1224712294010870623481041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26127195605565239967595541 1224712294010870623481041)
                    ·
                      rfl

theorem cell23_7155356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_7155356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155356 prefixEnd_7155356 := by exact prefixLift 7155356
  have htrace : WordTrace (prefixWord ++ tailWord_7155356) baseStart_7155356 baseEnd_7155356 := by
    simpa [prefixWord, tailWord_7155356, baseEnd_7155356] using wordTrace_append hprefix tailTrace_7155356
  have hstable : (prefixWord ++ tailWord_7155356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155356).length < 2 ^ (prefixWord ++ tailWord_7155356).sum := by decide
  have hdescent : baseEnd_7155356 < baseStart_7155356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155359 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7155359 : Nat := 118140960795 + 7155359 * 2 ^ 59
def prefixEnd_7155359 : Nat := 4983230072969 + 3 ^ 40 * 7155359 * 2
def baseEnd_7155359 : Nat := 3674138422474575358705609

theorem tailTrace_7155359 : CollatzResearch.WordTrace tailWord_7155359 prefixEnd_7155359 3674138422474575358705609 := by
  unfold tailWord_7155359
  simp only [CollatzResearch.WordTrace]
  refine ⟨260977382884363855870893131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173984921922909237247262087 260977382884363855870893131)
  ·
    refine ⟨391466074326545783806339697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260977382884363855870893131 391466074326545783806339697)
    ·
      refine ⟨293599555744909337854754773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391466074326545783806339697 293599555744909337854754773)
      ·
        refine ⟨6881239587771312605970815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 293599555744909337854754773 6881239587771312605970815)
        ·
          refine ⟨10321859381656968908956223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881239587771312605970815 10321859381656968908956223)
          ·
            refine ⟨15482789072485453363434335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10321859381656968908956223 15482789072485453363434335)
            ·
              refine ⟨23224183608728180045151503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15482789072485453363434335 23224183608728180045151503)
              ·
                refine ⟨34836275413092270067727255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23224183608728180045151503 34836275413092270067727255)
                ·
                  refine ⟨52254413119638405101590883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34836275413092270067727255 52254413119638405101590883)
                  ·
                    refine ⟨78381619679457607652386325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52254413119638405101590883 78381619679457607652386325)
                    ·
                      refine ⟨3674138422474575358705609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78381619679457607652386325 3674138422474575358705609)
                      ·
                        rfl

theorem cell23_7155359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7155359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155359 prefixEnd_7155359 := by exact prefixLift 7155359
  have htrace : WordTrace (prefixWord ++ tailWord_7155359) baseStart_7155359 baseEnd_7155359 := by
    simpa [prefixWord, tailWord_7155359, baseEnd_7155359] using wordTrace_append hprefix tailTrace_7155359
  have hstable : (prefixWord ++ tailWord_7155359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155359).length < 2 ^ (prefixWord ++ tailWord_7155359).sum := by decide
  have hdescent : baseEnd_7155359 < baseStart_7155359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155365 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_7155365 : Nat := 118140960795 + 7155365 * 2 ^ 59
def prefixEnd_7155365 : Nat := 4983230072969 + 3 ^ 40 * 7155365 * 2
def baseEnd_7155365 : Nat := 1224713834452834111743527

theorem tailTrace_7155365 : CollatzResearch.WordTrace tailWord_7155365 prefixEnd_7155365 1224713834452834111743527 := by
  unfold tailWord_7155365
  simp only [CollatzResearch.WordTrace]
  refine ⟨260977601722342118895611549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173985067814894745930407699 260977601722342118895611549)
  ·
    refine ⟨97866600645878294585854331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260977601722342118895611549 97866600645878294585854331)
    ·
      refine ⟨146799900968817441878781497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97866600645878294585854331 146799900968817441878781497)
      ·
        refine ⟨110099925726613081409086123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146799900968817441878781497 110099925726613081409086123)
        ·
          refine ⟨165149888589919622113629185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110099925726613081409086123 165149888589919622113629185)
          ·
            refine ⟨123862416442439716585221889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165149888589919622113629185 123862416442439716585221889)
            ·
              refine ⟨92896812331829787438916417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123862416442439716585221889 92896812331829787438916417)
              ·
                refine ⟨69672609248872340579187313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92896812331829787438916417 69672609248872340579187313)
                ·
                  refine ⟨52254456936654255434390485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69672609248872340579187313 52254456936654255434390485)
                  ·
                    refine ⟨1224713834452834111743527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52254456936654255434390485 1224713834452834111743527)
                    ·
                      rfl

theorem cell23_7155365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_7155365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155365 prefixEnd_7155365 := by exact prefixLift 7155365
  have htrace : WordTrace (prefixWord ++ tailWord_7155365) baseStart_7155365 baseEnd_7155365 := by
    simpa [prefixWord, tailWord_7155365, baseEnd_7155365] using wordTrace_append hprefix tailTrace_7155365
  have hstable : (prefixWord ++ tailWord_7155365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155365).length < 2 ^ (prefixWord ++ tailWord_7155365).sum := by decide
  have hdescent : baseEnd_7155365 < baseStart_7155365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155372 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 7, 2]
def baseStart_7155372 : Nat := 118140960795 + 7155372 * 2 ^ 59
def prefixEnd_7155372 : Nat := 4983230072969 + 3 ^ 40 * 7155372 * 2
def baseEnd_7155372 : Nat := 3674145097723083807843049

theorem tailTrace_7155372 : CollatzResearch.WordTrace tailWord_7155372 prefixEnd_7155372 3674145097723083807843049 := by
  unfold tailWord_7155372
  simp only [CollatzResearch.WordTrace]
  refine ⟨130488928516658379545558185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173985238022211172727410913 130488928516658379545558185)
  ·
    refine ⟨97866696387493784659168639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130488928516658379545558185 97866696387493784659168639)
    ·
      refine ⟨146800044581240676988752959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97866696387493784659168639 146800044581240676988752959)
      ·
        refine ⟨220200066871861015483129439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146800044581240676988752959 220200066871861015483129439)
        ·
          refine ⟨330300100307791523224694159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220200066871861015483129439 330300100307791523224694159)
          ·
            refine ⟨495450150461687284837041239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330300100307791523224694159 495450150461687284837041239)
            ·
              refine ⟨743175225692530927255561859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495450150461687284837041239 743175225692530927255561859)
              ·
                refine ⟨1114762838538796390883342789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743175225692530927255561859 1114762838538796390883342789)
                ·
                  refine ⟨209018032226024323290626773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114762838538796390883342789 209018032226024323290626773)
                  ·
                    refine ⟨4898860130297445077124065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 209018032226024323290626773 4898860130297445077124065)
                    ·
                      refine ⟨3674145097723083807843049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4898860130297445077124065 3674145097723083807843049)
                      ·
                        rfl

theorem cell23_7155372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_7155372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155372 prefixEnd_7155372 := by exact prefixLift 7155372
  have htrace : WordTrace (prefixWord ++ tailWord_7155372) baseStart_7155372 baseEnd_7155372 := by
    simpa [prefixWord, tailWord_7155372, baseEnd_7155372] using wordTrace_append hprefix tailTrace_7155372
  have hstable : (prefixWord ++ tailWord_7155372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155372).length < 2 ^ (prefixWord ++ tailWord_7155372).sum := by decide
  have hdescent : baseEnd_7155372 < baseStart_7155372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155375 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_7155375 : Nat := 118140960795 + 7155375 * 2 ^ 59
def prefixEnd_7155375 : Nat := 4983230072969 + 3 ^ 40 * 7155375 * 2
def baseEnd_7155375 : Nat := 3674146638165047296105535

theorem tailTrace_7155375 : CollatzResearch.WordTrace tailWord_7155375 prefixEnd_7155375 3674146638165047296105535 := by
  unfold tailWord_7155375
  simp only [CollatzResearch.WordTrace]
  refine ⟨260977966452305890603475579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173985310968203927068983719 260977966452305890603475579)
  ·
    refine ⟨391466949678458835905213369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260977966452305890603475579 391466949678458835905213369)
    ·
      refine ⟨293600212258844126928910027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391466949678458835905213369 293600212258844126928910027)
      ·
        refine ⟨440400318388266190393365041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293600212258844126928910027 440400318388266190393365041)
        ·
          refine ⟨330300238791199642795023781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440400318388266190393365041 330300238791199642795023781)
          ·
            refine ⟨61931294773349933024066959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330300238791199642795023781 61931294773349933024066959)
            ·
              refine ⟨92896942160024899536100439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61931294773349933024066959 92896942160024899536100439)
              ·
                refine ⟨139345413240037349304150659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92896942160024899536100439 139345413240037349304150659)
                ·
                  refine ⟨209018119860056023956225989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139345413240037349304150659 209018119860056023956225989)
                  ·
                    refine ⟨39190897473760504491792373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209018119860056023956225989 39190897473760504491792373)
                    ·
                      refine ⟨3674146638165047296105535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39190897473760504491792373 3674146638165047296105535)
                      ·
                        rfl

theorem cell23_7155375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_7155375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155375 prefixEnd_7155375 := by exact prefixLift 7155375
  have htrace : WordTrace (prefixWord ++ tailWord_7155375) baseStart_7155375 baseEnd_7155375 := by
    simpa [prefixWord, tailWord_7155375, baseEnd_7155375] using wordTrace_append hprefix tailTrace_7155375
  have hstable : (prefixWord ++ tailWord_7155375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155375).length < 2 ^ (prefixWord ++ tailWord_7155375).sum := by decide
  have hdescent : baseEnd_7155375 < baseStart_7155375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155396 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_7155396 : Nat := 118140960795 + 7155396 * 2 ^ 59
def prefixEnd_7155396 : Nat := 4983230072969 + 3 ^ 40 * 7155396 * 2
def baseEnd_7155396 : Nat := 3674157421258791713942939

theorem tailTrace_7155396 : CollatzResearch.WordTrace tailWord_7155396 prefixEnd_7155396 3674157421258791713942939 := by
  unfold tailWord_7155396
  simp only [CollatzResearch.WordTrace]
  refine ⟨130489366192614905594995021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173985821590153207459993361 130489366192614905594995021)
  ·
    refine ⟨48933512322230589598123133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130489366192614905594995021 48933512322230589598123133)
    ·
      refine ⟨18350067120836471099296175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48933512322230589598123133 18350067120836471099296175)
      ·
        refine ⟨27525100681254706648944263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18350067120836471099296175 27525100681254706648944263)
        ·
          refine ⟨41287651021882059973416395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27525100681254706648944263 41287651021882059973416395)
          ·
            refine ⟨61931476532823089960124593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41287651021882059973416395 61931476532823089960124593)
            ·
              refine ⟨46448607399617317470093445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61931476532823089960124593 46448607399617317470093445)
              ·
                refine ⟨8709113887428247025642521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46448607399617317470093445 8709113887428247025642521)
                ·
                  refine ⟨6531835415571185269231891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8709113887428247025642521 6531835415571185269231891)
                  ·
                    refine ⟨9797753123356777903847837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6531835415571185269231891 9797753123356777903847837)
                    ·
                      refine ⟨3674157421258791713942939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9797753123356777903847837 3674157421258791713942939)
                      ·
                        rfl

theorem cell23_7155396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_7155396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155396 prefixEnd_7155396 := by exact prefixLift 7155396
  have htrace : WordTrace (prefixWord ++ tailWord_7155396) baseStart_7155396 baseEnd_7155396 := by
    simpa [prefixWord, tailWord_7155396, baseEnd_7155396] using wordTrace_append hprefix tailTrace_7155396
  have hstable : (prefixWord ++ tailWord_7155396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155396).length < 2 ^ (prefixWord ++ tailWord_7155396).sum := by decide
  have hdescent : baseEnd_7155396 < baseStart_7155396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155489 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 2, 5]
def baseStart_7155489 : Nat := 118140960795 + 7155489 * 2 ^ 59
def prefixEnd_7155489 : Nat := 4983230072969 + 3 ^ 40 * 7155489 * 2
def baseEnd_7155489 : Nat := 1224735058319886616693337

theorem tailTrace_7155489 : CollatzResearch.WordTrace tailWord_7155489 prefixEnd_7155489 1224735058319886616693337 := by
  unfold tailWord_7155489
  simp only [CollatzResearch.WordTrace]
  refine ⟨260982124373892888073125521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173988082915928592048750347 260982124373892888073125521)
  ·
    refine ⟨195736593280419666054844141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260982124373892888073125521 195736593280419666054844141)
    ·
      refine ⟨73401222480157374770566553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195736593280419666054844141 73401222480157374770566553)
      ·
        refine ⟨55050916860118031077924915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73401222480157374770566553 55050916860118031077924915)
        ·
          refine ⟨82576375290177046616887373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55050916860118031077924915 82576375290177046616887373)
          ·
            refine ⟨30966140733816392481332765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82576375290177046616887373 30966140733816392481332765)
            ·
              refine ⟨11612302775181147180499787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30966140733816392481332765 11612302775181147180499787)
              ·
                refine ⟨17418454162771720770749681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612302775181147180499787 17418454162771720770749681)
                ·
                  refine ⟨13063840622078790578062261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17418454162771720770749681 13063840622078790578062261)
                  ·
                    refine ⟨1224735058319886616693337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13063840622078790578062261 1224735058319886616693337)
                    ·
                      rfl

theorem cell23_7155489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_7155489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155489 prefixEnd_7155489 := by exact prefixLift 7155489
  have htrace : WordTrace (prefixWord ++ tailWord_7155489) baseStart_7155489 baseEnd_7155489 := by
    simpa [prefixWord, tailWord_7155489, baseEnd_7155489] using wordTrace_append hprefix tailTrace_7155489
  have hstable : (prefixWord ++ tailWord_7155489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155489).length < 2 ^ (prefixWord ++ tailWord_7155489).sum := by decide
  have hdescent : baseEnd_7155489 < baseStart_7155489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155609 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 6, 4]
def baseStart_7155609 : Nat := 118140960795 + 7155609 * 2 ^ 59
def prefixEnd_7155609 : Nat := 4983230072969 + 3 ^ 40 * 7155609 * 2
def baseEnd_7155609 : Nat := 1224755597546066460193153

theorem tailTrace_7155609 : CollatzResearch.WordTrace tailWord_7155609 prefixEnd_7155609 1224755597546066460193153 := by
  unfold tailWord_7155609
  simp only [CollatzResearch.WordTrace]
  refine ⟨260986501133458148567493881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173991000755638765711662587 260986501133458148567493881)
  ·
    refine ⟨195739875850093611425620411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260986501133458148567493881 195739875850093611425620411)
    ·
      refine ⟨293609813775140417138430617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195739875850093611425620411 293609813775140417138430617)
      ·
        refine ⟨220207360331355312853822963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293609813775140417138430617 220207360331355312853822963)
        ·
          refine ⟨330311040497032969280734445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220207360331355312853822963 330311040497032969280734445)
          ·
            refine ⟨123866640186387363480275417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330311040497032969280734445 123866640186387363480275417)
            ·
              refine ⟨92899980139790522610206563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123866640186387363480275417 92899980139790522610206563)
              ·
                refine ⟨139349970209685783915309845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92899980139790522610206563 139349970209685783915309845)
                ·
                  refine ⟨6532029853579021121030149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139349970209685783915309845 6532029853579021121030149)
                  ·
                    refine ⟨1224755597546066460193153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532029853579021121030149 1224755597546066460193153)
                    ·
                      rfl

theorem cell23_7155609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_7155609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155609 prefixEnd_7155609 := by exact prefixLift 7155609
  have htrace : WordTrace (prefixWord ++ tailWord_7155609) baseStart_7155609 baseEnd_7155609 := by
    simpa [prefixWord, tailWord_7155609, baseEnd_7155609] using wordTrace_append hprefix tailTrace_7155609
  have hstable : (prefixWord ++ tailWord_7155609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155609).length < 2 ^ (prefixWord ++ tailWord_7155609).sum := by decide
  have hdescent : baseEnd_7155609 < baseStart_7155609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155613 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_7155613 : Nat := 118140960795 + 7155613 * 2 ^ 59
def prefixEnd_7155613 : Nat := 4983230072969 + 3 ^ 40 * 7155613 * 2
def baseEnd_7155613 : Nat := 1224756282186939121643147

theorem tailTrace_7155613 : CollatzResearch.WordTrace tailWord_7155613 prefixEnd_7155613 1224756282186939121643147 := by
  unfold tailWord_7155613
  simp only [CollatzResearch.WordTrace]
  refine ⟨260986647025443657250639493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173991098016962438167092995 260986647025443657250639493)
  ·
    refine ⟨48934996317270685734494905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260986647025443657250639493 48934996317270685734494905)
    ·
      refine ⟨36701247237953014300871179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48934996317270685734494905 36701247237953014300871179)
      ·
        refine ⟨55051870856929521451306769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36701247237953014300871179 55051870856929521451306769)
        ·
          refine ⟨41288903142697141088480077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55051870856929521451306769 41288903142697141088480077)
          ·
            refine ⟨15483338678511427908180029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41288903142697141088480077 15483338678511427908180029)
            ·
              refine ⟨5806252004441785465567511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15483338678511427908180029 5806252004441785465567511)
              ·
                refine ⟨8709378006662678198351267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806252004441785465567511 8709378006662678198351267)
                ·
                  refine ⟨13064067009994017297526901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8709378006662678198351267 13064067009994017297526901)
                  ·
                    refine ⟨1224756282186939121643147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13064067009994017297526901 1224756282186939121643147)
                    ·
                      rfl

theorem cell23_7155613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_7155613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155613 prefixEnd_7155613 := by exact prefixLift 7155613
  have htrace : WordTrace (prefixWord ++ tailWord_7155613) baseStart_7155613 baseEnd_7155613 := by
    simpa [prefixWord, tailWord_7155613, baseEnd_7155613] using wordTrace_append hprefix tailTrace_7155613
  have hstable : (prefixWord ++ tailWord_7155613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155613).length < 2 ^ (prefixWord ++ tailWord_7155613).sum := by decide
  have hdescent : baseEnd_7155613 < baseStart_7155613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155646 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_7155646 : Nat := 118140960795 + 7155646 * 2 ^ 59
def prefixEnd_7155646 : Nat := 4983230072969 + 3 ^ 40 * 7155646 * 2
def baseEnd_7155646 : Nat := 3674285791422415735816789

theorem tailTrace_7155646 : CollatzResearch.WordTrace tailWord_7155646 prefixEnd_7155646 3674285791422415735816789 := by
  unfold tailWord_7155646
  simp only [CollatzResearch.WordTrace]
  refine ⟨32623481329290512985823849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173991900422882735924393861 32623481329290512985823849)
  ·
    refine ⟨24467610996967884739367887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32623481329290512985823849 24467610996967884739367887)
    ·
      refine ⟨36701416495451827109051831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24467610996967884739367887 36701416495451827109051831)
      ·
        refine ⟨55052124743177740663577747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36701416495451827109051831 55052124743177740663577747)
        ·
          refine ⟨82578187114766610995366621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55052124743177740663577747 82578187114766610995366621)
          ·
            refine ⟨30966820168037479123262483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82578187114766610995366621 30966820168037479123262483)
            ·
              refine ⟨46450230252056218684893725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30966820168037479123262483 46450230252056218684893725)
              ·
                refine ⟨17418836344521082006835147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46450230252056218684893725 17418836344521082006835147)
                ·
                  refine ⟨26128254516781623010252721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17418836344521082006835147 26128254516781623010252721)
                  ·
                    refine ⟨19596190887586217257689541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26128254516781623010252721 19596190887586217257689541)
                    ·
                      refine ⟨3674285791422415735816789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19596190887586217257689541 3674285791422415735816789)
                      ·
                        rfl

theorem cell23_7155646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_7155646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155646 prefixEnd_7155646 := by exact prefixLift 7155646
  have htrace : WordTrace (prefixWord ++ tailWord_7155646) baseStart_7155646 baseEnd_7155646 := by
    simpa [prefixWord, tailWord_7155646, baseEnd_7155646] using wordTrace_append hprefix tailTrace_7155646
  have hstable : (prefixWord ++ tailWord_7155646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155646).length < 2 ^ (prefixWord ++ tailWord_7155646).sum := by decide
  have hdescent : baseEnd_7155646 < baseStart_7155646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155656 : List Nat := [2, 1, 3, 1, 4, 2, 3, 7]
def baseStart_7155656 : Nat := 118140960795 + 7155656 * 2 ^ 59
def prefixEnd_7155656 : Nat := 4983230072969 + 3 ^ 40 * 7155656 * 2
def baseEnd_7155656 : Nat := 136084849119591136914509

theorem tailTrace_7155656 : CollatzResearch.WordTrace tailWord_7155656 prefixEnd_7155656 136084849119591136914509 := by
  unfold tailWord_7155656
  simp only [CollatzResearch.WordTrace]
  refine ⟨130494107682143937797227411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173992143576191917062969881 130494107682143937797227411)
  ·
    refine ⟨195741161523215906695841117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130494107682143937797227411 195741161523215906695841117)
    ·
      refine ⟨73402935571205965010940419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195741161523215906695841117 73402935571205965010940419)
      ·
        refine ⟨110104403356808947516410629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73402935571205965010940419 110104403356808947516410629)
        ·
          refine ⟨20644575629401677659326993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110104403356808947516410629 20644575629401677659326993)
          ·
            refine ⟨15483431722051258244495245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20644575629401677659326993 15483431722051258244495245)
            ·
              refine ⟨5806286895769221841685717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15483431722051258244495245 5806286895769221841685717)
              ·
                refine ⟨136084849119591136914509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5806286895769221841685717 136084849119591136914509)
                ·
                  rfl

theorem cell23_7155656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 7].length) (baseStart_7155656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155656 prefixEnd_7155656 := by exact prefixLift 7155656
  have htrace : WordTrace (prefixWord ++ tailWord_7155656) baseStart_7155656 baseEnd_7155656 := by
    simpa [prefixWord, tailWord_7155656, baseEnd_7155656] using wordTrace_append hprefix tailTrace_7155656
  have hstable : (prefixWord ++ tailWord_7155656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155656).length < 2 ^ (prefixWord ++ tailWord_7155656).sum := by decide
  have hdescent : baseEnd_7155656 < baseStart_7155656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155677 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_7155677 : Nat := 118140960795 + 7155677 * 2 ^ 59
def prefixEnd_7155677 : Nat := 4983230072969 + 3 ^ 40 * 7155677 * 2
def baseEnd_7155677 : Nat := 1224767236440901704843049

theorem tailTrace_7155677 : CollatzResearch.WordTrace tailWord_7155677 prefixEnd_7155677 1224767236440901704843049 := by
  unfold tailWord_7155677
  simp only [CollatzResearch.WordTrace]
  refine ⟨260988981297211796180969285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173992654198141197453979523 260988981297211796180969285)
  ·
    refine ⟨48935433993227211783931741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260988981297211796180969285 48935433993227211783931741)
    ·
      refine ⟨18350787747460204418974403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48935433993227211783931741 18350787747460204418974403)
      ·
        refine ⟨27526181621190306628461605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18350787747460204418974403 27526181621190306628461605)
        ·
          refine ⟨5161159053973182492836551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27526181621190306628461605 5161159053973182492836551)
          ·
            refine ⟨7741738580959773739254827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161159053973182492836551 7741738580959773739254827)
            ·
              refine ⟨11612607871439660608882241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741738580959773739254827 11612607871439660608882241)
              ·
                refine ⟨8709455903579745456661681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11612607871439660608882241 8709455903579745456661681)
                ·
                  refine ⟨6532091927684809092496261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8709455903579745456661681 6532091927684809092496261)
                  ·
                    refine ⟨1224767236440901704843049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532091927684809092496261 1224767236440901704843049)
                    ·
                      rfl

theorem cell23_7155677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_7155677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155677 prefixEnd_7155677 := by exact prefixLift 7155677
  have htrace : WordTrace (prefixWord ++ tailWord_7155677) baseStart_7155677 baseEnd_7155677 := by
    simpa [prefixWord, tailWord_7155677, baseEnd_7155677] using wordTrace_append hprefix tailTrace_7155677
  have hstable : (prefixWord ++ tailWord_7155677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155677).length < 2 ^ (prefixWord ++ tailWord_7155677).sum := by decide
  have hdescent : baseEnd_7155677 < baseStart_7155677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155683 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 3]
def baseStart_7155683 : Nat := 118140960795 + 7155683 * 2 ^ 59
def prefixEnd_7155683 : Nat := 4983230072969 + 3 ^ 40 * 7155683 * 2
def baseEnd_7155683 : Nat := 3674304790206632091054119

theorem tailTrace_7155683 : CollatzResearch.WordTrace tailWord_7155683 prefixEnd_7155683 3674304790206632091054119 := by
  unfold tailWord_7155683
  simp only [CollatzResearch.WordTrace]
  refine ⟨260989200135190059205687703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173992800090126706137125135 260989200135190059205687703)
  ·
    refine ⟨391483800202785088808531555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260989200135190059205687703 391483800202785088808531555)
    ·
      refine ⟨587225700304177633212797333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391483800202785088808531555 587225700304177633212797333)
      ·
        refine ⟨27526204701758326556849875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 587225700304177633212797333 27526204701758326556849875)
        ·
          refine ⟨41289307052637489835274813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27526204701758326556849875 41289307052637489835274813)
          ·
            refine ⟨15483490144739058688228055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41289307052637489835274813 15483490144739058688228055)
            ·
              refine ⟨23225235217108588032342083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15483490144739058688228055 23225235217108588032342083)
              ·
                refine ⟨34837852825662882048513125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23225235217108588032342083 34837852825662882048513125)
                ·
                  refine ⟨6532097404811790384096211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34837852825662882048513125 6532097404811790384096211)
                  ·
                    refine ⟨9798146107217685576144317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6532097404811790384096211 9798146107217685576144317)
                    ·
                      refine ⟨3674304790206632091054119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798146107217685576144317 3674304790206632091054119)
                      ·
                        rfl

theorem cell23_7155683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_7155683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155683 prefixEnd_7155683 := by exact prefixLift 7155683
  have htrace : WordTrace (prefixWord ++ tailWord_7155683) baseStart_7155683 baseEnd_7155683 := by
    simpa [prefixWord, tailWord_7155683, baseEnd_7155683] using wordTrace_append hprefix tailTrace_7155683
  have hstable : (prefixWord ++ tailWord_7155683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155683).length < 2 ^ (prefixWord ++ tailWord_7155683).sum := by decide
  have hdescent : baseEnd_7155683 < baseStart_7155683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155723 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 6, 2, 2]
def baseStart_7155723 : Nat := 118140960795 + 7155723 * 2 ^ 59
def prefixEnd_7155723 : Nat := 4983230072969 + 3 ^ 40 * 7155723 * 2
def baseEnd_7155723 : Nat := 3674325329432811934553935

theorem tailTrace_7155723 : CollatzResearch.WordTrace tailWord_7155723 prefixEnd_7155723 3674325329432811934553935 := by
  unfold tailWord_7155723
  simp only [CollatzResearch.WordTrace]
  refine ⟨260990659055045146037143823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173993772703363430691429215 260990659055045146037143823)
  ·
    refine ⟨391485988582567719055715735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260990659055045146037143823 391485988582567719055715735)
    ·
      refine ⟨587228982873851578583573603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391485988582567719055715735 587228982873851578583573603)
      ·
        refine ⟨880843474310777367875360405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587228982873851578583573603 880843474310777367875360405)
        ·
          refine ⟨41289537858317689119157519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 880843474310777367875360405 41289537858317689119157519)
          ·
            refine ⟨61934306787476533678736279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41289537858317689119157519 61934306787476533678736279)
            ·
              refine ⟨92901460181214800518104419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61934306787476533678736279 92901460181214800518104419)
              ·
                refine ⟨139352190271822200777156629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92901460181214800518104419 139352190271822200777156629)
                ·
                  refine ⟨6532133918991665661429217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139352190271822200777156629 6532133918991665661429217)
                  ·
                    refine ⟨4899100439243749246071913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6532133918991665661429217 4899100439243749246071913)
                    ·
                      refine ⟨3674325329432811934553935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4899100439243749246071913 3674325329432811934553935)
                      ·
                        rfl

theorem cell23_7155723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 2, 2].length) (baseStart_7155723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155723 prefixEnd_7155723 := by exact prefixLift 7155723
  have htrace : WordTrace (prefixWord ++ tailWord_7155723) baseStart_7155723 baseEnd_7155723 := by
    simpa [prefixWord, tailWord_7155723, baseEnd_7155723] using wordTrace_append hprefix tailTrace_7155723
  have hstable : (prefixWord ++ tailWord_7155723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155723).length < 2 ^ (prefixWord ++ tailWord_7155723).sum := by decide
  have hdescent : baseEnd_7155723 < baseStart_7155723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155726 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7155726 : Nat := 118140960795 + 7155726 * 2 ^ 59
def prefixEnd_7155726 : Nat := 4983230072969 + 3 ^ 40 * 7155726 * 2
def baseEnd_7155726 : Nat := 3674326869874775422816421

theorem tailTrace_7155726 : CollatzResearch.WordTrace tailWord_7155726 prefixEnd_7155726 3674326869874775422816421 := by
  unfold tailWord_7155726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32623846059254284693687879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173993845649356185033002021 32623846059254284693687879)
  ·
    refine ⟨48935769088881427040531819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32623846059254284693687879 48935769088881427040531819)
    ·
      refine ⟨73403653633322140560797729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48935769088881427040531819 73403653633322140560797729)
      ·
        refine ⟨55052740224991605420598297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73403653633322140560797729 55052740224991605420598297)
        ·
          refine ⟨41289555168743704065448723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55052740224991605420598297 41289555168743704065448723)
          ·
            refine ⟨61934332753115556098173085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41289555168743704065448723 61934332753115556098173085)
            ·
              refine ⟨23225374782418333536814907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61934332753115556098173085 23225374782418333536814907)
              ·
                refine ⟨34838062173627500305222361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23225374782418333536814907 34838062173627500305222361)
                ·
                  refine ⟨26128546630220625228916771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34838062173627500305222361 26128546630220625228916771)
                  ·
                    refine ⟨39192819945330937843375157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26128546630220625228916771 39192819945330937843375157)
                    ·
                      refine ⟨3674326869874775422816421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39192819945330937843375157 3674326869874775422816421)
                      ·
                        rfl

theorem cell23_7155726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7155726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155726 prefixEnd_7155726 := by exact prefixLift 7155726
  have htrace : WordTrace (prefixWord ++ tailWord_7155726) baseStart_7155726 baseEnd_7155726 := by
    simpa [prefixWord, tailWord_7155726, baseEnd_7155726] using wordTrace_append hprefix tailTrace_7155726
  have hstable : (prefixWord ++ tailWord_7155726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155726).length < 2 ^ (prefixWord ++ tailWord_7155726).sum := by decide
  have hdescent : baseEnd_7155726 < baseStart_7155726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155740 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_7155740 : Nat := 118140960795 + 7155740 * 2 ^ 59
def prefixEnd_7155740 : Nat := 4983230072969 + 3 ^ 40 * 7155740 * 2
def baseEnd_7155740 : Nat := 3674334058603938368041357

theorem tailTrace_7155740 : CollatzResearch.WordTrace tailWord_7155740 prefixEnd_7155740 3674334058603938368041357 := by
  unfold tailWord_7155740
  simp only [CollatzResearch.WordTrace]
  refine ⟨130495639547991778970256337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173994186063989038627008449 130495639547991778970256337)
  ·
    refine ⟨97871729660993834227692253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130495639547991778970256337 97871729660993834227692253)
    ·
      refine ⟨36701898622872687835384595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97871729660993834227692253 36701898622872687835384595)
      ·
        refine ⟨55052847934309031753076893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36701898622872687835384595 55052847934309031753076893)
        ·
          refine ⟨20644817975365886907403835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55052847934309031753076893 20644817975365886907403835)
          ·
            refine ⟨30967226963048830361105753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20644817975365886907403835 30967226963048830361105753)
            ·
              refine ⟨23225420222286622770829315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30967226963048830361105753 23225420222286622770829315)
              ·
                refine ⟨34838130333429934156243973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23225420222286622770829315 34838130333429934156243973)
                ·
                  refine ⟨6532149437518112654295745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34838130333429934156243973 6532149437518112654295745)
                  ·
                    refine ⟨4899112078138584490721809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6532149437518112654295745 4899112078138584490721809)
                    ·
                      refine ⟨3674334058603938368041357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4899112078138584490721809 3674334058603938368041357)
                      ·
                        rfl

theorem cell23_7155740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_7155740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155740 prefixEnd_7155740 := by exact prefixLift 7155740
  have htrace : WordTrace (prefixWord ++ tailWord_7155740) baseStart_7155740 baseEnd_7155740 := by
    simpa [prefixWord, tailWord_7155740, baseEnd_7155740] using wordTrace_append hprefix tailTrace_7155740
  have hstable : (prefixWord ++ tailWord_7155740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155740).length < 2 ^ (prefixWord ++ tailWord_7155740).sum := by decide
  have hdescent : baseEnd_7155740 < baseStart_7155740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155751 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7155751 : Nat := 118140960795 + 7155751 * 2 ^ 59
def prefixEnd_7155751 : Nat := 4983230072969 + 3 ^ 40 * 7155751 * 2
def baseEnd_7155751 : Nat := 3674339706891137825003807

theorem tailTrace_7155751 : CollatzResearch.WordTrace tailWord_7155751 prefixEnd_7155751 3674339706891137825003807 := by
  unfold tailWord_7155751
  simp only [CollatzResearch.WordTrace]
  refine ⟨260991680298943706819163107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173994453532629137879442071 260991680298943706819163107)
  ·
    refine ⟨391487520448415560228744661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260991680298943706819163107 391487520448415560228744661)
    ·
      refine ⟨9175488760509739692861203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 391487520448415560228744661 9175488760509739692861203)
      ·
        refine ⟨13763233140764609539291805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175488760509739692861203 13763233140764609539291805)
        ·
          refine ⟨5161212427786728577234427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13763233140764609539291805 5161212427786728577234427)
          ·
            refine ⟨7741818641680092865851641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161212427786728577234427 7741818641680092865851641)
            ·
              refine ⟨5806363981260069649388731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7741818641680092865851641 5806363981260069649388731)
              ·
                refine ⟨8709545971890104474083097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806363981260069649388731 8709545971890104474083097)
                ·
                  refine ⟨6532159478917578355562323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8709545971890104474083097 6532159478917578355562323)
                  ·
                    refine ⟨9798239218376367533343485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6532159478917578355562323 9798239218376367533343485)
                    ·
                      refine ⟨3674339706891137825003807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798239218376367533343485 3674339706891137825003807)
                      ·
                        rfl

theorem cell23_7155751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7155751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155751 prefixEnd_7155751 := by exact prefixLift 7155751
  have htrace : WordTrace (prefixWord ++ tailWord_7155751) baseStart_7155751 baseEnd_7155751 := by
    simpa [prefixWord, tailWord_7155751, baseEnd_7155751] using wordTrace_append hprefix tailTrace_7155751
  have hstable : (prefixWord ++ tailWord_7155751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155751).length < 2 ^ (prefixWord ++ tailWord_7155751).sum := by decide
  have hdescent : baseEnd_7155751 < baseStart_7155751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155759 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 1, 7]
def baseStart_7155759 : Nat := 118140960795 + 7155759 * 2 ^ 59
def prefixEnd_7155759 : Nat := 4983230072969 + 3 ^ 40 * 7155759 * 2
def baseEnd_7155759 : Nat := 1224781271578791264567923

theorem tailTrace_7155759 : CollatzResearch.WordTrace tailWord_7155759 prefixEnd_7155759 1224781271578791264567923 := by
  unfold tailWord_7155759
  simp only [CollatzResearch.WordTrace]
  refine ⟨260991972082914724185454331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173994648055276482790302887 260991972082914724185454331)
  ·
    refine ⟨391487958124372086278181497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260991972082914724185454331 391487958124372086278181497)
    ·
      refine ⟨293615968593279064708636123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391487958124372086278181497 293615968593279064708636123)
      ·
        refine ⟨440423952889918597062954185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293615968593279064708636123 440423952889918597062954185)
        ·
          refine ⟨330317964667438947797215639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440423952889918597062954185 330317964667438947797215639)
          ·
            refine ⟨495476947001158421695823459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330317964667438947797215639 495476947001158421695823459)
            ·
              refine ⟨743215420501737632543735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495476947001158421695823459 743215420501737632543735189)
              ·
                refine ⟨34838222836018951525487587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 743215420501737632543735189 34838222836018951525487587)
                ·
                  refine ⟨52257334254028427288231381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34838222836018951525487587 52257334254028427288231381)
                  ·
                    refine ⟨1224781271578791264567923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52257334254028427288231381 1224781271578791264567923)
                    ·
                      rfl

theorem cell23_7155759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_7155759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155759 prefixEnd_7155759 := by exact prefixLift 7155759
  have htrace : WordTrace (prefixWord ++ tailWord_7155759) baseStart_7155759 baseEnd_7155759 := by
    simpa [prefixWord, tailWord_7155759, baseEnd_7155759] using wordTrace_append hprefix tailTrace_7155759
  have hstable : (prefixWord ++ tailWord_7155759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155759).length < 2 ^ (prefixWord ++ tailWord_7155759).sum := by decide
  have hdescent : baseEnd_7155759 < baseStart_7155759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155776 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_7155776 : Nat := 118140960795 + 7155776 * 2 ^ 59
def prefixEnd_7155776 : Nat := 4983230072969 + 3 ^ 40 * 7155776 * 2
def baseEnd_7155776 : Nat := 1224784181302500075730397

theorem tailTrace_7155776 : CollatzResearch.WordTrace tailWord_7155776 prefixEnd_7155776 1224784181302500075730397 := by
  unfold tailWord_7155776
  simp only [CollatzResearch.WordTrace]
  refine ⟨130496296061926568044411591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173995061415902090725882121 130496296061926568044411591)
  ·
    refine ⟨195744444092889852066617387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130496296061926568044411591 195744444092889852066617387)
    ·
      refine ⟨293616666139334778099926081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195744444092889852066617387 293616666139334778099926081)
      ·
        refine ⟨220212499604501083574944561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293616666139334778099926081 220212499604501083574944561)
        ·
          refine ⟨165159374703375812681208421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220212499604501083574944561 165159374703375812681208421)
          ·
            refine ⟨30967382756882964877726579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165159374703375812681208421 30967382756882964877726579)
            ·
              refine ⟨46451074135324447316589869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30967382756882964877726579 46451074135324447316589869)
              ·
                refine ⟨17419152800746667743721201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46451074135324447316589869 17419152800746667743721201)
                ·
                  refine ⟨13064364600560000807790901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17419152800746667743721201 13064364600560000807790901)
                  ·
                    refine ⟨1224784181302500075730397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13064364600560000807790901 1224784181302500075730397)
                    ·
                      rfl

theorem cell23_7155776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_7155776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155776 prefixEnd_7155776 := by exact prefixLift 7155776
  have htrace : WordTrace (prefixWord ++ tailWord_7155776) baseStart_7155776 baseEnd_7155776 := by
    simpa [prefixWord, tailWord_7155776, baseEnd_7155776] using wordTrace_append hprefix tailTrace_7155776
  have hstable : (prefixWord ++ tailWord_7155776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155776).length < 2 ^ (prefixWord ++ tailWord_7155776).sum := by decide
  have hdescent : baseEnd_7155776 < baseStart_7155776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155796 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_7155796 : Nat := 118140960795 + 7155796 * 2 ^ 59
def prefixEnd_7155796 : Nat := 4983230072969 + 3 ^ 40 * 7155796 * 2
def baseEnd_7155796 : Nat := 3674362813520590148941099

theorem tailTrace_7155796 : CollatzResearch.WordTrace tailWord_7155796 prefixEnd_7155796 3674362813520590148941099 := by
  unfold tailWord_7155796
  simp only [CollatzResearch.WordTrace]
  refine ⟨130496660791890339752275621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173995547722520453003034161 130496660791890339752275621)
  ·
    refine ⟨24468123898479438703551679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130496660791890339752275621 24468123898479438703551679)
    ·
      refine ⟨36702185847719158055327519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24468123898479438703551679 36702185847719158055327519)
      ·
        refine ⟨55053278771578737082991279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36702185847719158055327519 55053278771578737082991279)
        ·
          refine ⟨82579918157368105624486919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55053278771578737082991279 82579918157368105624486919)
          ·
            refine ⟨123869877236052158436730379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82579918157368105624486919 123869877236052158436730379)
            ·
              refine ⟨185804815854078237655095569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123869877236052158436730379 185804815854078237655095569)
              ·
                refine ⟨139353611890558678241321677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185804815854078237655095569 139353611890558678241321677)
                ·
                  refine ⟨52257604458959504340495629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139353611890558678241321677 52257604458959504340495629)
                  ·
                    refine ⟨19596601672109814127685861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52257604458959504340495629 19596601672109814127685861)
                    ·
                      refine ⟨3674362813520590148941099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19596601672109814127685861 3674362813520590148941099)
                      ·
                        rfl

theorem cell23_7155796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_7155796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155796 prefixEnd_7155796 := by exact prefixLift 7155796
  have htrace : WordTrace (prefixWord ++ tailWord_7155796) baseStart_7155796 baseEnd_7155796 := by
    simpa [prefixWord, tailWord_7155796, baseEnd_7155796] using wordTrace_append hprefix tailTrace_7155796
  have hstable : (prefixWord ++ tailWord_7155796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155796).length < 2 ^ (prefixWord ++ tailWord_7155796).sum := by decide
  have hdescent : baseEnd_7155796 < baseStart_7155796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155813 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 6, 2]
def baseStart_7155813 : Nat := 118140960795 + 7155813 * 2 ^ 59
def prefixEnd_7155813 : Nat := 4983230072969 + 3 ^ 40 * 7155813 * 2
def baseEnd_7155813 : Nat := 3674371542691716582428521

theorem tailTrace_7155813 : CollatzResearch.WordTrace tailWord_7155813 prefixEnd_7155813 3674371542691716582428521 := by
  unfold tailWord_7155813
  simp only [CollatzResearch.WordTrace]
  refine ⟨260993941624719091407920093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173995961083146060938613395 260993941624719091407920093)
  ·
    refine ⟨97872728109269659277970035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260993941624719091407920093 97872728109269659277970035)
    ·
      refine ⟨146809092163904488916955053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97872728109269659277970035 146809092163904488916955053)
      ·
        refine ⟨55053409561464183343858145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146809092163904488916955053 55053409561464183343858145)
        ·
          refine ⟨41290057171098137507893609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55053409561464183343858145 41290057171098137507893609)
          ·
            refine ⟨30967542878323603130920207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41290057171098137507893609 30967542878323603130920207)
            ·
              refine ⟨46451314317485404696380311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30967542878323603130920207 46451314317485404696380311)
              ·
                refine ⟨69676971476228107044570467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46451314317485404696380311 69676971476228107044570467)
                ·
                  refine ⟨104515457214342160566855701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69676971476228107044570467 104515457214342160566855701)
                  ·
                    refine ⟨4899162056922288776571361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104515457214342160566855701 4899162056922288776571361)
                    ·
                      refine ⟨3674371542691716582428521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4899162056922288776571361 3674371542691716582428521)
                      ·
                        rfl

theorem cell23_7155813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_7155813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155813 prefixEnd_7155813 := by exact prefixLift 7155813
  have htrace : WordTrace (prefixWord ++ tailWord_7155813) baseStart_7155813 baseEnd_7155813 := by
    simpa [prefixWord, tailWord_7155813, baseEnd_7155813] using wordTrace_append hprefix tailTrace_7155813
  have hstable : (prefixWord ++ tailWord_7155813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155813).length < 2 ^ (prefixWord ++ tailWord_7155813).sum := by decide
  have hdescent : baseEnd_7155813 < baseStart_7155813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155823 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 3, 4]
def baseStart_7155823 : Nat := 118140960795 + 7155823 * 2 ^ 59
def prefixEnd_7155823 : Nat := 4983230072969 + 3 ^ 40 * 7155823 * 2
def baseEnd_7155823 : Nat := 1224792225832753847767825

theorem tailTrace_7155823 : CollatzResearch.WordTrace tailWord_7155823 prefixEnd_7155823 1224792225832753847767825 := by
  unfold tailWord_7155823
  simp only [CollatzResearch.WordTrace]
  refine ⟨260994306354682863115784123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173996204236455242077189415 260994306354682863115784123)
  ·
    refine ⟨391491459532024294673676185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260994306354682863115784123 391491459532024294673676185)
    ·
      refine ⟨293618594649018221005257139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391491459532024294673676185 293618594649018221005257139)
      ·
        refine ⟨440427891973527331507885709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293618594649018221005257139 440427891973527331507885709)
        ·
          refine ⟨165160459490072749315457141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440427891973527331507885709 165160459490072749315457141)
          ·
            refine ⟨15483793077194320248324107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165160459490072749315457141 15483793077194320248324107)
            ·
              refine ⟨23225689615791480372486161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15483793077194320248324107 23225689615791480372486161)
              ·
                refine ⟨17419267211843610279364621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23225689615791480372486161 17419267211843610279364621)
                ·
                  refine ⟨6532225204441353854761733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17419267211843610279364621 6532225204441353854761733)
                  ·
                    refine ⟨1224792225832753847767825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532225204441353854761733 1224792225832753847767825)
                    ·
                      rfl

theorem cell23_7155823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_7155823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155823 prefixEnd_7155823 := by exact prefixLift 7155823
  have htrace : WordTrace (prefixWord ++ tailWord_7155823) baseStart_7155823 baseEnd_7155823 := by
    simpa [prefixWord, tailWord_7155823, baseEnd_7155823] using wordTrace_append hprefix tailTrace_7155823
  have hstable : (prefixWord ++ tailWord_7155823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155823).length < 2 ^ (prefixWord ++ tailWord_7155823).sum := by decide
  have hdescent : baseEnd_7155823 < baseStart_7155823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155830 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7155830 : Nat := 118140960795 + 7155830 * 2 ^ 59
def prefixEnd_7155830 : Nat := 4983230072969 + 3 ^ 40 * 7155830 * 2
def baseEnd_7155830 : Nat := 3674380271862843015915943

theorem tailTrace_7155830 : CollatzResearch.WordTrace tailWord_7155830 prefixEnd_7155830 3674380271862843015915943 := by
  unfold tailWord_7155830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16312160104103593956955559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173996374443771668874192629 16312160104103593956955559)
  ·
    refine ⟨24468240156155390935433339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16312160104103593956955559 24468240156155390935433339)
    ·
      refine ⟨36702360234233086403150009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24468240156155390935433339 36702360234233086403150009)
      ·
        refine ⟨27526770175674814802362507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36702360234233086403150009 27526770175674814802362507)
        ·
          refine ⟨41290155263512222203543761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27526770175674814802362507 41290155263512222203543761)
          ·
            refine ⟨30967616447634166652657821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41290155263512222203543761 30967616447634166652657821)
            ·
              refine ⟨11612856167862812494746683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30967616447634166652657821 11612856167862812494746683)
              ·
                refine ⟨17419284251794218742120025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612856167862812494746683 17419284251794218742120025)
                ·
                  refine ⟨13064463188845664056590019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17419284251794218742120025 13064463188845664056590019)
                  ·
                    refine ⟨19596694783268496084885029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13064463188845664056590019 19596694783268496084885029)
                    ·
                      refine ⟨3674380271862843015915943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19596694783268496084885029 3674380271862843015915943)
                      ·
                        rfl

theorem cell23_7155830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7155830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155830 prefixEnd_7155830 := by exact prefixLift 7155830
  have htrace : WordTrace (prefixWord ++ tailWord_7155830) baseStart_7155830 baseEnd_7155830 := by
    simpa [prefixWord, tailWord_7155830, baseEnd_7155830] using wordTrace_append hprefix tailTrace_7155830
  have hstable : (prefixWord ++ tailWord_7155830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155830).length < 2 ^ (prefixWord ++ tailWord_7155830).sum := by decide
  have hdescent : baseEnd_7155830 < baseStart_7155830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155833 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_7155833 : Nat := 118140960795 + 7155833 * 2 ^ 59
def prefixEnd_7155833 : Nat := 4983230072969 + 3 ^ 40 * 7155833 * 2
def baseEnd_7155833 : Nat := 3674381812304806504178429

theorem tailTrace_7155833 : CollatzResearch.WordTrace tailWord_7155833 prefixEnd_7155833 3674381812304806504178429 := by
  unfold tailWord_7155833
  simp only [CollatzResearch.WordTrace]
  refine ⟨260994671084646634823648153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173996447389764423215765435 260994671084646634823648153)
  ·
    refine ⟨195746003313484976117736115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260994671084646634823648153 195746003313484976117736115)
    ·
      refine ⟨293619004970227464176604173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195746003313484976117736115 293619004970227464176604173)
      ·
        refine ⟨110107126863835299066226565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293619004970227464176604173 110107126863835299066226565)
        ·
          refine ⟨20645086286969118574917481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110107126863835299066226565 20645086286969118574917481)
          ·
            refine ⟨15483814715226838931188111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20645086286969118574917481 15483814715226838931188111)
            ·
              refine ⟨23225722072840258396782167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15483814715226838931188111 23225722072840258396782167)
              ·
                refine ⟨34838583109260387595173251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23225722072840258396782167 34838583109260387595173251)
                ·
                  refine ⟨52257874663890581392759877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34838583109260387595173251 52257874663890581392759877)
                  ·
                    refine ⟨9798351499479484011142477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52257874663890581392759877 9798351499479484011142477)
                    ·
                      refine ⟨3674381812304806504178429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798351499479484011142477 3674381812304806504178429)
                      ·
                        rfl

theorem cell23_7155833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_7155833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155833 prefixEnd_7155833 := by exact prefixLift 7155833
  have htrace : WordTrace (prefixWord ++ tailWord_7155833) baseStart_7155833 baseEnd_7155833 := by
    simpa [prefixWord, tailWord_7155833, baseEnd_7155833] using wordTrace_append hprefix tailTrace_7155833
  have hstable : (prefixWord ++ tailWord_7155833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155833).length < 2 ^ (prefixWord ++ tailWord_7155833).sum := by decide
  have hdescent : baseEnd_7155833 < baseStart_7155833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155890 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_7155890 : Nat := 118140960795 + 7155890 * 2 ^ 59
def prefixEnd_7155890 : Nat := 4983230072969 + 3 ^ 40 * 7155890 * 2
def baseEnd_7155890 : Nat := 3674411080702112781165667

theorem tailTrace_7155890 : CollatzResearch.WordTrace tailWord_7155890 prefixEnd_7155890 3674411080702112781165667 := by
  unfold tailWord_7155890
  simp only [CollatzResearch.WordTrace]
  refine ⟨65249187511360033389618281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173997833363626755705648749 65249187511360033389618281)
  ·
    refine ⟨48936890633520025042213711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65249187511360033389618281 48936890633520025042213711)
    ·
      refine ⟨73405335950280037563320567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48936890633520025042213711 73405335950280037563320567)
      ·
        refine ⟨110108003925420056344980851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73405335950280037563320567 110108003925420056344980851)
        ·
          refine ⟨165162005888130084517471277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110108003925420056344980851 165162005888130084517471277)
          ·
            refine ⟨61935752208048781694051729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165162005888130084517471277 61935752208048781694051729)
            ·
              refine ⟨46451814156036586270538797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61935752208048781694051729 46451814156036586270538797)
              ·
                refine ⟨17419430308513719851452049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46451814156036586270538797 17419430308513719851452049)
                ·
                  refine ⟨13064572731385289888589037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17419430308513719851452049 13064572731385289888589037)
                  ·
                    refine ⟨4899214774269483708220889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13064572731385289888589037 4899214774269483708220889)
                    ·
                      refine ⟨3674411080702112781165667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4899214774269483708220889 3674411080702112781165667)
                      ·
                        rfl

theorem cell23_7155890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_7155890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155890 prefixEnd_7155890 := by exact prefixLift 7155890
  have htrace : WordTrace (prefixWord ++ tailWord_7155890) baseStart_7155890 baseEnd_7155890 := by
    simpa [prefixWord, tailWord_7155890, baseEnd_7155890] using wordTrace_append hprefix tailTrace_7155890
  have hstable : (prefixWord ++ tailWord_7155890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155890).length < 2 ^ (prefixWord ++ tailWord_7155890).sum := by decide
  have hdescent : baseEnd_7155890 < baseStart_7155890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155896 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_7155896 : Nat := 118140960795 + 7155896 * 2 ^ 59
def prefixEnd_7155896 : Nat := 4983230072969 + 3 ^ 40 * 7155896 * 2
def baseEnd_7155896 : Nat := 1224804720528679919230213

theorem tailTrace_7155896 : CollatzResearch.WordTrace tailWord_7155896 prefixEnd_7155896 1224804720528679919230213 := by
  unfold tailWord_7155896
  simp only [CollatzResearch.WordTrace]
  refine ⟨130498484441709198291595771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173997979255612264388794361 130498484441709198291595771)
  ·
    refine ⟨195747726662563797437393657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130498484441709198291595771 195747726662563797437393657)
    ·
      refine ⟨146810794996922848078045243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195747726662563797437393657 146810794996922848078045243)
      ·
        refine ⟨220216192495384272117067865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146810794996922848078045243 220216192495384272117067865)
        ·
          refine ⟨165162144371538204087800899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220216192495384272117067865 165162144371538204087800899)
          ·
            refine ⟨247743216557307306131701349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165162144371538204087800899 247743216557307306131701349)
            ·
              refine ⟨46451853104495119899694003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247743216557307306131701349 46451853104495119899694003)
              ·
                refine ⟨69677779656742679849541005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46451853104495119899694003 69677779656742679849541005)
                ·
                  refine ⟨26129167371278504943577877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69677779656742679849541005 26129167371278504943577877)
                  ·
                    refine ⟨1224804720528679919230213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26129167371278504943577877 1224804720528679919230213)
                    ·
                      rfl

theorem cell23_7155896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_7155896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155896 prefixEnd_7155896 := by exact prefixLift 7155896
  have htrace : WordTrace (prefixWord ++ tailWord_7155896) baseStart_7155896 baseEnd_7155896 := by
    simpa [prefixWord, tailWord_7155896, baseEnd_7155896] using wordTrace_append hprefix tailTrace_7155896
  have hstable : (prefixWord ++ tailWord_7155896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155896).length < 2 ^ (prefixWord ++ tailWord_7155896).sum := by decide
  have hdescent : baseEnd_7155896 < baseStart_7155896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155914 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_7155914 : Nat := 118140960795 + 7155914 * 2 ^ 59
def prefixEnd_7155914 : Nat := 4983230072969 + 3 ^ 40 * 7155914 * 2
def baseEnd_7155914 : Nat := 3674423404237820687265557

theorem tailTrace_7155914 : CollatzResearch.WordTrace tailWord_7155914 prefixEnd_7155914 3674423404237820687265557 := by
  unfold tailWord_7155914
  simp only [CollatzResearch.WordTrace]
  refine ⟨65249406349338296414336699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173998416931568790438231197 65249406349338296414336699)
  ·
    refine ⟨97874109524007444621505049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65249406349338296414336699 97874109524007444621505049)
    ·
      refine ⟨73405582143005583466128787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97874109524007444621505049 73405582143005583466128787)
      ·
        refine ⟨110108373214508375199193181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73405582143005583466128787 110108373214508375199193181)
        ·
          refine ⟨41290639955440640699697443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110108373214508375199193181 41290639955440640699697443)
          ·
            refine ⟨61935959933160961049546165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41290639955440640699697443 61935959933160961049546165)
            ·
              refine ⟨5806496243733840098394953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61935959933160961049546165 5806496243733840098394953)
              ·
                refine ⟨4354872182800380073796215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806496243733840098394953 4354872182800380073796215)
                ·
                  refine ⟨6532308274200570110694323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354872182800380073796215 6532308274200570110694323)
                  ·
                    refine ⟨9798462411300855166041485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6532308274200570110694323 9798462411300855166041485)
                    ·
                      refine ⟨3674423404237820687265557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798462411300855166041485 3674423404237820687265557)
                      ·
                        rfl

theorem cell23_7155914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_7155914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155914 prefixEnd_7155914 := by exact prefixLift 7155914
  have htrace : WordTrace (prefixWord ++ tailWord_7155914) baseStart_7155914 baseEnd_7155914 := by
    simpa [prefixWord, tailWord_7155914, baseEnd_7155914] using wordTrace_append hprefix tailTrace_7155914
  have hstable : (prefixWord ++ tailWord_7155914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155914).length < 2 ^ (prefixWord ++ tailWord_7155914).sum := by decide
  have hdescent : baseEnd_7155914 < baseStart_7155914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155943 : List Nat := [1, 1, 5, 3, 1, 1, 2, 9]
def baseStart_7155943 : Nat := 118140960795 + 7155943 * 2 ^ 59
def prefixEnd_7155943 : Nat := 4983230072969 + 3 ^ 40 * 7155943 * 2
def baseEnd_7155943 : Nat := 136090307228770410140849

theorem tailTrace_7155943 : CollatzResearch.WordTrace tailWord_7155943 prefixEnd_7155943 136090307228770410140849 := by
  unfold tailWord_7155943
  simp only [CollatzResearch.WordTrace]
  refine ⟨260998683114248123610152483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173999122076165415740101655 260998683114248123610152483)
  ·
    refine ⟨391498024671372185415228725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260998683114248123610152483 391498024671372185415228725)
    ·
      refine ⟨36702939812941142382677693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391498024671372185415228725 36702939812941142382677693)
      ·
        refine ⟨13763602429852928393504135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36702939812941142382677693 13763602429852928393504135)
        ·
          refine ⟨20645403644779392590256203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13763602429852928393504135 20645403644779392590256203)
          ·
            refine ⟨30968105467169088885384305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20645403644779392590256203 30968105467169088885384305)
            ·
              refine ⟨23226079100376816664038229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30968105467169088885384305 23226079100376816664038229)
              ·
                refine ⟨136090307228770410140849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23226079100376816664038229 136090307228770410140849)
                ·
                  rfl

theorem cell23_7155943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 9].length) (baseStart_7155943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155943 prefixEnd_7155943 := by exact prefixLift 7155943
  have htrace : WordTrace (prefixWord ++ tailWord_7155943) baseStart_7155943 baseEnd_7155943 := by
    simpa [prefixWord, tailWord_7155943, baseEnd_7155943] using wordTrace_append hprefix tailTrace_7155943
  have hstable : (prefixWord ++ tailWord_7155943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155943).length < 2 ^ (prefixWord ++ tailWord_7155943).sum := by decide
  have hdescent : baseEnd_7155943 < baseStart_7155943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155953 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_7155953 : Nat := 118140960795 + 7155953 * 2 ^ 59
def prefixEnd_7155953 : Nat := 4983230072969 + 3 ^ 40 * 7155953 * 2
def baseEnd_7155953 : Nat := 3674443429983346034677877

theorem tailTrace_7155953 : CollatzResearch.WordTrace tailWord_7155953 prefixEnd_7155953 3674443429983346034677877 := by
  unfold tailWord_7155953
  simp only [CollatzResearch.WordTrace]
  refine ⟨260999047844211895318016513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173999365229474596878677675 260999047844211895318016513)
  ·
    refine ⟨195749285883158921488512385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260999047844211895318016513 195749285883158921488512385)
    ·
      refine ⟨146811964412369191116384289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195749285883158921488512385 146811964412369191116384289)
      ·
        refine ⟨110108973309276893337288217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146811964412369191116384289 110108973309276893337288217)
        ·
          refine ⟨82581729981957670002966163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110108973309276893337288217 82581729981957670002966163)
          ·
            refine ⟨123872594972936505004449245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82581729981957670002966163 123872594972936505004449245)
            ·
              refine ⟨46452223114851189376668467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123872594972936505004449245 46452223114851189376668467)
              ·
                refine ⟨69678334672276784065002701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46452223114851189376668467 69678334672276784065002701)
                ·
                  refine ⟨26129375502103794024376013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69678334672276784065002701 26129375502103794024376013)
                  ·
                    refine ⟨9798515813288922759141005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26129375502103794024376013 9798515813288922759141005)
                    ·
                      refine ⟨3674443429983346034677877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798515813288922759141005 3674443429983346034677877)
                      ·
                        rfl

theorem cell23_7155953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_7155953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155953 prefixEnd_7155953 := by exact prefixLift 7155953
  have htrace : WordTrace (prefixWord ++ tailWord_7155953) baseStart_7155953 baseEnd_7155953 := by
    simpa [prefixWord, tailWord_7155953, baseEnd_7155953] using wordTrace_append hprefix tailTrace_7155953
  have hstable : (prefixWord ++ tailWord_7155953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155953).length < 2 ^ (prefixWord ++ tailWord_7155953).sum := by decide
  have hdescent : baseEnd_7155953 < baseStart_7155953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7155980 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 5, 3, 2]
def baseStart_7155980 : Nat := 118140960795 + 7155980 * 2 ^ 59
def prefixEnd_7155980 : Nat := 4983230072969 + 3 ^ 40 * 7155980 * 2
def baseEnd_7155980 : Nat := 3674457293961017429040253

theorem tailTrace_7155980 : CollatzResearch.WordTrace tailWord_7155980 prefixEnd_7155980 3674457293961017429040253 := by
  unfold tailWord_7155980
  simp only [CollatzResearch.WordTrace]
  refine ⟨130500016307557039464624697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174000021743409385952832929 130500016307557039464624697)
  ·
    refine ⟨97875012230667779598468523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130500016307557039464624697 97875012230667779598468523)
    ·
      refine ⟨146812518346001669397702785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97875012230667779598468523 146812518346001669397702785)
      ·
        refine ⟨110109388759501252048277089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146812518346001669397702785 110109388759501252048277089)
        ·
          refine ⟨82582041569625939036207817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110109388759501252048277089 82582041569625939036207817)
          ·
            refine ⟨61936531177219454277155863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82582041569625939036207817 61936531177219454277155863)
            ·
              refine ⟨92904796765829181415733795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61936531177219454277155863 92904796765829181415733795)
              ·
                refine ⟨139357195148743772123600693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92904796765829181415733795 139357195148743772123600693)
                ·
                  refine ⟨13064737045194728636587565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139357195148743772123600693 13064737045194728636587565)
                  ·
                    refine ⟨4899276391948023238720337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13064737045194728636587565 4899276391948023238720337)
                    ·
                      refine ⟨3674457293961017429040253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4899276391948023238720337 3674457293961017429040253)
                      ·
                        rfl

theorem cell23_7155980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_7155980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7155980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7155980 prefixEnd_7155980 := by exact prefixLift 7155980
  have htrace : WordTrace (prefixWord ++ tailWord_7155980) baseStart_7155980 baseEnd_7155980 := by
    simpa [prefixWord, tailWord_7155980, baseEnd_7155980] using wordTrace_append hprefix tailTrace_7155980
  have hstable : (prefixWord ++ tailWord_7155980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7155980).length < 2 ^ (prefixWord ++ tailWord_7155980).sum := by decide
  have hdescent : baseEnd_7155980 < baseStart_7155980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7155980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156020 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7156020 : Nat := 118140960795 + 7156020 * 2 ^ 59
def prefixEnd_7156020 : Nat := 4983230072969 + 3 ^ 40 * 7156020 * 2
def baseEnd_7156020 : Nat := 1224825944395732424180023

theorem tailTrace_7156020 : CollatzResearch.WordTrace tailWord_7156020 prefixEnd_7156020 1224825944395732424180023 := by
  unfold tailWord_7156020
  simp only [CollatzResearch.WordTrace]
  refine ⟨130500745767484582880352757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174000994356646110507137009 130500745767484582880352757)
  ·
    refine ⟨12234444915701679645033071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130500745767484582880352757 12234444915701679645033071)
    ·
      refine ⟨18351667373552519467549607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234444915701679645033071 18351667373552519467549607)
      ·
        refine ⟨27527501060328779201324411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18351667373552519467549607 27527501060328779201324411)
        ·
          refine ⟨41291251590493168801986617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27527501060328779201324411 41291251590493168801986617)
          ·
            refine ⟨30968438692869876601489963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41291251590493168801986617 30968438692869876601489963)
            ·
              refine ⟨46452658039304814902234945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30968438692869876601489963 46452658039304814902234945)
              ·
                refine ⟨34839493529478611176676209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46452658039304814902234945 34839493529478611176676209)
                ·
                  refine ⟨26129620147108958382507157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34839493529478611176676209 26129620147108958382507157)
                  ·
                    refine ⟨1224825944395732424180023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26129620147108958382507157 1224825944395732424180023)
                    ·
                      rfl

theorem cell23_7156020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7156020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156020 prefixEnd_7156020 := by exact prefixLift 7156020
  have htrace : WordTrace (prefixWord ++ tailWord_7156020) baseStart_7156020 baseEnd_7156020 := by
    simpa [prefixWord, tailWord_7156020, baseEnd_7156020] using wordTrace_append hprefix tailTrace_7156020
  have hstable : (prefixWord ++ tailWord_7156020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156020).length < 2 ^ (prefixWord ++ tailWord_7156020).sum := by decide
  have hdescent : baseEnd_7156020 < baseStart_7156020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156043 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 3]
def baseStart_7156043 : Nat := 118140960795 + 7156043 * 2 ^ 59
def prefixEnd_7156043 : Nat := 4983230072969 + 3 ^ 40 * 7156043 * 2
def baseEnd_7156043 : Nat := 3674489643242250682552463

theorem tailTrace_7156043 : CollatzResearch.WordTrace tailWord_7156043 prefixEnd_7156043 3674489643242250682552463 := by
  unfold tailWord_7156043
  simp only [CollatzResearch.WordTrace]
  refine ⟨261002330413885840688792783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174001553609257227125861855 261002330413885840688792783)
  ·
    refine ⟨391503495620828761033189175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261002330413885840688792783 391503495620828761033189175)
    ·
      refine ⟨587255243431243141549783763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391503495620828761033189175 587255243431243141549783763)
      ·
        refine ⟨880882865146864712324675645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587255243431243141549783763 880882865146864712324675645)
        ·
          refine ⟨330331074430074267121753367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 880882865146864712324675645 330331074430074267121753367)
          ·
            refine ⟨495496611645111400682630051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330331074430074267121753367 495496611645111400682630051)
            ·
              refine ⟨743244917467667101023945077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495496611645111400682630051 743244917467667101023945077)
              ·
                refine ⟨69679211012593790720994851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 743244917467667101023945077 69679211012593790720994851)
                ·
                  refine ⟨104518816518890686081492277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69679211012593790720994851 104518816518890686081492277)
                  ·
                    refine ⟨9798639048646001820139901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104518816518890686081492277 9798639048646001820139901)
                    ·
                      refine ⟨3674489643242250682552463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9798639048646001820139901 3674489643242250682552463)
                      ·
                        rfl

theorem cell23_7156043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 3].length) (baseStart_7156043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7156043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7156043 prefixEnd_7156043 := by exact prefixLift 7156043
  have htrace : WordTrace (prefixWord ++ tailWord_7156043) baseStart_7156043 baseEnd_7156043 := by
    simpa [prefixWord, tailWord_7156043, baseEnd_7156043] using wordTrace_append hprefix tailTrace_7156043
  have hstable : (prefixWord ++ tailWord_7156043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156043).length < 2 ^ (prefixWord ++ tailWord_7156043).sum := by decide
  have hdescent : baseEnd_7156043 < baseStart_7156043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
