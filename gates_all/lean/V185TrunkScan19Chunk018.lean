import V185TrunkScan19Chunk017

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_181744 : List Nat := [2, 1, 1, 1, 3, 6, 5]
def baseStart_181744 : Nat := 118140960795 + 181744 * 2 ^ 59
def prefixEnd_181744 : Nat := 4983230072969 + 3 ^ 40 * 181744 * 2
def baseEnd_181744 : Nat := 18433980853499685820085

theorem tailTrace_181744 : CollatzResearch.WordTrace tailWord_181744 prefixEnd_181744 18433980853499685820085 := by
  unfold tailWord_181744
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314374126790001124568143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4419165502386668166090857 3314374126790001124568143)
  ·
    refine ⟨4971561190185001686852215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3314374126790001124568143 4971561190185001686852215)
    ·
      refine ⟨7457341785277502530278323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4971561190185001686852215 7457341785277502530278323)
      ·
        refine ⟨11186012677916253795417485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7457341785277502530278323 11186012677916253795417485)
        ·
          refine ⟨4194754754218595173281557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11186012677916253795417485 4194754754218595173281557)
          ·
            refine ⟨196629129103996648747573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4194754754218595173281557 196629129103996648747573)
            ·
              refine ⟨18433980853499685820085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196629129103996648747573 18433980853499685820085)
              ·
                rfl

theorem cell19_181744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_181744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181744 prefixEnd_181744 := by exact prefixLift 181744
  have htrace : WordTrace (prefixWord ++ tailWord_181744) baseStart_181744 baseEnd_181744 := by
    simpa [prefixWord, tailWord_181744, baseEnd_181744] using wordTrace_append hprefix tailTrace_181744
  have hstable : (prefixWord ++ tailWord_181744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181744).length < 2 ^ (prefixWord ++ tailWord_181744).sum := by decide
  have hdescent : baseEnd_181744 < baseStart_181744 := by decide
  rcases family_descends (prefixWord ++ tailWord_181744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181761 : List Nat := [1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_181761 : Nat := 118140960795 + 181761 * 2 ^ 59
def prefixEnd_181761 : Nat := 4983230072969 + 3 ^ 40 * 181761 * 2
def baseEnd_181761 : Nat := 55307115402648055082431

theorem tailTrace_181761 : CollatzResearch.WordTrace tailWord_181761 prefixEnd_181761 55307115402648055082431 := by
  unfold tailWord_181761
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629368294518414152505137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4419578863012276101670091 6629368294518414152505137)
  ·
    refine ⟨4972026220888810614378853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6629368294518414152505137 4972026220888810614378853)
    ·
      refine ⟨932254916416651990196035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4972026220888810614378853 932254916416651990196035)
      ·
        refine ⟨1398382374624977985294053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932254916416651990196035 1398382374624977985294053)
        ·
          refine ⟨262196695242183372242635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1398382374624977985294053 262196695242183372242635)
          ·
            refine ⟨393295042863275058363953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262196695242183372242635 393295042863275058363953)
            ·
              refine ⟨294971282147456293772965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393295042863275058363953 294971282147456293772965)
              ·
                refine ⟨55307115402648055082431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294971282147456293772965 55307115402648055082431)
                ·
                  rfl

theorem cell19_181761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_181761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181761 prefixEnd_181761 := by exact prefixLift 181761
  have htrace : WordTrace (prefixWord ++ tailWord_181761) baseStart_181761 baseEnd_181761 := by
    simpa [prefixWord, tailWord_181761, baseEnd_181761] using wordTrace_append hprefix tailTrace_181761
  have hstable : (prefixWord ++ tailWord_181761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181761).length < 2 ^ (prefixWord ++ tailWord_181761).sum := by decide
  have hdescent : baseEnd_181761 < baseStart_181761 := by decide
  rcases family_descends (prefixWord ++ tailWord_181761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181814 : List Nat := [5, 1, 2, 1, 4, 1, 1, 4]
def baseStart_181814 : Nat := 118140960795 + 181814 * 2 ^ 59
def prefixEnd_181814 : Nat := 4983230072969 + 3 ^ 40 * 181814 * 2
def baseEnd_181814 : Nat := 55323242498759635904509

theorem tailTrace_181814 : CollatzResearch.WordTrace tailWord_181814 prefixEnd_181814 55323242498759635904509 := by
  unfold tailWord_181814
  simp only [CollatzResearch.WordTrace]
  refine ⟨414456335207900262761531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4420867575550936136122997 414456335207900262761531)
  ·
    refine ⟨621684502811850394142297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414456335207900262761531 621684502811850394142297)
    ·
      refine ⟨466263377108887795606723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 621684502811850394142297 466263377108887795606723)
      ·
        refine ⟨699395065663331693410085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466263377108887795606723 699395065663331693410085)
        ·
          refine ⟨131136574811874692514391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 699395065663331693410085 131136574811874692514391)
          ·
            refine ⟨196704862217812038771587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131136574811874692514391 196704862217812038771587)
            ·
              refine ⟨295057293326718058157381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196704862217812038771587 295057293326718058157381)
              ·
                refine ⟨55323242498759635904509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295057293326718058157381 55323242498759635904509)
                ·
                  rfl

theorem cell19_181814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_181814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181814 prefixEnd_181814 := by exact prefixLift 181814
  have htrace : WordTrace (prefixWord ++ tailWord_181814) baseStart_181814 baseEnd_181814 := by
    simpa [prefixWord, tailWord_181814, baseEnd_181814] using wordTrace_append hprefix tailTrace_181814
  have hstable : (prefixWord ++ tailWord_181814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181814).length < 2 ^ (prefixWord ++ tailWord_181814).sum := by decide
  have hdescent : baseEnd_181814 < baseStart_181814 := by decide
  rcases family_descends (prefixWord ++ tailWord_181814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181879 : List Nat := [1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_181879 : Nat := 118140960795 + 181879 * 2 ^ 59
def prefixEnd_181879 : Nat := 4983230072969 + 3 ^ 40 * 181879 * 2
def baseEnd_181879 : Nat := 55343021012858744459887

theorem tailTrace_181879 : CollatzResearch.WordTrace tailWord_181879 prefixEnd_181879 55343021012858744459887 := by
  unfold tailWord_181879
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633672108090920305300691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4422448072060613536867127 6633672108090920305300691)
  ·
    refine ⟨9950508162136380457951037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633672108090920305300691 9950508162136380457951037)
    ·
      refine ⟨3731440560801142671731639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9950508162136380457951037 3731440560801142671731639)
      ·
        refine ⟨5597160841201714007597459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731440560801142671731639 5597160841201714007597459)
        ·
          refine ⟨8395741261802571011396189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5597160841201714007597459 8395741261802571011396189)
          ·
            refine ⟨3148402973175964129273571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8395741261802571011396189 3148402973175964129273571)
            ·
              refine ⟨4722604459763946193910357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148402973175964129273571 4722604459763946193910357)
              ·
                refine ⟨55343021012858744459887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4722604459763946193910357 55343021012858744459887)
                ·
                  rfl

theorem cell19_181879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_181879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181879 prefixEnd_181879 := by exact prefixLift 181879
  have htrace : WordTrace (prefixWord ++ tailWord_181879) baseStart_181879 baseEnd_181879 := by
    simpa [prefixWord, tailWord_181879, baseEnd_181879] using wordTrace_append hprefix tailTrace_181879
  have hstable : (prefixWord ++ tailWord_181879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181879).length < 2 ^ (prefixWord ++ tailWord_181879).sum := by decide
  have hdescent : baseEnd_181879 < baseStart_181879 := by decide
  rcases family_descends (prefixWord ++ tailWord_181879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181892 : List Nat := [2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_181892 : Nat := 118140960795 + 181892 * 2 ^ 59
def prefixEnd_181892 : Nat := 4983230072969 + 3 ^ 40 * 181892 * 2
def baseEnd_181892 : Nat := 55346976715678566170963

theorem tailTrace_181892 : CollatzResearch.WordTrace tailWord_181892 prefixEnd_181892 55346976715678566170963 := by
  unfold tailWord_181892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317073128521911762761965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4422764171362549017015953 3317073128521911762761965)
  ·
    refine ⟨1243902423195716911035737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3317073128521911762761965 1243902423195716911035737)
    ·
      refine ⟨932926817396787683276803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1243902423195716911035737 932926817396787683276803)
      ·
        refine ⟨1399390226095181524915205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932926817396787683276803 1399390226095181524915205)
        ·
          refine ⟨262385667392846535921601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1399390226095181524915205 262385667392846535921601)
          ·
            refine ⟨196789250544634901941201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262385667392846535921601 196789250544634901941201)
            ·
              refine ⟨147591937908476176455901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196789250544634901941201 147591937908476176455901)
              ·
                refine ⟨55346976715678566170963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147591937908476176455901 55346976715678566170963)
                ·
                  rfl

theorem cell19_181892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_181892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181892 prefixEnd_181892 := by exact prefixLift 181892
  have htrace : WordTrace (prefixWord ++ tailWord_181892) baseStart_181892 baseEnd_181892 := by
    simpa [prefixWord, tailWord_181892, baseEnd_181892] using wordTrace_append hprefix tailTrace_181892
  have hstable : (prefixWord ++ tailWord_181892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181892).length < 2 ^ (prefixWord ++ tailWord_181892).sum := by decide
  have hdescent : baseEnd_181892 < baseStart_181892 := by decide
  rcases family_descends (prefixWord ++ tailWord_181892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181928 : List Nat := [2, 1, 7, 1, 1, 1, 2, 4]
def baseStart_181928 : Nat := 118140960795 + 181928 * 2 ^ 59
def prefixEnd_181928 : Nat := 4983230072969 + 3 ^ 40 * 181928 * 2
def baseEnd_181928 : Nat := 55357930969641149370865

theorem tailTrace_181928 : CollatzResearch.WordTrace tailWord_181928 prefixEnd_181928 55357930969641149370865 := by
  unfold tailWord_181928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317729642456700836917219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4423639523275601115889625 3317729642456700836917219)
  ·
    refine ⟨4976594463685051255375829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3317729642456700836917219 4976594463685051255375829)
    ·
      refine ⟨116638932742618388797871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4976594463685051255375829 116638932742618388797871)
      ·
        refine ⟨174958399113927583196807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116638932742618388797871 174958399113927583196807)
        ·
          refine ⟨262437598670891374795211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174958399113927583196807 262437598670891374795211)
          ·
            refine ⟨393656398006337062192817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262437598670891374795211 393656398006337062192817)
            ·
              refine ⟨295242298504752796644613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393656398006337062192817 295242298504752796644613)
              ·
                refine ⟨55357930969641149370865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295242298504752796644613 55357930969641149370865)
                ·
                  rfl

theorem cell19_181928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_181928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181928 prefixEnd_181928 := by exact prefixLift 181928
  have htrace : WordTrace (prefixWord ++ tailWord_181928) baseStart_181928 baseEnd_181928 := by
    simpa [prefixWord, tailWord_181928, baseEnd_181928] using wordTrace_append hprefix tailTrace_181928
  have hstable : (prefixWord ++ tailWord_181928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181928).length < 2 ^ (prefixWord ++ tailWord_181928).sum := by decide
  have hdescent : baseEnd_181928 < baseStart_181928 := by decide
  rcases family_descends (prefixWord ++ tailWord_181928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181936 : List Nat := [2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_181936 : Nat := 118140960795 + 181936 * 2 ^ 59
def prefixEnd_181936 : Nat := 4983230072969 + 3 ^ 40 * 181936 * 2
def baseEnd_181936 : Nat := 55360365248299501193065

theorem tailTrace_181936 : CollatzResearch.WordTrace tailWord_181936 prefixEnd_181936 55360365248299501193065 := by
  unfold tailWord_181936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317875534442209520062831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4423834045922946026750441 3317875534442209520062831)
  ·
    refine ⟨4976813301663314280094247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3317875534442209520062831 4976813301663314280094247)
    ·
      refine ⟨7465219952494971420141371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4976813301663314280094247 7465219952494971420141371)
      ·
        refine ⟨11197829928742457130212057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465219952494971420141371 11197829928742457130212057)
        ·
          refine ⟨8398372446556842847659043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11197829928742457130212057 8398372446556842847659043)
          ·
            refine ⟨12597558669835264271488565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398372446556842847659043 12597558669835264271488565)
            ·
              refine ⟨1181021125297056025452053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12597558669835264271488565 1181021125297056025452053)
              ·
                refine ⟨55360365248299501193065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1181021125297056025452053 55360365248299501193065)
                ·
                  rfl

theorem cell19_181936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_181936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181936 prefixEnd_181936 := by exact prefixLift 181936
  have htrace : WordTrace (prefixWord ++ tailWord_181936) baseStart_181936 baseEnd_181936 := by
    simpa [prefixWord, tailWord_181936, baseEnd_181936] using wordTrace_append hprefix tailTrace_181936
  have hstable : (prefixWord ++ tailWord_181936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181936).length < 2 ^ (prefixWord ++ tailWord_181936).sum := by decide
  have hdescent : baseEnd_181936 < baseStart_181936 := by decide
  rcases family_descends (prefixWord ++ tailWord_181936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181972 : List Nat := [2, 4, 1, 3, 1, 8]
def baseStart_181972 : Nat := 118140960795 + 181972 * 2 ^ 59
def prefixEnd_181972 : Nat := 4983230072969 + 3 ^ 40 * 181972 * 2
def baseEnd_181972 : Nat := 6152368833584676043663

theorem tailTrace_181972 : CollatzResearch.WordTrace tailWord_181972 prefixEnd_181972 6152368833584676043663 := by
  unfold tailWord_181972
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318532048376998594218085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4424709397835998125624113 3318532048376998594218085)
  ·
    refine ⟨622224759070687236415891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3318532048376998594218085 622224759070687236415891)
    ·
      refine ⟨933337138606030854623837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622224759070687236415891 933337138606030854623837)
      ·
        refine ⟨350001426977261570483939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 933337138606030854623837 350001426977261570483939)
        ·
          refine ⟨525002140465892355725909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350001426977261570483939 525002140465892355725909)
          ·
            refine ⟨6152368833584676043663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 525002140465892355725909 6152368833584676043663)
            ·
              rfl

theorem cell19_181972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_181972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181972 prefixEnd_181972 := by exact prefixLift 181972
  have htrace : WordTrace (prefixWord ++ tailWord_181972) baseStart_181972 baseEnd_181972 := by
    simpa [prefixWord, tailWord_181972, baseEnd_181972] using wordTrace_append hprefix tailTrace_181972
  have hstable : (prefixWord ++ tailWord_181972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181972).length < 2 ^ (prefixWord ++ tailWord_181972).sum := by decide
  have hdescent : baseEnd_181972 < baseStart_181972 := by decide
  rcases family_descends (prefixWord ++ tailWord_181972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181987 : List Nat := [1, 1, 1, 7, 3, 1, 1, 4]
def baseStart_181987 : Nat := 118140960795 + 181987 * 2 ^ 59
def prefixEnd_181987 : Nat := 4983230072969 + 3 ^ 40 * 181987 * 2
def baseEnd_181987 : Nat := 55375883774746494059593

theorem tailTrace_181987 : CollatzResearch.WordTrace tailWord_181987 prefixEnd_181987 55375883774746494059593 := by
  unfold tailWord_181987
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637611191699654750232215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4425074127799769833488143 6637611191699654750232215)
  ·
    refine ⟨9956416787549482125348323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6637611191699654750232215 9956416787549482125348323)
    ·
      refine ⟨14934625181324223188022485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9956416787549482125348323 14934625181324223188022485)
      ·
        refine ⟨350030277687286480969277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14934625181324223188022485 350030277687286480969277)
        ·
          refine ⟨131261354132732430363479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350030277687286480969277 131261354132732430363479)
          ·
            refine ⟨196892031199098645545219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131261354132732430363479 196892031199098645545219)
            ·
              refine ⟨295338046798647968317829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196892031199098645545219 295338046798647968317829)
              ·
                refine ⟨55375883774746494059593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295338046798647968317829 55375883774746494059593)
                ·
                  rfl

theorem cell19_181987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_181987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_181987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_181987 prefixEnd_181987 := by exact prefixLift 181987
  have htrace : WordTrace (prefixWord ++ tailWord_181987) baseStart_181987 baseEnd_181987 := by
    simpa [prefixWord, tailWord_181987, baseEnd_181987] using wordTrace_append hprefix tailTrace_181987
  have hstable : (prefixWord ++ tailWord_181987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181987).length < 2 ^ (prefixWord ++ tailWord_181987).sum := by decide
  have hdescent : baseEnd_181987 < baseStart_181987 := by decide
  rcases family_descends (prefixWord ++ tailWord_181987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182004 : List Nat := [2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_182004 : Nat := 118140960795 + 182004 * 2 ^ 59
def prefixEnd_182004 : Nat := 4983230072969 + 3 ^ 40 * 182004 * 2
def baseEnd_182004 : Nat := 55381056616895491681769

theorem tailTrace_182004 : CollatzResearch.WordTrace tailWord_182004 prefixEnd_182004 55381056616895491681769 := by
  unfold tailWord_182004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319115616319033326800533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4425487488425377769067377 3319115616319033326800533)
  ·
    refine ⟨155583544514954687193775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3319115616319033326800533 155583544514954687193775)
    ·
      refine ⟨233375316772432030790663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155583544514954687193775 233375316772432030790663)
      ·
        refine ⟨350062975158648046185995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233375316772432030790663 350062975158648046185995)
        ·
          refine ⟨525094462737972069278993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350062975158648046185995 525094462737972069278993)
          ·
            refine ⟨393820847053479051959245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525094462737972069278993 393820847053479051959245)
            ·
              refine ⟨147682817645054644484717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393820847053479051959245 147682817645054644484717)
              ·
                refine ⟨55381056616895491681769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147682817645054644484717 55381056616895491681769)
                ·
                  rfl

theorem cell19_182004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_182004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182004 prefixEnd_182004 := by exact prefixLift 182004
  have htrace : WordTrace (prefixWord ++ tailWord_182004) baseStart_182004 baseEnd_182004 := by
    simpa [prefixWord, tailWord_182004, baseEnd_182004] using wordTrace_append hprefix tailTrace_182004
  have hstable : (prefixWord ++ tailWord_182004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182004).length < 2 ^ (prefixWord ++ tailWord_182004).sum := by decide
  have hdescent : baseEnd_182004 < baseStart_182004 := by decide
  rcases family_descends (prefixWord ++ tailWord_182004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182065 : List Nat := [1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_182065 : Nat := 118140960795 + 182065 * 2 ^ 59
def prefixEnd_182065 : Nat := 4983230072969 + 3 ^ 40 * 182065 * 2
def baseEnd_182065 : Nat := 55399617991665424326047

theorem tailTrace_182065 : CollatzResearch.WordTrace tailWord_182065 prefixEnd_182065 55399617991665424326047 := by
  unfold tailWord_182065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640456085417074071571649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4426970723611382714381099 6640456085417074071571649)
  ·
    refine ⟨4980342064062805553678737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6640456085417074071571649 4980342064062805553678737)
    ·
      refine ⟨3735256548047104165259053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4980342064062805553678737 3735256548047104165259053)
      ·
        refine ⟨1400721205517664061972145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3735256548047104165259053 1400721205517664061972145)
        ·
          refine ⟨1050540904138248046479109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400721205517664061972145 1050540904138248046479109)
          ·
            refine ⟨196976419525921508714833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1050540904138248046479109 196976419525921508714833)
            ·
              refine ⟨147732314644441131536125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196976419525921508714833 147732314644441131536125)
              ·
                refine ⟨55399617991665424326047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147732314644441131536125 55399617991665424326047)
                ·
                  rfl

theorem cell19_182065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_182065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182065 prefixEnd_182065 := by exact prefixLift 182065
  have htrace : WordTrace (prefixWord ++ tailWord_182065) baseStart_182065 baseEnd_182065 := by
    simpa [prefixWord, tailWord_182065, baseEnd_182065] using wordTrace_append hprefix tailTrace_182065
  have hstable : (prefixWord ++ tailWord_182065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182065).length < 2 ^ (prefixWord ++ tailWord_182065).sum := by decide
  have hdescent : baseEnd_182065 < baseStart_182065 := by decide
  rcases family_descends (prefixWord ++ tailWord_182065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182067 : List Nat := [1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_182067 : Nat := 118140960795 + 182067 * 2 ^ 59
def prefixEnd_182067 : Nat := 4983230072969 + 3 ^ 40 * 182067 * 2
def baseEnd_182067 : Nat := 55400226561330012281597

theorem tailTrace_182067 : CollatzResearch.WordTrace tailWord_182067 prefixEnd_182067 55400226561330012281597 := by
  unfold tailWord_182067
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640529031409828413144455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4427019354273218942096303 6640529031409828413144455)
  ·
    refine ⟨9960793547114742619716683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640529031409828413144455 9960793547114742619716683)
    ·
      refine ⟨14941190320672113929575025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9960793547114742619716683 14941190320672113929575025)
      ·
        refine ⟨11205892740504085447181269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14941190320672113929575025 11205892740504085447181269)
        ·
          refine ⟨262638111105564502668311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11205892740504085447181269 262638111105564502668311)
          ·
            refine ⟨393957166658346754002467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262638111105564502668311 393957166658346754002467)
            ·
              refine ⟨590935749987520131003701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393957166658346754002467 590935749987520131003701)
              ·
                refine ⟨55400226561330012281597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 590935749987520131003701 55400226561330012281597)
                ·
                  rfl

theorem cell19_182067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_182067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182067 prefixEnd_182067 := by exact prefixLift 182067
  have htrace : WordTrace (prefixWord ++ tailWord_182067) baseStart_182067 baseEnd_182067 := by
    simpa [prefixWord, tailWord_182067, baseEnd_182067] using wordTrace_append hprefix tailTrace_182067
  have hstable : (prefixWord ++ tailWord_182067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182067).length < 2 ^ (prefixWord ++ tailWord_182067).sum := by decide
  have hdescent : baseEnd_182067 < baseStart_182067 := by decide
  rcases family_descends (prefixWord ++ tailWord_182067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182088 : List Nat := [2, 1, 3, 1, 1, 4, 7]
def baseStart_182088 : Nat := 118140960795 + 182088 * 2 ^ 59
def prefixEnd_182088 : Nat := 4983230072969 + 3 ^ 40 * 182088 * 2
def baseEnd_182088 : Nat := 18468872180936061938291

theorem tailTrace_182088 : CollatzResearch.WordTrace tailWord_182088 prefixEnd_182088 18468872180936061938291 := by
  unfold tailWord_182088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320647482166874499829459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4427529976222499333105945 3320647482166874499829459)
  ·
    refine ⟨4980971223250311749744189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3320647482166874499829459 4980971223250311749744189)
    ·
      refine ⟨1867864208718866906154071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4980971223250311749744189 1867864208718866906154071)
      ·
        refine ⟨2801796313078300359231107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867864208718866906154071 2801796313078300359231107)
        ·
          refine ⟨4202694469617450538846661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801796313078300359231107 4202694469617450538846661)
          ·
            refine ⟨788005213053271976033749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4202694469617450538846661 788005213053271976033749)
            ·
              refine ⟨18468872180936061938291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 788005213053271976033749 18468872180936061938291)
              ·
                rfl

theorem cell19_182088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_182088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182088 prefixEnd_182088 := by exact prefixLift 182088
  have htrace : WordTrace (prefixWord ++ tailWord_182088) baseStart_182088 baseEnd_182088 := by
    simpa [prefixWord, tailWord_182088, baseEnd_182088] using wordTrace_append hprefix tailTrace_182088
  have hstable : (prefixWord ++ tailWord_182088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182088).length < 2 ^ (prefixWord ++ tailWord_182088).sum := by decide
  have hdescent : baseEnd_182088 < baseStart_182088 := by decide
  rcases family_descends (prefixWord ++ tailWord_182088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182158 : List Nat := [4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_182158 : Nat := 118140960795 + 182158 * 2 ^ 59
def prefixEnd_182158 : Nat := 4983230072969 + 3 ^ 40 * 182158 * 2
def baseEnd_182158 : Nat := 55427916481068764259127

theorem tailTrace_182158 : CollatzResearch.WordTrace tailWord_182158 prefixEnd_182158 55427916481068764259127 := by
  unfold tailWord_182158
  simp only [CollatzResearch.WordTrace]
  refine ⟨830481009260018869338391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4429232049386767303138085 830481009260018869338391)
  ·
    refine ⟨1245721513890028304007587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830481009260018869338391 1245721513890028304007587)
    ·
      refine ⟨1868582270835042456011381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245721513890028304007587 1868582270835042456011381)
      ·
        refine ⟨175179587890785230251067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1868582270835042456011381 175179587890785230251067)
        ·
          refine ⟨262769381836177845376601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175179587890785230251067 262769381836177845376601)
          ·
            refine ⟨197077036377133384032451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262769381836177845376601 197077036377133384032451)
            ·
              refine ⟨295615554565700076048677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197077036377133384032451 295615554565700076048677)
              ·
                refine ⟨55427916481068764259127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295615554565700076048677 55427916481068764259127)
                ·
                  rfl

theorem cell19_182158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_182158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182158 prefixEnd_182158 := by exact prefixLift 182158
  have htrace : WordTrace (prefixWord ++ tailWord_182158) baseStart_182158 baseEnd_182158 := by
    simpa [prefixWord, tailWord_182158, baseEnd_182158] using wordTrace_append hprefix tailTrace_182158
  have hstable : (prefixWord ++ tailWord_182158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182158).length < 2 ^ (prefixWord ++ tailWord_182158).sum := by decide
  have hdescent : baseEnd_182158 < baseStart_182158 := by decide
  rcases family_descends (prefixWord ++ tailWord_182158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182234 : List Nat := [3, 1, 1, 2, 6, 1, 2, 3]
def baseStart_182234 : Nat := 118140960795 + 182234 * 2 ^ 59
def prefixEnd_182234 : Nat := 4983230072969 + 3 ^ 40 * 182234 * 2
def baseEnd_182234 : Nat := 55451042128323106570031

theorem tailTrace_182234 : CollatzResearch.WordTrace tailWord_182234 prefixEnd_182234 55451042128323106570031 := by
  unfold tailWord_182234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661655005451203983618439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4431080014536543956315837 1661655005451203983618439)
  ·
    refine ⟨2492482508176805975427659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1661655005451203983618439 2492482508176805975427659)
    ·
      refine ⟨3738723762265208963141489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2492482508176805975427659 3738723762265208963141489)
      ·
        refine ⟨2804042821698906722356117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3738723762265208963141489 2804042821698906722356117)
        ·
          refine ⟨131439507267136252610443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2804042821698906722356117 131439507267136252610443)
          ·
            refine ⟨197159260900704378915665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131439507267136252610443 197159260900704378915665)
            ·
              refine ⟨147869445675528284186749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197159260900704378915665 147869445675528284186749)
              ·
                refine ⟨55451042128323106570031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147869445675528284186749 55451042128323106570031)
                ·
                  rfl

theorem cell19_182234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_182234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182234 prefixEnd_182234 := by exact prefixLift 182234
  have htrace : WordTrace (prefixWord ++ tailWord_182234) baseStart_182234 baseEnd_182234 := by
    simpa [prefixWord, tailWord_182234, baseEnd_182234] using wordTrace_append hprefix tailTrace_182234
  have hstable : (prefixWord ++ tailWord_182234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182234).length < 2 ^ (prefixWord ++ tailWord_182234).sum := by decide
  have hdescent : baseEnd_182234 < baseStart_182234 := by decide
  rcases family_descends (prefixWord ++ tailWord_182234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182253 : List Nat := [1, 5, 1, 4, 2, 1, 5]
def baseStart_182253 : Nat := 118140960795 + 182253 * 2 ^ 59
def prefixEnd_182253 : Nat := 4983230072969 + 3 ^ 40 * 182253 * 2
def baseEnd_182253 : Nat := 18485607846712230715919

theorem tailTrace_182253 : CollatzResearch.WordTrace tailWord_182253 prefixEnd_182253 18485607846712230715919 := by
  unfold tailWord_182253
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647313008735982179415413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4431542005823988119610275 6647313008735982179415413)
  ·
    refine ⟨623185594568998329320195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6647313008735982179415413 623185594568998329320195)
    ·
      refine ⟨934778391853497493980293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623185594568998329320195 934778391853497493980293)
      ·
        refine ⟨175270948472530780121305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 934778391853497493980293 175270948472530780121305)
        ·
          refine ⟨131453211354398085090979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175270948472530780121305 131453211354398085090979)
          ·
            refine ⟨197179817031597127636469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131453211354398085090979 197179817031597127636469)
            ·
              refine ⟨18485607846712230715919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197179817031597127636469 18485607846712230715919)
              ·
                rfl

theorem cell19_182253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_182253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182253 prefixEnd_182253 := by exact prefixLift 182253
  have htrace : WordTrace (prefixWord ++ tailWord_182253) baseStart_182253 baseEnd_182253 := by
    simpa [prefixWord, tailWord_182253, baseEnd_182253] using wordTrace_append hprefix tailTrace_182253
  have hstable : (prefixWord ++ tailWord_182253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182253).length < 2 ^ (prefixWord ++ tailWord_182253).sum := by decide
  have hdescent : baseEnd_182253 < baseStart_182253 := by decide
  rcases family_descends (prefixWord ++ tailWord_182253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182257 : List Nat := [1, 2, 2, 2, 5, 2, 5]
def baseStart_182257 : Nat := 118140960795 + 182257 * 2 ^ 59
def prefixEnd_182257 : Nat := 4983230072969 + 3 ^ 40 * 182257 * 2
def baseEnd_182257 : Nat := 18486013559821956019619

theorem tailTrace_182257 : CollatzResearch.WordTrace tailWord_182257 prefixEnd_182257 18486013559821956019619 := by
  unfold tailWord_182257
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647458900721490862561025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4431639267147660575040683 6647458900721490862561025)
  ·
    refine ⟨4985594175541118146920769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6647458900721490862561025 4985594175541118146920769)
    ·
      refine ⟨3739195631655838610190577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4985594175541118146920769 3739195631655838610190577)
      ·
        refine ⟨2804396723741878957642933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3739195631655838610190577 2804396723741878957642933)
        ·
          refine ⟨262912192850801152279025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2804396723741878957642933 262912192850801152279025)
          ·
            refine ⟨197184144638100864209269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262912192850801152279025 197184144638100864209269)
            ·
              refine ⟨18486013559821956019619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197184144638100864209269 18486013559821956019619)
              ·
                rfl

theorem cell19_182257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_182257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182257 prefixEnd_182257 := by exact prefixLift 182257
  have htrace : WordTrace (prefixWord ++ tailWord_182257) baseStart_182257 baseEnd_182257 := by
    simpa [prefixWord, tailWord_182257, baseEnd_182257] using wordTrace_append hprefix tailTrace_182257
  have hstable : (prefixWord ++ tailWord_182257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182257).length < 2 ^ (prefixWord ++ tailWord_182257).sum := by decide
  have hdescent : baseEnd_182257 < baseStart_182257 := by decide
  rcases family_descends (prefixWord ++ tailWord_182257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182312 : List Nat := [2, 1, 5, 3, 2, 6]
def baseStart_182312 : Nat := 118140960795 + 182312 * 2 ^ 59
def prefixEnd_182312 : Nat := 4983230072969 + 3 ^ 40 * 182312 * 2
def baseEnd_182312 : Nat := 6163864038360226315165

theorem tailTrace_182312 : CollatzResearch.WordTrace tailWord_182312 prefixEnd_182312 6163864038360226315165 := by
  unfold tailWord_182312
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324732457761117627906595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4432976610348156837208793 3324732457761117627906595)
  ·
    refine ⟨4987098686641676441859893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3324732457761117627906595 4987098686641676441859893)
    ·
      refine ⟨467540501872657166424365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4987098686641676441859893 467540501872657166424365)
      ·
        refine ⟨175327688202246437409137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467540501872657166424365 175327688202246437409137)
        ·
          refine ⟨131495766151684828056853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175327688202246437409137 131495766151684828056853)
          ·
            refine ⟨6163864038360226315165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131495766151684828056853 6163864038360226315165)
            ·
              rfl

theorem cell19_182312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_182312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182312 prefixEnd_182312 := by exact prefixLift 182312
  have htrace : WordTrace (prefixWord ++ tailWord_182312) baseStart_182312 baseEnd_182312 := by
    simpa [prefixWord, tailWord_182312, baseEnd_182312] using wordTrace_append hprefix tailTrace_182312
  have hstable : (prefixWord ++ tailWord_182312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182312).length < 2 ^ (prefixWord ++ tailWord_182312).sum := by decide
  have hdescent : baseEnd_182312 < baseStart_182312 := by decide
  rcases family_descends (prefixWord ++ tailWord_182312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182335 : List Nat := [1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_182335 : Nat := 118140960795 + 182335 * 2 ^ 59
def prefixEnd_182335 : Nat := 4983230072969 + 3 ^ 40 * 182335 * 2
def baseEnd_182335 : Nat := 55481774896384798325311

theorem tailTrace_182335 : CollatzResearch.WordTrace tailWord_182335 prefixEnd_182335 55481774896384798325311 := by
  unfold tailWord_182335
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650303794438910183900459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4433535862959273455933639 6650303794438910183900459)
  ·
    refine ⟨9975455691658365275850689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6650303794438910183900459 9975455691658365275850689)
    ·
      refine ⟨7481591768743773956888017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9975455691658365275850689 7481591768743773956888017)
      ·
        refine ⟨5611193826557830467666013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7481591768743773956888017 5611193826557830467666013)
        ·
          refine ⟨2104197684959186425374755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5611193826557830467666013 2104197684959186425374755)
          ·
            refine ⟨3156296527438779638062133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104197684959186425374755 3156296527438779638062133)
            ·
              refine ⟨295902799447385591068325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3156296527438779638062133 295902799447385591068325)
              ·
                refine ⟨55481774896384798325311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295902799447385591068325 55481774896384798325311)
                ·
                  rfl

theorem cell19_182335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_182335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182335 prefixEnd_182335 := by exact prefixLift 182335
  have htrace : WordTrace (prefixWord ++ tailWord_182335) baseStart_182335 baseEnd_182335 := by
    simpa [prefixWord, tailWord_182335, baseEnd_182335] using wordTrace_append hprefix tailTrace_182335
  have hstable : (prefixWord ++ tailWord_182335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182335).length < 2 ^ (prefixWord ++ tailWord_182335).sum := by decide
  have hdescent : baseEnd_182335 < baseStart_182335 := by decide
  rcases family_descends (prefixWord ++ tailWord_182335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182373 : List Nat := [1, 3, 1, 3, 2, 3, 6]
def baseStart_182373 : Nat := 118140960795 + 182373 * 2 ^ 59
def prefixEnd_182373 : Nat := 4983230072969 + 3 ^ 40 * 182373 * 2
def baseEnd_182373 : Nat := 18497779240003989826921

theorem tailTrace_182373 : CollatzResearch.WordTrace tailWord_182373 prefixEnd_182373 18497779240003989826921 := by
  unfold tailWord_182373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651689768301242673783773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4434459845534161782522515 6651689768301242673783773)
  ·
    refine ⟨2494383663112966002668915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6651689768301242673783773 2494383663112966002668915)
    ·
      refine ⟨3741575494669449004003373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494383663112966002668915 3741575494669449004003373)
      ·
        refine ⟨1403090810501043376501265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3741575494669449004003373 1403090810501043376501265)
        ·
          refine ⟨1052318107875782532375949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1403090810501043376501265 1052318107875782532375949)
          ·
            refine ⟨394619290453418449640981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052318107875782532375949 394619290453418449640981)
            ·
              refine ⟨18497779240003989826921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 394619290453418449640981 18497779240003989826921)
              ·
                rfl

theorem cell19_182373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_182373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182373 prefixEnd_182373 := by exact prefixLift 182373
  have htrace : WordTrace (prefixWord ++ tailWord_182373) baseStart_182373 baseEnd_182373 := by
    simpa [prefixWord, tailWord_182373, baseEnd_182373] using wordTrace_append hprefix tailTrace_182373
  have hstable : (prefixWord ++ tailWord_182373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182373).length < 2 ^ (prefixWord ++ tailWord_182373).sum := by decide
  have hdescent : baseEnd_182373 < baseStart_182373 := by decide
  rcases family_descends (prefixWord ++ tailWord_182373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182426 : List Nat := [3, 1, 1, 5, 3, 1, 5]
def baseStart_182426 : Nat := 118140960795 + 182426 * 2 ^ 59
def prefixEnd_182426 : Nat := 4983230072969 + 3 ^ 40 * 182426 * 2
def baseEnd_182426 : Nat := 18503154938707850100947

theorem tailTrace_182426 : CollatzResearch.WordTrace tailWord_182426 prefixEnd_182426 18503154938707850100947 := by
  unfold tailWord_182426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663405709277308181365783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4435748558072821816975421 1663405709277308181365783)
  ·
    refine ⟨2495108563915962272048675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1663405709277308181365783 2495108563915962272048675)
    ·
      refine ⟨3742662845873943408073013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495108563915962272048675 3742662845873943408073013)
      ·
        refine ⟨350874641800682194506845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3742662845873943408073013 350874641800682194506845)
        ·
          refine ⟨131577990675255822940067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350874641800682194506845 131577990675255822940067)
          ·
            refine ⟨197366986012883734410101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131577990675255822940067 197366986012883734410101)
            ·
              refine ⟨18503154938707850100947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197366986012883734410101 18503154938707850100947)
              ·
                rfl

theorem cell19_182426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_182426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182426 prefixEnd_182426 := by exact prefixLift 182426
  have htrace : WordTrace (prefixWord ++ tailWord_182426) baseStart_182426 baseEnd_182426 := by
    simpa [prefixWord, tailWord_182426, baseEnd_182426] using wordTrace_append hprefix tailTrace_182426
  have hstable : (prefixWord ++ tailWord_182426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182426).length < 2 ^ (prefixWord ++ tailWord_182426).sum := by decide
  have hdescent : baseEnd_182426 < baseStart_182426 := by decide
  rcases family_descends (prefixWord ++ tailWord_182426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182485 : List Nat := [1, 3, 2, 4, 3, 6]
def baseStart_182485 : Nat := 118140960795 + 182485 * 2 ^ 59
def prefixEnd_182485 : Nat := 4983230072969 + 3 ^ 40 * 182485 * 2
def baseEnd_182485 : Nat := 6169713069025432776841

theorem tailTrace_182485 : CollatzResearch.WordTrace tailWord_182485 prefixEnd_182485 6169713069025432776841 := by
  unfold tailWord_182485
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655774743895485801860909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4437183162596990534573939 6655774743895485801860909)
  ·
    refine ⟨2495915528960807175697841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6655774743895485801860909 2495915528960807175697841)
    ·
      refine ⟨1871936646720605381773381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2495915528960807175697841 1871936646720605381773381)
      ·
        refine ⟨350988121260113509082509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1871936646720605381773381 350988121260113509082509)
        ·
          refine ⟨131620545472542565905941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350988121260113509082509 131620545472542565905941)
          ·
            refine ⟨6169713069025432776841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131620545472542565905941 6169713069025432776841)
            ·
              rfl

theorem cell19_182485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_182485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182485 prefixEnd_182485 := by exact prefixLift 182485
  have htrace : WordTrace (prefixWord ++ tailWord_182485) baseStart_182485 baseEnd_182485 := by
    simpa [prefixWord, tailWord_182485, baseEnd_182485] using wordTrace_append hprefix tailTrace_182485
  have hstable : (prefixWord ++ tailWord_182485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182485).length < 2 ^ (prefixWord ++ tailWord_182485).sum := by decide
  have hdescent : baseEnd_182485 < baseStart_182485 := by decide
  rcases family_descends (prefixWord ++ tailWord_182485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182498 : List Nat := [3, 3, 4, 1, 1, 2, 1, 4]
def baseStart_182498 : Nat := 118140960795 + 182498 * 2 ^ 59
def prefixEnd_182498 : Nat := 4983230072969 + 3 ^ 40 * 182498 * 2
def baseEnd_182498 : Nat := 55531373324048716702645

theorem tailTrace_182498 : CollatzResearch.WordTrace tailWord_182498 prefixEnd_182498 55531373324048716702645 := by
  unfold tailWord_182498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664062223212097255521037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4437499261898926014722765 1664062223212097255521037)
  ·
    refine ⟨624023333704536470820389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1664062223212097255521037 624023333704536470820389)
    ·
      refine ⟨117004375069600588278823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 624023333704536470820389 117004375069600588278823)
      ·
        refine ⟨175506562604400882418235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117004375069600588278823 175506562604400882418235)
        ·
          refine ⟨263259843906601323627353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175506562604400882418235 263259843906601323627353)
          ·
            refine ⟨197444882929950992720515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263259843906601323627353 197444882929950992720515)
            ·
              refine ⟨296167324394926489080773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197444882929950992720515 296167324394926489080773)
              ·
                refine ⟨55531373324048716702645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296167324394926489080773 55531373324048716702645)
                ·
                  rfl

theorem cell19_182498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_182498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182498 prefixEnd_182498 := by exact prefixLift 182498
  have htrace : WordTrace (prefixWord ++ tailWord_182498) baseStart_182498 baseEnd_182498 := by
    simpa [prefixWord, tailWord_182498, baseEnd_182498] using wordTrace_append hprefix tailTrace_182498
  have hstable : (prefixWord ++ tailWord_182498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182498).length < 2 ^ (prefixWord ++ tailWord_182498).sum := by decide
  have hdescent : baseEnd_182498 < baseStart_182498 := by decide
  rcases family_descends (prefixWord ++ tailWord_182498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182504 : List Nat := [2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_182504 : Nat := 118140960795 + 182504 * 2 ^ 59
def prefixEnd_182504 : Nat := 4983230072969 + 3 ^ 40 * 182504 * 2
def baseEnd_182504 : Nat := 55533199033042480569295

theorem tailTrace_182504 : CollatzResearch.WordTrace tailWord_182504 prefixEnd_182504 55533199033042480569295 := by
  unfold tailWord_182504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328233865413326023401283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4437645153884434697868377 3328233865413326023401283)
  ·
    refine ⟨4992350798119989035101925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3328233865413326023401283 4992350798119989035101925)
    ·
      refine ⟨936065774647497944081611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4992350798119989035101925 936065774647497944081611)
      ·
        refine ⟨1404098661971246916122417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936065774647497944081611 1404098661971246916122417)
        ·
          refine ⟨1053073996478435187091813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1404098661971246916122417 1053073996478435187091813)
          ·
            refine ⟨197451374339706597579715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1053073996478435187091813 197451374339706597579715)
            ·
              refine ⟨296177061509559896369573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197451374339706597579715 296177061509559896369573)
              ·
                refine ⟨55533199033042480569295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296177061509559896369573 55533199033042480569295)
                ·
                  rfl

theorem cell19_182504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_182504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182504 prefixEnd_182504 := by exact prefixLift 182504
  have htrace : WordTrace (prefixWord ++ tailWord_182504) baseStart_182504 baseEnd_182504 := by
    simpa [prefixWord, tailWord_182504, baseEnd_182504] using wordTrace_append hprefix tailTrace_182504
  have hstable : (prefixWord ++ tailWord_182504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182504).length < 2 ^ (prefixWord ++ tailWord_182504).sum := by decide
  have hdescent : baseEnd_182504 < baseStart_182504 := by decide
  rcases family_descends (prefixWord ++ tailWord_182504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182574 : List Nat := [4, 1, 3, 3, 2, 1, 2, 3]
def baseStart_182574 : Nat := 118140960795 + 182574 * 2 ^ 59
def prefixEnd_182574 : Nat := 4983230072969 + 3 ^ 40 * 182574 * 2
def baseEnd_182574 : Nat := 55554498971303059013549

theorem tailTrace_182574 : CollatzResearch.WordTrace tailWord_182574 prefixEnd_182574 55554498971303059013549 := by
  unfold tailWord_182574
  simp only [CollatzResearch.WordTrace]
  refine ⟨832377605071631750231347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4439347227048702667900517 832377605071631750231347)
  ·
    refine ⟨1248566407607447625347021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832377605071631750231347 1248566407607447625347021)
    ·
      refine ⟨468212402852792859505133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1248566407607447625347021 468212402852792859505133)
      ·
        refine ⟨175579651069797322314425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468212402852792859505133 175579651069797322314425)
        ·
          refine ⟨131684738302347991735819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175579651069797322314425 131684738302347991735819)
          ·
            refine ⟨197527107453521987603729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131684738302347991735819 197527107453521987603729)
            ·
              refine ⟨148145330590141490702797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197527107453521987603729 148145330590141490702797)
              ·
                refine ⟨55554498971303059013549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148145330590141490702797 55554498971303059013549)
                ·
                  rfl

theorem cell19_182574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_182574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182574 prefixEnd_182574 := by exact prefixLift 182574
  have htrace : WordTrace (prefixWord ++ tailWord_182574) baseStart_182574 baseEnd_182574 := by
    simpa [prefixWord, tailWord_182574, baseEnd_182574] using wordTrace_append hprefix tailTrace_182574
  have hstable : (prefixWord ++ tailWord_182574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182574).length < 2 ^ (prefixWord ++ tailWord_182574).sum := by decide
  have hdescent : baseEnd_182574 < baseStart_182574 := by decide
  rcases family_descends (prefixWord ++ tailWord_182574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182578 : List Nat := [3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_182578 : Nat := 118140960795 + 182578 * 2 ^ 59
def prefixEnd_182578 : Nat := 4983230072969 + 3 ^ 40 * 182578 * 2
def baseEnd_182578 : Nat := 55555716110632234924649

theorem tailTrace_182578 : CollatzResearch.WordTrace tailWord_182578 prefixEnd_182578 55555716110632234924649 := by
  unfold tailWord_182578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664791683139640671249097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4439444488372375123330925 1664791683139640671249097)
  ·
    refine ⟨1248593762354730503436823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1664791683139640671249097 1248593762354730503436823)
    ·
      refine ⟨1872890643532095755155235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1248593762354730503436823 1872890643532095755155235)
      ·
        refine ⟨2809335965298143632732853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872890643532095755155235 2809335965298143632732853)
        ·
          refine ⟨263375246746700965568705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2809335965298143632732853 263375246746700965568705)
          ·
            refine ⟨197531435060025724176529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263375246746700965568705 197531435060025724176529)
            ·
              refine ⟨148148576295019293132397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197531435060025724176529 148148576295019293132397)
              ·
                refine ⟨55555716110632234924649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148148576295019293132397 55555716110632234924649)
                ·
                  rfl

theorem cell19_182578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_182578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182578 prefixEnd_182578 := by exact prefixLift 182578
  have htrace : WordTrace (prefixWord ++ tailWord_182578) baseStart_182578 baseEnd_182578 := by
    simpa [prefixWord, tailWord_182578, baseEnd_182578] using wordTrace_append hprefix tailTrace_182578
  have hstable : (prefixWord ++ tailWord_182578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182578).length < 2 ^ (prefixWord ++ tailWord_182578).sum := by decide
  have hdescent : baseEnd_182578 < baseStart_182578 := by decide
  rcases family_descends (prefixWord ++ tailWord_182578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182580 : List Nat := [2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_182580 : Nat := 118140960795 + 182580 * 2 ^ 59
def prefixEnd_182580 : Nat := 4983230072969 + 3 ^ 40 * 182580 * 2
def baseEnd_182580 : Nat := 55556324680296822880199

theorem tailTrace_182580 : CollatzResearch.WordTrace tailWord_182580 prefixEnd_182580 55556324680296822880199 := by
  unfold tailWord_182580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329619839275658513284597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4439493119034211351046129 3329619839275658513284597)
  ·
    refine ⟨312151859932092985620431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3329619839275658513284597 312151859932092985620431)
    ·
      refine ⟨468227789898139478430647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312151859932092985620431 468227789898139478430647)
      ·
        refine ⟨702341684847209217645971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468227789898139478430647 702341684847209217645971)
        ·
          refine ⟨1053512527270813826468957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702341684847209217645971 1053512527270813826468957)
          ·
            refine ⟨395067197726555184925859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1053512527270813826468957 395067197726555184925859)
            ·
              refine ⟨592600796589832777388789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395067197726555184925859 592600796589832777388789)
              ·
                refine ⟨55556324680296822880199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 592600796589832777388789 55556324680296822880199)
                ·
                  rfl

theorem cell19_182580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_182580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182580 prefixEnd_182580 := by exact prefixLift 182580
  have htrace : WordTrace (prefixWord ++ tailWord_182580) baseStart_182580 baseEnd_182580 := by
    simpa [prefixWord, tailWord_182580, baseEnd_182580] using wordTrace_append hprefix tailTrace_182580
  have hstable : (prefixWord ++ tailWord_182580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182580).length < 2 ^ (prefixWord ++ tailWord_182580).sum := by decide
  have hdescent : baseEnd_182580 < baseStart_182580 := by decide
  rcases family_descends (prefixWord ++ tailWord_182580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182751 : List Nat := [1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_182751 : Nat := 118140960795 + 182751 * 2 ^ 59
def prefixEnd_182751 : Nat := 4983230072969 + 3 ^ 40 * 182751 * 2
def baseEnd_182751 : Nat := 55608357386619093079733

theorem tailTrace_182751 : CollatzResearch.WordTrace tailWord_182751 prefixEnd_182751 55608357386619093079733 := by
  unfold tailWord_182751
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665476560931813231044107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4443651040621208820696071 6665476560931813231044107)
  ·
    refine ⟨9998214841397719846566161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6665476560931813231044107 9998214841397719846566161)
    ·
      refine ⟨7498661131048289884924621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9998214841397719846566161 7498661131048289884924621)
      ·
        refine ⟨2811997924143108706846733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7498661131048289884924621 2811997924143108706846733)
        ·
          refine ⟨1054499221553665765067525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2811997924143108706846733 1054499221553665765067525)
          ·
            refine ⟨197718604041312330950161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1054499221553665765067525 197718604041312330950161)
            ·
              refine ⟨148288953030984248212621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197718604041312330950161 148288953030984248212621)
              ·
                refine ⟨55608357386619093079733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148288953030984248212621 55608357386619093079733)
                ·
                  rfl

theorem cell19_182751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_182751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182751 prefixEnd_182751 := by exact prefixLift 182751
  have htrace : WordTrace (prefixWord ++ tailWord_182751) baseStart_182751 baseEnd_182751 := by
    simpa [prefixWord, tailWord_182751, baseEnd_182751] using wordTrace_append hprefix tailTrace_182751
  have hstable : (prefixWord ++ tailWord_182751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182751).length < 2 ^ (prefixWord ++ tailWord_182751).sum := by decide
  have hdescent : baseEnd_182751 < baseStart_182751 := by decide
  rcases family_descends (prefixWord ++ tailWord_182751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182770 : List Nat := [3, 2, 1, 4, 2, 2, 5]
def baseStart_182770 : Nat := 118140960795 + 182770 * 2 ^ 59
def prefixEnd_182770 : Nat := 4983230072969 + 3 ^ 40 * 182770 * 2
def baseEnd_182770 : Nat := 18538046266144226219153

theorem tailTrace_182770 : CollatzResearch.WordTrace tailWord_182770 prefixEnd_182770 18538046266144226219153 := by
  unfold tailWord_182770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666542386965744868996441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4444113031908652983990509 1666542386965744868996441)
  ·
    refine ⟨1249906790224308651747331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1666542386965744868996441 1249906790224308651747331)
    ·
      refine ⟨1874860185336462977620997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249906790224308651747331 1874860185336462977620997)
      ·
        refine ⟨351536284750586808303937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1874860185336462977620997 351536284750586808303937)
        ·
          refine ⟨263652213562940106227953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351536284750586808303937 263652213562940106227953)
          ·
            refine ⟨197739160172205079670965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263652213562940106227953 197739160172205079670965)
            ·
              refine ⟨18538046266144226219153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197739160172205079670965 18538046266144226219153)
              ·
                rfl

theorem cell19_182770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_182770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182770 prefixEnd_182770 := by exact prefixLift 182770
  have htrace : WordTrace (prefixWord ++ tailWord_182770) baseStart_182770 baseEnd_182770 := by
    simpa [prefixWord, tailWord_182770, baseEnd_182770] using wordTrace_append hprefix tailTrace_182770
  have hstable : (prefixWord ++ tailWord_182770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182770).length < 2 ^ (prefixWord ++ tailWord_182770).sum := by decide
  have hdescent : baseEnd_182770 < baseStart_182770 := by decide
  rcases family_descends (prefixWord ++ tailWord_182770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182869 : List Nat := [1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_182869 : Nat := 118140960795 + 182869 * 2 ^ 59
def prefixEnd_182869 : Nat := 4983230072969 + 3 ^ 40 * 182869 * 2
def baseEnd_182869 : Nat := 55644262996829782457189

theorem tailTrace_182869 : CollatzResearch.WordTrace tailWord_182869 prefixEnd_182869 55644262996829782457189 := by
  unfold tailWord_182869
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669780374504319383839661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4446520249669546255893107 6669780374504319383839661)
  ·
    refine ⟨2501167640439119768939873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6669780374504319383839661 2501167640439119768939873)
    ·
      refine ⟨1875875730329339826704905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2501167640439119768939873 1875875730329339826704905)
      ·
        refine ⟨1406906797747004870028679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875875730329339826704905 1406906797747004870028679)
        ·
          refine ⟨2110360196620507305043019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406906797747004870028679 2110360196620507305043019)
          ·
            refine ⟨3165540294930760957564529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110360196620507305043019 3165540294930760957564529)
            ·
              refine ⟨2374155221198070718173397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165540294930760957564529 2374155221198070718173397)
              ·
                refine ⟨55644262996829782457189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2374155221198070718173397 55644262996829782457189)
                ·
                  rfl

theorem cell19_182869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_182869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182869 prefixEnd_182869 := by exact prefixLift 182869
  have htrace : WordTrace (prefixWord ++ tailWord_182869) baseStart_182869 baseEnd_182869 := by
    simpa [prefixWord, tailWord_182869, baseEnd_182869] using wordTrace_append hprefix tailTrace_182869
  have hstable : (prefixWord ++ tailWord_182869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182869).length < 2 ^ (prefixWord ++ tailWord_182869).sum := by decide
  have hdescent : baseEnd_182869 < baseStart_182869 := by decide
  rcases family_descends (prefixWord ++ tailWord_182869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182914 : List Nat := [3, 4, 3, 1, 2, 1, 2, 3]
def baseStart_182914 : Nat := 118140960795 + 182914 * 2 ^ 59
def prefixEnd_182914 : Nat := 4983230072969 + 3 ^ 40 * 182914 * 2
def baseEnd_182914 : Nat := 55657955814283011457067

theorem tailTrace_182914 : CollatzResearch.WordTrace tailWord_182914 prefixEnd_182914 55657955814283011457067 := by
  unfold tailWord_182914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667855414835323017306949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4447614439560861379485197 1667855414835323017306949)
  ·
    refine ⟨312722890281623065745053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1667855414835323017306949 312722890281623065745053)
    ·
      refine ⟨117271083855608649654395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312722890281623065745053 117271083855608649654395)
      ·
        refine ⟨175906625783412974481593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117271083855608649654395 175906625783412974481593)
        ·
          refine ⟨131929969337559730861195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175906625783412974481593 131929969337559730861195)
          ·
            refine ⟨197894954006339596291793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131929969337559730861195 197894954006339596291793)
            ·
              refine ⟨148421215504754697218845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197894954006339596291793 148421215504754697218845)
              ·
                refine ⟨55657955814283011457067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148421215504754697218845 55657955814283011457067)
                ·
                  rfl

theorem cell19_182914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_182914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_182914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_182914 prefixEnd_182914 := by exact prefixLift 182914
  have htrace : WordTrace (prefixWord ++ tailWord_182914) baseStart_182914 baseEnd_182914 := by
    simpa [prefixWord, tailWord_182914, baseEnd_182914] using wordTrace_append hprefix tailTrace_182914
  have hstable : (prefixWord ++ tailWord_182914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182914).length < 2 ^ (prefixWord ++ tailWord_182914).sum := by decide
  have hdescent : baseEnd_182914 < baseStart_182914 := by decide
  rcases family_descends (prefixWord ++ tailWord_182914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183093 : List Nat := [1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_183093 : Nat := 118140960795 + 183093 * 2 ^ 59
def prefixEnd_183093 : Nat := 4983230072969 + 3 ^ 40 * 183093 * 2
def baseEnd_183093 : Nat := 55712422799263633478801

theorem tailTrace_183093 : CollatzResearch.WordTrace tailWord_183093 prefixEnd_183093 55712422799263633478801 := by
  unfold tailWord_183093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6677950325692805639993933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4451966883795203759995955 6677950325692805639993933)
  ·
    refine ⟨2504231372134802114997725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6677950325692805639993933 2504231372134802114997725)
    ·
      refine ⟨939086764550550793124147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2504231372134802114997725 939086764550550793124147)
      ·
        refine ⟨1408630146825826189686221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939086764550550793124147 1408630146825826189686221)
        ·
          refine ⟨528236305059684821132333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1408630146825826189686221 528236305059684821132333)
          ·
            refine ⟨198088614397381807924625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528236305059684821132333 198088614397381807924625)
            ·
              refine ⟨148566460798036355943469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198088614397381807924625 148566460798036355943469)
              ·
                refine ⟨55712422799263633478801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148566460798036355943469 55712422799263633478801)
                ·
                  rfl

theorem cell19_183093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_183093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183093 prefixEnd_183093 := by exact prefixLift 183093
  have htrace : WordTrace (prefixWord ++ tailWord_183093) baseStart_183093 baseEnd_183093 := by
    simpa [prefixWord, tailWord_183093, baseEnd_183093] using wordTrace_append hprefix tailTrace_183093
  have hstable : (prefixWord ++ tailWord_183093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183093).length < 2 ^ (prefixWord ++ tailWord_183093).sum := by decide
  have hdescent : baseEnd_183093 < baseStart_183093 := by decide
  rcases family_descends (prefixWord ++ tailWord_183093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183110 : List Nat := [6, 1, 1, 2, 2, 2, 5]
def baseStart_183110 : Nat := 118140960795 + 183110 * 2 ^ 59
def prefixEnd_183110 : Nat := 4983230072969 + 3 ^ 40 * 183110 * 2
def baseEnd_183110 : Nat := 18572531880470877033659

theorem tailTrace_183110 : CollatzResearch.WordTrace tailWord_183110 prefixEnd_183110 18572531880470877033659 := by
  unfold tailWord_183110
  simp only [CollatzResearch.WordTrace]
  refine ⟨208705323957225548230087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4452380244420811695575189 208705323957225548230087)
  ·
    refine ⟨313057985935838322345131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208705323957225548230087 313057985935838322345131)
    ·
      refine ⟨469586978903757483517697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313057985935838322345131 469586978903757483517697)
      ·
        refine ⟨352190234177818112638273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469586978903757483517697 352190234177818112638273)
        ·
          refine ⟨264142675633363584478705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352190234177818112638273 264142675633363584478705)
          ·
            refine ⟨198107006725022688359029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264142675633363584478705 198107006725022688359029)
            ·
              refine ⟨18572531880470877033659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198107006725022688359029 18572531880470877033659)
              ·
                rfl

theorem cell19_183110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_183110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183110 prefixEnd_183110 := by exact prefixLift 183110
  have htrace : WordTrace (prefixWord ++ tailWord_183110) baseStart_183110 baseEnd_183110 := by
    simpa [prefixWord, tailWord_183110, baseEnd_183110] using wordTrace_append hprefix tailTrace_183110
  have hstable : (prefixWord ++ tailWord_183110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183110).length < 2 ^ (prefixWord ++ tailWord_183110).sum := by decide
  have hdescent : baseEnd_183110 < baseStart_183110 := by decide
  rcases family_descends (prefixWord ++ tailWord_183110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183116 : List Nat := [2, 2, 1, 3, 3, 1, 7]
def baseStart_183116 : Nat := 118140960795 + 183116 * 2 ^ 59
def prefixEnd_183116 : Nat := 4983230072969 + 3 ^ 40 * 183116 * 2
def baseEnd_183116 : Nat := 18573140450135464989209

theorem tailTrace_183116 : CollatzResearch.WordTrace tailWord_183116 prefixEnd_183116 18573140450135464989209 := by
  unfold tailWord_183116
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339394602304740284040601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4452526136406320378720801 3339394602304740284040601)
  ·
    refine ⟨2504545951728555213030451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3339394602304740284040601 2504545951728555213030451)
    ·
      refine ⟨3756818927592832819545677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504545951728555213030451 3756818927592832819545677)
      ·
        refine ⟨1408807097847312307329629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3756818927592832819545677 1408807097847312307329629)
        ·
          refine ⟨528302661692742115248611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1408807097847312307329629 528302661692742115248611)
          ·
            refine ⟨792453992539113172872917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528302661692742115248611 792453992539113172872917)
            ·
              refine ⟨18573140450135464989209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 792453992539113172872917 18573140450135464989209)
              ·
                rfl

theorem cell19_183116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_183116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183116 prefixEnd_183116 := by exact prefixLift 183116
  have htrace : WordTrace (prefixWord ++ tailWord_183116) baseStart_183116 baseEnd_183116 := by
    simpa [prefixWord, tailWord_183116, baseEnd_183116] using wordTrace_append hprefix tailTrace_183116
  have hstable : (prefixWord ++ tailWord_183116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183116).length < 2 ^ (prefixWord ++ tailWord_183116).sum := by decide
  have hdescent : baseEnd_183116 < baseStart_183116 := by decide
  rcases family_descends (prefixWord ++ tailWord_183116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183135 : List Nat := [1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_183135 : Nat := 118140960795 + 183135 * 2 ^ 59
def prefixEnd_183135 : Nat := 4983230072969 + 3 ^ 40 * 183135 * 2
def baseEnd_183135 : Nat := 55725202762219980545353

theorem tailTrace_183135 : CollatzResearch.WordTrace tailWord_183135 prefixEnd_183135 55725202762219980545353 := by
  unfold tailWord_183135
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679482191540646813022859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4452988127693764542015239 6679482191540646813022859)
  ·
    refine ⟨10019223287310970219534289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679482191540646813022859 10019223287310970219534289)
    ·
      refine ⟨7514417465483227664650717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10019223287310970219534289 7514417465483227664650717)
      ·
        refine ⟨2817906549556210374244019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7514417465483227664650717 2817906549556210374244019)
        ·
          refine ⟨4226859824334315561366029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817906549556210374244019 4226859824334315561366029)
          ·
            refine ⟨1585072434125368335512261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4226859824334315561366029 1585072434125368335512261)
            ·
              refine ⟨297201081398506562908549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1585072434125368335512261 297201081398506562908549)
              ·
                refine ⟨55725202762219980545353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297201081398506562908549 55725202762219980545353)
                ·
                  rfl

theorem cell19_183135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_183135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183135 prefixEnd_183135 := by exact prefixLift 183135
  have htrace : WordTrace (prefixWord ++ tailWord_183135) baseStart_183135 baseEnd_183135 := by
    simpa [prefixWord, tailWord_183135, baseEnd_183135] using wordTrace_append hprefix tailTrace_183135
  have hstable : (prefixWord ++ tailWord_183135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183135).length < 2 ^ (prefixWord ++ tailWord_183135).sum := by decide
  have hdescent : baseEnd_183135 < baseStart_183135 := by decide
  rcases family_descends (prefixWord ++ tailWord_183135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183154 : List Nat := [3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_183154 : Nat := 118140960795 + 183154 * 2 ^ 59
def prefixEnd_183154 : Nat := 4983230072969 + 3 ^ 40 * 183154 * 2
def baseEnd_183154 : Nat := 55730984174033566123079

theorem tailTrace_183154 : CollatzResearch.WordTrace tailWord_183154 prefixEnd_183154 55730984174033566123079 := by
  unfold tailWord_183154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670043794617953264491129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4453450118981208705309677 1670043794617953264491129)
  ·
    refine ⟨1252532845963464948368347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1670043794617953264491129 1252532845963464948368347)
    ·
      refine ⟨1878799268945197422552521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252532845963464948368347 1878799268945197422552521)
      ·
        refine ⟨1409099451708898066914391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878799268945197422552521 1409099451708898066914391)
        ·
          refine ⟨2113649177563347100371587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409099451708898066914391 2113649177563347100371587)
          ·
            refine ⟨3170473766345020650557381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113649177563347100371587 3170473766345020650557381)
            ·
              refine ⟨594463831189691371979509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3170473766345020650557381 594463831189691371979509)
              ·
                refine ⟨55730984174033566123079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 594463831189691371979509 55730984174033566123079)
                ·
                  rfl

theorem cell19_183154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_183154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183154 prefixEnd_183154 := by exact prefixLift 183154
  have htrace : WordTrace (prefixWord ++ tailWord_183154) baseStart_183154 baseEnd_183154 := by
    simpa [prefixWord, tailWord_183154, baseEnd_183154] using wordTrace_append hprefix tailTrace_183154
  have hstable : (prefixWord ++ tailWord_183154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183154).length < 2 ^ (prefixWord ++ tailWord_183154).sum := by decide
  have hdescent : baseEnd_183154 < baseStart_183154 := by decide
  rcases family_descends (prefixWord ++ tailWord_183154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183186 : List Nat := [3, 2, 3, 2, 3, 1, 1, 4]
def baseStart_183186 : Nat := 118140960795 + 183186 * 2 ^ 59
def prefixEnd_183186 : Nat := 4983230072969 + 3 ^ 40 * 183186 * 2
def baseEnd_183186 : Nat := 55740721288666973411881

theorem tailTrace_183186 : CollatzResearch.WordTrace tailWord_183186 prefixEnd_183186 55740721288666973411881 := by
  unfold tailWord_183186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670335578588970630782353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4454228209570588348752941 1670335578588970630782353)
  ·
    refine ⟨1252751683941727973086765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1670335578588970630782353 1252751683941727973086765)
    ·
      refine ⟨469781881478147989907537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1252751683941727973086765 469781881478147989907537)
      ·
        refine ⟨352336411108610992430653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469781881478147989907537 352336411108610992430653)
        ·
          refine ⟨132126154165729122161495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352336411108610992430653 132126154165729122161495)
          ·
            refine ⟨198189231248593683242243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132126154165729122161495 198189231248593683242243)
            ·
              refine ⟨297283846872890524863365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198189231248593683242243 297283846872890524863365)
              ·
                refine ⟨55740721288666973411881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297283846872890524863365 55740721288666973411881)
                ·
                  rfl

theorem cell19_183186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_183186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183186 prefixEnd_183186 := by exact prefixLift 183186
  have htrace : WordTrace (prefixWord ++ tailWord_183186) baseStart_183186 baseEnd_183186 := by
    simpa [prefixWord, tailWord_183186, baseEnd_183186] using wordTrace_append hprefix tailTrace_183186
  have hstable : (prefixWord ++ tailWord_183186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183186).length < 2 ^ (prefixWord ++ tailWord_183186).sum := by decide
  have hdescent : baseEnd_183186 < baseStart_183186 := by decide
  rcases family_descends (prefixWord ++ tailWord_183186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183207 : List Nat := [1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_183207 : Nat := 118140960795 + 183207 * 2 ^ 59
def prefixEnd_183207 : Nat := 4983230072969 + 3 ^ 40 * 183207 * 2
def baseEnd_183207 : Nat := 55747111270145146945157

theorem tailTrace_183207 : CollatzResearch.WordTrace tailWord_183207 prefixEnd_183207 55747111270145146945157 := by
  unfold tailWord_183207
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682108247279803109643875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4454738831519868739762583 6682108247279803109643875)
  ·
    refine ⟨10023162370919704664465813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6682108247279803109643875 10023162370919704664465813)
    ·
      refine ⟨469835736136861156146835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10023162370919704664465813 469835736136861156146835)
      ·
        refine ⟨704753604205291734220253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469835736136861156146835 704753604205291734220253)
        ·
          refine ⟨264282601576984400332595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 704753604205291734220253 264282601576984400332595)
          ·
            refine ⟨396423902365476600498893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264282601576984400332595 396423902365476600498893)
            ·
              refine ⟨148658963387053725187085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396423902365476600498893 148658963387053725187085)
              ·
                refine ⟨55747111270145146945157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148658963387053725187085 55747111270145146945157)
                ·
                  rfl

theorem cell19_183207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_183207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183207 prefixEnd_183207 := by exact prefixLift 183207
  have htrace : WordTrace (prefixWord ++ tailWord_183207) baseStart_183207 baseEnd_183207 := by
    simpa [prefixWord, tailWord_183207, baseEnd_183207] using wordTrace_append hprefix tailTrace_183207
  have hstable : (prefixWord ++ tailWord_183207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183207).length < 2 ^ (prefixWord ++ tailWord_183207).sum := by decide
  have hdescent : baseEnd_183207 < baseStart_183207 := by decide
  rcases family_descends (prefixWord ++ tailWord_183207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183230 : List Nat := [4, 2, 1, 1, 1, 2, 8]
def baseStart_183230 : Nat := 118140960795 + 183230 * 2 ^ 59
def prefixEnd_183230 : Nat := 4983230072969 + 3 ^ 40 * 183230 * 2
def baseEnd_183230 : Nat := 18584703273762636144661

theorem tailTrace_183230 : CollatzResearch.WordTrace tailWord_183230 prefixEnd_183230 18584703273762636144661 := by
  unfold tailWord_183230
  simp only [CollatzResearch.WordTrace]
  refine ⟨835368390774559754716393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4455298084130985358487429 835368390774559754716393)
  ·
    refine ⟨626526293080919816037295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 835368390774559754716393 626526293080919816037295)
    ·
      refine ⟨939789439621379724055943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626526293080919816037295 939789439621379724055943)
      ·
        refine ⟨1409684159432069586083915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939789439621379724055943 1409684159432069586083915)
        ·
          refine ⟨2114526239148104379125873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409684159432069586083915 2114526239148104379125873)
          ·
            refine ⟨1585894679361078284344405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114526239148104379125873 1585894679361078284344405)
            ·
              refine ⟨18584703273762636144661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1585894679361078284344405 18584703273762636144661)
              ·
                rfl

theorem cell19_183230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_183230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183230 prefixEnd_183230 := by exact prefixLift 183230
  have htrace : WordTrace (prefixWord ++ tailWord_183230) baseStart_183230 baseEnd_183230 := by
    simpa [prefixWord, tailWord_183230, baseEnd_183230] using wordTrace_append hprefix tailTrace_183230
  have hstable : (prefixWord ++ tailWord_183230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183230).length < 2 ^ (prefixWord ++ tailWord_183230).sum := by decide
  have hdescent : baseEnd_183230 < baseStart_183230 := by decide
  rcases family_descends (prefixWord ++ tailWord_183230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183306 : List Nat := [3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_183306 : Nat := 118140960795 + 183306 * 2 ^ 59
def prefixEnd_183306 : Nat := 4983230072969 + 3 ^ 40 * 183306 * 2
def baseEnd_183306 : Nat := 55777235468542250744887

theorem tailTrace_183306 : CollatzResearch.WordTrace tailWord_183306 prefixEnd_183306 55777235468542250744887 := by
  unfold tailWord_183306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671429768480285754374443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4457146049280762011665181 1671429768480285754374443)
  ·
    refine ⟨2507144652720428631561665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671429768480285754374443 2507144652720428631561665)
    ·
      refine ⟨1880358489540321473671249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2507144652720428631561665 1880358489540321473671249)
      ·
        refine ⟨1410268867155241105253437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1880358489540321473671249 1410268867155241105253437)
        ·
          refine ⟨528850825183215414470039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1410268867155241105253437 528850825183215414470039)
          ·
            refine ⟨793276237774823121705059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528850825183215414470039 793276237774823121705059)
            ·
              refine ⟨1189914356662234682557589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793276237774823121705059 1189914356662234682557589)
              ·
                refine ⟨55777235468542250744887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1189914356662234682557589 55777235468542250744887)
                ·
                  rfl

theorem cell19_183306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_183306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183306 prefixEnd_183306 := by exact prefixLift 183306
  have htrace : WordTrace (prefixWord ++ tailWord_183306) baseStart_183306 baseEnd_183306 := by
    simpa [prefixWord, tailWord_183306, baseEnd_183306] using wordTrace_append hprefix tailTrace_183306
  have hstable : (prefixWord ++ tailWord_183306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183306).length < 2 ^ (prefixWord ++ tailWord_183306).sum := by decide
  have hdescent : baseEnd_183306 < baseStart_183306 := by decide
  rcases family_descends (prefixWord ++ tailWord_183306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183534 : List Nat := [4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_183534 : Nat := 118140960795 + 183534 * 2 ^ 59
def prefixEnd_183534 : Nat := 4983230072969 + 3 ^ 40 * 183534 * 2
def baseEnd_183534 : Nat := 55846612410305277677599

theorem tailTrace_183534 : CollatzResearch.WordTrace tailWord_183534 prefixEnd_183534 55846612410305277677599 := by
  unfold tailWord_183534
  simp only [CollatzResearch.WordTrace]
  refine ⟨836754364636892244599707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4462689944730091971198437 836754364636892244599707)
  ·
    refine ⟨1255131546955338366899561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836754364636892244599707 1255131546955338366899561)
    ·
      refine ⟨941348660216503775174671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1255131546955338366899561 941348660216503775174671)
      ·
        refine ⟨1412022990324755662762007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941348660216503775174671 1412022990324755662762007)
        ·
          refine ⟨2118034485487133494143011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412022990324755662762007 2118034485487133494143011)
          ·
            refine ⟨3177051728230700241214517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118034485487133494143011 3177051728230700241214517)
            ·
              refine ⟨297848599521628147613861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3177051728230700241214517 297848599521628147613861)
              ·
                refine ⟨55846612410305277677599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297848599521628147613861 55846612410305277677599)
                ·
                  rfl

theorem cell19_183534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_183534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183534 prefixEnd_183534 := by exact prefixLift 183534
  have htrace : WordTrace (prefixWord ++ tailWord_183534) baseStart_183534 baseEnd_183534 := by
    simpa [prefixWord, tailWord_183534, baseEnd_183534] using wordTrace_append hprefix tailTrace_183534
  have hstable : (prefixWord ++ tailWord_183534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183534).length < 2 ^ (prefixWord ++ tailWord_183534).sum := by decide
  have hdescent : baseEnd_183534 < baseStart_183534 := by decide
  rcases family_descends (prefixWord ++ tailWord_183534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183606 : List Nat := [5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_183606 : Nat := 118140960795 + 183606 * 2 ^ 59
def prefixEnd_183606 : Nat := 4983230072969 + 3 ^ 40 * 183606 * 2
def baseEnd_183606 : Nat := 55868520918230444077403

theorem tailTrace_183606 : CollatzResearch.WordTrace tailWord_183606 prefixEnd_183606 55868520918230444077403 := by
  unfold tailWord_183606
  simp only [CollatzResearch.WordTrace]
  refine ⟨418541310802143390838667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4464440648556196168945781 418541310802143390838667)
  ·
    refine ⟨627811966203215086258001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 418541310802143390838667 627811966203215086258001)
    ·
      refine ⟨470858974652411314693501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627811966203215086258001 470858974652411314693501)
      ·
        refine ⟨176572115494654243010063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470858974652411314693501 176572115494654243010063)
        ·
          refine ⟨264858173241981364515095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176572115494654243010063 264858173241981364515095)
          ·
            refine ⟨397287259862972046772643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264858173241981364515095 397287259862972046772643)
            ·
              refine ⟨595930889794458070158965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397287259862972046772643 595930889794458070158965)
              ·
                refine ⟨55868520918230444077403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 595930889794458070158965 55868520918230444077403)
                ·
                  rfl

theorem cell19_183606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_183606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183606 prefixEnd_183606 := by exact prefixLift 183606
  have htrace : WordTrace (prefixWord ++ tailWord_183606) baseStart_183606 baseEnd_183606 := by
    simpa [prefixWord, tailWord_183606, baseEnd_183606] using wordTrace_append hprefix tailTrace_183606
  have hstable : (prefixWord ++ tailWord_183606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183606).length < 2 ^ (prefixWord ++ tailWord_183606).sum := by decide
  have hdescent : baseEnd_183606 < baseStart_183606 := by decide
  rcases family_descends (prefixWord ++ tailWord_183606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183648 : List Nat := [2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_183648 : Nat := 118140960795 + 183648 * 2 ^ 59
def prefixEnd_183648 : Nat := 4983230072969 + 3 ^ 40 * 183648 * 2
def baseEnd_183648 : Nat := 55881300881186791143955

theorem tailTrace_183648 : CollatzResearch.WordTrace tailWord_183648 prefixEnd_183648 55881300881186791143955 := by
  unfold tailWord_183648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349096419341067713223799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4465461892454756950965065 3349096419341067713223799)
  ·
    refine ⟨5023644629011601569835699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349096419341067713223799 5023644629011601569835699)
    ·
      refine ⟨7535466943517402354753549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023644629011601569835699 7535466943517402354753549)
      ·
        refine ⟨2825800103819025883032581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7535466943517402354753549 2825800103819025883032581)
        ·
          refine ⟨529837519466067353068609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2825800103819025883032581 529837519466067353068609)
          ·
            refine ⟨397378139599550514801457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529837519466067353068609 397378139599550514801457)
            ·
              refine ⟨298033604699662886101093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397378139599550514801457 298033604699662886101093)
              ·
                refine ⟨55881300881186791143955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298033604699662886101093 55881300881186791143955)
                ·
                  rfl

theorem cell19_183648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_183648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183648 prefixEnd_183648 := by exact prefixLift 183648
  have htrace : WordTrace (prefixWord ++ tailWord_183648) baseStart_183648 baseEnd_183648 := by
    simpa [prefixWord, tailWord_183648, baseEnd_183648] using wordTrace_append hprefix tailTrace_183648
  have hstable : (prefixWord ++ tailWord_183648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183648).length < 2 ^ (prefixWord ++ tailWord_183648).sum := by decide
  have hdescent : baseEnd_183648 < baseStart_183648 := by decide
  rcases family_descends (prefixWord ++ tailWord_183648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183688 : List Nat := [2, 1, 3, 3, 1, 9]
def baseStart_183688 : Nat := 118140960795 + 183688 * 2 ^ 59
def prefixEnd_183688 : Nat := 4983230072969 + 3 ^ 40 * 183688 * 2
def baseEnd_183688 : Nat := 6210385808275394472773

theorem tailTrace_183688 : CollatzResearch.WordTrace tailWord_183688 prefixEnd_183688 6210385808275394472773 := by
  unfold tailWord_183688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349825879268611128951859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4466434505691481505269145 3349825879268611128951859)
  ·
    refine ⟨5024738818902916693427789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349825879268611128951859 5024738818902916693427789)
    ·
      refine ⟨1884277057088593760035421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5024738818902916693427789 1884277057088593760035421)
      ·
        refine ⟨706603896408222660013283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1884277057088593760035421 706603896408222660013283)
        ·
          refine ⟨1059905844612333990019925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706603896408222660013283 1059905844612333990019925)
          ·
            refine ⟨6210385808275394472773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1059905844612333990019925 6210385808275394472773)
            ·
              rfl

theorem cell19_183688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_183688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183688 prefixEnd_183688 := by exact prefixLift 183688
  have htrace : WordTrace (prefixWord ++ tailWord_183688) baseStart_183688 baseEnd_183688 := by
    simpa [prefixWord, tailWord_183688, baseEnd_183688] using wordTrace_append hprefix tailTrace_183688
  have hstable : (prefixWord ++ tailWord_183688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183688).length < 2 ^ (prefixWord ++ tailWord_183688).sum := by decide
  have hdescent : baseEnd_183688 < baseStart_183688 := by decide
  rcases family_descends (prefixWord ++ tailWord_183688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183705 : List Nat := [1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_183705 : Nat := 118140960795 + 183705 * 2 ^ 59
def prefixEnd_183705 : Nat := 4983230072969 + 3 ^ 40 * 183705 * 2
def baseEnd_183705 : Nat := 55898645116627547877133

theorem tailTrace_183705 : CollatzResearch.WordTrace tailWord_183705 prefixEnd_183705 55898645116627547877133 := by
  unfold tailWord_183705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6700271799475634161272569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4466847866317089440848379 6700271799475634161272569)
  ·
    refine ⟨5025203849606725620954427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6700271799475634161272569 5025203849606725620954427)
    ·
      refine ⟨7537805774410088431431641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5025203849606725620954427 7537805774410088431431641)
      ·
        refine ⟨5653354330807566323573731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7537805774410088431431641 5653354330807566323573731)
        ·
          refine ⟨8480031496211349485360597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5653354330807566323573731 8480031496211349485360597)
          ·
            refine ⟨198750738192453503563139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8480031496211349485360597 198750738192453503563139)
            ·
              refine ⟨298126107288680255344709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198750738192453503563139 298126107288680255344709)
              ·
                refine ⟨55898645116627547877133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298126107288680255344709 55898645116627547877133)
                ·
                  rfl

theorem cell19_183705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_183705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183705 prefixEnd_183705 := by exact prefixLift 183705
  have htrace : WordTrace (prefixWord ++ tailWord_183705) baseStart_183705 baseEnd_183705 := by
    simpa [prefixWord, tailWord_183705, baseEnd_183705] using wordTrace_append hprefix tailTrace_183705
  have hstable : (prefixWord ++ tailWord_183705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183705).length < 2 ^ (prefixWord ++ tailWord_183705).sum := by decide
  have hdescent : baseEnd_183705 < baseStart_183705 := by decide
  rcases family_descends (prefixWord ++ tailWord_183705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183720 : List Nat := [2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_183720 : Nat := 118140960795 + 183720 * 2 ^ 59
def prefixEnd_183720 : Nat := 4983230072969 + 3 ^ 40 * 183720 * 2
def baseEnd_183720 : Nat := 55903209389111957543759

theorem tailTrace_183720 : CollatzResearch.WordTrace tailWord_183720 prefixEnd_183720 55903209389111957543759 := by
  unfold tailWord_183720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350409447210645861534307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4467212596280861148712409 3350409447210645861534307)
  ·
    refine ⟨5025614170815968792301461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3350409447210645861534307 5025614170815968792301461)
    ·
      refine ⟨235575664256998537139131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5025614170815968792301461 235575664256998537139131)
      ·
        refine ⟨353363496385497805708697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235575664256998537139131 353363496385497805708697)
        ·
          refine ⟨265022622289123354281523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353363496385497805708697 265022622289123354281523)
          ·
            refine ⟨397533933433685031422285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265022622289123354281523 397533933433685031422285)
            ·
              refine ⟨149075225037631886783357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397533933433685031422285 149075225037631886783357)
              ·
                refine ⟨55903209389111957543759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149075225037631886783357 55903209389111957543759)
                ·
                  rfl

theorem cell19_183720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_183720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183720 prefixEnd_183720 := by exact prefixLift 183720
  have htrace : WordTrace (prefixWord ++ tailWord_183720) baseStart_183720 baseEnd_183720 := by
    simpa [prefixWord, tailWord_183720, baseEnd_183720] using wordTrace_append hprefix tailTrace_183720
  have hstable : (prefixWord ++ tailWord_183720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183720).length < 2 ^ (prefixWord ++ tailWord_183720).sum := by decide
  have hdescent : baseEnd_183720 < baseStart_183720 := by decide
  rcases family_descends (prefixWord ++ tailWord_183720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183779 : List Nat := [1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_183779 : Nat := 118140960795 + 183779 * 2 ^ 59
def prefixEnd_183779 : Nat := 4983230072969 + 3 ^ 40 * 183779 * 2
def baseEnd_183779 : Nat := 55921162194217302232487

theorem tailTrace_183779 : CollatzResearch.WordTrace tailWord_183779 prefixEnd_183779 55921162194217302232487 := by
  unfold tailWord_183779
  simp only [CollatzResearch.WordTrace]
  refine ⟨6702970801207544799466391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4468647200805029866310927 6702970801207544799466391)
  ·
    refine ⟨10054456201811317199199587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6702970801207544799466391 10054456201811317199199587)
    ·
      refine ⟨15081684302716975798799381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054456201811317199199587 15081684302716975798799381)
      ·
        refine ⟨706953951689858240568721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15081684302716975798799381 706953951689858240568721)
        ·
          refine ⟨530215463767393680426541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706953951689858240568721 530215463767393680426541)
          ·
            refine ⟨198830798912772630159953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530215463767393680426541 198830798912772630159953)
            ·
              refine ⟨149123099184579472619965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198830798912772630159953 149123099184579472619965)
              ·
                refine ⟨55921162194217302232487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149123099184579472619965 55921162194217302232487)
                ·
                  rfl

theorem cell19_183779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_183779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183779 prefixEnd_183779 := by exact prefixLift 183779
  have htrace : WordTrace (prefixWord ++ tailWord_183779) baseStart_183779 baseEnd_183779 := by
    simpa [prefixWord, tailWord_183779, baseEnd_183779] using wordTrace_append hprefix tailTrace_183779
  have hstable : (prefixWord ++ tailWord_183779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183779).length < 2 ^ (prefixWord ++ tailWord_183779).sum := by decide
  have hdescent : baseEnd_183779 < baseStart_183779 := by decide
  rcases family_descends (prefixWord ++ tailWord_183779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183781 : List Nat := [1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_183781 : Nat := 118140960795 + 183781 * 2 ^ 59
def prefixEnd_183781 : Nat := 4983230072969 + 3 ^ 40 * 183781 * 2
def baseEnd_183781 : Nat := 55921770763881890188037

theorem tailTrace_183781 : CollatzResearch.WordTrace tailWord_183781 prefixEnd_183781 55921770763881890188037 := by
  unfold tailWord_183781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703043747200299141039197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4468695831466866094026131 6703043747200299141039197)
  ·
    refine ⟨2513641405200112177889699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6703043747200299141039197 2513641405200112177889699)
    ·
      refine ⟨3770462107800168266834549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2513641405200112177889699 3770462107800168266834549)
      ·
        refine ⟨353480822606265775015739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3770462107800168266834549 353480822606265775015739)
        ·
          refine ⟨530221233909398662523609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353480822606265775015739 530221233909398662523609)
          ·
            refine ⟨397665925432048996892707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530221233909398662523609 397665925432048996892707)
            ·
              refine ⟨596498888148073495339061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397665925432048996892707 596498888148073495339061)
              ·
                refine ⟨55921770763881890188037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596498888148073495339061 55921770763881890188037)
                ·
                  rfl

theorem cell19_183781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_183781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183781 prefixEnd_183781 := by exact prefixLift 183781
  have htrace : WordTrace (prefixWord ++ tailWord_183781) baseStart_183781 baseEnd_183781 := by
    simpa [prefixWord, tailWord_183781, baseEnd_183781] using wordTrace_append hprefix tailTrace_183781
  have hstable : (prefixWord ++ tailWord_183781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183781).length < 2 ^ (prefixWord ++ tailWord_183781).sum := by decide
  have hdescent : baseEnd_183781 < baseStart_183781 := by decide
  rcases family_descends (prefixWord ++ tailWord_183781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183819 : List Nat := [1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_183819 : Nat := 118140960795 + 183819 * 2 ^ 59
def prefixEnd_183819 : Nat := 4983230072969 + 3 ^ 40 * 183819 * 2
def baseEnd_183819 : Nat := 55933333587509061343489

theorem tailTrace_183819 : CollatzResearch.WordTrace tailWord_183819 prefixEnd_183819 55933333587509061343489 := by
  unfold tailWord_183819
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704429721062631630922511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4469619814041754420615007 6704429721062631630922511)
  ·
    refine ⟨10056644581593947446383767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6704429721062631630922511 10056644581593947446383767)
    ·
      refine ⟨15084966872390921169575651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10056644581593947446383767 15084966872390921169575651)
      ·
        refine ⟨22627450308586381754363477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15084966872390921169575651 22627450308586381754363477)
        ·
          refine ⟨265165433303746661183947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 22627450308586381754363477 265165433303746661183947)
          ·
            refine ⟨397748149955619991775921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265165433303746661183947 397748149955619991775921)
            ·
              refine ⟨298311112466714993831941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397748149955619991775921 298311112466714993831941)
              ·
                refine ⟨55933333587509061343489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298311112466714993831941 55933333587509061343489)
                ·
                  rfl

theorem cell19_183819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_183819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183819 prefixEnd_183819 := by exact prefixLift 183819
  have htrace : WordTrace (prefixWord ++ tailWord_183819) baseStart_183819 baseEnd_183819 := by
    simpa [prefixWord, tailWord_183819, baseEnd_183819] using wordTrace_append hprefix tailTrace_183819
  have hstable : (prefixWord ++ tailWord_183819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183819).length < 2 ^ (prefixWord ++ tailWord_183819).sum := by decide
  have hdescent : baseEnd_183819 < baseStart_183819 := by decide
  rcases family_descends (prefixWord ++ tailWord_183819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183895 : List Nat := [1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_183895 : Nat := 118140960795 + 183895 * 2 ^ 59
def prefixEnd_183895 : Nat := 4983230072969 + 3 ^ 40 * 183895 * 2
def baseEnd_183895 : Nat := 55956459234763403654393

theorem tailTrace_183895 : CollatzResearch.WordTrace tailWord_183895 prefixEnd_183895 55956459234763403654393 := by
  unfold tailWord_183895
  simp only [CollatzResearch.WordTrace]
  refine ⟨6707201668787296610689139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4471467779191531073792759 6707201668787296610689139)
  ·
    refine ⟨10060802503180944916033709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6707201668787296610689139 10060802503180944916033709)
    ·
      refine ⟨3772800938692854343512641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10060802503180944916033709 3772800938692854343512641)
      ·
        refine ⟨2829600704019640757634481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3772800938692854343512641 2829600704019640757634481)
        ·
          refine ⟨2122200528014730568225861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829600704019640757634481 2122200528014730568225861)
          ·
            refine ⟨397912599002761981542349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2122200528014730568225861 397912599002761981542349)
            ·
              refine ⟨149217224626035743078381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397912599002761981542349 149217224626035743078381)
              ·
                refine ⟨55956459234763403654393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149217224626035743078381 55956459234763403654393)
                ·
                  rfl

theorem cell19_183895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_183895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183895 prefixEnd_183895 := by exact prefixLift 183895
  have htrace : WordTrace (prefixWord ++ tailWord_183895) baseStart_183895 baseEnd_183895 := by
    simpa [prefixWord, tailWord_183895, baseEnd_183895] using wordTrace_append hprefix tailTrace_183895
  have hstable : (prefixWord ++ tailWord_183895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183895).length < 2 ^ (prefixWord ++ tailWord_183895).sum := by decide
  have hdescent : baseEnd_183895 < baseStart_183895 := by decide
  rcases family_descends (prefixWord ++ tailWord_183895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183950 : List Nat := [4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_183950 : Nat := 118140960795 + 183950 * 2 ^ 59
def prefixEnd_183950 : Nat := 4983230072969 + 3 ^ 40 * 183950 * 2
def baseEnd_183950 : Nat := 55973194900539572432021

theorem tailTrace_183950 : CollatzResearch.WordTrace tailWord_183950 prefixEnd_183950 55973194900539572432021 := by
  unfold tailWord_183950
  simp only [CollatzResearch.WordTrace]
  refine ⟨838650960448505125492663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4472805122392027335960869 838650960448505125492663)
  ·
    refine ⟨1257976440672757688238995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 838650960448505125492663 1257976440672757688238995)
    ·
      refine ⟨1886964661009136532358493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1257976440672757688238995 1886964661009136532358493)
      ·
        refine ⟨707611747878426199634435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1886964661009136532358493 707611747878426199634435)
        ·
          refine ⟨1061417621817639299451653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707611747878426199634435 1061417621817639299451653)
          ·
            refine ⟨199015804090807368647185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1061417621817639299451653 199015804090807368647185)
            ·
              refine ⟨149261853068105526485389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199015804090807368647185 149261853068105526485389)
              ·
                refine ⟨55973194900539572432021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149261853068105526485389 55973194900539572432021)
                ·
                  rfl

theorem cell19_183950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_183950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_183950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_183950 prefixEnd_183950 := by exact prefixLift 183950
  have htrace : WordTrace (prefixWord ++ tailWord_183950) baseStart_183950 baseEnd_183950 := by
    simpa [prefixWord, tailWord_183950, baseEnd_183950] using wordTrace_append hprefix tailTrace_183950
  have hstable : (prefixWord ++ tailWord_183950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183950).length < 2 ^ (prefixWord ++ tailWord_183950).sum := by decide
  have hdescent : baseEnd_183950 < baseStart_183950 := by decide
  rcases family_descends (prefixWord ++ tailWord_183950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184028 : List Nat := [2, 2, 5, 1, 2, 7]
def baseStart_184028 : Nat := 118140960795 + 184028 * 2 ^ 59
def prefixEnd_184028 : Nat := 4983230072969 + 3 ^ 40 * 184028 * 2
def baseEnd_184028 : Nat := 6221881013050944744275

theorem tailTrace_184028 : CollatzResearch.WordTrace tailWord_184028 prefixEnd_184028 6221881013050944744275 := by
  unfold tailWord_184028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356026288652730162640369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4474701718203640216853825 3356026288652730162640369)
  ·
    refine ⟨2517019716489547621980277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3356026288652730162640369 2517019716489547621980277)
    ·
      refine ⟨235970598420895089560651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2517019716489547621980277 235970598420895089560651)
      ·
        refine ⟨353955897631342634340977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235970598420895089560651 353955897631342634340977)
        ·
          refine ⟨265466923223506975755733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353955897631342634340977 265466923223506975755733)
          ·
            refine ⟨6221881013050944744275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265466923223506975755733 6221881013050944744275)
            ·
              rfl

theorem cell19_184028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_184028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184028 prefixEnd_184028 := by exact prefixLift 184028
  have htrace : WordTrace (prefixWord ++ tailWord_184028) baseStart_184028 baseEnd_184028 := by
    simpa [prefixWord, tailWord_184028, baseEnd_184028] using wordTrace_append hprefix tailTrace_184028
  have hstable : (prefixWord ++ tailWord_184028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184028).length < 2 ^ (prefixWord ++ tailWord_184028).sum := by decide
  have hdescent : baseEnd_184028 < baseStart_184028 := by decide
  rcases family_descends (prefixWord ++ tailWord_184028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184049 : List Nat := [1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_184049 : Nat := 118140960795 + 184049 * 2 ^ 59
def prefixEnd_184049 : Nat := 4983230072969 + 3 ^ 40 * 184049 * 2
def baseEnd_184049 : Nat := 56003319098936676231751

theorem tailTrace_184049 : CollatzResearch.WordTrace tailWord_184049 prefixEnd_184049 56003319098936676231751 := by
  unfold tailWord_184049
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712818510229380911795201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4475212340152920607863467 6712818510229380911795201)
  ·
    refine ⟨5034613882672035683846401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6712818510229380911795201 5034613882672035683846401)
    ·
      refine ⟨3775960412004026762884801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5034613882672035683846401 3775960412004026762884801)
      ·
        refine ⟨2831970309003020072163601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3775960412004026762884801 2831970309003020072163601)
        ·
          refine ⟨2123977731752265054122701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2831970309003020072163601 2123977731752265054122701)
          ·
            refine ⟨796491649407099395296013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2123977731752265054122701 796491649407099395296013)
            ·
              refine ⟨298684368527662273236005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 796491649407099395296013 298684368527662273236005)
              ·
                refine ⟨56003319098936676231751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298684368527662273236005 56003319098936676231751)
                ·
                  rfl

theorem cell19_184049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_184049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184049 prefixEnd_184049 := by exact prefixLift 184049
  have htrace : WordTrace (prefixWord ++ tailWord_184049) baseStart_184049 baseEnd_184049 := by
    simpa [prefixWord, tailWord_184049, baseEnd_184049] using wordTrace_append hprefix tailTrace_184049
  have hstable : (prefixWord ++ tailWord_184049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184049).length < 2 ^ (prefixWord ++ tailWord_184049).sum := by decide
  have hdescent : baseEnd_184049 < baseStart_184049 := by decide
  rcases family_descends (prefixWord ++ tailWord_184049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184087 : List Nat := [1, 1, 3, 4, 2, 2, 6]
def baseStart_184087 : Nat := 118140960795 + 184087 * 2 ^ 59
def prefixEnd_184087 : Nat := 4983230072969 + 3 ^ 40 * 184087 * 2
def baseEnd_184087 : Nat := 18671627307521282462401

theorem tailTrace_184087 : CollatzResearch.WordTrace tailWord_184087 prefixEnd_184087 18671627307521282462401 := by
  unfold tailWord_184087
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714204484091713401678515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4476136322727808934452343 6714204484091713401678515)
  ·
    refine ⟨10071306726137570102517773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714204484091713401678515 10071306726137570102517773)
    ·
      refine ⟨3776740022301588788444165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10071306726137570102517773 3776740022301588788444165)
      ·
        refine ⟨708138754181547897833281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3776740022301588788444165 708138754181547897833281)
        ·
          refine ⟨531104065636160923374961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708138754181547897833281 531104065636160923374961)
          ·
            refine ⟨398328049227120692531221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531104065636160923374961 398328049227120692531221)
            ·
              refine ⟨18671627307521282462401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 398328049227120692531221 18671627307521282462401)
              ·
                rfl

theorem cell19_184087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_184087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184087 prefixEnd_184087 := by exact prefixLift 184087
  have htrace : WordTrace (prefixWord ++ tailWord_184087) baseStart_184087 baseEnd_184087 := by
    simpa [prefixWord, tailWord_184087, baseEnd_184087] using wordTrace_append hprefix tailTrace_184087
  have hstable : (prefixWord ++ tailWord_184087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184087).length < 2 ^ (prefixWord ++ tailWord_184087).sum := by decide
  have hdescent : baseEnd_184087 < baseStart_184087 := by decide
  rcases family_descends (prefixWord ++ tailWord_184087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184216 : List Nat := [2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_184216 : Nat := 118140960795 + 184216 * 2 ^ 59
def prefixEnd_184216 : Nat := 4983230072969 + 3 ^ 40 * 184216 * 2
def baseEnd_184216 : Nat := 56054134665929770520185

theorem tailTrace_184216 : CollatzResearch.WordTrace tailWord_184216 prefixEnd_184216 56054134665929770520185 := by
  unfold tailWord_184216
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359454750312184216562251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4479273000416245622083001 3359454750312184216562251)
  ·
    refine ⟨5039182125468276324843377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359454750312184216562251 5039182125468276324843377)
    ·
      refine ⟨3779386594101207243632533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5039182125468276324843377 3779386594101207243632533)
      ·
        refine ⟨177158746598494089545275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3779386594101207243632533 177158746598494089545275)
        ·
          refine ⟨265738119897741134317913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177158746598494089545275 265738119897741134317913)
          ·
            refine ⟨199303589923305850738435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265738119897741134317913 199303589923305850738435)
            ·
              refine ⟨298955384884958776107653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199303589923305850738435 298955384884958776107653)
              ·
                refine ⟨56054134665929770520185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298955384884958776107653 56054134665929770520185)
                ·
                  rfl

theorem cell19_184216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_184216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184216 prefixEnd_184216 := by exact prefixLift 184216
  have htrace : WordTrace (prefixWord ++ tailWord_184216) baseStart_184216 baseEnd_184216 := by
    simpa [prefixWord, tailWord_184216, baseEnd_184216] using wordTrace_append hprefix tailTrace_184216
  have hstable : (prefixWord ++ tailWord_184216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184216).length < 2 ^ (prefixWord ++ tailWord_184216).sum := by decide
  have hdescent : baseEnd_184216 < baseStart_184216 := by decide
  rcases family_descends (prefixWord ++ tailWord_184216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184218 : List Nat := [3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_184218 : Nat := 118140960795 + 184218 * 2 ^ 59
def prefixEnd_184218 : Nat := 4983230072969 + 3 ^ 40 * 184218 * 2
def baseEnd_184218 : Nat := 56054743235594358475735

theorem tailTrace_184218 : CollatzResearch.WordTrace tailWord_184218 prefixEnd_184218 56054743235594358475735 := by
  unfold tailWord_184218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679745611654280693674327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4479321631078081849798205 1679745611654280693674327)
  ·
    refine ⟨2519618417481421040511491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679745611654280693674327 2519618417481421040511491)
    ·
      refine ⟨3779427626222131560767237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519618417481421040511491 3779427626222131560767237)
      ·
        refine ⟨708642679916649667643857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3779427626222131560767237 708642679916649667643857)
        ·
          refine ⟨531482009937487250732893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708642679916649667643857 531482009937487250732893)
          ·
            refine ⟨199305753726557719024835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531482009937487250732893 199305753726557719024835)
            ·
              refine ⟨298958630589836578537253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199305753726557719024835 298958630589836578537253)
              ·
                refine ⟨56054743235594358475735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298958630589836578537253 56054743235594358475735)
                ·
                  rfl

theorem cell19_184218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_184218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184218 prefixEnd_184218 := by exact prefixLift 184218
  have htrace : WordTrace (prefixWord ++ tailWord_184218) baseStart_184218 baseEnd_184218 := by
    simpa [prefixWord, tailWord_184218, baseEnd_184218] using wordTrace_append hprefix tailTrace_184218
  have hstable : (prefixWord ++ tailWord_184218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184218).length < 2 ^ (prefixWord ++ tailWord_184218).sum := by decide
  have hdescent : baseEnd_184218 < baseStart_184218 := by decide
  rcases family_descends (prefixWord ++ tailWord_184218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184239 : List Nat := [1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_184239 : Nat := 118140960795 + 184239 * 2 ^ 59
def prefixEnd_184239 : Nat := 4983230072969 + 3 ^ 40 * 184239 * 2
def baseEnd_184239 : Nat := 56061133217072532009011

theorem tailTrace_184239 : CollatzResearch.WordTrace tailWord_184239 prefixEnd_184239 56061133217072532009011 := by
  unfold tailWord_184239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719748379541043361211771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4479832253027362240807847 6719748379541043361211771)
  ·
    refine ⟨10079622569311565041817657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6719748379541043361211771 10079622569311565041817657)
    ·
      refine ⟨7559716926983673781363243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10079622569311565041817657 7559716926983673781363243)
      ·
        refine ⟨11339575390475510672044865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559716926983673781363243 11339575390475510672044865)
        ·
          refine ⟨8504681542856633004033649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11339575390475510672044865 8504681542856633004033649)
          ·
            refine ⟨6378511157142474753025237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8504681542856633004033649 6378511157142474753025237)
            ·
              refine ⟨149496355245526752024029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6378511157142474753025237 149496355245526752024029)
              ·
                refine ⟨56061133217072532009011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149496355245526752024029 56061133217072532009011)
                ·
                  rfl

theorem cell19_184239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_184239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184239 prefixEnd_184239 := by exact prefixLift 184239
  have htrace : WordTrace (prefixWord ++ tailWord_184239) baseStart_184239 baseEnd_184239 := by
    simpa [prefixWord, tailWord_184239, baseEnd_184239] using wordTrace_append hprefix tailTrace_184239
  have hstable : (prefixWord ++ tailWord_184239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184239).length < 2 ^ (prefixWord ++ tailWord_184239).sum := by decide
  have hdescent : baseEnd_184239 < baseStart_184239 := by decide
  rcases family_descends (prefixWord ++ tailWord_184239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184279 : List Nat := [1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_184279 : Nat := 118140960795 + 184279 * 2 ^ 59
def prefixEnd_184279 : Nat := 4983230072969 + 3 ^ 40 * 184279 * 2
def baseEnd_184279 : Nat := 56073304610364291120013

theorem tailTrace_184279 : CollatzResearch.WordTrace tailWord_184279 prefixEnd_184279 56073304610364291120013 := by
  unfold tailWord_184279
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721207299396130192667891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4480804866264086795111927 6721207299396130192667891)
  ·
    refine ⟨10081810949094195289001837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721207299396130192667891 10081810949094195289001837)
    ·
      refine ⟨3780679105910323233375689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10081810949094195289001837 3780679105910323233375689)
      ·
        refine ⟨2835509329432742425031767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3780679105910323233375689 2835509329432742425031767)
        ·
          refine ⟨4253263994149113637547651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835509329432742425031767 4253263994149113637547651)
          ·
            refine ⟨6379895991223670456321477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253263994149113637547651 6379895991223670456321477)
            ·
              refine ⟨1196230498354438210560277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6379895991223670456321477 1196230498354438210560277)
              ·
                refine ⟨56073304610364291120013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1196230498354438210560277 56073304610364291120013)
                ·
                  rfl

theorem cell19_184279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_184279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184279 prefixEnd_184279 := by exact prefixLift 184279
  have htrace : WordTrace (prefixWord ++ tailWord_184279) baseStart_184279 baseEnd_184279 := by
    simpa [prefixWord, tailWord_184279, baseEnd_184279] using wordTrace_append hprefix tailTrace_184279
  have hstable : (prefixWord ++ tailWord_184279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184279).length < 2 ^ (prefixWord ++ tailWord_184279).sum := by decide
  have hdescent : baseEnd_184279 < baseStart_184279 := by decide
  rcases family_descends (prefixWord ++ tailWord_184279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184290 : List Nat := [3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_184290 : Nat := 118140960795 + 184290 * 2 ^ 59
def prefixEnd_184290 : Nat := 4983230072969 + 3 ^ 40 * 184290 * 2
def baseEnd_184290 : Nat := 56076651743519524875539

theorem tailTrace_184290 : CollatzResearch.WordTrace tailWord_184290 prefixEnd_184290 56076651743519524875539 := by
  unfold tailWord_184290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680402125589069767829581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4481072334904186047545549 1680402125589069767829581)
  ·
    refine ⟨630150797095901162936093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1680402125589069767829581 630150797095901162936093)
    ·
      refine ⟨236306548910962936101035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 630150797095901162936093 236306548910962936101035)
      ·
        refine ⟨354459823366444404151553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236306548910962936101035 354459823366444404151553)
        ·
          refine ⟨265844867524833303113665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354459823366444404151553 265844867524833303113665)
          ·
            refine ⟨199383650643624977335249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265844867524833303113665 199383650643624977335249)
            ·
              refine ⟨149537737982718733001437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199383650643624977335249 149537737982718733001437)
              ·
                refine ⟨56076651743519524875539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149537737982718733001437 56076651743519524875539)
                ·
                  rfl

theorem cell19_184290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_184290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184290 prefixEnd_184290 := by exact prefixLift 184290
  have htrace : WordTrace (prefixWord ++ tailWord_184290) baseStart_184290 baseEnd_184290 := by
    simpa [prefixWord, tailWord_184290, baseEnd_184290] using wordTrace_append hprefix tailTrace_184290
  have hstable : (prefixWord ++ tailWord_184290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184290).length < 2 ^ (prefixWord ++ tailWord_184290).sum := by decide
  have hdescent : baseEnd_184290 < baseStart_184290 := by decide
  rcases family_descends (prefixWord ++ tailWord_184290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184317 : List Nat := [1, 4, 1, 1, 1, 2, 9]
def baseStart_184317 : Nat := 118140960795 + 184317 * 2 ^ 59
def prefixEnd_184317 : Nat := 4983230072969 + 3 ^ 40 * 184317 * 2
def baseEnd_184317 : Nat := 18694955811330487425155

theorem tailTrace_184317 : CollatzResearch.WordTrace tailWord_184317 prefixEnd_184317 18694955811330487425155 := by
  unfold tailWord_184317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722593273258462682551205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4481728848838975121700803 6722593273258462682551205)
  ·
    refine ⟨1260486238735961752978351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6722593273258462682551205 1260486238735961752978351)
    ·
      refine ⟨1890729358103942629467527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260486238735961752978351 1890729358103942629467527)
      ·
        refine ⟨2836094037155913944201291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890729358103942629467527 2836094037155913944201291)
        ·
          refine ⟨4254141055733870916301937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836094037155913944201291 4254141055733870916301937)
          ·
            refine ⟨3190605791800403187226453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4254141055733870916301937 3190605791800403187226453)
            ·
              refine ⟨18694955811330487425155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3190605791800403187226453 18694955811330487425155)
              ·
                rfl

theorem cell19_184317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_184317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184317 prefixEnd_184317 := by exact prefixLift 184317
  have htrace : WordTrace (prefixWord ++ tailWord_184317) baseStart_184317 baseEnd_184317 := by
    simpa [prefixWord, tailWord_184317, baseEnd_184317] using wordTrace_append hprefix tailTrace_184317
  have hstable : (prefixWord ++ tailWord_184317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184317).length < 2 ^ (prefixWord ++ tailWord_184317).sum := by decide
  have hdescent : baseEnd_184317 < baseStart_184317 := by decide
  rcases family_descends (prefixWord ++ tailWord_184317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184326 : List Nat := [6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_184326 : Nat := 118140960795 + 184326 * 2 ^ 59
def prefixEnd_184326 : Nat := 4983230072969 + 3 ^ 40 * 184326 * 2
def baseEnd_184326 : Nat := 56087605997482108075441

theorem tailTrace_184326 : CollatzResearch.WordTrace tailWord_184326 prefixEnd_184326 56087605997482108075441 := by
  unfold tailWord_184326
  simp only [CollatzResearch.WordTrace]
  refine ⟨210091297819558038113401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4481947686817238146419221 210091297819558038113401)
  ·
    refine ⟨157568473364668528585051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210091297819558038113401 157568473364668528585051)
    ·
      refine ⟨236352710047002792877577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157568473364668528585051 236352710047002792877577)
      ·
        refine ⟨177264532535252094658183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236352710047002792877577 177264532535252094658183)
        ·
          refine ⟨265896798802878141987275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177264532535252094658183 265896798802878141987275)
          ·
            refine ⟨398845198204317212980913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265896798802878141987275 398845198204317212980913)
            ·
              refine ⟨299133898653237909735685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398845198204317212980913 299133898653237909735685)
              ·
                refine ⟨56087605997482108075441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299133898653237909735685 56087605997482108075441)
                ·
                  rfl

theorem cell19_184326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_184326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184326 prefixEnd_184326 := by exact prefixLift 184326
  have htrace : WordTrace (prefixWord ++ tailWord_184326) baseStart_184326 baseEnd_184326 := by
    simpa [prefixWord, tailWord_184326, baseEnd_184326] using wordTrace_append hprefix tailTrace_184326
  have hstable : (prefixWord ++ tailWord_184326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184326).length < 2 ^ (prefixWord ++ tailWord_184326).sum := by decide
  have hdescent : baseEnd_184326 < baseStart_184326 := by decide
  rcases family_descends (prefixWord ++ tailWord_184326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184334 : List Nat := [4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_184334 : Nat := 118140960795 + 184334 * 2 ^ 59
def prefixEnd_184334 : Nat := 4983230072969 + 3 ^ 40 * 184334 * 2
def baseEnd_184334 : Nat := 56090040276140459897641

theorem tailTrace_184334 : CollatzResearch.WordTrace tailWord_184334 prefixEnd_184334 56090040276140459897641 := by
  unfold tailWord_184334
  simp only [CollatzResearch.WordTrace]
  refine ⟨840401664274609323240007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4482142209464583057280037 840401664274609323240007)
  ·
    refine ⟨1260602496411913984860011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840401664274609323240007 1260602496411913984860011)
    ·
      refine ⟨1890903744617870977290017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260602496411913984860011 1890903744617870977290017)
      ·
        refine ⟨1418177808463403232967513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1890903744617870977290017 1418177808463403232967513)
        ·
          refine ⟨1063633356347552424725635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418177808463403232967513 1063633356347552424725635)
          ·
            refine ⟨1595450034521328637088453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063633356347552424725635 1595450034521328637088453)
            ·
              refine ⟨299146881472749119454085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1595450034521328637088453 299146881472749119454085)
              ·
                refine ⟨56090040276140459897641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299146881472749119454085 56090040276140459897641)
                ·
                  rfl

theorem cell19_184334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_184334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184334 prefixEnd_184334 := by exact prefixLift 184334
  have htrace : WordTrace (prefixWord ++ tailWord_184334) baseStart_184334 baseEnd_184334 := by
    simpa [prefixWord, tailWord_184334, baseEnd_184334] using wordTrace_append hprefix tailTrace_184334
  have hstable : (prefixWord ++ tailWord_184334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184334).length < 2 ^ (prefixWord ++ tailWord_184334).sum := by decide
  have hdescent : baseEnd_184334 < baseStart_184334 := by decide
  rcases family_descends (prefixWord ++ tailWord_184334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184355 : List Nat := [1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_184355 : Nat := 118140960795 + 184355 * 2 ^ 59
def prefixEnd_184355 : Nat := 4983230072969 + 3 ^ 40 * 184355 * 2
def baseEnd_184355 : Nat := 56096430257618633430917

theorem tailTrace_184355 : CollatzResearch.WordTrace tailWord_184355 prefixEnd_184355 56096430257618633430917 := by
  unfold tailWord_184355
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723979247120795172434519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4482652831413863448289679 6723979247120795172434519)
  ·
    refine ⟨10085968870681192758651779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723979247120795172434519 10085968870681192758651779)
    ·
      refine ⟨15128953306021789137977669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085968870681192758651779 15128953306021789137977669)
      ·
        refine ⟨2836678744879085463370813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15128953306021789137977669 2836678744879085463370813)
        ·
          refine ⟨1063754529329657048764055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2836678744879085463370813 1063754529329657048764055)
          ·
            refine ⟨1595631793994485573146083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063754529329657048764055 1595631793994485573146083)
            ·
              refine ⟨2393447690991728359719125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595631793994485573146083 2393447690991728359719125)
              ·
                refine ⟨56096430257618633430917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2393447690991728359719125 56096430257618633430917)
                ·
                  rfl

theorem cell19_184355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_184355 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184355 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184355 prefixEnd_184355 := by exact prefixLift 184355
  have htrace : WordTrace (prefixWord ++ tailWord_184355) baseStart_184355 baseEnd_184355 := by
    simpa [prefixWord, tailWord_184355, baseEnd_184355] using wordTrace_append hprefix tailTrace_184355
  have hstable : (prefixWord ++ tailWord_184355).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184355).length < 2 ^ (prefixWord ++ tailWord_184355).sum := by decide
  have hdescent : baseEnd_184355 < baseStart_184355 := by decide
  rcases family_descends (prefixWord ++ tailWord_184355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184372 : List Nat := [2, 5, 1, 2, 9]
def baseStart_184372 : Nat := 118140960795 + 184372 * 2 ^ 59
def prefixEnd_184372 : Nat := 4983230072969 + 3 ^ 40 * 184372 * 2
def baseEnd_184372 : Nat := 2077837151843245594559

theorem tailTrace_184372 : CollatzResearch.WordTrace tailWord_184372 prefixEnd_184372 2077837151843245594559 := by
  unfold tailWord_184372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362299644029603537901685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4483066192039471383868913 3362299644029603537901685)
  ·
    refine ⟨315215591627775331678283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3362299644029603537901685 315215591627775331678283)
    ·
      refine ⟨472823387441662997517425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315215591627775331678283 472823387441662997517425)
      ·
        refine ⟨354617540581247248138069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472823387441662997517425 354617540581247248138069)
        ·
          refine ⟨2077837151843245594559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 354617540581247248138069 2077837151843245594559)
          ·
            rfl

theorem cell19_184372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 9].length) (baseStart_184372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184372 prefixEnd_184372 := by exact prefixLift 184372
  have htrace : WordTrace (prefixWord ++ tailWord_184372) baseStart_184372 baseEnd_184372 := by
    simpa [prefixWord, tailWord_184372, baseEnd_184372] using wordTrace_append hprefix tailTrace_184372
  have hstable : (prefixWord ++ tailWord_184372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184372).length < 2 ^ (prefixWord ++ tailWord_184372).sum := by decide
  have hdescent : baseEnd_184372 < baseStart_184372 := by decide
  rcases family_descends (prefixWord ++ tailWord_184372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184410 : List Nat := [3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_184410 : Nat := 118140960795 + 184410 * 2 ^ 59
def prefixEnd_184410 : Nat := 4983230072969 + 3 ^ 40 * 184410 * 2
def baseEnd_184410 : Nat := 56113165923394802208545

theorem tailTrace_184410 : CollatzResearch.WordTrace tailWord_184410 prefixEnd_184410 56113165923394802208545 := by
  unfold tailWord_184410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681496315480384891421671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4483990174614359710457789 1681496315480384891421671)
  ·
    refine ⟨2522244473220577337132507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1681496315480384891421671 2522244473220577337132507)
    ·
      refine ⟨3783366709830866005698761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522244473220577337132507 3783366709830866005698761)
      ·
        refine ⟨2837525032373149504274071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3783366709830866005698761 2837525032373149504274071)
        ·
          refine ⟨4256287548559724256411107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837525032373149504274071 4256287548559724256411107)
          ·
            refine ⟨6384431322839586384616661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256287548559724256411107 6384431322839586384616661)
            ·
              refine ⟨149635109129052805889453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6384431322839586384616661 149635109129052805889453)
              ·
                refine ⟨56113165923394802208545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149635109129052805889453 56113165923394802208545)
                ·
                  rfl

theorem cell19_184410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_184410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184410 prefixEnd_184410 := by exact prefixLift 184410
  have htrace : WordTrace (prefixWord ++ tailWord_184410) baseStart_184410 baseEnd_184410 := by
    simpa [prefixWord, tailWord_184410, baseEnd_184410] using wordTrace_append hprefix tailTrace_184410
  have hstable : (prefixWord ++ tailWord_184410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184410).length < 2 ^ (prefixWord ++ tailWord_184410).sum := by decide
  have hdescent : baseEnd_184410 < baseStart_184410 := by decide
  rcases family_descends (prefixWord ++ tailWord_184410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184431 : List Nat := [1, 1, 2, 1, 3, 5, 6]
def baseStart_184431 : Nat := 118140960795 + 184431 * 2 ^ 59
def prefixEnd_184431 : Nat := 4983230072969 + 3 ^ 40 * 184431 * 2
def baseEnd_184431 : Nat := 18706518634957658580607

theorem tailTrace_184431 : CollatzResearch.WordTrace tailWord_184431 prefixEnd_184431 18706518634957658580607 := by
  unfold tailWord_184431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726751194845460152201147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4484500796563640101467431 6726751194845460152201147)
  ·
    refine ⟨10090126792268190228301721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6726751194845460152201147 10090126792268190228301721)
    ·
      refine ⟨7567595094201142671226291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10090126792268190228301721 7567595094201142671226291)
      ·
        refine ⟨11351392641301714006839437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567595094201142671226291 11351392641301714006839437)
        ·
          refine ⟨4256772240488142752564789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11351392641301714006839437 4256772240488142752564789)
          ·
            refine ⟨399072397545763383052949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4256772240488142752564789 399072397545763383052949)
            ·
              refine ⟨18706518634957658580607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 399072397545763383052949 18706518634957658580607)
              ·
                rfl

theorem cell19_184431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_184431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184431 prefixEnd_184431 := by exact prefixLift 184431
  have htrace : WordTrace (prefixWord ++ tailWord_184431) baseStart_184431 baseEnd_184431 := by
    simpa [prefixWord, tailWord_184431, baseEnd_184431] using wordTrace_append hprefix tailTrace_184431
  have hstable : (prefixWord ++ tailWord_184431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184431).length < 2 ^ (prefixWord ++ tailWord_184431).sum := by decide
  have hdescent : baseEnd_184431 < baseStart_184431 := by decide
  rcases family_descends (prefixWord ++ tailWord_184431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184469 : List Nat := [1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_184469 : Nat := 118140960795 + 184469 * 2 ^ 59
def prefixEnd_184469 : Nat := 4983230072969 + 3 ^ 40 * 184469 * 2
def baseEnd_184469 : Nat := 56131118728500146897273

theorem tailTrace_184469 : CollatzResearch.WordTrace tailWord_184469 prefixEnd_184469 56131118728500146897273 := by
  unfold tailWord_184469
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728137168707792642084461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4485424779138528428056307 6728137168707792642084461)
  ·
    refine ⟨2523051438265422240781673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6728137168707792642084461 2523051438265422240781673)
    ·
      refine ⟨1892288578699066680586255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2523051438265422240781673 1892288578699066680586255)
      ·
        refine ⟨2838432868048600020879383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892288578699066680586255 2838432868048600020879383)
        ·
          refine ⟨4257649302072900031319075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838432868048600020879383 4257649302072900031319075)
          ·
            refine ⟨6386473953109350046978613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257649302072900031319075 6386473953109350046978613)
            ·
              refine ⟨598731933104001566904245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6386473953109350046978613 598731933104001566904245)
              ·
                refine ⟨56131118728500146897273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 598731933104001566904245 56131118728500146897273)
                ·
                  rfl

theorem cell19_184469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_184469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184469 prefixEnd_184469 := by exact prefixLift 184469
  have htrace : WordTrace (prefixWord ++ tailWord_184469) baseStart_184469 baseEnd_184469 := by
    simpa [prefixWord, tailWord_184469, baseEnd_184469] using wordTrace_append hprefix tailTrace_184469
  have hstable : (prefixWord ++ tailWord_184469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184469).length < 2 ^ (prefixWord ++ tailWord_184469).sum := by decide
  have hdescent : baseEnd_184469 < baseStart_184469 := by decide
  rcases family_descends (prefixWord ++ tailWord_184469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184484 : List Nat := [2, 3, 1, 2, 5, 1, 5]
def baseStart_184484 : Nat := 118140960795 + 184484 * 2 ^ 59
def prefixEnd_184484 : Nat := 4983230072969 + 3 ^ 40 * 184484 * 2
def baseEnd_184484 : Nat := 18711894333661518854633

theorem tailTrace_184484 : CollatzResearch.WordTrace tailWord_184484 prefixEnd_184484 18711894333661518854633 := by
  unfold tailWord_184484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364342131826725101940253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4485789509102300135920337 3364342131826725101940253)
  ·
    refine ⟨1261628299435021913227595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3364342131826725101940253 1261628299435021913227595)
    ·
      refine ⟨1892442449152532869841393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261628299435021913227595 1892442449152532869841393)
      ·
        refine ⟨1419331836864399652381045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1892442449152532869841393 1419331836864399652381045)
        ·
          refine ⟨133062359706037467410723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1419331836864399652381045 133062359706037467410723)
          ·
            refine ⟨199593539559056201116085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133062359706037467410723 199593539559056201116085)
            ·
              refine ⟨18711894333661518854633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199593539559056201116085 18711894333661518854633)
              ·
                rfl

theorem cell19_184484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_184484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184484 prefixEnd_184484 := by exact prefixLift 184484
  have htrace : WordTrace (prefixWord ++ tailWord_184484) baseStart_184484 baseEnd_184484 := by
    simpa [prefixWord, tailWord_184484, baseEnd_184484] using wordTrace_append hprefix tailTrace_184484
  have hstable : (prefixWord ++ tailWord_184484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184484).length < 2 ^ (prefixWord ++ tailWord_184484).sum := by decide
  have hdescent : baseEnd_184484 < baseStart_184484 := by decide
  rcases family_descends (prefixWord ++ tailWord_184484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184507 : List Nat := [1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_184507 : Nat := 118140960795 + 184507 * 2 ^ 59
def prefixEnd_184507 : Nat := 4983230072969 + 3 ^ 40 * 184507 * 2
def baseEnd_184507 : Nat := 56142681552127318052725

theorem tailTrace_184507 : CollatzResearch.WordTrace tailWord_184507 prefixEnd_184507 56142681552127318052725 := by
  unfold tailWord_184507
  simp only [CollatzResearch.WordTrace]
  refine ⟨6729523142570125131967775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4486348761713416754645183 6729523142570125131967775)
  ·
    refine ⟨10094284713855187697951663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6729523142570125131967775 10094284713855187697951663)
    ·
      refine ⟨15141427070782781546927495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10094284713855187697951663 15141427070782781546927495)
      ·
        refine ⟨22712140606174172320391243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15141427070782781546927495 22712140606174172320391243)
        ·
          refine ⟨34068210909261258480586865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22712140606174172320391243 34068210909261258480586865)
          ·
            refine ⟨25551158181945943860440149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34068210909261258480586865 25551158181945943860440149)
            ·
              refine ⟨299427634944679029614533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 25551158181945943860440149 299427634944679029614533)
              ·
                refine ⟨56142681552127318052725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299427634944679029614533 56142681552127318052725)
                ·
                  rfl

theorem cell19_184507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_184507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184507 prefixEnd_184507 := by exact prefixLift 184507
  have htrace : WordTrace (prefixWord ++ tailWord_184507) baseStart_184507 baseEnd_184507 := by
    simpa [prefixWord, tailWord_184507, baseEnd_184507] using wordTrace_append hprefix tailTrace_184507
  have hstable : (prefixWord ++ tailWord_184507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184507).length < 2 ^ (prefixWord ++ tailWord_184507).sum := by decide
  have hdescent : baseEnd_184507 < baseStart_184507 := by decide
  rcases family_descends (prefixWord ++ tailWord_184507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184562 : List Nat := [3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_184562 : Nat := 118140960795 + 184562 * 2 ^ 59
def prefixEnd_184562 : Nat := 4983230072969 + 3 ^ 40 * 184562 * 2
def baseEnd_184562 : Nat := 56159417217903486830353

theorem tailTrace_184562 : CollatzResearch.WordTrace tailWord_184562 prefixEnd_184562 56159417217903486830353 := by
  unfold tailWord_184562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682882289342717381304985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4487686104913913016813293 1682882289342717381304985)
  ·
    refine ⟨1262161717007038035978739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1682882289342717381304985 1262161717007038035978739)
    ·
      refine ⟨1893242575510557053968109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262161717007038035978739 1893242575510557053968109)
      ·
        refine ⟨709965965816458895238041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1893242575510557053968109 709965965816458895238041)
        ·
          refine ⟨532474474362344171428531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709965965816458895238041 532474474362344171428531)
          ·
            refine ⟨798711711543516257142797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532474474362344171428531 798711711543516257142797)
            ·
              refine ⟨299516891828818596428549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798711711543516257142797 299516891828818596428549)
              ·
                refine ⟨56159417217903486830353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299516891828818596428549 56159417217903486830353)
                ·
                  rfl

theorem cell19_184562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_184562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184562 prefixEnd_184562 := by exact prefixLift 184562
  have htrace : WordTrace (prefixWord ++ tailWord_184562) baseStart_184562 baseEnd_184562 := by
    simpa [prefixWord, tailWord_184562, baseEnd_184562] using wordTrace_append hprefix tailTrace_184562
  have hstable : (prefixWord ++ tailWord_184562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184562).length < 2 ^ (prefixWord ++ tailWord_184562).sum := by decide
  have hdescent : baseEnd_184562 < baseStart_184562 := by decide
  rcases family_descends (prefixWord ++ tailWord_184562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184638 : List Nat := [4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_184638 : Nat := 118140960795 + 184638 * 2 ^ 59
def prefixEnd_184638 : Nat := 4983230072969 + 3 ^ 40 * 184638 * 2
def baseEnd_184638 : Nat := 56182542865157829141257

theorem tailTrace_184638 : CollatzResearch.WordTrace tailWord_184638 prefixEnd_184638 56182542865157829141257 := by
  unfold tailWord_184638
  simp only [CollatzResearch.WordTrace]
  refine ⟨841787638136941813123321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4489534070063689669991045 841787638136941813123321)
  ·
    refine ⟨631340728602706359842491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 841787638136941813123321 631340728602706359842491)
    ·
      refine ⟨947011092904059539763737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631340728602706359842491 947011092904059539763737)
      ·
        refine ⟨710258319678044654822803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 947011092904059539763737 710258319678044654822803)
        ·
          refine ⟨1065387479517066982234205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710258319678044654822803 1065387479517066982234205)
          ·
            refine ⟨399520304818900118337827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1065387479517066982234205 399520304818900118337827)
            ·
              refine ⟨599280457228350177506741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399520304818900118337827 599280457228350177506741)
              ·
                refine ⟨56182542865157829141257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 599280457228350177506741 56182542865157829141257)
                ·
                  rfl

theorem cell19_184638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_184638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184638 prefixEnd_184638 := by exact prefixLift 184638
  have htrace : WordTrace (prefixWord ++ tailWord_184638) baseStart_184638 baseEnd_184638 := by
    simpa [prefixWord, tailWord_184638, baseEnd_184638] using wordTrace_append hprefix tailTrace_184638
  have hstable : (prefixWord ++ tailWord_184638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184638).length < 2 ^ (prefixWord ++ tailWord_184638).sum := by decide
  have hdescent : baseEnd_184638 < baseStart_184638 := by decide
  rcases family_descends (prefixWord ++ tailWord_184638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184714 : List Nat := [3, 1, 2, 5, 1, 7]
def baseStart_184714 : Nat := 118140960795 + 184714 * 2 ^ 59
def prefixEnd_184714 : Nat := 4983230072969 + 3 ^ 40 * 184714 * 2
def baseEnd_184714 : Nat := 6245074279156907939129

theorem tailTrace_184714 : CollatzResearch.WordTrace tailWord_184714 prefixEnd_184714 6245074279156907939129 := by
  unfold tailWord_184714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684268263205049871188299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4491382035213466323168797 1684268263205049871188299)
  ·
    refine ⟨2526402394807574806782449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1684268263205049871188299 2526402394807574806782449)
    ·
      refine ⟨1894801796105681105086837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2526402394807574806782449 1894801796105681105086837)
      ·
        refine ⟨177637668384907603601891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1894801796105681105086837 177637668384907603601891)
        ·
          refine ⟨266456502577361405402837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177637668384907603601891 266456502577361405402837)
          ·
            refine ⟨6245074279156907939129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 266456502577361405402837 6245074279156907939129)
            ·
              rfl

theorem cell19_184714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_184714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184714 prefixEnd_184714 := by exact prefixLift 184714
  have htrace : WordTrace (prefixWord ++ tailWord_184714) baseStart_184714 baseEnd_184714 := by
    simpa [prefixWord, tailWord_184714, baseEnd_184714] using wordTrace_append hprefix tailTrace_184714
  have hstable : (prefixWord ++ tailWord_184714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184714).length < 2 ^ (prefixWord ++ tailWord_184714).sum := by decide
  have hdescent : baseEnd_184714 < baseStart_184714 := by decide
  rcases family_descends (prefixWord ++ tailWord_184714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184746 : List Nat := [3, 1, 6, 1, 1, 1, 3, 3]
def baseStart_184746 : Nat := 118140960795 + 184746 * 2 ^ 59
def prefixEnd_184746 : Nat := 4983230072969 + 3 ^ 40 * 184746 * 2
def baseEnd_184746 : Nat := 56215405627045578740963

theorem tailTrace_184746 : CollatzResearch.WordTrace tailWord_184746 prefixEnd_184746 56215405627045578740963 := by
  unfold tailWord_184746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684560047176067237479523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4492160125802845966612061 1684560047176067237479523)
  ·
    refine ⟨2526840070764100856219285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1684560047176067237479523 2526840070764100856219285)
    ·
      refine ⟨118445628317067227635279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2526840070764100856219285 118445628317067227635279)
      ·
        refine ⟨177668442475600841452919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118445628317067227635279 177668442475600841452919)
        ·
          refine ⟨266502663713401262179379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177668442475600841452919 266502663713401262179379)
          ·
            refine ⟨399753995570101893269069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266502663713401262179379 399753995570101893269069)
            ·
              refine ⟨149907748338788209975901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399753995570101893269069 149907748338788209975901)
              ·
                refine ⟨56215405627045578740963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149907748338788209975901 56215405627045578740963)
                ·
                  rfl

theorem cell19_184746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_184746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184746 prefixEnd_184746 := by exact prefixLift 184746
  have htrace : WordTrace (prefixWord ++ tailWord_184746) baseStart_184746 baseEnd_184746 := by
    simpa [prefixWord, tailWord_184746, baseEnd_184746] using wordTrace_append hprefix tailTrace_184746
  have hstable : (prefixWord ++ tailWord_184746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184746).length < 2 ^ (prefixWord ++ tailWord_184746).sum := by decide
  have hdescent : baseEnd_184746 < baseStart_184746 := by decide
  rcases family_descends (prefixWord ++ tailWord_184746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184790 : List Nat := [5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_184790 : Nat := 118140960795 + 184790 * 2 ^ 59
def prefixEnd_184790 : Nat := 4983230072969 + 3 ^ 40 * 184790 * 2
def baseEnd_184790 : Nat := 56228794159666513763065

theorem tailTrace_184790 : CollatzResearch.WordTrace tailWord_184790 prefixEnd_184790 56228794159666513763065 := by
  unfold tailWord_184790
  simp only [CollatzResearch.WordTrace]
  refine ⟨421240312534054029032489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4493230000363242976346549 421240312534054029032489)
  ·
    refine ⟨315930234400540521774367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 421240312534054029032489 315930234400540521774367)
    ·
      refine ⟨473895351600810782661551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315930234400540521774367 473895351600810782661551)
      ·
        refine ⟨710843027401216173992327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473895351600810782661551 710843027401216173992327)
        ·
          refine ⟨1066264541101824260988491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710843027401216173992327 1066264541101824260988491)
          ·
            refine ⟨1599396811652736391482737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066264541101824260988491 1599396811652736391482737)
            ·
              refine ⟨1199547608739552293612053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599396811652736391482737 1199547608739552293612053)
              ·
                refine ⟨56228794159666513763065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1199547608739552293612053 56228794159666513763065)
                ·
                  rfl

theorem cell19_184790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_184790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184790 prefixEnd_184790 := by exact prefixLift 184790
  have htrace : WordTrace (prefixWord ++ tailWord_184790) baseStart_184790 baseEnd_184790 := by
    simpa [prefixWord, tailWord_184790, baseEnd_184790] using wordTrace_append hprefix tailTrace_184790
  have hstable : (prefixWord ++ tailWord_184790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184790).length < 2 ^ (prefixWord ++ tailWord_184790).sum := by decide
  have hdescent : baseEnd_184790 < baseStart_184790 := by decide
  rcases family_descends (prefixWord ++ tailWord_184790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184805 : List Nat := [1, 3, 1, 5, 3, 1, 2, 3]
def baseStart_184805 : Nat := 118140960795 + 184805 * 2 ^ 59
def prefixEnd_184805 : Nat := 4983230072969 + 3 ^ 40 * 184805 * 2
def baseEnd_184805 : Nat := 56233358432150923429691

theorem tailTrace_184805 : CollatzResearch.WordTrace tailWord_184805 prefixEnd_184805 56233358432150923429691 := by
  unfold tailWord_184805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740392095490522026315869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4493594730327014684210579 6740392095490522026315869)
  ·
    refine ⟨2527647035808945759868451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6740392095490522026315869 2527647035808945759868451)
    ·
      refine ⟨3791470553713418639802677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2527647035808945759868451 3791470553713418639802677)
      ·
        refine ⟨355450364410632997481501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3791470553713418639802677 355450364410632997481501)
        ·
          refine ⟨133293886653987374055563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355450364410632997481501 133293886653987374055563)
          ·
            refine ⟨199940829980981061083345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133293886653987374055563 199940829980981061083345)
            ·
              refine ⟨149955622485735795812509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199940829980981061083345 149955622485735795812509)
              ·
                refine ⟨56233358432150923429691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149955622485735795812509 56233358432150923429691)
                ·
                  rfl

theorem cell19_184805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_184805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184805 prefixEnd_184805 := by exact prefixLift 184805
  have htrace : WordTrace (prefixWord ++ tailWord_184805) baseStart_184805 baseEnd_184805 := by
    simpa [prefixWord, tailWord_184805, baseEnd_184805] using wordTrace_append hprefix tailTrace_184805
  have hstable : (prefixWord ++ tailWord_184805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184805).length < 2 ^ (prefixWord ++ tailWord_184805).sum := by decide
  have hdescent : baseEnd_184805 < baseStart_184805 := by decide
  rcases family_descends (prefixWord ++ tailWord_184805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184845 : List Nat := [1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_184845 : Nat := 118140960795 + 184845 * 2 ^ 59
def prefixEnd_184845 : Nat := 4983230072969 + 3 ^ 40 * 184845 * 2
def baseEnd_184845 : Nat := 56245529825442682540693

theorem tailTrace_184845 : CollatzResearch.WordTrace tailWord_184845 prefixEnd_184845 56245529825442682540693 := by
  unfold tailWord_184845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741851015345608857771989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4494567343563739238514659 6741851015345608857771989)
  ·
    refine ⟨158012133172162707604031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6741851015345608857771989 158012133172162707604031)
    ·
      refine ⟨237018199758244061406047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158012133172162707604031 237018199758244061406047)
      ·
        refine ⟨355527299637366092109071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237018199758244061406047 355527299637366092109071)
        ·
          refine ⟨533290949456049138163607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355527299637366092109071 533290949456049138163607)
          ·
            refine ⟨799936424184073707245411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533290949456049138163607 799936424184073707245411)
            ·
              refine ⟨1199904636276110560868117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799936424184073707245411 1199904636276110560868117)
              ·
                refine ⟨56245529825442682540693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1199904636276110560868117 56245529825442682540693)
                ·
                  rfl

theorem cell19_184845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_184845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184845 prefixEnd_184845 := by exact prefixLift 184845
  have htrace : WordTrace (prefixWord ++ tailWord_184845) baseStart_184845 baseEnd_184845 := by
    simpa [prefixWord, tailWord_184845, baseEnd_184845] using wordTrace_append hprefix tailTrace_184845
  have hstable : (prefixWord ++ tailWord_184845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184845).length < 2 ^ (prefixWord ++ tailWord_184845).sum := by decide
  have hdescent : baseEnd_184845 < baseStart_184845 := by decide
  rcases family_descends (prefixWord ++ tailWord_184845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184902 : List Nat := [6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_184902 : Nat := 118140960795 + 184902 * 2 ^ 59
def prefixEnd_184902 : Nat := 4983230072969 + 3 ^ 40 * 184902 * 2
def baseEnd_184902 : Nat := 56262874060883439273871

theorem tailTrace_184902 : CollatzResearch.WordTrace tailWord_184902 prefixEnd_184902 56262874060883439273871 := by
  unfold tailWord_184902
  simp only [CollatzResearch.WordTrace]
  refine ⟨210747811754347112268655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4495953317426071728397973 210747811754347112268655)
  ·
    refine ⟨316121717631520668402983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210747811754347112268655 316121717631520668402983)
    ·
      refine ⟨474182576447281002604475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316121717631520668402983 474182576447281002604475)
      ·
        refine ⟨711273864670921503906713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474182576447281002604475 711273864670921503906713)
        ·
          refine ⟨533455398503191127930035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711273864670921503906713 533455398503191127930035)
          ·
            refine ⟨800183097754786691895053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533455398503191127930035 800183097754786691895053)
            ·
              refine ⟨300068661658045009460645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 800183097754786691895053 300068661658045009460645)
              ·
                refine ⟨56262874060883439273871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300068661658045009460645 56262874060883439273871)
                ·
                  rfl

theorem cell19_184902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_184902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184902 prefixEnd_184902 := by exact prefixLift 184902
  have htrace : WordTrace (prefixWord ++ tailWord_184902) baseStart_184902 baseEnd_184902 := by
    simpa [prefixWord, tailWord_184902, baseEnd_184902] using wordTrace_append hprefix tailTrace_184902
  have hstable : (prefixWord ++ tailWord_184902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184902).length < 2 ^ (prefixWord ++ tailWord_184902).sum := by decide
  have hdescent : baseEnd_184902 < baseStart_184902 := by decide
  rcases family_descends (prefixWord ++ tailWord_184902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184906 : List Nat := [3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_184906 : Nat := 118140960795 + 184906 * 2 ^ 59
def prefixEnd_184906 : Nat := 4983230072969 + 3 ^ 40 * 184906 * 2
def baseEnd_184906 : Nat := 56264091200212615184971

theorem tailTrace_184906 : CollatzResearch.WordTrace tailWord_184906 prefixEnd_184906 56264091200212615184971 := by
  unfold tailWord_184906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686018967031154068935643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4496050578749744183828381 1686018967031154068935643)
  ·
    refine ⟨2529028450546731103403465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686018967031154068935643 2529028450546731103403465)
    ·
      refine ⟨1896771337910048327552599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2529028450546731103403465 1896771337910048327552599)
      ·
        refine ⟨2845157006865072491328899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896771337910048327552599 2845157006865072491328899)
        ·
          refine ⟨4267735510297608736993349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845157006865072491328899 4267735510297608736993349)
          ·
            refine ⟨800200408180801638186253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4267735510297608736993349 800200408180801638186253)
            ·
              refine ⟨300075153067800614319845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 800200408180801638186253 300075153067800614319845)
              ·
                refine ⟨56264091200212615184971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300075153067800614319845 56264091200212615184971)
                ·
                  rfl

theorem cell19_184906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_184906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184906 prefixEnd_184906 := by exact prefixLift 184906
  have htrace : WordTrace (prefixWord ++ tailWord_184906) baseStart_184906 baseEnd_184906 := by
    simpa [prefixWord, tailWord_184906, baseEnd_184906] using wordTrace_append hprefix tailTrace_184906
  have hstable : (prefixWord ++ tailWord_184906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184906).length < 2 ^ (prefixWord ++ tailWord_184906).sum := by decide
  have hdescent : baseEnd_184906 < baseStart_184906 := by decide
  rcases family_descends (prefixWord ++ tailWord_184906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184927 : List Nat := [1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_184927 : Nat := 118140960795 + 184927 * 2 ^ 59
def prefixEnd_184927 : Nat := 4983230072969 + 3 ^ 40 * 184927 * 2
def baseEnd_184927 : Nat := 56270481181690788718247

theorem tailTrace_184927 : CollatzResearch.WordTrace tailWord_184927 prefixEnd_184927 56270481181690788718247 := by
  unfold tailWord_184927
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744841801048536862257035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4496561200699024574838023 6744841801048536862257035)
  ·
    refine ⟨10117262701572805293385553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744841801048536862257035 10117262701572805293385553)
    ·
      refine ⟨7587947026179603970039165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10117262701572805293385553 7587947026179603970039165)
      ·
        refine ⟨2845480134817351488764687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7587947026179603970039165 2845480134817351488764687)
        ·
          refine ⟨4268220202226027233147031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845480134817351488764687 4268220202226027233147031)
          ·
            refine ⟨6402330303339040849720547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268220202226027233147031 6402330303339040849720547)
            ·
              refine ⟨9603495455008561274580821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402330303339040849720547 9603495455008561274580821)
              ·
                refine ⟨56270481181690788718247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9603495455008561274580821 56270481181690788718247)
                ·
                  rfl

theorem cell19_184927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_184927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184927 prefixEnd_184927 := by exact prefixLift 184927
  have htrace : WordTrace (prefixWord ++ tailWord_184927) baseStart_184927 baseEnd_184927 := by
    simpa [prefixWord, tailWord_184927, baseEnd_184927] using wordTrace_append hprefix tailTrace_184927
  have hstable : (prefixWord ++ tailWord_184927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184927).length < 2 ^ (prefixWord ++ tailWord_184927).sum := by decide
  have hdescent : baseEnd_184927 < baseStart_184927 := by decide
  rcases family_descends (prefixWord ++ tailWord_184927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184944 : List Nat := [2, 1, 1, 1, 7, 1, 6]
def baseStart_184944 : Nat := 118140960795 + 184944 * 2 ^ 59
def prefixEnd_184944 : Nat := 4983230072969 + 3 ^ 40 * 184944 * 2
def baseEnd_184944 : Nat := 18758551341279928780141

theorem tailTrace_184944 : CollatzResearch.WordTrace tailWord_184944 prefixEnd_184944 18758551341279928780141 := by
  unfold tailWord_184944
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372730920993474382812943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4496974561324632510417257 3372730920993474382812943)
  ·
    refine ⟨5059096381490211574219415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372730920993474382812943 5059096381490211574219415)
    ·
      refine ⟨7588644572235317361329123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059096381490211574219415 7588644572235317361329123)
      ·
        refine ⟨11382966858352976041993685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7588644572235317361329123 11382966858352976041993685)
        ·
          refine ⟨266788285742647875984227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11382966858352976041993685 266788285742647875984227)
          ·
            refine ⟨400182428613971813976341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266788285742647875984227 400182428613971813976341)
            ·
              refine ⟨18758551341279928780141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 400182428613971813976341 18758551341279928780141)
              ·
                rfl

theorem cell19_184944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_184944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184944 prefixEnd_184944 := by exact prefixLift 184944
  have htrace : WordTrace (prefixWord ++ tailWord_184944) baseStart_184944 baseEnd_184944 := by
    simpa [prefixWord, tailWord_184944, baseEnd_184944] using wordTrace_append hprefix tailTrace_184944
  have hstable : (prefixWord ++ tailWord_184944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184944).length < 2 ^ (prefixWord ++ tailWord_184944).sum := by decide
  have hdescent : baseEnd_184944 < baseStart_184944 := by decide
  rcases family_descends (prefixWord ++ tailWord_184944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184978 : List Nat := [3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_184978 : Nat := 118140960795 + 184978 * 2 ^ 59
def prefixEnd_184978 : Nat := 4983230072969 + 3 ^ 40 * 184978 * 2
def baseEnd_184978 : Nat := 56285999708137781584775

theorem tailTrace_184978 : CollatzResearch.WordTrace tailWord_184978 prefixEnd_184978 56285999708137781584775 := by
  unfold tailWord_184978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686675480965943143090897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4497801282575848381575725 1686675480965943143090897)
  ·
    refine ⟨1265006610724457357318173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1686675480965943143090897 1265006610724457357318173)
    ·
      refine ⟨474377479021671508994315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1265006610724457357318173 474377479021671508994315)
      ·
        refine ⟨711566218532507263491473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474377479021671508994315 711566218532507263491473)
        ·
          refine ⟨533674663899380447618605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711566218532507263491473 533674663899380447618605)
          ·
            refine ⟨200127998962267667856977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 533674663899380447618605 200127998962267667856977)
            ·
              refine ⟨150095999221700750892733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200127998962267667856977 150095999221700750892733)
              ·
                refine ⟨56285999708137781584775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150095999221700750892733 56285999708137781584775)
                ·
                  rfl

theorem cell19_184978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_184978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184978 prefixEnd_184978 := by exact prefixLift 184978
  have htrace : WordTrace (prefixWord ++ tailWord_184978) baseStart_184978 baseEnd_184978 := by
    simpa [prefixWord, tailWord_184978, baseEnd_184978] using wordTrace_append hprefix tailTrace_184978
  have hstable : (prefixWord ++ tailWord_184978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184978).length < 2 ^ (prefixWord ++ tailWord_184978).sum := by decide
  have hdescent : baseEnd_184978 < baseStart_184978 := by decide
  rcases family_descends (prefixWord ++ tailWord_184978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184980 : List Nat := [2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_184980 : Nat := 118140960795 + 184980 * 2 ^ 59
def prefixEnd_184980 : Nat := 4983230072969 + 3 ^ 40 * 184980 * 2
def baseEnd_184980 : Nat := 56286608277802369540325

theorem tailTrace_184980 : CollatzResearch.WordTrace tailWord_184980 prefixEnd_184980 56286608277802369540325 := by
  unfold tailWord_184980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373387434928263456968197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4497849913237684609290929 3373387434928263456968197)
  ·
    refine ⟨632510144049049398181537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3373387434928263456968197 632510144049049398181537)
    ·
      refine ⟨474382608036787048636153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 632510144049049398181537 474382608036787048636153)
      ·
        refine ⟨355786956027590286477115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474382608036787048636153 355786956027590286477115)
        ·
          refine ⟨533680434041385429715673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355786956027590286477115 533680434041385429715673)
          ·
            refine ⟨400260325531039072286755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533680434041385429715673 400260325531039072286755)
            ·
              refine ⟨600390488296558608430133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400260325531039072286755 600390488296558608430133)
              ·
                refine ⟨56286608277802369540325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600390488296558608430133 56286608277802369540325)
                ·
                  rfl

theorem cell19_184980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_184980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_184980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_184980 prefixEnd_184980 := by exact prefixLift 184980
  have htrace : WordTrace (prefixWord ++ tailWord_184980) baseStart_184980 baseEnd_184980 := by
    simpa [prefixWord, tailWord_184980, baseEnd_184980] using wordTrace_append hprefix tailTrace_184980
  have hstable : (prefixWord ++ tailWord_184980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184980).length < 2 ^ (prefixWord ++ tailWord_184980).sum := by decide
  have hdescent : baseEnd_184980 < baseStart_184980 := by decide
  rcases family_descends (prefixWord ++ tailWord_184980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185020 : List Nat := [2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_185020 : Nat := 118140960795 + 185020 * 2 ^ 59
def prefixEnd_185020 : Nat := 4983230072969 + 3 ^ 40 * 185020 * 2
def baseEnd_185020 : Nat := 56298779671094128651327

theorem tailTrace_185020 : CollatzResearch.WordTrace tailWord_185020 prefixEnd_185020 56298779671094128651327 := by
  unfold tailWord_185020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374116894855806872696257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4498822526474409163595009 3374116894855806872696257)
  ·
    refine ⟨2530587671141855154522193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3374116894855806872696257 2530587671141855154522193)
    ·
      refine ⟨1897940753356391365891645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2530587671141855154522193 1897940753356391365891645)
      ·
        refine ⟨711727782508646762209367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1897940753356391365891645 711727782508646762209367)
        ·
          refine ⟨1067591673762970143314051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711727782508646762209367 1067591673762970143314051)
          ·
            refine ⟨1601387510644455214971077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067591673762970143314051 1601387510644455214971077)
            ·
              refine ⟨300260158245835352807077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1601387510644455214971077 300260158245835352807077)
              ·
                refine ⟨56298779671094128651327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300260158245835352807077 56298779671094128651327)
                ·
                  rfl

theorem cell19_185020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_185020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185020 prefixEnd_185020 := by exact prefixLift 185020
  have htrace : WordTrace (prefixWord ++ tailWord_185020) baseStart_185020 baseEnd_185020 := by
    simpa [prefixWord, tailWord_185020, baseEnd_185020] using wordTrace_append hprefix tailTrace_185020
  have hstable : (prefixWord ++ tailWord_185020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185020).length < 2 ^ (prefixWord ++ tailWord_185020).sum := by decide
  have hdescent : baseEnd_185020 < baseStart_185020 := by decide
  rcases family_descends (prefixWord ++ tailWord_185020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185041 : List Nat := [1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_185041 : Nat := 118140960795 + 185041 * 2 ^ 59
def prefixEnd_185041 : Nat := 4983230072969 + 3 ^ 40 * 185041 * 2
def baseEnd_185041 : Nat := 56305169652572302184603

theorem tailTrace_185041 : CollatzResearch.WordTrace tailWord_185041 prefixEnd_185041 56305169652572302184603 := by
  unfold tailWord_185041
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748999722635534331906977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4499333148423689554604651 6748999722635534331906977)
  ·
    refine ⟨5061749791976650748930233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6748999722635534331906977 5061749791976650748930233)
    ·
      refine ⟨3796312343982488061697675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5061749791976650748930233 3796312343982488061697675)
      ·
        refine ⟨5694468515973732092546513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796312343982488061697675 5694468515973732092546513)
        ·
          refine ⟨4270851386980299069409885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5694468515973732092546513 4270851386980299069409885)
          ·
            refine ⟨1601569270117612151028707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4270851386980299069409885 1601569270117612151028707)
            ·
              refine ⟨2402353905176418226543061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601569270117612151028707 2402353905176418226543061)
              ·
                refine ⟨56305169652572302184603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2402353905176418226543061 56305169652572302184603)
                ·
                  rfl

theorem cell19_185041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_185041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185041 prefixEnd_185041 := by exact prefixLift 185041
  have htrace : WordTrace (prefixWord ++ tailWord_185041) baseStart_185041 baseEnd_185041 := by
    simpa [prefixWord, tailWord_185041, baseEnd_185041] using wordTrace_append hprefix tailTrace_185041
  have hstable : (prefixWord ++ tailWord_185041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185041).length < 2 ^ (prefixWord ++ tailWord_185041).sum := by decide
  have hdescent : baseEnd_185041 < baseStart_185041 := by decide
  rcases family_descends (prefixWord ++ tailWord_185041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185060 : List Nat := [2, 3, 1, 1, 1, 11]
def baseStart_185060 : Nat := 118140960795 + 185060 * 2 ^ 59
def prefixEnd_185060 : Nat := 4983230072969 + 3 ^ 40 * 185060 * 2
def baseEnd_185060 : Nat := 6256772340487320862481

theorem tailTrace_185060 : CollatzResearch.WordTrace tailWord_185060 prefixEnd_185060 6256772340487320862481 := by
  unfold tailWord_185060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374846354783350288424317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4499795139711133717899089 3374846354783350288424317)
  ·
    refine ⟨1265567383043756358159119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3374846354783350288424317 1265567383043756358159119)
    ·
      refine ⟨1898351074565634537238679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1265567383043756358159119 1898351074565634537238679)
      ·
        refine ⟨2847526611848451805858019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898351074565634537238679 2847526611848451805858019)
        ·
          refine ⟨4271289917772677708787029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847526611848451805858019 4271289917772677708787029)
          ·
            refine ⟨6256772340487320862481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4271289917772677708787029 6256772340487320862481)
            ·
              rfl

theorem cell19_185060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_185060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185060 prefixEnd_185060 := by exact prefixLift 185060
  have htrace : WordTrace (prefixWord ++ tailWord_185060) baseStart_185060 baseEnd_185060 := by
    simpa [prefixWord, tailWord_185060, baseEnd_185060] using wordTrace_append hprefix tailTrace_185060
  have hstable : (prefixWord ++ tailWord_185060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185060).length < 2 ^ (prefixWord ++ tailWord_185060).sum := by decide
  have hdescent : baseEnd_185060 < baseStart_185060 := by decide
  rcases family_descends (prefixWord ++ tailWord_185060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185149 : List Nat := [1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_185149 : Nat := 118140960795 + 185149 * 2 ^ 59
def prefixEnd_185149 : Nat := 4983230072969 + 3 ^ 40 * 185149 * 2
def baseEnd_185149 : Nat := 56338032414460051784309

theorem tailTrace_185149 : CollatzResearch.WordTrace tailWord_185149 prefixEnd_185149 56338032414460051784309 := by
  unfold tailWord_185149
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752938806244268776838501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4501959204162845851225667 6752938806244268776838501)
  ·
    refine ⟨1266176026170800395657219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6752938806244268776838501 1266176026170800395657219)
    ·
      refine ⟨1899264039256200593485829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266176026170800395657219 1899264039256200593485829)
      ·
        refine ⟨356112007360537611278593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1899264039256200593485829 356112007360537611278593)
        ·
          refine ⟨267084005520403208458945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356112007360537611278593 267084005520403208458945)
          ·
            refine ⟨200313004140302406344209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267084005520403208458945 200313004140302406344209)
            ·
              refine ⟨150234753105226804758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200313004140302406344209 150234753105226804758157)
              ·
                refine ⟨56338032414460051784309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150234753105226804758157 56338032414460051784309)
                ·
                  rfl

theorem cell19_185149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_185149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185149 prefixEnd_185149 := by exact prefixLift 185149
  have htrace : WordTrace (prefixWord ++ tailWord_185149) baseStart_185149 baseEnd_185149 := by
    simpa [prefixWord, tailWord_185149, baseEnd_185149] using wordTrace_append hprefix tailTrace_185149
  have hstable : (prefixWord ++ tailWord_185149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185149).length < 2 ^ (prefixWord ++ tailWord_185149).sum := by decide
  have hdescent : baseEnd_185149 < baseStart_185149 := by decide
  rcases family_descends (prefixWord ++ tailWord_185149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185151 : List Nat := [1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_185151 : Nat := 118140960795 + 185151 * 2 ^ 59
def prefixEnd_185151 : Nat := 4983230072969 + 3 ^ 40 * 185151 * 2
def baseEnd_185151 : Nat := 56338640984124639739859

theorem tailTrace_185151 : CollatzResearch.WordTrace tailWord_185151 prefixEnd_185151 56338640984124639739859 := by
  unfold tailWord_185151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753011752237023118411307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4502007834824682078940871 6753011752237023118411307)
  ·
    refine ⟨10129517628355534677616961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753011752237023118411307 10129517628355534677616961)
    ·
      refine ⟨7597138221266651008212721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10129517628355534677616961 7597138221266651008212721)
      ·
        refine ⟨5697853665949988256159541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7597138221266651008212721 5697853665949988256159541)
        ·
          refine ⟨534173781182811399014957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5697853665949988256159541 534173781182811399014957)
          ·
            refine ⟨200315167943554274630609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534173781182811399014957 200315167943554274630609)
            ·
              refine ⟨150236375957665705972957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200315167943554274630609 150236375957665705972957)
              ·
                refine ⟨56338640984124639739859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150236375957665705972957 56338640984124639739859)
                ·
                  rfl

theorem cell19_185151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_185151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185151 prefixEnd_185151 := by exact prefixLift 185151
  have htrace : WordTrace (prefixWord ++ tailWord_185151) baseStart_185151 baseEnd_185151 := by
    simpa [prefixWord, tailWord_185151, baseEnd_185151] using wordTrace_append hprefix tailTrace_185151
  have hstable : (prefixWord ++ tailWord_185151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185151).length < 2 ^ (prefixWord ++ tailWord_185151).sum := by decide
  have hdescent : baseEnd_185151 < baseStart_185151 := by decide
  rcases family_descends (prefixWord ++ tailWord_185151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185155 : List Nat := [1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_185155 : Nat := 118140960795 + 185155 * 2 ^ 59
def prefixEnd_185155 : Nat := 4983230072969 + 3 ^ 40 * 185155 * 2
def baseEnd_185155 : Nat := 56339858123453815650959

theorem tailTrace_185155 : CollatzResearch.WordTrace tailWord_185155 prefixEnd_185155 56339858123453815650959 := by
  unfold tailWord_185155
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753157644222531801556919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4502105096148354534371279 6753157644222531801556919)
  ·
    refine ⟨10129736466333797702335379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753157644222531801556919 10129736466333797702335379)
    ·
      refine ⟨15194604699500696553503069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10129736466333797702335379 15194604699500696553503069)
      ·
        refine ⟨5697976762312761207563651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15194604699500696553503069 5697976762312761207563651)
        ·
          refine ⟨8546965143469141811345477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697976762312761207563651 8546965143469141811345477)
          ·
            refine ⟨1602555964400464089627277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8546965143469141811345477 1602555964400464089627277)
            ·
              refine ⟨600958486650174033610229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1602555964400464089627277 600958486650174033610229)
              ·
                refine ⟨56339858123453815650959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600958486650174033610229 56339858123453815650959)
                ·
                  rfl

theorem cell19_185155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_185155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185155 prefixEnd_185155 := by exact prefixLift 185155
  have htrace : WordTrace (prefixWord ++ tailWord_185155) baseStart_185155 baseEnd_185155 := by
    simpa [prefixWord, tailWord_185155, baseEnd_185155] using wordTrace_append hprefix tailTrace_185155
  have hstable : (prefixWord ++ tailWord_185155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185155).length < 2 ^ (prefixWord ++ tailWord_185155).sum := by decide
  have hdescent : baseEnd_185155 < baseStart_185155 := by decide
  rcases family_descends (prefixWord ++ tailWord_185155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185191 : List Nat := [1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_185191 : Nat := 118140960795 + 185191 * 2 ^ 59
def prefixEnd_185191 : Nat := 4983230072969 + 3 ^ 40 * 185191 * 2
def baseEnd_185191 : Nat := 56350812377416398850861

theorem tailTrace_185191 : CollatzResearch.WordTrace tailWord_185191 prefixEnd_185191 56350812377416398850861 := by
  unfold tailWord_185191
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754470672092109949867427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4502980448061406633244951 6754470672092109949867427)
  ·
    refine ⟨10131706008138164924801141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6754470672092109949867427 10131706008138164924801141)
    ·
      refine ⟨949847438262952961700107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10131706008138164924801141 949847438262952961700107)
      ·
        refine ⟨1424771157394429442550161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949847438262952961700107 1424771157394429442550161)
        ·
          refine ⟨1068578368045822081912621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424771157394429442550161 1068578368045822081912621)
          ·
            refine ⟨400716888017183280717233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1068578368045822081912621 400716888017183280717233)
            ·
              refine ⟨300537666012887460537925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400716888017183280717233 300537666012887460537925)
              ·
                refine ⟨56350812377416398850861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300537666012887460537925 56350812377416398850861)
                ·
                  rfl

theorem cell19_185191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_185191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185191 prefixEnd_185191 := by exact prefixLift 185191
  have htrace : WordTrace (prefixWord ++ tailWord_185191) baseStart_185191 baseEnd_185191 := by
    simpa [prefixWord, tailWord_185191, baseEnd_185191] using wordTrace_append hprefix tailTrace_185191
  have hstable : (prefixWord ++ tailWord_185191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185191).length < 2 ^ (prefixWord ++ tailWord_185191).sum := by decide
  have hdescent : baseEnd_185191 < baseStart_185191 := by decide
  rcases family_descends (prefixWord ++ tailWord_185191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185244 : List Nat := [2, 2, 3, 3, 3, 1, 1, 4]
def baseStart_185244 : Nat := 118140960795 + 185244 * 2 ^ 59
def prefixEnd_185244 : Nat := 4983230072969 + 3 ^ 40 * 185244 * 2
def baseEnd_185244 : Nat := 56366939473527979672939

theorem tailTrace_185244 : CollatzResearch.WordTrace tailWord_185244 prefixEnd_185244 56366939473527979672939 := by
  unfold tailWord_185244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378201870450050000773393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4504269160600066667697857 3378201870450050000773393)
  ·
    refine ⟨2533651402837537500580045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3378201870450050000773393 2533651402837537500580045)
    ·
      refine ⟨950119276064076562717517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2533651402837537500580045 950119276064076562717517)
      ·
        refine ⟨356294728524028711019069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 950119276064076562717517 356294728524028711019069)
        ·
          refine ⟨133610523196510766632151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356294728524028711019069 133610523196510766632151)
          ·
            refine ⟨200415784794766149948227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133610523196510766632151 200415784794766149948227)
            ·
              refine ⟨300623677192149224922341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200415784794766149948227 300623677192149224922341)
              ·
                refine ⟨56366939473527979672939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300623677192149224922341 56366939473527979672939)
                ·
                  rfl

theorem cell19_185244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_185244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185244 prefixEnd_185244 := by exact prefixLift 185244
  have htrace : WordTrace (prefixWord ++ tailWord_185244) baseStart_185244 baseEnd_185244 := by
    simpa [prefixWord, tailWord_185244, baseEnd_185244] using wordTrace_append hprefix tailTrace_185244
  have hstable : (prefixWord ++ tailWord_185244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185244).length < 2 ^ (prefixWord ++ tailWord_185244).sum := by decide
  have hdescent : baseEnd_185244 < baseStart_185244 := by decide
  rcases family_descends (prefixWord ++ tailWord_185244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185265 : List Nat := [1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_185265 : Nat := 118140960795 + 185265 * 2 ^ 59
def prefixEnd_185265 : Nat := 4983230072969 + 3 ^ 40 * 185265 * 2
def baseEnd_185265 : Nat := 56373329455006153206215

theorem tailTrace_185265 : CollatzResearch.WordTrace tailWord_185265 prefixEnd_185265 56373329455006153206215 := by
  unfold tailWord_185265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757169673824020588061249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4504779782549347058707499 6757169673824020588061249)
  ·
    refine ⟨5067877255368015441045937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6757169673824020588061249 5067877255368015441045937)
    ·
      refine ⟨3800907941526011580784453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5067877255368015441045937 3800907941526011580784453)
      ·
        refine ⟨712670239036127171397085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3800907941526011580784453 712670239036127171397085)
        ·
          refine ⟨267251339638547689273907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 712670239036127171397085 267251339638547689273907)
          ·
            refine ⟨400877009457821533910861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267251339638547689273907 400877009457821533910861)
            ·
              refine ⟨150328878546683075216573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400877009457821533910861 150328878546683075216573)
              ·
                refine ⟨56373329455006153206215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150328878546683075216573 56373329455006153206215)
                ·
                  rfl

theorem cell19_185265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_185265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185265 prefixEnd_185265 := by exact prefixLift 185265
  have htrace : WordTrace (prefixWord ++ tailWord_185265) baseStart_185265 baseEnd_185265 := by
    simpa [prefixWord, tailWord_185265, baseEnd_185265] using wordTrace_append hprefix tailTrace_185265
  have hstable : (prefixWord ++ tailWord_185265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185265).length < 2 ^ (prefixWord ++ tailWord_185265).sum := by decide
  have hdescent : baseEnd_185265 < baseStart_185265 := by decide
  rcases family_descends (prefixWord ++ tailWord_185265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185284 : List Nat := [2, 3, 3, 3, 1, 1, 6]
def baseStart_185284 : Nat := 118140960795 + 185284 * 2 ^ 59
def prefixEnd_185284 : Nat := 4983230072969 + 3 ^ 40 * 185284 * 2
def baseEnd_185284 : Nat := 18793036955606579594647

theorem tailTrace_185284 : CollatzResearch.WordTrace tailWord_185284 prefixEnd_185284 18793036955606579594647 := by
  unfold tailWord_185284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378931330377593416501453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4505241773836791222001937 3378931330377593416501453)
  ·
    refine ⟨1267099248891597531188045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3378931330377593416501453 1267099248891597531188045)
    ·
      refine ⟨475162218334349074195517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1267099248891597531188045 475162218334349074195517)
      ·
        refine ⟨178185831875380902823319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475162218334349074195517 178185831875380902823319)
        ·
          refine ⟨267278747813071354234979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178185831875380902823319 267278747813071354234979)
          ·
            refine ⟨400918121719607031352469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267278747813071354234979 400918121719607031352469)
            ·
              refine ⟨18793036955606579594647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 400918121719607031352469 18793036955606579594647)
              ·
                rfl

theorem cell19_185284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_185284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185284 prefixEnd_185284 := by exact prefixLift 185284
  have htrace : WordTrace (prefixWord ++ tailWord_185284) baseStart_185284 baseEnd_185284 := by
    simpa [prefixWord, tailWord_185284, baseEnd_185284] using wordTrace_append hprefix tailTrace_185284
  have hstable : (prefixWord ++ tailWord_185284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185284).length < 2 ^ (prefixWord ++ tailWord_185284).sum := by decide
  have hdescent : baseEnd_185284 < baseStart_185284 := by decide
  rcases family_descends (prefixWord ++ tailWord_185284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185322 : List Nat := [3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_185322 : Nat := 118140960795 + 185322 * 2 ^ 59
def prefixEnd_185322 : Nat := 4983230072969 + 3 ^ 40 * 185322 * 2
def baseEnd_185322 : Nat := 56390673690446909939393

theorem tailTrace_185322 : CollatzResearch.WordTrace tailWord_185322 prefixEnd_185322 56390673690446909939393 := by
  unfold tailWord_185322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689812158654379830721555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4506165756411679548590813 1689812158654379830721555)
  ·
    refine ⟨2534718237981569746082333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689812158654379830721555 2534718237981569746082333)
    ·
      refine ⟨950519339243088654780875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2534718237981569746082333 950519339243088654780875)
      ·
        refine ⟨1425779008864632982171313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950519339243088654780875 1425779008864632982171313)
        ·
          refine ⟨1069334256648474736628485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425779008864632982171313 1069334256648474736628485)
          ·
            refine ⟨200500173121589013117841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1069334256648474736628485 200500173121589013117841)
            ·
              refine ⟨150375129841191759838381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200500173121589013117841 150375129841191759838381)
              ·
                refine ⟨56390673690446909939393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150375129841191759838381 56390673690446909939393)
                ·
                  rfl

theorem cell19_185322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_185322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185322 prefixEnd_185322 := by exact prefixLift 185322
  have htrace : WordTrace (prefixWord ++ tailWord_185322) baseStart_185322 baseEnd_185322 := by
    simpa [prefixWord, tailWord_185322, baseEnd_185322] using wordTrace_append hprefix tailTrace_185322
  have hstable : (prefixWord ++ tailWord_185322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185322).length < 2 ^ (prefixWord ++ tailWord_185322).sum := by decide
  have hdescent : baseEnd_185322 < baseStart_185322 := by decide
  rcases family_descends (prefixWord ++ tailWord_185322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185345 : List Nat := [1, 2, 4, 1, 2, 2, 7]
def baseStart_185345 : Nat := 118140960795 + 185345 * 2 ^ 59
def prefixEnd_185345 : Nat := 4983230072969 + 3 ^ 40 * 185345 * 2
def baseEnd_185345 : Nat := 18799224080529890476073

theorem tailTrace_185345 : CollatzResearch.WordTrace tailWord_185345 prefixEnd_185345 18799224080529890476073 := by
  unfold tailWord_185345
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760087513534194250973489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4506725009022796167315659 6760087513534194250973489)
  ·
    refine ⟨5070065635150645688230117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6760087513534194250973489 5070065635150645688230117)
    ·
      refine ⟨950637306590746066543147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5070065635150645688230117 950637306590746066543147)
      ·
        refine ⟨1425955959886119099814721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950637306590746066543147 1425955959886119099814721)
        ·
          refine ⟨1069466969914589324861041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425955959886119099814721 1069466969914589324861041)
          ·
            refine ⟨802100227435941993645781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069466969914589324861041 802100227435941993645781)
            ·
              refine ⟨18799224080529890476073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 802100227435941993645781 18799224080529890476073)
              ·
                rfl

theorem cell19_185345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_185345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185345 prefixEnd_185345 := by exact prefixLift 185345
  have htrace : WordTrace (prefixWord ++ tailWord_185345) baseStart_185345 baseEnd_185345 := by
    simpa [prefixWord, tailWord_185345, baseEnd_185345] using wordTrace_append hprefix tailTrace_185345
  have hstable : (prefixWord ++ tailWord_185345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185345).length < 2 ^ (prefixWord ++ tailWord_185345).sum := by decide
  have hdescent : baseEnd_185345 < baseStart_185345 := by decide
  rcases family_descends (prefixWord ++ tailWord_185345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185495 : List Nat := [1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_185495 : Nat := 118140960795 + 185495 * 2 ^ 59
def prefixEnd_185495 : Nat := 4983230072969 + 3 ^ 40 * 185495 * 2
def baseEnd_185495 : Nat := 56443314966433768094477

theorem tailTrace_185495 : CollatzResearch.WordTrace tailWord_185495 prefixEnd_185495 56443314966433768094477 := by
  unfold tailWord_185495
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765558462990769868933939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4510372308660513245955959 6765558462990769868933939)
  ·
    refine ⟨10148337694486154803400909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6765558462990769868933939 10148337694486154803400909)
    ·
      refine ⟨3805626635432308051275341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10148337694486154803400909 3805626635432308051275341)
      ·
        refine ⟨1427109988287115519228253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3805626635432308051275341 1427109988287115519228253)
        ·
          refine ⟨535166245607668319710595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1427109988287115519228253 535166245607668319710595)
          ·
            refine ⟨802749368411502479565893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535166245607668319710595 802749368411502479565893)
            ·
              refine ⟨150515506577156714918605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 802749368411502479565893 150515506577156714918605)
              ·
                refine ⟨56443314966433768094477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150515506577156714918605 56443314966433768094477)
                ·
                  rfl

theorem cell19_185495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_185495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185495 prefixEnd_185495 := by exact prefixLift 185495
  have htrace : WordTrace (prefixWord ++ tailWord_185495) baseStart_185495 baseEnd_185495 := by
    simpa [prefixWord, tailWord_185495, baseEnd_185495] using wordTrace_append hprefix tailTrace_185495
  have hstable : (prefixWord ++ tailWord_185495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185495).length < 2 ^ (prefixWord ++ tailWord_185495).sum := by decide
  have hdescent : baseEnd_185495 < baseStart_185495 := by decide
  rcases family_descends (prefixWord ++ tailWord_185495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185514 : List Nat := [3, 1, 5, 1, 1, 1, 7]
def baseStart_185514 : Nat := 118140960795 + 185514 * 2 ^ 59
def prefixEnd_185514 : Nat := 4983230072969 + 3 ^ 40 * 185514 * 2
def baseEnd_185514 : Nat := 18816365459415784557401

theorem tailTrace_185514 : CollatzResearch.WordTrace tailWord_185514 prefixEnd_185514 18816365459415784557401 := by
  unfold tailWord_185514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691562862480484028468899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4510834299947957409250397 1691562862480484028468899)
  ·
    refine ⟨2537344293720726042703349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1691562862480484028468899 2537344293720726042703349)
    ·
      refine ⟨237876027536318066503439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2537344293720726042703349 237876027536318066503439)
      ·
        refine ⟨356814041304477099755159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237876027536318066503439 356814041304477099755159)
        ·
          refine ⟨535221061956715649632739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356814041304477099755159 535221061956715649632739)
          ·
            refine ⟨802831592935073474449109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535221061956715649632739 802831592935073474449109)
            ·
              refine ⟨18816365459415784557401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 802831592935073474449109 18816365459415784557401)
              ·
                rfl

theorem cell19_185514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_185514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185514 prefixEnd_185514 := by exact prefixLift 185514
  have htrace : WordTrace (prefixWord ++ tailWord_185514) baseStart_185514 baseEnd_185514 := by
    simpa [prefixWord, tailWord_185514, baseEnd_185514] using wordTrace_append hprefix tailTrace_185514
  have hstable : (prefixWord ++ tailWord_185514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185514).length < 2 ^ (prefixWord ++ tailWord_185514).sum := by decide
  have hdescent : baseEnd_185514 < baseStart_185514 := by decide
  rcases family_descends (prefixWord ++ tailWord_185514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185554 : List Nat := [3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_185554 : Nat := 118140960795 + 185554 * 2 ^ 59
def prefixEnd_185554 : Nat := 4983230072969 + 3 ^ 40 * 185554 * 2
def baseEnd_185554 : Nat := 56461267771539112783205

theorem tailTrace_185554 : CollatzResearch.WordTrace tailWord_185554 prefixEnd_185554 56461267771539112783205 := by
  unfold tailWord_185554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691927592444255736332929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4511806913184681963554477 1691927592444255736332929)
  ·
    refine ⟨1268945694333191802249697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1691927592444255736332929 1268945694333191802249697)
    ·
      refine ⟨951709270749893851687273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1268945694333191802249697 951709270749893851687273)
      ·
        refine ⟨713781953062420388765455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951709270749893851687273 713781953062420388765455)
        ·
          refine ⟨1070672929593630583148183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713781953062420388765455 1070672929593630583148183)
          ·
            refine ⟨1606009394390445874722275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070672929593630583148183 1606009394390445874722275)
            ·
              refine ⟨2409014091585668812083413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606009394390445874722275 2409014091585668812083413)
              ·
                refine ⟨56461267771539112783205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2409014091585668812083413 56461267771539112783205)
                ·
                  rfl

theorem cell19_185554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_185554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185554 prefixEnd_185554 := by exact prefixLift 185554
  have htrace : WordTrace (prefixWord ++ tailWord_185554) baseStart_185554 baseEnd_185554 := by
    simpa [prefixWord, tailWord_185554, baseEnd_185554] using wordTrace_append hprefix tailTrace_185554
  have hstable : (prefixWord ++ tailWord_185554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185554).length < 2 ^ (prefixWord ++ tailWord_185554).sum := by decide
  have hdescent : baseEnd_185554 < baseStart_185554 := by decide
  rcases family_descends (prefixWord ++ tailWord_185554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185573 : List Nat := [1, 3, 1, 4, 3, 7]
def baseStart_185573 : Nat := 118140960795 + 185573 * 2 ^ 59
def prefixEnd_185573 : Nat := 4983230072969 + 3 ^ 40 * 185573 * 2
def baseEnd_185573 : Nat := 6274116575928077595659

theorem tailTrace_185573 : CollatzResearch.WordTrace tailWord_185573 prefixEnd_185573 6274116575928077595659 := by
  unfold tailWord_185573
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768403356708189190273373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4512268904472126126848915 6768403356708189190273373)
  ·
    refine ⟨2538151258765570946352515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6768403356708189190273373 2538151258765570946352515)
    ·
      refine ⟨3807226888148356419528773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538151258765570946352515 3807226888148356419528773)
      ·
        refine ⟨713855041527816828661645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3807226888148356419528773 713855041527816828661645)
        ·
          refine ⟨267695640572931310748117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 713855041527816828661645 267695640572931310748117)
          ·
            refine ⟨6274116575928077595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 267695640572931310748117 6274116575928077595659)
            ·
              rfl

theorem cell19_185573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_185573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185573 prefixEnd_185573 := by exact prefixLift 185573
  have htrace : WordTrace (prefixWord ++ tailWord_185573) baseStart_185573 baseEnd_185573 := by
    simpa [prefixWord, tailWord_185573, baseEnd_185573] using wordTrace_append hprefix tailTrace_185573
  have hstable : (prefixWord ++ tailWord_185573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185573).length < 2 ^ (prefixWord ++ tailWord_185573).sum := by decide
  have hdescent : baseEnd_185573 < baseStart_185573 := by decide
  rcases family_descends (prefixWord ++ tailWord_185573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185687 : List Nat := [1, 1, 3, 2, 3, 4, 5]
def baseStart_185687 : Nat := 118140960795 + 185687 * 2 ^ 59
def prefixEnd_185687 : Nat := 4983230072969 + 3 ^ 40 * 185687 * 2
def baseEnd_185687 : Nat := 18833912551411403942429

theorem tailTrace_185687 : CollatzResearch.WordTrace tailWord_185687 prefixEnd_185687 18833912551411403942429 := by
  unfold tailWord_185687
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772561278295186659923315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4515040852196791106615543 6772561278295186659923315)
  ·
    refine ⟨10158841917442779989884973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6772561278295186659923315 10158841917442779989884973)
    ·
      refine ⟨3809565719041042496206865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10158841917442779989884973 3809565719041042496206865)
      ·
        refine ⟨2857174289280781872155149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3809565719041042496206865 2857174289280781872155149)
        ·
          refine ⟨1071440358480293202058181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2857174289280781872155149 1071440358480293202058181)
          ·
            refine ⟨200895067215054975385909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1071440358480293202058181 200895067215054975385909)
            ·
              refine ⟨18833912551411403942429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200895067215054975385909 18833912551411403942429)
              ·
                rfl

theorem cell19_185687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_185687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185687 prefixEnd_185687 := by exact prefixLift 185687
  have htrace : WordTrace (prefixWord ++ tailWord_185687) baseStart_185687 baseEnd_185687 := by
    simpa [prefixWord, tailWord_185687, baseEnd_185687] using wordTrace_append hprefix tailTrace_185687
  have hstable : (prefixWord ++ tailWord_185687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185687).length < 2 ^ (prefixWord ++ tailWord_185687).sum := by decide
  have hdescent : baseEnd_185687 < baseStart_185687 := by decide
  rcases family_descends (prefixWord ++ tailWord_185687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185689 : List Nat := [1, 2, 1, 2, 2, 2, 9]
def baseStart_185689 : Nat := 118140960795 + 185689 * 2 ^ 59
def prefixEnd_185689 : Nat := 4983230072969 + 3 ^ 40 * 185689 * 2
def baseEnd_185689 : Nat := 18834115407966266594279

theorem tailTrace_185689 : CollatzResearch.WordTrace tailWord_185689 prefixEnd_185689 18834115407966266594279 := by
  unfold tailWord_185689
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772634224287941001496121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4515089482858627334330747 6772634224287941001496121)
  ·
    refine ⟨5079475668215955751122091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6772634224287941001496121 5079475668215955751122091)
    ·
      refine ⟨7619213502323933626683137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5079475668215955751122091 7619213502323933626683137)
      ·
        refine ⟨5714410126742950220012353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7619213502323933626683137 5714410126742950220012353)
        ·
          refine ⟨4285807595057212665009265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5714410126742950220012353 4285807595057212665009265)
          ·
            refine ⟨3214355696292909498756949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285807595057212665009265 3214355696292909498756949)
            ·
              refine ⟨18834115407966266594279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3214355696292909498756949 18834115407966266594279)
              ·
                rfl

theorem cell19_185689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_185689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185689 prefixEnd_185689 := by exact prefixLift 185689
  have htrace : WordTrace (prefixWord ++ tailWord_185689) baseStart_185689 baseEnd_185689 := by
    simpa [prefixWord, tailWord_185689, baseEnd_185689] using wordTrace_append hprefix tailTrace_185689
  have hstable : (prefixWord ++ tailWord_185689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185689).length < 2 ^ (prefixWord ++ tailWord_185689).sum := by decide
  have hdescent : baseEnd_185689 < baseStart_185689 := by decide
  rcases family_descends (prefixWord ++ tailWord_185689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185704 : List Nat := [2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_185704 : Nat := 118140960795 + 185704 * 2 ^ 59
def prefixEnd_185704 : Nat := 4983230072969 + 3 ^ 40 * 185704 * 2
def baseEnd_185704 : Nat := 56506910496383209449463

theorem tailTrace_185704 : CollatzResearch.WordTrace tailWord_185704 prefixEnd_185704 56506910496383209449463 := by
  unfold tailWord_185704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3386590659616799281646083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4515454212822399042194777 3386590659616799281646083)
  ·
    refine ⟨5079885989425198922469125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3386590659616799281646083 5079885989425198922469125)
    ·
      refine ⟨952478623017224797962961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5079885989425198922469125 952478623017224797962961)
      ·
        refine ⟨714358967262918598472221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 952478623017224797962961 714358967262918598472221)
        ·
          refine ⟨267884612723594474427083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 714358967262918598472221 267884612723594474427083)
          ·
            refine ⟨401826919085391711640625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267884612723594474427083 401826919085391711640625)
            ·
              refine ⟨301370189314043783730469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401826919085391711640625 301370189314043783730469)
              ·
                refine ⟨56506910496383209449463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301370189314043783730469 56506910496383209449463)
                ·
                  rfl

theorem cell19_185704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_185704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185704 prefixEnd_185704 := by exact prefixLift 185704
  have htrace : WordTrace (prefixWord ++ tailWord_185704) baseStart_185704 baseEnd_185704 := by
    simpa [prefixWord, tailWord_185704, baseEnd_185704] using wordTrace_append hprefix tailTrace_185704
  have hstable : (prefixWord ++ tailWord_185704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185704).length < 2 ^ (prefixWord ++ tailWord_185704).sum := by decide
  have hdescent : baseEnd_185704 < baseStart_185704 := by decide
  rcases family_descends (prefixWord ++ tailWord_185704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185742 : List Nat := [4, 1, 1, 4, 3, 6]
def baseStart_185742 : Nat := 118140960795 + 185742 * 2 ^ 59
def prefixEnd_185742 : Nat := 4983230072969 + 3 ^ 40 * 185742 * 2
def baseEnd_185742 : Nat := 6279830368890042289435

theorem tailTrace_185742 : CollatzResearch.WordTrace tailWord_185742 prefixEnd_185742 6279830368890042289435 := by
  unfold tailWord_185742
  simp only [CollatzResearch.WordTrace]
  refine ⟨846820911636991381646935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4516378195397287368783653 846820911636991381646935)
  ·
    refine ⟨1270231367455487072470403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 846820911636991381646935 1270231367455487072470403)
    ·
      refine ⟨1905347051183230608705605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270231367455487072470403 1905347051183230608705605)
      ·
        refine ⟨357252572096855739132301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1905347051183230608705605 357252572096855739132301)
        ·
          refine ⟨133969714536320902174613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357252572096855739132301 133969714536320902174613)
          ·
            refine ⟨6279830368890042289435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133969714536320902174613 6279830368890042289435)
            ·
              rfl

theorem cell19_185742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_185742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185742 prefixEnd_185742 := by exact prefixLift 185742
  have htrace : WordTrace (prefixWord ++ tailWord_185742) baseStart_185742 baseEnd_185742 := by
    simpa [prefixWord, tailWord_185742, baseEnd_185742] using wordTrace_append hprefix tailTrace_185742
  have hstable : (prefixWord ++ tailWord_185742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185742).length < 2 ^ (prefixWord ++ tailWord_185742).sum := by decide
  have hdescent : baseEnd_185742 < baseStart_185742 := by decide
  rcases family_descends (prefixWord ++ tailWord_185742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185765 : List Nat := [1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_185765 : Nat := 118140960795 + 185765 * 2 ^ 59
def prefixEnd_185765 : Nat := 4983230072969 + 3 ^ 40 * 185765 * 2
def baseEnd_185765 : Nat := 56525471871153142093741

theorem tailTrace_185765 : CollatzResearch.WordTrace tailWord_185765 prefixEnd_185765 56525471871153142093741 := by
  unfold tailWord_185765
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775406172012605981262749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4516937448008403987508499 6775406172012605981262749)
  ·
    refine ⟨2540777314504727242973531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6775406172012605981262749 2540777314504727242973531)
    ·
      refine ⟨3811165971757090864460297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2540777314504727242973531 3811165971757090864460297)
      ·
        refine ⟨2858374478817818148345223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3811165971757090864460297 2858374478817818148345223)
        ·
          refine ⟨4287561718226727222517835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858374478817818148345223 4287561718226727222517835)
          ·
            refine ⟨6431342577340090833776753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287561718226727222517835 6431342577340090833776753)
            ·
              refine ⟨4823506933005068125332565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6431342577340090833776753 4823506933005068125332565)
              ·
                refine ⟨56525471871153142093741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4823506933005068125332565 56525471871153142093741)
                ·
                  rfl

theorem cell19_185765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_185765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185765 prefixEnd_185765 := by exact prefixLift 185765
  have htrace : WordTrace (prefixWord ++ tailWord_185765) baseStart_185765 baseEnd_185765 := by
    simpa [prefixWord, tailWord_185765, baseEnd_185765] using wordTrace_append hprefix tailTrace_185765
  have hstable : (prefixWord ++ tailWord_185765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185765).length < 2 ^ (prefixWord ++ tailWord_185765).sum := by decide
  have hdescent : baseEnd_185765 < baseStart_185765 := by decide
  rcases family_descends (prefixWord ++ tailWord_185765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185784 : List Nat := [2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_185784 : Nat := 118140960795 + 185784 * 2 ^ 59
def prefixEnd_185784 : Nat := 4983230072969 + 3 ^ 40 * 185784 * 2
def baseEnd_185784 : Nat := 56531253282966727671467

theorem tailTrace_185784 : CollatzResearch.WordTrace tailWord_185784 prefixEnd_185784 56531253282966727671467 := by
  unfold tailWord_185784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388049579471886113102203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4517399439295848150802937 3388049579471886113102203)
  ·
    refine ⟨5082074369207829169653305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3388049579471886113102203 5082074369207829169653305)
    ·
      refine ⟨3811555776905871877239979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5082074369207829169653305 3811555776905871877239979)
      ·
        refine ⟨5717333665358807815859969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3811555776905871877239979 5717333665358807815859969)
        ·
          refine ⟨4288000249019105861894977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5717333665358807815859969 4288000249019105861894977)
          ·
            refine ⟨3216000186764329396421233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4288000249019105861894977 3216000186764329396421233)
            ·
              refine ⟨2412000140073247047315925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216000186764329396421233 2412000140073247047315925)
              ·
                refine ⟨56531253282966727671467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2412000140073247047315925 56531253282966727671467)
                ·
                  rfl

theorem cell19_185784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_185784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185784 prefixEnd_185784 := by exact prefixLift 185784
  have htrace : WordTrace (prefixWord ++ tailWord_185784) baseStart_185784 baseEnd_185784 := by
    simpa [prefixWord, tailWord_185784, baseEnd_185784] using wordTrace_append hprefix tailTrace_185784
  have hstable : (prefixWord ++ tailWord_185784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185784).length < 2 ^ (prefixWord ++ tailWord_185784).sum := by decide
  have hdescent : baseEnd_185784 < baseStart_185784 := by decide
  rcases family_descends (prefixWord ++ tailWord_185784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185837 : List Nat := [1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_185837 : Nat := 118140960795 + 185837 * 2 ^ 59
def prefixEnd_185837 : Nat := 4983230072969 + 3 ^ 40 * 185837 * 2
def baseEnd_185837 : Nat := 56547380379078308493545

theorem tailTrace_185837 : CollatzResearch.WordTrace tailWord_185837 prefixEnd_185837 56547380379078308493545 := by
  unfold tailWord_185837
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778032227751762277883765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4518688151834508185255843 6778032227751762277883765)
  ·
    refine ⟨635440521351727713551603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6778032227751762277883765 635440521351727713551603)
    ·
      refine ⟨953160782027591570327405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635440521351727713551603 953160782027591570327405)
      ·
        refine ⟨357435293260346838872777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 953160782027591570327405 357435293260346838872777)
        ·
          refine ⟨268076469945260129154583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357435293260346838872777 268076469945260129154583)
          ·
            refine ⟨402114704917890193731875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268076469945260129154583 402114704917890193731875)
            ·
              refine ⟨603172057376835290597813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402114704917890193731875 603172057376835290597813)
              ·
                refine ⟨56547380379078308493545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603172057376835290597813 56547380379078308493545)
                ·
                  rfl

theorem cell19_185837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_185837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185837 prefixEnd_185837 := by exact prefixLift 185837
  have htrace : WordTrace (prefixWord ++ tailWord_185837) baseStart_185837 baseEnd_185837 := by
    simpa [prefixWord, tailWord_185837, baseEnd_185837] using wordTrace_append hprefix tailTrace_185837
  have hstable : (prefixWord ++ tailWord_185837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185837).length < 2 ^ (prefixWord ++ tailWord_185837).sum := by decide
  have hdescent : baseEnd_185837 < baseStart_185837 := by decide
  rcases family_descends (prefixWord ++ tailWord_185837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185839 : List Nat := [1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_185839 : Nat := 118140960795 + 185839 * 2 ^ 59
def prefixEnd_185839 : Nat := 4983230072969 + 3 ^ 40 * 185839 * 2
def baseEnd_185839 : Nat := 56547988948742896449095

theorem tailTrace_185839 : CollatzResearch.WordTrace tailWord_185839 prefixEnd_185839 56547988948742896449095 := by
  unfold tailWord_185839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778105173744516619456571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4518736782496344412971047 6778105173744516619456571)
  ·
    refine ⟨10167157760616774929184857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6778105173744516619456571 10167157760616774929184857)
    ·
      refine ⟨7625368320462581196888643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10167157760616774929184857 7625368320462581196888643)
      ·
        refine ⟨11438052480693871795332965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7625368320462581196888643 11438052480693871795332965)
        ·
          refine ⟨2144634840130100961624931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11438052480693871795332965 2144634840130100961624931)
          ·
            refine ⟨3216952260195151442437397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144634840130100961624931 3216952260195151442437397)
            ·
              refine ⟨150794637196647723864253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3216952260195151442437397 150794637196647723864253)
              ·
                refine ⟨56547988948742896449095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150794637196647723864253 56547988948742896449095)
                ·
                  rfl

theorem cell19_185839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_185839 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185839 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185839 prefixEnd_185839 := by exact prefixLift 185839
  have htrace : WordTrace (prefixWord ++ tailWord_185839) baseStart_185839 baseEnd_185839 := by
    simpa [prefixWord, tailWord_185839, baseEnd_185839] using wordTrace_append hprefix tailTrace_185839
  have hstable : (prefixWord ++ tailWord_185839).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185839).length < 2 ^ (prefixWord ++ tailWord_185839).sum := by decide
  have hdescent : baseEnd_185839 < baseStart_185839 := by decide
  rcases family_descends (prefixWord ++ tailWord_185839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185854 : List Nat := [4, 2, 2, 3, 1, 2, 5]
def baseStart_185854 : Nat := 118140960795 + 185854 * 2 ^ 59
def prefixEnd_185854 : Nat := 4983230072969 + 3 ^ 40 * 185854 * 2
def baseEnd_185854 : Nat := 18850851073742435371907

theorem tailTrace_185854 : CollatzResearch.WordTrace tailWord_185854 prefixEnd_185854 18850851073742435371907 := by
  unfold tailWord_185854
  simp only [CollatzResearch.WordTrace]
  refine ⟨847331533586271772656577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4519101512460116120835077 847331533586271772656577)
  ·
    refine ⟨635498650189703829492433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 847331533586271772656577 635498650189703829492433)
    ·
      refine ⟨476623987642277872119325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 635498650189703829492433 476623987642277872119325)
      ·
        refine ⟨178733995365854202044747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476623987642277872119325 178733995365854202044747)
        ·
          refine ⟨268100993048781303067121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178733995365854202044747 268100993048781303067121)
          ·
            refine ⟨201075744786585977300341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268100993048781303067121 201075744786585977300341)
            ·
              refine ⟨18850851073742435371907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201075744786585977300341 18850851073742435371907)
              ·
                rfl

theorem cell19_185854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_185854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185854 prefixEnd_185854 := by exact prefixLift 185854
  have htrace : WordTrace (prefixWord ++ tailWord_185854) baseStart_185854 baseEnd_185854 := by
    simpa [prefixWord, tailWord_185854, baseEnd_185854] using wordTrace_append hprefix tailTrace_185854
  have hstable : (prefixWord ++ tailWord_185854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185854).length < 2 ^ (prefixWord ++ tailWord_185854).sum := by decide
  have hdescent : baseEnd_185854 < baseStart_185854 := by decide
  rcases family_descends (prefixWord ++ tailWord_185854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185877 : List Nat := [1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_185877 : Nat := 118140960795 + 185877 * 2 ^ 59
def prefixEnd_185877 : Nat := 4983230072969 + 3 ^ 40 * 185877 * 2
def baseEnd_185877 : Nat := 56559551772370067604547

theorem tailTrace_185877 : CollatzResearch.WordTrace tailWord_185877 prefixEnd_185877 56559551772370067604547 := by
  unfold tailWord_185877
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779491147606849109339885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4519660765071232739559923 6779491147606849109339885)
  ·
    refine ⟨2542309180352568416002457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6779491147606849109339885 2542309180352568416002457)
    ·
      refine ⟨1906731885264426312001843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542309180352568416002457 1906731885264426312001843)
      ·
        refine ⟨2860097827896639468002765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906731885264426312001843 2860097827896639468002765)
        ·
          refine ⟨1072536685461239800501037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2860097827896639468002765 1072536685461239800501037)
          ·
            refine ⟨402201257047964925187889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1072536685461239800501037 402201257047964925187889)
            ·
              refine ⟨301650942785973693890917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402201257047964925187889 301650942785973693890917)
              ·
                refine ⟨56559551772370067604547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301650942785973693890917 56559551772370067604547)
                ·
                  rfl

theorem cell19_185877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_185877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185877 prefixEnd_185877 := by exact prefixLift 185877
  have htrace : WordTrace (prefixWord ++ tailWord_185877) baseStart_185877 baseEnd_185877 := by
    simpa [prefixWord, tailWord_185877, baseEnd_185877] using wordTrace_append hprefix tailTrace_185877
  have hstable : (prefixWord ++ tailWord_185877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185877).length < 2 ^ (prefixWord ++ tailWord_185877).sum := by decide
  have hdescent : baseEnd_185877 < baseStart_185877 := by decide
  rcases family_descends (prefixWord ++ tailWord_185877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185917 : List Nat := [1, 4, 1, 3, 10]
def baseStart_185917 : Nat := 118140960795 + 185917 * 2 ^ 59
def prefixEnd_185917 : Nat := 4983230072969 + 3 ^ 40 * 185917 * 2
def baseEnd_185917 : Nat := 2095249006135623211687

theorem tailTrace_185917 : CollatzResearch.WordTrace tailWord_185917 prefixEnd_185917 2095249006135623211687 := by
  unfold tailWord_185917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780950067461935940796005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4520633378307957293864003 6780950067461935940796005)
  ·
    refine ⟨1271428137649112988899251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6780950067461935940796005 1271428137649112988899251)
    ·
      refine ⟨1907142206473669483348877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271428137649112988899251 1907142206473669483348877)
      ·
        refine ⟨715178327427626056255829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1907142206473669483348877 715178327427626056255829)
        ·
          refine ⟨2095249006135623211687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 715178327427626056255829 2095249006135623211687)
          ·
            rfl

theorem cell19_185917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 10].length) (baseStart_185917 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185917 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185917 prefixEnd_185917 := by exact prefixLift 185917
  have htrace : WordTrace (prefixWord ++ tailWord_185917) baseStart_185917 baseEnd_185917 := by
    simpa [prefixWord, tailWord_185917, baseEnd_185917] using wordTrace_append hprefix tailTrace_185917
  have hstable : (prefixWord ++ tailWord_185917).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185917).length < 2 ^ (prefixWord ++ tailWord_185917).sum := by decide
  have hdescent : baseEnd_185917 < baseStart_185917 := by decide
  rcases family_descends (prefixWord ++ tailWord_185917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185953 : List Nat := [1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_185953 : Nat := 118140960795 + 185953 * 2 ^ 59
def prefixEnd_185953 : Nat := 4983230072969 + 3 ^ 40 * 185953 * 2
def baseEnd_185953 : Nat := 56582677419624409915451

theorem tailTrace_185953 : CollatzResearch.WordTrace tailWord_185953 prefixEnd_185953 56582677419624409915451 := by
  unfold tailWord_185953
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782263095331514089106513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4521508730221009392737675 6782263095331514089106513)
  ·
    refine ⟨5086697321498635566829885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6782263095331514089106513 5086697321498635566829885)
    ·
      refine ⟨1907511495561988337561207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5086697321498635566829885 1907511495561988337561207)
      ·
        refine ⟨2861267243342982506341811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907511495561988337561207 2861267243342982506341811)
        ·
          refine ⟨4291900865014473759512717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861267243342982506341811 4291900865014473759512717)
          ·
            refine ⟨1609462824380427659817269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4291900865014473759512717 1609462824380427659817269)
            ·
              refine ⟨150887139785665093107869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1609462824380427659817269 150887139785665093107869)
              ·
                refine ⟨56582677419624409915451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150887139785665093107869 56582677419624409915451)
                ·
                  rfl

theorem cell19_185953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_185953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_185953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_185953 prefixEnd_185953 := by exact prefixLift 185953
  have htrace : WordTrace (prefixWord ++ tailWord_185953) baseStart_185953 baseEnd_185953 := by
    simpa [prefixWord, tailWord_185953, baseEnd_185953] using wordTrace_append hprefix tailTrace_185953
  have hstable : (prefixWord ++ tailWord_185953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185953).length < 2 ^ (prefixWord ++ tailWord_185953).sum := by decide
  have hdescent : baseEnd_185953 < baseStart_185953 := by decide
  rcases family_descends (prefixWord ++ tailWord_185953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186004 : List Nat := [2, 4, 2, 2, 3, 1, 2, 3]
def baseStart_186004 : Nat := 118140960795 + 186004 * 2 ^ 59
def prefixEnd_186004 : Nat := 4983230072969 + 3 ^ 40 * 186004 * 2
def baseEnd_186004 : Nat := 56598195946071402781979

theorem tailTrace_186004 : CollatzResearch.WordTrace tailWord_186004 prefixEnd_186004 56598195946071402781979 := by
  unfold tailWord_186004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392061609073374899606533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4522748812097833199475377 3392061609073374899606533)
  ·
    refine ⟨636011551701257793676225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3392061609073374899606533 636011551701257793676225)
    ·
      refine ⟨477008663775943345257169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636011551701257793676225 477008663775943345257169)
      ·
        refine ⟨357756497831957508942877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477008663775943345257169 357756497831957508942877)
        ·
          refine ⟨134158686686984065853579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357756497831957508942877 134158686686984065853579)
          ·
            refine ⟨201238030030476098780369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134158686686984065853579 201238030030476098780369)
            ·
              refine ⟨150928522522857074085277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201238030030476098780369 150928522522857074085277)
              ·
                refine ⟨56598195946071402781979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150928522522857074085277 56598195946071402781979)
                ·
                  rfl

theorem cell19_186004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_186004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186004 prefixEnd_186004 := by exact prefixLift 186004
  have htrace : WordTrace (prefixWord ++ tailWord_186004) baseStart_186004 baseEnd_186004 := by
    simpa [prefixWord, tailWord_186004, baseEnd_186004] using wordTrace_append hprefix tailTrace_186004
  have hstable : (prefixWord ++ tailWord_186004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186004).length < 2 ^ (prefixWord ++ tailWord_186004).sum := by decide
  have hdescent : baseEnd_186004 < baseStart_186004 := by decide
  rcases family_descends (prefixWord ++ tailWord_186004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186008 : List Nat := [2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_186008 : Nat := 118140960795 + 186008 * 2 ^ 59
def prefixEnd_186008 : Nat := 4983230072969 + 3 ^ 40 * 186008 * 2
def baseEnd_186008 : Nat := 56599413085400578693079

theorem tailTrace_186008 : CollatzResearch.WordTrace tailWord_186008 prefixEnd_186008 56599413085400578693079 := by
  unfold tailWord_186008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392134555066129241179339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4522846073421505654905785 3392134555066129241179339)
  ·
    refine ⟨5088201832599193861769009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392134555066129241179339 5088201832599193861769009)
    ·
      refine ⟨3816151374449395396326757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5088201832599193861769009 3816151374449395396326757)
      ·
        refine ⟨715528382709261636811267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3816151374449395396326757 715528382709261636811267)
        ·
          refine ⟨1073292574063892455216901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715528382709261636811267 1073292574063892455216901)
          ·
            refine ⟨201242357636979835353169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1073292574063892455216901 201242357636979835353169)
            ·
              refine ⟨150931768227734876514877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201242357636979835353169 150931768227734876514877)
              ·
                refine ⟨56599413085400578693079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150931768227734876514877 56599413085400578693079)
                ·
                  rfl

theorem cell19_186008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_186008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186008 prefixEnd_186008 := by exact prefixLift 186008
  have htrace : WordTrace (prefixWord ++ tailWord_186008) baseStart_186008 baseEnd_186008 := by
    simpa [prefixWord, tailWord_186008, baseEnd_186008] using wordTrace_append hprefix tailTrace_186008
  have hstable : (prefixWord ++ tailWord_186008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186008).length < 2 ^ (prefixWord ++ tailWord_186008).sum := by decide
  have hdescent : baseEnd_186008 < baseStart_186008 := by decide
  rcases family_descends (prefixWord ++ tailWord_186008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186088 : List Nat := [2, 1, 4, 1, 3, 8]
def baseStart_186088 : Nat := 118140960795 + 186088 * 2 ^ 59
def prefixEnd_186088 : Nat := 4983230072969 + 3 ^ 40 * 186088 * 2
def baseEnd_186088 : Nat := 6291528430220455212787

theorem tailTrace_186088 : CollatzResearch.WordTrace tailWord_186088 prefixEnd_186088 6291528430220455212787 := by
  unfold tailWord_186088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393593474921216072635459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4524791299894954763513945 3393593474921216072635459)
  ·
    refine ⟨5090390212381824108953189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3393593474921216072635459 5090390212381824108953189)
    ·
      refine ⟨954448164821592020428723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5090390212381824108953189 954448164821592020428723)
      ·
        refine ⟨1431672247232388030643085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954448164821592020428723 1431672247232388030643085)
        ·
          refine ⟨536877092712145511491157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1431672247232388030643085 536877092712145511491157)
          ·
            refine ⟨6291528430220455212787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 536877092712145511491157 6291528430220455212787)
            ·
              rfl

theorem cell19_186088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_186088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186088 prefixEnd_186088 := by exact prefixLift 186088
  have htrace : WordTrace (prefixWord ++ tailWord_186088) baseStart_186088 baseEnd_186088 := by
    simpa [prefixWord, tailWord_186088, baseEnd_186088] using wordTrace_append hprefix tailTrace_186088
  have hstable : (prefixWord ++ tailWord_186088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186088).length < 2 ^ (prefixWord ++ tailWord_186088).sum := by decide
  have hdescent : baseEnd_186088 < baseStart_186088 := by decide
  rcases family_descends (prefixWord ++ tailWord_186088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186126 : List Nat := [4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_186126 : Nat := 118140960795 + 186126 * 2 ^ 59
def prefixEnd_186126 : Nat := 4983230072969 + 3 ^ 40 * 186126 * 2
def baseEnd_186126 : Nat := 56635318695611268070535

theorem tailTrace_186126 : CollatzResearch.WordTrace tailWord_186126 prefixEnd_186126 56635318695611268070535 := by
  unfold tailWord_186126
  simp only [CollatzResearch.WordTrace]
  refine ⟨848571615463095579394279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4525715282469843090102821 848571615463095579394279)
  ·
    refine ⟨1272857423194643369091419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 848571615463095579394279 1272857423194643369091419)
    ·
      refine ⟨1909286134791965053637129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272857423194643369091419 1909286134791965053637129)
      ·
        refine ⟨1431964601093973790227847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1909286134791965053637129 1431964601093973790227847)
        ·
          refine ⟨2147946901640960685341771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431964601093973790227847 2147946901640960685341771)
          ·
            refine ⟨3221920352461441028012657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147946901640960685341771 3221920352461441028012657)
            ·
              refine ⟨2416440264346080771009493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3221920352461441028012657 2416440264346080771009493)
              ·
                refine ⟨56635318695611268070535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2416440264346080771009493 56635318695611268070535)
                ·
                  rfl

theorem cell19_186126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_186126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186126 prefixEnd_186126 := by exact prefixLift 186126
  have htrace : WordTrace (prefixWord ++ tailWord_186126) baseStart_186126 baseEnd_186126 := by
    simpa [prefixWord, tailWord_186126, baseEnd_186126] using wordTrace_append hprefix tailTrace_186126
  have hstable : (prefixWord ++ tailWord_186126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186126).length < 2 ^ (prefixWord ++ tailWord_186126).sum := by decide
  have hdescent : baseEnd_186126 < baseStart_186126 := by decide
  rcases family_descends (prefixWord ++ tailWord_186126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186145 : List Nat := [1, 2, 3, 2, 1, 4, 6]
def baseStart_186145 : Nat := 118140960795 + 186145 * 2 ^ 59
def prefixEnd_186145 : Nat := 4983230072969 + 3 ^ 40 * 186145 * 2
def baseEnd_186145 : Nat := 18880366702474951216087

theorem tailTrace_186145 : CollatzResearch.WordTrace tailWord_186145 prefixEnd_186145 18880366702474951216087 := by
  unfold tailWord_186145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789265910635930880095889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4526177273757287253397259 6789265910635930880095889)
  ·
    refine ⟨5091949432976948160071917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6789265910635930880095889 5091949432976948160071917)
    ·
      refine ⟨1909481037366355560026969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5091949432976948160071917 1909481037366355560026969)
      ·
        refine ⟨1432110778024766670020227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1909481037366355560026969 1432110778024766670020227)
        ·
          refine ⟨2148166167037150005030341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432110778024766670020227 2148166167037150005030341)
          ·
            refine ⟨402781156319465625943189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2148166167037150005030341 402781156319465625943189)
            ·
              refine ⟨18880366702474951216087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 402781156319465625943189 18880366702474951216087)
              ·
                rfl

theorem cell19_186145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_186145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186145 prefixEnd_186145 := by exact prefixLift 186145
  have htrace : WordTrace (prefixWord ++ tailWord_186145) baseStart_186145 baseEnd_186145 := by
    simpa [prefixWord, tailWord_186145, baseEnd_186145] using wordTrace_append hprefix tailTrace_186145
  have hstable : (prefixWord ++ tailWord_186145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186145).length < 2 ^ (prefixWord ++ tailWord_186145).sum := by decide
  have hdescent : baseEnd_186145 < baseStart_186145 := by decide
  rcases family_descends (prefixWord ++ tailWord_186145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186221 : List Nat := [1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_186221 : Nat := 118140960795 + 186221 * 2 ^ 59
def prefixEnd_186221 : Nat := 4983230072969 + 3 ^ 40 * 186221 * 2
def baseEnd_186221 : Nat := 56664225754679195959165

theorem tailTrace_186221 : CollatzResearch.WordTrace tailWord_186221 prefixEnd_186221 56664225754679195959165 := by
  unfold tailWord_186221
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792037858360595859862517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4528025238907063906575011 6792037858360595859862517)
  ·
    refine ⟨636753549221305861862111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6792037858360595859862517 636753549221305861862111)
    ·
      refine ⟨955130323831958792793167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636753549221305861862111 955130323831958792793167)
      ·
        refine ⟨1432695485747938189189751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955130323831958792793167 1432695485747938189189751)
        ·
          refine ⟨2149043228621907283784627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432695485747938189189751 2149043228621907283784627)
          ·
            refine ⟨3223564842932860925676941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149043228621907283784627 3223564842932860925676941)
            ·
              refine ⟨1208836816099822847128853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3223564842932860925676941 1208836816099822847128853)
              ·
                refine ⟨56664225754679195959165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1208836816099822847128853 56664225754679195959165)
                ·
                  rfl

theorem cell19_186221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_186221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186221 prefixEnd_186221 := by exact prefixLift 186221
  have htrace : WordTrace (prefixWord ++ tailWord_186221) baseStart_186221 baseEnd_186221 := by
    simpa [prefixWord, tailWord_186221, baseEnd_186221] using wordTrace_append hprefix tailTrace_186221
  have hstable : (prefixWord ++ tailWord_186221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186221).length < 2 ^ (prefixWord ++ tailWord_186221).sum := by decide
  have hdescent : baseEnd_186221 < baseStart_186221 := by decide
  rcases family_descends (prefixWord ++ tailWord_186221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186270 : List Nat := [4, 3, 1, 3, 2, 1, 1, 4]
def baseStart_186270 : Nat := 118140960795 + 186270 * 2 ^ 59
def prefixEnd_186270 : Nat := 4983230072969 + 3 ^ 40 * 186270 * 2
def baseEnd_186270 : Nat := 56679135711461600870143

theorem tailTrace_186270 : CollatzResearch.WordTrace tailWord_186270 prefixEnd_186270 56679135711461600870143 := by
  unfold tailWord_186270
  simp only [CollatzResearch.WordTrace]
  refine ⟨849228129397884653549533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4529216690122051485597509 849228129397884653549533)
  ·
    refine ⟨318460548524206745081075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 849228129397884653549533 318460548524206745081075)
    ·
      refine ⟨477690822786310117621613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318460548524206745081075 477690822786310117621613)
      ·
        refine ⟨179134058544866294108105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477690822786310117621613 179134058544866294108105)
        ·
          refine ⟨134350543908649720581079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179134058544866294108105 134350543908649720581079)
          ·
            refine ⟨201525815862974580871619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134350543908649720581079 201525815862974580871619)
            ·
              refine ⟨302288723794461871307429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201525815862974580871619 302288723794461871307429)
              ·
                refine ⟨56679135711461600870143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302288723794461871307429 56679135711461600870143)
                ·
                  rfl

theorem cell19_186270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_186270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186270 prefixEnd_186270 := by exact prefixLift 186270
  have htrace : WordTrace (prefixWord ++ tailWord_186270) baseStart_186270 baseEnd_186270 := by
    simpa [prefixWord, tailWord_186270, baseEnd_186270] using wordTrace_append hprefix tailTrace_186270
  have hstable : (prefixWord ++ tailWord_186270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186270).length < 2 ^ (prefixWord ++ tailWord_186270).sum := by decide
  have hdescent : baseEnd_186270 < baseStart_186270 := by decide
  rcases family_descends (prefixWord ++ tailWord_186270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186274 : List Nat := [3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_186274 : Nat := 118140960795 + 186274 * 2 ^ 59
def prefixEnd_186274 : Nat := 4983230072969 + 3 ^ 40 * 186274 * 2
def baseEnd_186274 : Nat := 56680352850790776781243

theorem tailTrace_186274 : CollatzResearch.WordTrace tailWord_186274 prefixEnd_186274 56680352850790776781243 := by
  unfold tailWord_186274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698492731792146477885469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4529313951445723941027917 1698492731792146477885469)
  ·
    refine ⟨636934774422054929207051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1698492731792146477885469 636934774422054929207051)
    ·
      refine ⟨955402161633082393810577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636934774422054929207051 955402161633082393810577)
      ·
        refine ⟨716551621224811795357933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955402161633082393810577 716551621224811795357933)
        ·
          refine ⟨268706857959304423259225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716551621224811795357933 268706857959304423259225)
          ·
            refine ⟨201530143469478317444419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268706857959304423259225 201530143469478317444419)
            ·
              refine ⟨302295215204217476166629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201530143469478317444419 302295215204217476166629)
              ·
                refine ⟨56680352850790776781243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302295215204217476166629 56680352850790776781243)
                ·
                  rfl

theorem cell19_186274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_186274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186274 prefixEnd_186274 := by exact prefixLift 186274
  have htrace : WordTrace (prefixWord ++ tailWord_186274) baseStart_186274 baseEnd_186274 := by
    simpa [prefixWord, tailWord_186274, baseEnd_186274] using wordTrace_append hprefix tailTrace_186274
  have hstable : (prefixWord ++ tailWord_186274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186274).length < 2 ^ (prefixWord ++ tailWord_186274).sum := by decide
  have hdescent : baseEnd_186274 < baseStart_186274 := by decide
  rcases family_descends (prefixWord ++ tailWord_186274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186276 : List Nat := [2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_186276 : Nat := 118140960795 + 186276 * 2 ^ 59
def prefixEnd_186276 : Nat := 4983230072969 + 3 ^ 40 * 186276 * 2
def baseEnd_186276 : Nat := 56680961420455364736793

theorem tailTrace_186276 : CollatzResearch.WordTrace tailWord_186276 prefixEnd_186276 56680961420455364736793 := by
  unfold tailWord_186276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397021936580670126557341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4529362582107560168743121 3397021936580670126557341)
  ·
    refine ⟨1273883226217751297459003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3397021936580670126557341 1273883226217751297459003)
    ·
      refine ⟨1910824839326626946188505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273883226217751297459003 1910824839326626946188505)
      ·
        refine ⟨1433118629494970209641379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910824839326626946188505 1433118629494970209641379)
        ·
          refine ⟨2149677944242455314462069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433118629494970209641379 2149677944242455314462069)
          ·
            refine ⟨201532307272730185730819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2149677944242455314462069 201532307272730185730819)
            ·
              refine ⟨302298460909095278596229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201532307272730185730819 302298460909095278596229)
              ·
                refine ⟨56680961420455364736793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302298460909095278596229 56680961420455364736793)
                ·
                  rfl

theorem cell19_186276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_186276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186276 prefixEnd_186276 := by exact prefixLift 186276
  have htrace : WordTrace (prefixWord ++ tailWord_186276) baseStart_186276 baseEnd_186276 := by
    simpa [prefixWord, tailWord_186276, baseEnd_186276] using wordTrace_append hprefix tailTrace_186276
  have hstable : (prefixWord ++ tailWord_186276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186276).length < 2 ^ (prefixWord ++ tailWord_186276).sum := by decide
  have hdescent : baseEnd_186276 < baseStart_186276 := by decide
  rcases family_descends (prefixWord ++ tailWord_186276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186316 : List Nat := [2, 2, 1, 4, 1, 3, 6]
def baseStart_186316 : Nat := 118140960795 + 186316 * 2 ^ 59
def prefixEnd_186316 : Nat := 4983230072969 + 3 ^ 40 * 186316 * 2
def baseEnd_186316 : Nat := 18897710937915707949265

theorem tailTrace_186316 : CollatzResearch.WordTrace tailWord_186316 prefixEnd_186316 18897710937915707949265 := by
  unfold tailWord_186316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397751396508213542285401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4530335195344284723047201 3397751396508213542285401)
  ·
    refine ⟨2548313547381160156714051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3397751396508213542285401 2548313547381160156714051)
    ·
      refine ⟨3822470321071740235071077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548313547381160156714051 3822470321071740235071077)
      ·
        refine ⟨716713185200951294075827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3822470321071740235071077 716713185200951294075827)
        ·
          refine ⟨1075069777801426941113741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716713185200951294075827 1075069777801426941113741)
          ·
            refine ⟨403151166675535102917653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1075069777801426941113741 403151166675535102917653)
            ·
              refine ⟨18897710937915707949265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403151166675535102917653 18897710937915707949265)
              ·
                rfl

theorem cell19_186316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_186316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186316 prefixEnd_186316 := by exact prefixLift 186316
  have htrace : WordTrace (prefixWord ++ tailWord_186316) baseStart_186316 baseEnd_186316 := by
    simpa [prefixWord, tailWord_186316, baseEnd_186316] using wordTrace_append hprefix tailTrace_186316
  have hstable : (prefixWord ++ tailWord_186316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186316).length < 2 ^ (prefixWord ++ tailWord_186316).sum := by decide
  have hdescent : baseEnd_186316 < baseStart_186316 := by decide
  rcases family_descends (prefixWord ++ tailWord_186316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186350 : List Nat := [4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_186350 : Nat := 118140960795 + 186350 * 2 ^ 59
def prefixEnd_186350 : Nat := 4983230072969 + 3 ^ 40 * 186350 * 2
def baseEnd_186350 : Nat := 56703478498045119092147

theorem tailTrace_186350 : CollatzResearch.WordTrace tailWord_186350 prefixEnd_186350 56703478498045119092147 := by
  unfold tailWord_186350
  simp only [CollatzResearch.WordTrace]
  refine ⟨849592859361656361413563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4531161916595500594205669 849592859361656361413563)
  ·
    refine ⟨1274389289042484542120345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 849592859361656361413563 1274389289042484542120345)
    ·
      refine ⟨955791966781863406590259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274389289042484542120345 955791966781863406590259)
      ·
        refine ⟨1433687950172795109885389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955791966781863406590259 1433687950172795109885389)
        ·
          refine ⟨537632981314798166207021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1433687950172795109885389 537632981314798166207021)
          ·
            refine ⟨201612367993049312327633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537632981314798166207021 201612367993049312327633)
            ·
              refine ⟨151209275994786984245725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201612367993049312327633 151209275994786984245725)
              ·
                refine ⟨56703478498045119092147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151209275994786984245725 56703478498045119092147)
                ·
                  rfl

theorem cell19_186350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_186350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186350 prefixEnd_186350 := by exact prefixLift 186350
  have htrace : WordTrace (prefixWord ++ tailWord_186350) baseStart_186350 baseEnd_186350 := by
    simpa [prefixWord, tailWord_186350, baseEnd_186350] using wordTrace_append hprefix tailTrace_186350
  have hstable : (prefixWord ++ tailWord_186350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186350).length < 2 ^ (prefixWord ++ tailWord_186350).sum := by decide
  have hdescent : baseEnd_186350 < baseStart_186350 := by decide
  rcases family_descends (prefixWord ++ tailWord_186350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186373 : List Nat := [1, 3, 1, 1, 2, 6, 5]
def baseStart_186373 : Nat := 118140960795 + 186373 * 2 ^ 59
def prefixEnd_186373 : Nat := 4983230072969 + 3 ^ 40 * 186373 * 2
def baseEnd_186373 : Nat := 18903492349729293526991

theorem tailTrace_186373 : CollatzResearch.WordTrace tailWord_186373 prefixEnd_186373 18903492349729293526991 := by
  unfold tailWord_186373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797581753809925819395773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4531721169206617212930515 6797581753809925819395773)
  ·
    refine ⟨2549093157678722182273415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6797581753809925819395773 2549093157678722182273415)
    ·
      refine ⟨3823639736518083273410123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2549093157678722182273415 3823639736518083273410123)
      ·
        refine ⟨5735459604777124910115185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823639736518083273410123 5735459604777124910115185)
        ·
          refine ⟨4301594703582843682586389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735459604777124910115185 4301594703582843682586389)
          ·
            refine ⟨201637251730445797621237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4301594703582843682586389 201637251730445797621237)
            ·
              refine ⟨18903492349729293526991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201637251730445797621237 18903492349729293526991)
              ·
                rfl

theorem cell19_186373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_186373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186373 prefixEnd_186373 := by exact prefixLift 186373
  have htrace : WordTrace (prefixWord ++ tailWord_186373) baseStart_186373 baseEnd_186373 := by
    simpa [prefixWord, tailWord_186373, baseEnd_186373] using wordTrace_append hprefix tailTrace_186373
  have hstable : (prefixWord ++ tailWord_186373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186373).length < 2 ^ (prefixWord ++ tailWord_186373).sum := by decide
  have hdescent : baseEnd_186373 < baseStart_186373 := by decide
  rcases family_descends (prefixWord ++ tailWord_186373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186392 : List Nat := [2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_186392 : Nat := 118140960795 + 186392 * 2 ^ 59
def prefixEnd_186392 : Nat := 4983230072969 + 3 ^ 40 * 186392 * 2
def baseEnd_186392 : Nat := 56716258461001466158699

theorem tailTrace_186392 : CollatzResearch.WordTrace tailWord_186392 prefixEnd_186392 56716258461001466158699 := by
  unfold tailWord_186392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399137370370546032168715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4532183160494061376224953 3399137370370546032168715)
  ·
    refine ⟨5098706055555819048253073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3399137370370546032168715 5098706055555819048253073)
    ·
      refine ⟨3824029541666864286189805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5098706055555819048253073 3824029541666864286189805)
      ·
        refine ⟨1434011078125074107321177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3824029541666864286189805 1434011078125074107321177)
        ·
          refine ⟨1075508308593805580490883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434011078125074107321177 1075508308593805580490883)
          ·
            refine ⟨1613262462890708370736325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075508308593805580490883 1613262462890708370736325)
            ·
              refine ⟨302486711792007819513061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1613262462890708370736325 302486711792007819513061)
              ·
                refine ⟨56716258461001466158699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302486711792007819513061 56716258461001466158699)
                ·
                  rfl

theorem cell19_186392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_186392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186392 prefixEnd_186392 := by exact prefixLift 186392
  have htrace : WordTrace (prefixWord ++ tailWord_186392) baseStart_186392 baseEnd_186392 := by
    simpa [prefixWord, tailWord_186392, baseEnd_186392] using wordTrace_append hprefix tailTrace_186392
  have hstable : (prefixWord ++ tailWord_186392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186392).length < 2 ^ (prefixWord ++ tailWord_186392).sum := by decide
  have hdescent : baseEnd_186392 < baseStart_186392 := by decide
  rcases family_descends (prefixWord ++ tailWord_186392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186430 : List Nat := [4, 2, 1, 3, 9]
def baseStart_186430 : Nat := 118140960795 + 186430 * 2 ^ 59
def prefixEnd_186430 : Nat := 4983230072969 + 3 ^ 40 * 186430 * 2
def baseEnd_186430 : Nat := 2101030417949208789413

theorem tailTrace_186430 : CollatzResearch.WordTrace tailWord_186430 prefixEnd_186430 2101030417949208789413 := by
  unfold tailWord_186430
  simp only [CollatzResearch.WordTrace]
  refine ⟨849957589325428069277593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4533107143068949702813829 849957589325428069277593)
  ·
    refine ⟨637468191994071051958195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 849957589325428069277593 637468191994071051958195)
    ·
      refine ⟨956202287991106577937293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637468191994071051958195 956202287991106577937293)
      ·
        refine ⟨358575857996664966726485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 956202287991106577937293 358575857996664966726485)
        ·
          refine ⟨2101030417949208789413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 358575857996664966726485 2101030417949208789413)
          ·
            rfl

theorem cell19_186430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 9].length) (baseStart_186430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186430 prefixEnd_186430 := by exact prefixLift 186430
  have htrace : WordTrace (prefixWord ++ tailWord_186430) baseStart_186430 baseEnd_186430 := by
    simpa [prefixWord, tailWord_186430, baseEnd_186430] using wordTrace_append hprefix tailTrace_186430
  have hstable : (prefixWord ++ tailWord_186430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186430).length < 2 ^ (prefixWord ++ tailWord_186430).sum := by decide
  have hdescent : baseEnd_186430 < baseStart_186430 := by decide
  rcases family_descends (prefixWord ++ tailWord_186430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186432 : List Nat := [2, 1, 1, 2, 2, 11]
def baseStart_186432 : Nat := 118140960795 + 186432 * 2 ^ 59
def prefixEnd_186432 : Nat := 4983230072969 + 3 ^ 40 * 186432 * 2
def baseEnd_186432 : Nat := 6303158872699247252189

theorem tailTrace_186432 : CollatzResearch.WordTrace tailWord_186432 prefixEnd_186432 6303158872699247252189 := by
  unfold tailWord_186432
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399866830298089447896775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4533155773730785930529033 3399866830298089447896775)
  ·
    refine ⟨5099800245447134171845163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3399866830298089447896775 5099800245447134171845163)
    ·
      refine ⟨7649700368170701257767745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5099800245447134171845163 7649700368170701257767745)
      ·
        refine ⟨5737275276128025943325809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7649700368170701257767745 5737275276128025943325809)
        ·
          refine ⟨4302956457096019457494357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5737275276128025943325809 4302956457096019457494357)
          ·
            refine ⟨6303158872699247252189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4302956457096019457494357 6303158872699247252189)
            ·
              rfl

theorem cell19_186432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_186432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186432 prefixEnd_186432 := by exact prefixLift 186432
  have htrace : WordTrace (prefixWord ++ tailWord_186432) baseStart_186432 baseEnd_186432 := by
    simpa [prefixWord, tailWord_186432, baseEnd_186432] using wordTrace_append hprefix tailTrace_186432
  have hstable : (prefixWord ++ tailWord_186432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186432).length < 2 ^ (prefixWord ++ tailWord_186432).sum := by decide
  have hdescent : baseEnd_186432 < baseStart_186432 := by decide
  rcases family_descends (prefixWord ++ tailWord_186432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186525 : List Nat := [1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_186525 : Nat := 118140960795 + 186525 * 2 ^ 59
def prefixEnd_186525 : Nat := 4983230072969 + 3 ^ 40 * 186525 * 2
def baseEnd_186525 : Nat := 56756728343696565202781

theorem tailTrace_186525 : CollatzResearch.WordTrace tailWord_186525 prefixEnd_186525 56756728343696565202781 := by
  unfold tailWord_186525
  simp only [CollatzResearch.WordTrace]
  refine ⟨6803125649259255778929029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4535417099506170519286019 6803125649259255778929029)
  ·
    refine ⟨1275586059236110458549193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6803125649259255778929029 1275586059236110458549193)
    ·
      refine ⟨956689544427082843911895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1275586059236110458549193 956689544427082843911895)
      ·
        refine ⟨1435034316640624265867843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956689544427082843911895 1435034316640624265867843)
        ·
          refine ⟨2152551474960936398801765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435034316640624265867843 2152551474960936398801765)
          ·
            refine ⟨403603401555175574775331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2152551474960936398801765 403603401555175574775331)
            ·
              refine ⟨605405102332763362162997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403603401555175574775331 605405102332763362162997)
              ·
                refine ⟨56756728343696565202781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 605405102332763362162997 56756728343696565202781)
                ·
                  rfl

theorem cell19_186525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_186525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186525 prefixEnd_186525 := by exact prefixLift 186525
  have htrace : WordTrace (prefixWord ++ tailWord_186525) baseStart_186525 baseEnd_186525 := by
    simpa [prefixWord, tailWord_186525, baseEnd_186525] using wordTrace_append hprefix tailTrace_186525
  have hstable : (prefixWord ++ tailWord_186525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186525).length < 2 ^ (prefixWord ++ tailWord_186525).sum := by decide
  have hdescent : baseEnd_186525 < baseStart_186525 := by decide
  rcases family_descends (prefixWord ++ tailWord_186525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186565 : List Nat := [1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_186565 : Nat := 118140960795 + 186565 * 2 ^ 59
def prefixEnd_186565 : Nat := 4983230072969 + 3 ^ 40 * 186565 * 2
def baseEnd_186565 : Nat := 56768899736988324313783

theorem tailTrace_186565 : CollatzResearch.WordTrace tailWord_186565 prefixEnd_186565 56768899736988324313783 := by
  unfold tailWord_186565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804584569114342610385149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4536389712742895073590099 6804584569114342610385149)
  ·
    refine ⟨2551719213417878478894431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6804584569114342610385149 2551719213417878478894431)
    ·
      refine ⟨3827578820126817718341647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551719213417878478894431 3827578820126817718341647)
      ·
        refine ⟨5741368230190226577512471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827578820126817718341647 5741368230190226577512471)
        ·
          refine ⟨8612052345285339866268707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741368230190226577512471 8612052345285339866268707)
          ·
            refine ⟨12918078517928009799403061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8612052345285339866268707 12918078517928009799403061)
            ·
              refine ⟨1211069861055750918694037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12918078517928009799403061 1211069861055750918694037)
              ·
                refine ⟨56768899736988324313783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1211069861055750918694037 56768899736988324313783)
                ·
                  rfl

theorem cell19_186565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_186565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186565 prefixEnd_186565 := by exact prefixLift 186565
  have htrace : WordTrace (prefixWord ++ tailWord_186565) baseStart_186565 baseEnd_186565 := by
    simpa [prefixWord, tailWord_186565, baseEnd_186565] using wordTrace_append hprefix tailTrace_186565
  have hstable : (prefixWord ++ tailWord_186565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186565).length < 2 ^ (prefixWord ++ tailWord_186565).sum := by decide
  have hdescent : baseEnd_186565 < baseStart_186565 := by decide
  rcases family_descends (prefixWord ++ tailWord_186565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186620 : List Nat := [2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_186620 : Nat := 118140960795 + 186620 * 2 ^ 59
def prefixEnd_186620 : Nat := 4983230072969 + 3 ^ 40 * 186620 * 2
def baseEnd_186620 : Nat := 56785635402764493091411

theorem tailTrace_186620 : CollatzResearch.WordTrace tailWord_186620 prefixEnd_186620 56785635402764493091411 := by
  unfold tailWord_186620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403295291957543501818657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4537727055943391335758209 3403295291957543501818657)
  ·
    refine ⟨2552471468968157626363993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3403295291957543501818657 2552471468968157626363993)
    ·
      refine ⟨1914353601726118219772995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552471468968157626363993 1914353601726118219772995)
      ·
        refine ⟨2871530402589177329659493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914353601726118219772995 2871530402589177329659493)
        ·
          refine ⟨538411950485470749311155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2871530402589177329659493 538411950485470749311155)
          ·
            refine ⟨807617925728206123966733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538411950485470749311155 807617925728206123966733)
            ·
              refine ⟨302856722148077296487525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807617925728206123966733 302856722148077296487525)
              ·
                refine ⟨56785635402764493091411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302856722148077296487525 56785635402764493091411)
                ·
                  rfl

theorem cell19_186620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_186620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186620 prefixEnd_186620 := by exact prefixLift 186620
  have htrace : WordTrace (prefixWord ++ tailWord_186620) baseStart_186620 baseEnd_186620 := by
    simpa [prefixWord, tailWord_186620, baseEnd_186620] using wordTrace_append hprefix tailTrace_186620
  have hstable : (prefixWord ++ tailWord_186620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186620).length < 2 ^ (prefixWord ++ tailWord_186620).sum := by decide
  have hdescent : baseEnd_186620 < baseStart_186620 := by decide
  rcases family_descends (prefixWord ++ tailWord_186620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186658 : List Nat := [3, 3, 1, 1, 3, 2, 6]
def baseStart_186658 : Nat := 118140960795 + 186658 * 2 ^ 59
def prefixEnd_186658 : Nat := 4983230072969 + 3 ^ 40 * 186658 * 2
def baseEnd_186658 : Nat := 18932399408797221415621

theorem tailTrace_186658 : CollatzResearch.WordTrace tailWord_186658 prefixEnd_186658 18932399408797221415621 := by
  unfold tailWord_186658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701994139444354873380157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4538651038518279662347085 1701994139444354873380157)
  ·
    refine ⟨638247802291633077517559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1701994139444354873380157 638247802291633077517559)
    ·
      refine ⟨957371703437449616276339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638247802291633077517559 957371703437449616276339)
      ·
        refine ⟨1436057555156174424414509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957371703437449616276339 1436057555156174424414509)
        ·
          refine ⟨538521583183565409155441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1436057555156174424414509 538521583183565409155441)
          ·
            refine ⟨403891187387674056866581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538521583183565409155441 403891187387674056866581)
            ·
              refine ⟨18932399408797221415621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403891187387674056866581 18932399408797221415621)
              ·
                rfl

theorem cell19_186658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_186658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186658 prefixEnd_186658 := by exact prefixLift 186658
  have htrace : WordTrace (prefixWord ++ tailWord_186658) baseStart_186658 baseEnd_186658 := by
    simpa [prefixWord, tailWord_186658, baseEnd_186658] using wordTrace_append hprefix tailTrace_186658
  have hstable : (prefixWord ++ tailWord_186658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186658).length < 2 ^ (prefixWord ++ tailWord_186658).sum := by decide
  have hdescent : baseEnd_186658 < baseStart_186658 := by decide
  rcases family_descends (prefixWord ++ tailWord_186658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186696 : List Nat := [2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_186696 : Nat := 118140960795 + 186696 * 2 ^ 59
def prefixEnd_186696 : Nat := 4983230072969 + 3 ^ 40 * 186696 * 2
def baseEnd_186696 : Nat := 56808761050018835402315

theorem tailTrace_186696 : CollatzResearch.WordTrace tailWord_186696 prefixEnd_186696 56808761050018835402315 := by
  unfold tailWord_186696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404681265819875991701971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4539575021093167988935961 3404681265819875991701971)
  ·
    refine ⟨5107021898729813987552957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3404681265819875991701971 5107021898729813987552957)
    ·
      refine ⟨1915133212023680245332359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5107021898729813987552957 1915133212023680245332359)
      ·
        refine ⟨2872699818035520367998539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915133212023680245332359 2872699818035520367998539)
        ·
          refine ⟨4309049727053280551997809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872699818035520367998539 4309049727053280551997809)
          ·
            refine ⟨3231787295289960413998357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4309049727053280551997809 3231787295289960413998357)
            ·
              refine ⟨151490029466716894406173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3231787295289960413998357 151490029466716894406173)
              ·
                refine ⟨56808761050018835402315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151490029466716894406173 56808761050018835402315)
                ·
                  rfl

theorem cell19_186696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_186696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186696 prefixEnd_186696 := by exact prefixLift 186696
  have htrace : WordTrace (prefixWord ++ tailWord_186696) baseStart_186696 baseEnd_186696 := by
    simpa [prefixWord, tailWord_186696, baseEnd_186696] using wordTrace_append hprefix tailTrace_186696
  have hstable : (prefixWord ++ tailWord_186696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186696).length < 2 ^ (prefixWord ++ tailWord_186696).sum := by decide
  have hdescent : baseEnd_186696 < baseStart_186696 := by decide
  rcases family_descends (prefixWord ++ tailWord_186696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186736 : List Nat := [2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_186736 : Nat := 118140960795 + 186736 * 2 ^ 59
def prefixEnd_186736 : Nat := 4983230072969 + 3 ^ 40 * 186736 * 2
def baseEnd_186736 : Nat := 56820932443310594513317

theorem tailTrace_186736 : CollatzResearch.WordTrace tailWord_186736 prefixEnd_186736 56820932443310594513317 := by
  unfold tailWord_186736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3405410725747419407430031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4540547634329892543240041 3405410725747419407430031)
  ·
    refine ⟨5108116088621129111145047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3405410725747419407430031 5108116088621129111145047)
    ·
      refine ⟨7662174132931693666717571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5108116088621129111145047 7662174132931693666717571)
      ·
        refine ⟨11493261199397540500076357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7662174132931693666717571 11493261199397540500076357)
        ·
          refine ⟨2154986474887038843764317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11493261199397540500076357 2154986474887038843764317)
          ·
            refine ⟨808119928082639566411619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2154986474887038843764317 808119928082639566411619)
            ·
              refine ⟨1212179892123959349617429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808119928082639566411619 1212179892123959349617429)
              ·
                refine ⟨56820932443310594513317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1212179892123959349617429 56820932443310594513317)
                ·
                  rfl

theorem cell19_186736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_186736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186736 prefixEnd_186736 := by exact prefixLift 186736
  have htrace : WordTrace (prefixWord ++ tailWord_186736) baseStart_186736 baseEnd_186736 := by
    simpa [prefixWord, tailWord_186736, baseEnd_186736] using wordTrace_append hprefix tailTrace_186736
  have hstable : (prefixWord ++ tailWord_186736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186736).length < 2 ^ (prefixWord ++ tailWord_186736).sum := by decide
  have hdescent : baseEnd_186736 < baseStart_186736 := by decide
  rcases family_descends (prefixWord ++ tailWord_186736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186753 : List Nat := [1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_186753 : Nat := 118140960795 + 186753 * 2 ^ 59
def prefixEnd_186753 : Nat := 4983230072969 + 3 ^ 40 * 186753 * 2
def baseEnd_186753 : Nat := 56826105285459592135493

theorem tailTrace_186753 : CollatzResearch.WordTrace tailWord_186753 prefixEnd_186753 56826105285459592135493 := by
  unfold tailWord_186753
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811441492433250718228913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4540960994955500478819275 6811441492433250718228913)
  ·
    refine ⟨5108581119324938038671685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6811441492433250718228913 5108581119324938038671685)
    ·
      refine ⟨957858959873425882250941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5108581119324938038671685 957858959873425882250941)
      ·
        refine ⟨359197109952534705844103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 957858959873425882250941 359197109952534705844103)
        ·
          refine ⟨538795664928802058766155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359197109952534705844103 538795664928802058766155)
          ·
            refine ⟨808193497393203088149233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538795664928802058766155 808193497393203088149233)
            ·
              refine ⟨606145123044902316111925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808193497393203088149233 606145123044902316111925)
              ·
                refine ⟨56826105285459592135493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 606145123044902316111925 56826105285459592135493)
                ·
                  rfl

theorem cell19_186753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_186753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186753 prefixEnd_186753 := by exact prefixLift 186753
  have htrace : WordTrace (prefixWord ++ tailWord_186753) baseStart_186753 baseEnd_186753 := by
    simpa [prefixWord, tailWord_186753, baseEnd_186753] using wordTrace_append hprefix tailTrace_186753
  have hstable : (prefixWord ++ tailWord_186753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186753).length < 2 ^ (prefixWord ++ tailWord_186753).sum := by decide
  have hdescent : baseEnd_186753 < baseStart_186753 := by decide
  rcases family_descends (prefixWord ++ tailWord_186753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186772 : List Nat := [2, 4, 2, 1, 3, 7]
def baseStart_186772 : Nat := 118140960795 + 186772 * 2 ^ 59
def prefixEnd_186772 : Nat := 4983230072969 + 3 ^ 40 * 186772 * 2
def baseEnd_186772 : Nat := 6314654077474797523691

theorem tailTrace_186772 : CollatzResearch.WordTrace tailWord_186772 prefixEnd_186772 6314654077474797523691 := by
  unfold tailWord_186772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406067239682208481585285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4541422986242944642113713 3406067239682208481585285)
  ·
    refine ⟨638637607440414090297241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3406067239682208481585285 638637607440414090297241)
    ·
      refine ⟨478978205580310567722931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638637607440414090297241 478978205580310567722931)
      ·
        refine ⟨718467308370465851584397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478978205580310567722931 718467308370465851584397)
        ·
          refine ⟨269425240638924694344149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 718467308370465851584397 269425240638924694344149)
          ·
            refine ⟨6314654077474797523691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 269425240638924694344149 6314654077474797523691)
            ·
              rfl

theorem cell19_186772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_186772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186772 prefixEnd_186772 := by exact prefixLift 186772
  have htrace : WordTrace (prefixWord ++ tailWord_186772) baseStart_186772 baseEnd_186772 := by
    simpa [prefixWord, tailWord_186772, baseEnd_186772] using wordTrace_append hprefix tailTrace_186772
  have hstable : (prefixWord ++ tailWord_186772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186772).length < 2 ^ (prefixWord ++ tailWord_186772).sum := by decide
  have hdescent : baseEnd_186772 < baseStart_186772 := by decide
  rcases family_descends (prefixWord ++ tailWord_186772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186791 : List Nat := [1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_186791 : Nat := 118140960795 + 186791 * 2 ^ 59
def prefixEnd_186791 : Nat := 4983230072969 + 3 ^ 40 * 186791 * 2
def baseEnd_186791 : Nat := 56837668109086763290945

theorem tailTrace_186791 : CollatzResearch.WordTrace tailWord_186791 prefixEnd_186791 56837668109086763290945 := by
  unfold tailWord_186791
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812827466295583208112227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4541884977530388805408151 6812827466295583208112227)
  ·
    refine ⟨10219241199443374812168341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6812827466295583208112227 10219241199443374812168341)
    ·
      refine ⟨479026931223908194320391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10219241199443374812168341 479026931223908194320391)
      ·
        refine ⟨718540396835862291480587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479026931223908194320391 718540396835862291480587)
        ·
          refine ⟨1077810595253793437220881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718540396835862291480587 1077810595253793437220881)
          ·
            refine ⟨808357946440345077915661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077810595253793437220881 808357946440345077915661)
            ·
              refine ⟨303134229915129404218373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 808357946440345077915661 303134229915129404218373)
              ·
                refine ⟨56837668109086763290945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303134229915129404218373 56837668109086763290945)
                ·
                  rfl

theorem cell19_186791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_186791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186791 prefixEnd_186791 := by exact prefixLift 186791
  have htrace : WordTrace (prefixWord ++ tailWord_186791) baseStart_186791 baseEnd_186791 := by
    simpa [prefixWord, tailWord_186791, baseEnd_186791] using wordTrace_append hprefix tailTrace_186791
  have hstable : (prefixWord ++ tailWord_186791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186791).length < 2 ^ (prefixWord ++ tailWord_186791).sum := by decide
  have hdescent : baseEnd_186791 < baseStart_186791 := by decide
  rcases family_descends (prefixWord ++ tailWord_186791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186804 : List Nat := [2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_186804 : Nat := 118140960795 + 186804 * 2 ^ 59
def prefixEnd_186804 : Nat := 4983230072969 + 3 ^ 40 * 186804 * 2
def baseEnd_186804 : Nat := 56841623811906585002021

theorem tailTrace_186804 : CollatzResearch.WordTrace tailWord_186804 prefixEnd_186804 56841623811906585002021 := by
  unfold tailWord_186804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406650807624243214167733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4542201076832324285556977 3406650807624243214167733)
  ·
    refine ⟨319373513214772801328225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3406650807624243214167733 319373513214772801328225)
    ·
      refine ⟨239530134911079600996169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319373513214772801328225 239530134911079600996169)
      ·
        refine ⟨179647601183309700747127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239530134911079600996169 179647601183309700747127)
        ·
          refine ⟨269471401774964551120691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179647601183309700747127 269471401774964551120691)
          ·
            refine ⟨404207102662446826681037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269471401774964551120691 404207102662446826681037)
            ·
              refine ⟨151577663498417560005389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404207102662446826681037 151577663498417560005389)
              ·
                refine ⟨56841623811906585002021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151577663498417560005389 56841623811906585002021)
                ·
                  rfl

theorem cell19_186804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_186804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186804 prefixEnd_186804 := by exact prefixLift 186804
  have htrace : WordTrace (prefixWord ++ tailWord_186804) baseStart_186804 baseEnd_186804 := by
    simpa [prefixWord, tailWord_186804, baseEnd_186804] using wordTrace_append hprefix tailTrace_186804
  have hstable : (prefixWord ++ tailWord_186804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186804).length < 2 ^ (prefixWord ++ tailWord_186804).sum := by decide
  have hdescent : baseEnd_186804 < baseStart_186804 := by decide
  rcases family_descends (prefixWord ++ tailWord_186804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186882 : List Nat := [3, 4, 1, 2, 3, 1, 5]
def baseStart_186882 : Nat := 118140960795 + 186882 * 2 ^ 59
def prefixEnd_186882 : Nat := 4983230072969 + 3 ^ 40 * 186882 * 2
def baseEnd_186882 : Nat := 18955119342941838422825

theorem tailTrace_186882 : CollatzResearch.WordTrace tailWord_186882 prefixEnd_186882 18955119342941838422825 := by
  unfold tailWord_186882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704036627241476437418725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4544097672643937166449933 1704036627241476437418725)
  ·
    refine ⟨319506867607776832016011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1704036627241476437418725 319506867607776832016011)
    ·
      refine ⟨479260301411665248024017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319506867607776832016011 479260301411665248024017)
      ·
        refine ⟨359445226058748936018013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479260301411665248024017 359445226058748936018013)
        ·
          refine ⟨134791959772030851006755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359445226058748936018013 134791959772030851006755)
          ·
            refine ⟨202187939658046276510133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134791959772030851006755 202187939658046276510133)
            ·
              refine ⟨18955119342941838422825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202187939658046276510133 18955119342941838422825)
              ·
                rfl

theorem cell19_186882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_186882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186882 prefixEnd_186882 := by exact prefixLift 186882
  have htrace : WordTrace (prefixWord ++ tailWord_186882) baseStart_186882 baseEnd_186882 := by
    simpa [prefixWord, tailWord_186882, baseEnd_186882] using wordTrace_append hprefix tailTrace_186882
  have hstable : (prefixWord ++ tailWord_186882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186882).length < 2 ^ (prefixWord ++ tailWord_186882).sum := by decide
  have hdescent : baseEnd_186882 < baseStart_186882 := by decide
  rcases family_descends (prefixWord ++ tailWord_186882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186903 : List Nat := [1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_186903 : Nat := 118140960795 + 186903 * 2 ^ 59
def prefixEnd_186903 : Nat := 4983230072969 + 3 ^ 40 * 186903 * 2
def baseEnd_186903 : Nat := 56871748010303688801751

theorem tailTrace_186903 : CollatzResearch.WordTrace tailWord_186903 prefixEnd_186903 56871748010303688801751 := by
  unfold tailWord_186903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816912441889826336189363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4544608294593217557459575 6816912441889826336189363)
  ·
    refine ⟨10225368662834739504284045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6816912441889826336189363 10225368662834739504284045)
    ·
      refine ⟨3834513248563027314106517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10225368662834739504284045 3834513248563027314106517)
      ·
        refine ⟨179742808526391905348743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3834513248563027314106517 179742808526391905348743)
        ·
          refine ⟨269614212789587858023115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179742808526391905348743 269614212789587858023115)
          ·
            refine ⟨404421319184381787034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269614212789587858023115 404421319184381787034673)
            ·
              refine ⟨303315989388286340276005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404421319184381787034673 303315989388286340276005)
              ·
                refine ⟨56871748010303688801751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303315989388286340276005 56871748010303688801751)
                ·
                  rfl

theorem cell19_186903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_186903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186903 prefixEnd_186903 := by exact prefixLift 186903
  have htrace : WordTrace (prefixWord ++ tailWord_186903) baseStart_186903 baseEnd_186903 := by
    simpa [prefixWord, tailWord_186903, baseEnd_186903] using wordTrace_append hprefix tailTrace_186903
  have hstable : (prefixWord ++ tailWord_186903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186903).length < 2 ^ (prefixWord ++ tailWord_186903).sum := by decide
  have hdescent : baseEnd_186903 < baseStart_186903 := by decide
  rcases family_descends (prefixWord ++ tailWord_186903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186945 : List Nat := [1, 2, 5, 1, 1, 9]
def baseStart_186945 : Nat := 118140960795 + 186945 * 2 ^ 59
def prefixEnd_186945 : Nat := 4983230072969 + 3 ^ 40 * 186945 * 2
def baseEnd_186945 : Nat := 6320503108140003985367

theorem tailTrace_186945 : CollatzResearch.WordTrace tailWord_186945 prefixEnd_186945 6320503108140003985367 := by
  unfold tailWord_186945
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818444307737667509218289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4545629538491778339478859 6818444307737667509218289)
  ·
    refine ⟨5113833230803250631913717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6818444307737667509218289 5113833230803250631913717)
    ·
      refine ⟨479421865387804746741911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5113833230803250631913717 479421865387804746741911)
      ·
        refine ⟨719132798081707120112867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479421865387804746741911 719132798081707120112867)
        ·
          refine ⟨1078699197122560680169301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719132798081707120112867 1078699197122560680169301)
          ·
            refine ⟨6320503108140003985367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1078699197122560680169301 6320503108140003985367)
            ·
              rfl

theorem cell19_186945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_186945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_186945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_186945 prefixEnd_186945 := by exact prefixLift 186945
  have htrace : WordTrace (prefixWord ++ tailWord_186945) baseStart_186945 baseEnd_186945 := by
    simpa [prefixWord, tailWord_186945, baseEnd_186945] using wordTrace_append hprefix tailTrace_186945
  have hstable : (prefixWord ++ tailWord_186945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186945).length < 2 ^ (prefixWord ++ tailWord_186945).sum := by decide
  have hdescent : baseEnd_186945 < baseStart_186945 := by decide
  rcases family_descends (prefixWord ++ tailWord_186945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187034 : List Nat := [3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_187034 : Nat := 118140960795 + 187034 * 2 ^ 59
def prefixEnd_187034 : Nat := 4983230072969 + 3 ^ 40 * 187034 * 2
def baseEnd_187034 : Nat := 56911609323334199890283

theorem tailTrace_187034 : CollatzResearch.WordTrace tailWord_187034 prefixEnd_187034 56911609323334199890283 := by
  unfold tailWord_187034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705422601103808927302039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4547793602943490472805437 1705422601103808927302039)
  ·
    refine ⟨2558133901655713390953059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705422601103808927302039 2558133901655713390953059)
    ·
      refine ⟨3837200852483570086429589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558133901655713390953059 3837200852483570086429589)
      ·
        refine ⟨179868789960167347801387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3837200852483570086429589 179868789960167347801387)
        ·
          refine ⟨269803184940251021702081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179868789960167347801387 269803184940251021702081)
          ·
            refine ⟨202352388705188266276561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269803184940251021702081 202352388705188266276561)
            ·
              refine ⟨151764291528891199707421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202352388705188266276561 151764291528891199707421)
              ·
                refine ⟨56911609323334199890283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151764291528891199707421 56911609323334199890283)
                ·
                  rfl

theorem cell19_187034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_187034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187034 prefixEnd_187034 := by exact prefixLift 187034
  have htrace : WordTrace (prefixWord ++ tailWord_187034) baseStart_187034 baseEnd_187034 := by
    simpa [prefixWord, tailWord_187034, baseEnd_187034] using wordTrace_append hprefix tailTrace_187034
  have hstable : (prefixWord ++ tailWord_187034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187034).length < 2 ^ (prefixWord ++ tailWord_187034).sum := by decide
  have hdescent : baseEnd_187034 < baseStart_187034 := by decide
  rcases family_descends (prefixWord ++ tailWord_187034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187036 : List Nat := [2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_187036 : Nat := 118140960795 + 187036 * 2 ^ 59
def prefixEnd_187036 : Nat := 4983230072969 + 3 ^ 40 * 187036 * 2
def baseEnd_187036 : Nat := 56912217892998787845833

theorem tailTrace_187036 : CollatzResearch.WordTrace tailWord_187036 prefixEnd_187036 56912217892998787845833 := by
  unfold tailWord_187036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410881675203995025390481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4547842233605326700520641 3410881675203995025390481)
  ·
    refine ⟨2558161256402996269042861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3410881675203995025390481 2558161256402996269042861)
    ·
      refine ⟨959310471151123600891073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2558161256402996269042861 959310471151123600891073)
      ·
        refine ⟨719482853363342700668305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959310471151123600891073 719482853363342700668305)
        ·
          refine ⟨539612140022507025501229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 719482853363342700668305 539612140022507025501229)
          ·
            refine ⟨202354552508440134562961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539612140022507025501229 202354552508440134562961)
            ·
              refine ⟨151765914381330100922221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202354552508440134562961 151765914381330100922221)
              ·
                refine ⟨56912217892998787845833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151765914381330100922221 56912217892998787845833)
                ·
                  rfl

theorem cell19_187036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_187036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187036 prefixEnd_187036 := by exact prefixLift 187036
  have htrace : WordTrace (prefixWord ++ tailWord_187036) baseStart_187036 baseEnd_187036 := by
    simpa [prefixWord, tailWord_187036, baseEnd_187036] using wordTrace_append hprefix tailTrace_187036
  have hstable : (prefixWord ++ tailWord_187036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187036).length < 2 ^ (prefixWord ++ tailWord_187036).sum := by decide
  have hdescent : baseEnd_187036 < baseStart_187036 := by decide
  rcases family_descends (prefixWord ++ tailWord_187036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187038 : List Nat := [4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_187038 : Nat := 118140960795 + 187038 * 2 ^ 59
def prefixEnd_187038 : Nat := 4983230072969 + 3 ^ 40 * 187038 * 2
def baseEnd_187038 : Nat := 56912826462663375801383

theorem tailTrace_187038 : CollatzResearch.WordTrace tailWord_187038 prefixEnd_187038 56912826462663375801383 := by
  unfold tailWord_187038
  simp only [CollatzResearch.WordTrace]
  refine ⟨852729537050093049044221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4547890864267162928235845 852729537050093049044221)
  ·
    refine ⟨319773576393784893391583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 852729537050093049044221 319773576393784893391583)
    ·
      refine ⟨479660364590677340087375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319773576393784893391583 479660364590677340087375)
      ·
        refine ⟨719490546886016010131063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479660364590677340087375 719490546886016010131063)
        ·
          refine ⟨1079235820329024015196595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719490546886016010131063 1079235820329024015196595)
          ·
            refine ⟨1618853730493536022794893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079235820329024015196595 1618853730493536022794893)
            ·
              refine ⟨607070148935076008548085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1618853730493536022794893 607070148935076008548085)
              ·
                refine ⟨56912826462663375801383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 607070148935076008548085 56912826462663375801383)
                ·
                  rfl

theorem cell19_187038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_187038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187038 prefixEnd_187038 := by exact prefixLift 187038
  have htrace : WordTrace (prefixWord ++ tailWord_187038) baseStart_187038 baseEnd_187038 := by
    simpa [prefixWord, tailWord_187038, baseEnd_187038] using wordTrace_append hprefix tailTrace_187038
  have hstable : (prefixWord ++ tailWord_187038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187038).length < 2 ^ (prefixWord ++ tailWord_187038).sum := by decide
  have hdescent : baseEnd_187038 < baseStart_187038 := by decide
  rcases family_descends (prefixWord ++ tailWord_187038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187059 : List Nat := [1, 1, 1, 2, 3, 6, 5]
def baseStart_187059 : Nat := 118140960795 + 187059 * 2 ^ 59
def prefixEnd_187059 : Nat := 4983230072969 + 3 ^ 40 * 187059 * 2
def baseEnd_187059 : Nat := 18973072148047183111553

theorem tailTrace_187059 : CollatzResearch.WordTrace tailWord_187059 prefixEnd_187059 18973072148047183111553 := by
  unfold tailWord_187059
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822602229324664978868231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4548401486216443319245487 6822602229324664978868231)
  ·
    refine ⟨10233903343986997468302347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6822602229324664978868231 10233903343986997468302347)
    ·
      refine ⟨15350855015980496202453521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10233903343986997468302347 15350855015980496202453521)
      ·
        refine ⟨11513141261985372151840141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15350855015980496202453521 11513141261985372151840141)
        ·
          refine ⟨4317427973244514556940053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11513141261985372151840141 4317427973244514556940053)
          ·
            refine ⟨202379436245836619856565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4317427973244514556940053 202379436245836619856565)
            ·
              refine ⟨18973072148047183111553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202379436245836619856565 18973072148047183111553)
              ·
                rfl

theorem cell19_187059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_187059 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187059 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187059 prefixEnd_187059 := by exact prefixLift 187059
  have htrace : WordTrace (prefixWord ++ tailWord_187059) baseStart_187059 baseEnd_187059 := by
    simpa [prefixWord, tailWord_187059, baseEnd_187059] using wordTrace_append hprefix tailTrace_187059
  have hstable : (prefixWord ++ tailWord_187059).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187059).length < 2 ^ (prefixWord ++ tailWord_187059).sum := by decide
  have hdescent : baseEnd_187059 < baseStart_187059 := by decide
  rcases family_descends (prefixWord ++ tailWord_187059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187076 : List Nat := [2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_187076 : Nat := 118140960795 + 187076 * 2 ^ 59
def prefixEnd_187076 : Nat := 4983230072969 + 3 ^ 40 * 187076 * 2
def baseEnd_187076 : Nat := 56924389286290546956835

theorem tailTrace_187076 : CollatzResearch.WordTrace tailWord_187076 prefixEnd_187076 56924389286290546956835 := by
  unfold tailWord_187076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411611135131538441118541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4548814846842051254824721 3411611135131538441118541)
  ·
    refine ⟨1279354175674326915419453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3411611135131538441118541 1279354175674326915419453)
    ·
      refine ⟨479757815877872593282295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1279354175674326915419453 479757815877872593282295)
      ·
        refine ⟨719636723816808889923443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479757815877872593282295 719636723816808889923443)
        ·
          refine ⟨1079455085725213334885165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719636723816808889923443 1079455085725213334885165)
          ·
            refine ⟨404795657146955000581937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079455085725213334885165 404795657146955000581937)
            ·
              refine ⟨303596742860216250436453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404795657146955000581937 303596742860216250436453)
              ·
                refine ⟨56924389286290546956835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303596742860216250436453 56924389286290546956835)
                ·
                  rfl

theorem cell19_187076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_187076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187076 prefixEnd_187076 := by exact prefixLift 187076
  have htrace : WordTrace (prefixWord ++ tailWord_187076) baseStart_187076 baseEnd_187076 := by
    simpa [prefixWord, tailWord_187076, baseEnd_187076] using wordTrace_append hprefix tailTrace_187076
  have hstable : (prefixWord ++ tailWord_187076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187076).length < 2 ^ (prefixWord ++ tailWord_187076).sum := by decide
  have hdescent : baseEnd_187076 < baseStart_187076 := by decide
  rcases family_descends (prefixWord ++ tailWord_187076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187209 : List Nat := [1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_187209 : Nat := 118140960795 + 187209 * 2 ^ 59
def prefixEnd_187209 : Nat := 4983230072969 + 3 ^ 40 * 187209 * 2
def baseEnd_187209 : Nat := 56964859168985646000917

theorem tailTrace_187209 : CollatzResearch.WordTrace tailWord_187209 prefixEnd_187209 56964859168985646000917 := by
  unfold tailWord_187209
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828073178781240596828681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4552048785854160397885787 6828073178781240596828681)
  ·
    refine ⟨5121054884085930447621511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6828073178781240596828681 5121054884085930447621511)
    ·
      refine ⟨7681582326128895671432267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121054884085930447621511 7681582326128895671432267)
      ·
        refine ⟨11522373489193343507148401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681582326128895671432267 11522373489193343507148401)
        ·
          refine ⟨8641780116895007630361301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11522373489193343507148401 8641780116895007630361301)
          ·
            refine ⟨202541721489726741336593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8641780116895007630361301 202541721489726741336593)
            ·
              refine ⟨151906291117295056002445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202541721489726741336593 151906291117295056002445)
              ·
                refine ⟨56964859168985646000917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151906291117295056002445 56964859168985646000917)
                ·
                  rfl

theorem cell19_187209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_187209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187209 prefixEnd_187209 := by exact prefixLift 187209
  have htrace : WordTrace (prefixWord ++ tailWord_187209) baseStart_187209 baseEnd_187209 := by
    simpa [prefixWord, tailWord_187209, baseEnd_187209] using wordTrace_append hprefix tailTrace_187209
  have hstable : (prefixWord ++ tailWord_187209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187209).length < 2 ^ (prefixWord ++ tailWord_187209).sum := by decide
  have hdescent : baseEnd_187209 < baseStart_187209 := by decide
  rcases family_descends (prefixWord ++ tailWord_187209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187228 : List Nat := [2, 2, 4, 2, 1, 3, 5]
def baseStart_187228 : Nat := 118140960795 + 187228 * 2 ^ 59
def prefixEnd_187228 : Nat := 4983230072969 + 3 ^ 40 * 187228 * 2
def baseEnd_187228 : Nat := 18990213526933077192881

theorem tailTrace_187228 : CollatzResearch.WordTrace tailWord_187228 prefixEnd_187228 18990213526933077192881 := by
  unfold tailWord_187228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414383082856203420885169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4552510777141604561180225 3414383082856203420885169)
  ·
    refine ⟨2560787312142152565663877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3414383082856203420885169 2560787312142152565663877)
    ·
      refine ⟨480147621026653606061977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2560787312142152565663877 480147621026653606061977)
      ·
        refine ⟨360110715769990204546483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480147621026653606061977 360110715769990204546483)
        ·
          refine ⟨540166073654985306819725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360110715769990204546483 540166073654985306819725)
          ·
            refine ⟨202562277620619490057397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540166073654985306819725 202562277620619490057397)
            ·
              refine ⟨18990213526933077192881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202562277620619490057397 18990213526933077192881)
              ·
                rfl

theorem cell19_187228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_187228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187228 prefixEnd_187228 := by exact prefixLift 187228
  have htrace : WordTrace (prefixWord ++ tailWord_187228) baseStart_187228 baseEnd_187228 := by
    simpa [prefixWord, tailWord_187228, baseEnd_187228] using wordTrace_append hprefix tailTrace_187228
  have hstable : (prefixWord ++ tailWord_187228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187228).length < 2 ^ (prefixWord ++ tailWord_187228).sum := by decide
  have hdescent : baseEnd_187228 < baseStart_187228 := by decide
  rcases family_descends (prefixWord ++ tailWord_187228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187249 : List Nat := [1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_187249 : Nat := 118140960795 + 187249 * 2 ^ 59
def prefixEnd_187249 : Nat := 4983230072969 + 3 ^ 40 * 187249 * 2
def baseEnd_187249 : Nat := 56977030562277405111919

theorem tailTrace_187249 : CollatzResearch.WordTrace tailWord_187249 prefixEnd_187249 56977030562277405111919 := by
  unfold tailWord_187249
  simp only [CollatzResearch.WordTrace]
  refine ⟨6829532098636327428284801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4553021399090884952189867 6829532098636327428284801)
  ·
    refine ⟨5122149073977245571213601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6829532098636327428284801 5122149073977245571213601)
    ·
      refine ⟨3841611805482934178410201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5122149073977245571213601 3841611805482934178410201)
      ·
        refine ⟨2881208854112200633807651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3841611805482934178410201 2881208854112200633807651)
        ·
          refine ⟨4321813281168300950711477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881208854112200633807651 4321813281168300950711477)
          ·
            refine ⟨405169995109528214129201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4321813281168300950711477 405169995109528214129201)
            ·
              refine ⟨303877496332146160596901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405169995109528214129201 303877496332146160596901)
              ·
                refine ⟨56977030562277405111919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303877496332146160596901 56977030562277405111919)
                ·
                  rfl

theorem cell19_187249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_187249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187249 prefixEnd_187249 := by exact prefixLift 187249
  have htrace : WordTrace (prefixWord ++ tailWord_187249) baseStart_187249 baseEnd_187249 := by
    simpa [prefixWord, tailWord_187249, baseEnd_187249] using wordTrace_append hprefix tailTrace_187249
  have hstable : (prefixWord ++ tailWord_187249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187249).length < 2 ^ (prefixWord ++ tailWord_187249).sum := by decide
  have hdescent : baseEnd_187249 < baseStart_187249 := by decide
  rcases family_descends (prefixWord ++ tailWord_187249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187251 : List Nat := [1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_187251 : Nat := 118140960795 + 187251 * 2 ^ 59
def prefixEnd_187251 : Nat := 4983230072969 + 3 ^ 40 * 187251 * 2
def baseEnd_187251 : Nat := 56977639131941993067469

theorem tailTrace_187251 : CollatzResearch.WordTrace tailWord_187251 prefixEnd_187251 56977639131941993067469 := by
  unfold tailWord_187251
  simp only [CollatzResearch.WordTrace]
  refine ⟨6829605044629081769857607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4553070029752721179905071 6829605044629081769857607)
  ·
    refine ⟨10244407566943622654786411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6829605044629081769857607 10244407566943622654786411)
    ·
      refine ⟨15366611350415433982179617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10244407566943622654786411 15366611350415433982179617)
      ·
        refine ⟨11524958512811575486634713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15366611350415433982179617 11524958512811575486634713)
        ·
          refine ⟨8643718884608681614976035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11524958512811575486634713 8643718884608681614976035)
          ·
            refine ⟨12965578326913022422464053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643718884608681614976035 12965578326913022422464053)
            ·
              refine ⟨1215522968148095852106005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12965578326913022422464053 1215522968148095852106005)
              ·
                refine ⟨56977639131941993067469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1215522968148095852106005 56977639131941993067469)
                ·
                  rfl

theorem cell19_187251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_187251 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187251 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187251 prefixEnd_187251 := by exact prefixLift 187251
  have htrace : WordTrace (prefixWord ++ tailWord_187251) baseStart_187251 baseEnd_187251 := by
    simpa [prefixWord, tailWord_187251, baseEnd_187251] using wordTrace_append hprefix tailTrace_187251
  have hstable : (prefixWord ++ tailWord_187251).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187251).length < 2 ^ (prefixWord ++ tailWord_187251).sum := by decide
  have hdescent : baseEnd_187251 < baseStart_187251 := by decide
  rcases family_descends (prefixWord ++ tailWord_187251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187403 : List Nat := [1, 1, 1, 1, 6, 2, 7]
def baseStart_187403 : Nat := 118140960795 + 187403 * 2 ^ 59
def prefixEnd_187403 : Nat := 4983230072969 + 3 ^ 40 * 187403 * 2
def baseEnd_187403 : Nat := 19007963475483559229759

theorem tailTrace_187403 : CollatzResearch.WordTrace tailWord_187403 prefixEnd_187403 19007963475483559229759 := by
  unfold tailWord_187403
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835148940078411729390863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4556765960052274486260575 6835148940078411729390863)
  ·
    refine ⟨10252723410117617594086295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6835148940078411729390863 10252723410117617594086295)
    ·
      refine ⟨15379085115176426391129443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10252723410117617594086295 15379085115176426391129443)
      ·
        refine ⟨23068627672764639586694165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15379085115176426391129443 23068627672764639586694165)
        ·
          refine ⟨1081341922160842480626289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23068627672764639586694165 1081341922160842480626289)
          ·
            refine ⟨811006441620631860469717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081341922160842480626289 811006441620631860469717)
            ·
              refine ⟨19007963475483559229759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 811006441620631860469717 19007963475483559229759)
              ·
                rfl

theorem cell19_187403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_187403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187403 prefixEnd_187403 := by exact prefixLift 187403
  have htrace : WordTrace (prefixWord ++ tailWord_187403) baseStart_187403 baseEnd_187403 := by
    simpa [prefixWord, tailWord_187403, baseEnd_187403] using wordTrace_append hprefix tailTrace_187403
  have hstable : (prefixWord ++ tailWord_187403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187403).length < 2 ^ (prefixWord ++ tailWord_187403).sum := by decide
  have hdescent : baseEnd_187403 < baseStart_187403 := by decide
  rcases family_descends (prefixWord ++ tailWord_187403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187441 : List Nat := [1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_187441 : Nat := 118140960795 + 187441 * 2 ^ 59
def prefixEnd_187441 : Nat := 4983230072969 + 3 ^ 40 * 187441 * 2
def baseEnd_187441 : Nat := 57035453250077848844729

theorem tailTrace_187441 : CollatzResearch.WordTrace tailWord_187441 prefixEnd_187441 57035453250077848844729 := by
  unfold tailWord_187441
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836534913940744219274177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4557689942627162812849451 6836534913940744219274177)
  ·
    refine ⟨5127401185455558164455633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6836534913940744219274177 5127401185455558164455633)
    ·
      refine ⟨3845550889091668623341725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5127401185455558164455633 3845550889091668623341725)
      ·
        refine ⟨1442081583409375733753147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3845550889091668623341725 1442081583409375733753147)
        ·
          refine ⟨2163122375114063600629721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442081583409375733753147 2163122375114063600629721)
          ·
            refine ⟨1622341781335547700472291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163122375114063600629721 1622341781335547700472291)
            ·
              refine ⟨2433512672003321550708437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622341781335547700472291 2433512672003321550708437)
              ·
                refine ⟨57035453250077848844729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2433512672003321550708437 57035453250077848844729)
                ·
                  rfl

theorem cell19_187441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_187441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187441 prefixEnd_187441 := by exact prefixLift 187441
  have htrace : WordTrace (prefixWord ++ tailWord_187441) baseStart_187441 baseEnd_187441 := by
    simpa [prefixWord, tailWord_187441, baseEnd_187441] using wordTrace_append hprefix tailTrace_187441
  have hstable : (prefixWord ++ tailWord_187441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187441).length < 2 ^ (prefixWord ++ tailWord_187441).sum := by decide
  have hdescent : baseEnd_187441 < baseStart_187441 := by decide
  rcases family_descends (prefixWord ++ tailWord_187441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187517 : List Nat := [1, 4, 1, 1, 3, 1, 8]
def baseStart_187517 : Nat := 118140960795 + 187517 * 2 ^ 59
def prefixEnd_187517 : Nat := 4983230072969 + 3 ^ 40 * 187517 * 2
def baseEnd_187517 : Nat := 19019526299110730385211

theorem tailTrace_187517 : CollatzResearch.WordTrace tailWord_187517 prefixEnd_187517 19019526299110730385211 := by
  unfold tailWord_187517
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839306861665409199040805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4559537907776939466027203 6839306861665409199040805)
  ·
    refine ⟨1282370036562264224820151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6839306861665409199040805 1282370036562264224820151)
    ·
      refine ⟨1923555054843396337230227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282370036562264224820151 1923555054843396337230227)
      ·
        refine ⟨2885332582265094505845341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923555054843396337230227 2885332582265094505845341)
        ·
          refine ⟨1081999718349410439692003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2885332582265094505845341 1081999718349410439692003)
          ·
            refine ⟨1622999577524115659538005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081999718349410439692003 1622999577524115659538005)
            ·
              refine ⟨19019526299110730385211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1622999577524115659538005 19019526299110730385211)
              ·
                rfl

theorem cell19_187517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_187517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187517 prefixEnd_187517 := by exact prefixLift 187517
  have htrace : WordTrace (prefixWord ++ tailWord_187517) baseStart_187517 baseEnd_187517 := by
    simpa [prefixWord, tailWord_187517, baseEnd_187517] using wordTrace_append hprefix tailTrace_187517
  have hstable : (prefixWord ++ tailWord_187517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187517).length < 2 ^ (prefixWord ++ tailWord_187517).sum := by decide
  have hdescent : baseEnd_187517 < baseStart_187517 := by decide
  rcases family_descends (prefixWord ++ tailWord_187517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187631 : List Nat := [1, 1, 2, 1, 7, 7]
def baseStart_187631 : Nat := 118140960795 + 187631 * 2 ^ 59
def prefixEnd_187631 : Nat := 4983230072969 + 3 ^ 40 * 187631 * 2
def baseEnd_187631 : Nat := 6343696374245967180221

theorem tailTrace_187631 : CollatzResearch.WordTrace tailWord_187631 prefixEnd_187631 6343696374245967180221 := by
  unfold tailWord_187631
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843464783252406668690747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4562309855501604445793831 6843464783252406668690747)
  ·
    refine ⟨10265197174878610003036121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6843464783252406668690747 10265197174878610003036121)
    ·
      refine ⟨7698897881158957502277091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10265197174878610003036121 7698897881158957502277091)
      ·
        refine ⟨11548346821738436253415637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7698897881158957502277091 11548346821738436253415637)
        ·
          refine ⟨270664378634494599689429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11548346821738436253415637 270664378634494599689429)
          ·
            refine ⟨6343696374245967180221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 270664378634494599689429 6343696374245967180221)
            ·
              rfl

theorem cell19_187631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_187631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187631 prefixEnd_187631 := by exact prefixLift 187631
  have htrace : WordTrace (prefixWord ++ tailWord_187631) baseStart_187631 baseEnd_187631 := by
    simpa [prefixWord, tailWord_187631, baseEnd_187631] using wordTrace_append hprefix tailTrace_187631
  have hstable : (prefixWord ++ tailWord_187631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187631).length < 2 ^ (prefixWord ++ tailWord_187631).sum := by decide
  have hdescent : baseEnd_187631 < baseStart_187631 := by decide
  rcases family_descends (prefixWord ++ tailWord_187631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187646 : List Nat := [4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_187646 : Nat := 118140960795 + 187646 * 2 ^ 59
def prefixEnd_187646 : Nat := 4983230072969 + 3 ^ 40 * 187646 * 2
def baseEnd_187646 : Nat := 57097831640698114288615

theorem tailTrace_187646 : CollatzResearch.WordTrace tailWord_187646 prefixEnd_187646 57097831640698114288615 := by
  unfold tailWord_187646
  simp only [CollatzResearch.WordTrace]
  refine ⟨855501484774758028810849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4562674585465376153657861 855501484774758028810849)
  ·
    refine ⟨641626113581068521608137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 855501484774758028810849 641626113581068521608137)
    ·
      refine ⟨481219585185801391206103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 641626113581068521608137 481219585185801391206103)
      ·
        refine ⟨721829377778702086809155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481219585185801391206103 721829377778702086809155)
        ·
          refine ⟨1082744066668053130213733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721829377778702086809155 1082744066668053130213733)
          ·
            refine ⟨203014512500259961915075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1082744066668053130213733 203014512500259961915075)
            ·
              refine ⟨304521768750389942872613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203014512500259961915075 304521768750389942872613)
              ·
                refine ⟨57097831640698114288615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304521768750389942872613 57097831640698114288615)
                ·
                  rfl

theorem cell19_187646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_187646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187646 prefixEnd_187646 := by exact prefixLift 187646
  have htrace : WordTrace (prefixWord ++ tailWord_187646) baseStart_187646 baseEnd_187646 := by
    simpa [prefixWord, tailWord_187646, baseEnd_187646] using wordTrace_append hprefix tailTrace_187646
  have hstable : (prefixWord ++ tailWord_187646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187646).length < 2 ^ (prefixWord ++ tailWord_187646).sum := by decide
  have hdescent : baseEnd_187646 < baseStart_187646 := by decide
  rcases family_descends (prefixWord ++ tailWord_187646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187724 : List Nat := [2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_187724 : Nat := 118140960795 + 187724 * 2 ^ 59
def prefixEnd_187724 : Nat := 4983230072969 + 3 ^ 40 * 187724 * 2
def baseEnd_187724 : Nat := 57121565857617044555069

theorem tailTrace_187724 : CollatzResearch.WordTrace tailWord_187724 prefixEnd_187724 57121565857617044555069 := by
  unfold tailWord_187724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423428385957741775913113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4564571181276989034550817 3423428385957741775913113)
  ·
    refine ⟨2567571289468306331934835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3423428385957741775913113 2567571289468306331934835)
    ·
      refine ⟨3851356934202459497902253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567571289468306331934835 3851356934202459497902253)
      ·
        refine ⟨1444258850325922311713345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3851356934202459497902253 1444258850325922311713345)
        ·
          refine ⟨1083194137744441733785009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1444258850325922311713345 1083194137744441733785009)
          ·
            refine ⟨812395603308331300338757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083194137744441733785009 812395603308331300338757)
            ·
              refine ⟨152324175620312118813517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 812395603308331300338757 152324175620312118813517)
              ·
                refine ⟨57121565857617044555069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152324175620312118813517 57121565857617044555069)
                ·
                  rfl

theorem cell19_187724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_187724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187724 prefixEnd_187724 := by exact prefixLift 187724
  have htrace : WordTrace (prefixWord ++ tailWord_187724) baseStart_187724 baseEnd_187724 := by
    simpa [prefixWord, tailWord_187724, baseEnd_187724] using wordTrace_append hprefix tailTrace_187724
  have hstable : (prefixWord ++ tailWord_187724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187724).length < 2 ^ (prefixWord ++ tailWord_187724).sum := by decide
  have hdescent : baseEnd_187724 < baseStart_187724 := by decide
  rcases family_descends (prefixWord ++ tailWord_187724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187726 : List Nat := [4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_187726 : Nat := 118140960795 + 187726 * 2 ^ 59
def prefixEnd_187726 : Nat := 4983230072969 + 3 ^ 40 * 187726 * 2
def baseEnd_187726 : Nat := 57122174427281632510619

theorem tailTrace_187726 : CollatzResearch.WordTrace tailWord_187726 prefixEnd_187726 57122174427281632510619 := by
  unfold tailWord_187726
  simp only [CollatzResearch.WordTrace]
  refine ⟨855866214738529736674879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4564619811938825262266021 855866214738529736674879)
  ·
    refine ⟨1283799322107794605012319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 855866214738529736674879 1283799322107794605012319)
    ·
      refine ⟨1925698983161691907518479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283799322107794605012319 1925698983161691907518479)
      ·
        refine ⟨2888548474742537861277719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925698983161691907518479 2888548474742537861277719)
        ·
          refine ⟨4332822712113806791916579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2888548474742537861277719 4332822712113806791916579)
          ·
            refine ⟨6499234068170710187874869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4332822712113806791916579 6499234068170710187874869)
            ·
              refine ⟨609303193891004080113269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6499234068170710187874869 609303193891004080113269)
              ·
                refine ⟨57122174427281632510619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 609303193891004080113269 57122174427281632510619)
                ·
                  rfl

theorem cell19_187726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_187726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187726 prefixEnd_187726 := by exact prefixLift 187726
  have htrace : WordTrace (prefixWord ++ tailWord_187726) baseStart_187726 baseEnd_187726 := by
    simpa [prefixWord, tailWord_187726, baseEnd_187726] using wordTrace_append hprefix tailTrace_187726
  have hstable : (prefixWord ++ tailWord_187726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187726).length < 2 ^ (prefixWord ++ tailWord_187726).sum := by decide
  have hdescent : baseEnd_187726 < baseStart_187726 := by decide
  rcases family_descends (prefixWord ++ tailWord_187726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187783 : List Nat := [1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_187783 : Nat := 118140960795 + 187783 * 2 ^ 59
def prefixEnd_187783 : Nat := 4983230072969 + 3 ^ 40 * 187783 * 2
def baseEnd_187783 : Nat := 57139518662722389243797

theorem tailTrace_187783 : CollatzResearch.WordTrace tailWord_187783 prefixEnd_187783 57139518662722389243797 := by
  unfold tailWord_187783
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849008678701736628224003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4566005785801157752149335 6849008678701736628224003)
  ·
    refine ⟨10273513018052604942336005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6849008678701736628224003 10273513018052604942336005)
    ·
      refine ⟨1926283690884863426688001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10273513018052604942336005 1926283690884863426688001)
      ·
        refine ⟨1444712768163647570016001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1926283690884863426688001 1444712768163647570016001)
        ·
          refine ⟨1083534576122735677512001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1444712768163647570016001 1083534576122735677512001)
          ·
            refine ⟨812650932092051758134001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083534576122735677512001 812650932092051758134001)
            ·
              refine ⟨609488199069038818600501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812650932092051758134001 609488199069038818600501)
              ·
                refine ⟨57139518662722389243797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 609488199069038818600501 57139518662722389243797)
                ·
                  rfl

theorem cell19_187783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_187783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187783 prefixEnd_187783 := by exact prefixLift 187783
  have htrace : WordTrace (prefixWord ++ tailWord_187783) baseStart_187783 baseEnd_187783 := by
    simpa [prefixWord, tailWord_187783, baseEnd_187783] using wordTrace_append hprefix tailTrace_187783
  have hstable : (prefixWord ++ tailWord_187783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187783).length < 2 ^ (prefixWord ++ tailWord_187783).sum := by decide
  have hdescent : baseEnd_187783 < baseStart_187783 := by decide
  rcases family_descends (prefixWord ++ tailWord_187783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187800 : List Nat := [2, 1, 2, 5, 3, 6]
def baseStart_187800 : Nat := 118140960795 + 187800 * 2 ^ 59
def prefixEnd_187800 : Nat := 4983230072969 + 3 ^ 40 * 187800 * 2
def baseEnd_187800 : Nat := 6349410167207931873997

theorem tailTrace_187800 : CollatzResearch.WordTrace tailWord_187800 prefixEnd_187800 6349410167207931873997 := by
  unfold tailWord_187800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424814359820074265796427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4566419146426765687728569 3424814359820074265796427)
  ·
    refine ⟨5137221539730111398694641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3424814359820074265796427 5137221539730111398694641)
    ·
      refine ⟨3852916154797583549020981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5137221539730111398694641 3852916154797583549020981)
      ·
        refine ⟨361210889512273457720717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3852916154797583549020981 361210889512273457720717)
        ·
          refine ⟨135454083567102546645269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361210889512273457720717 135454083567102546645269)
          ·
            refine ⟨6349410167207931873997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135454083567102546645269 6349410167207931873997)
            ·
              rfl

theorem cell19_187800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_187800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187800 prefixEnd_187800 := by exact prefixLift 187800
  have htrace : WordTrace (prefixWord ++ tailWord_187800) baseStart_187800 baseEnd_187800 := by
    simpa [prefixWord, tailWord_187800, baseEnd_187800] using wordTrace_append hprefix tailTrace_187800
  have hstable : (prefixWord ++ tailWord_187800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187800).length < 2 ^ (prefixWord ++ tailWord_187800).sum := by decide
  have hdescent : baseEnd_187800 < baseStart_187800 := by decide
  rcases family_descends (prefixWord ++ tailWord_187800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187836 : List Nat := [2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_187836 : Nat := 118140960795 + 187836 * 2 ^ 59
def prefixEnd_187836 : Nat := 4983230072969 + 3 ^ 40 * 187836 * 2
def baseEnd_187836 : Nat := 57155645758833970065875

theorem tailTrace_187836 : CollatzResearch.WordTrace tailWord_187836 prefixEnd_187836 57155645758833970065875 := by
  unfold tailWord_187836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425470873754863339951681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4567294498339817786602241 3425470873754863339951681)
  ·
    refine ⟨2569103155316147504963761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3425470873754863339951681 2569103155316147504963761)
    ·
      refine ⟨1926827366487110628722821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2569103155316147504963761 1926827366487110628722821)
      ·
        refine ⟨361280131216333242885529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1926827366487110628722821 361280131216333242885529)
        ·
          refine ⟨270960098412249932164147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361280131216333242885529 270960098412249932164147)
          ·
            refine ⟨406440147618374898246221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270960098412249932164147 406440147618374898246221)
            ·
              refine ⟨152415055356890586842333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406440147618374898246221 152415055356890586842333)
              ·
                refine ⟨57155645758833970065875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152415055356890586842333 57155645758833970065875)
                ·
                  rfl

theorem cell19_187836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_187836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187836 prefixEnd_187836 := by exact prefixLift 187836
  have htrace : WordTrace (prefixWord ++ tailWord_187836) baseStart_187836 baseEnd_187836 := by
    simpa [prefixWord, tailWord_187836, baseEnd_187836] using wordTrace_append hprefix tailTrace_187836
  have hstable : (prefixWord ++ tailWord_187836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187836).length < 2 ^ (prefixWord ++ tailWord_187836).sum := by decide
  have hdescent : baseEnd_187836 < baseStart_187836 := by decide
  rcases family_descends (prefixWord ++ tailWord_187836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187893 : List Nat := [1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_187893 : Nat := 118140960795 + 187893 * 2 ^ 59
def prefixEnd_187893 : Nat := 4983230072969 + 3 ^ 40 * 187893 * 2
def baseEnd_187893 : Nat := 57172989994274726799053

theorem tailTrace_187893 : CollatzResearch.WordTrace tailWord_187893 prefixEnd_187893 57172989994274726799053 := by
  unfold tailWord_187893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6853020708303225414728333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4568680472202150276485555 6853020708303225414728333)
  ·
    refine ⟨2569882765613709530523125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6853020708303225414728333 2569882765613709530523125)
    ·
      refine ⟨240926509276285268486543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2569882765613709530523125 240926509276285268486543)
      ·
        refine ⟨361389763914427902729815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240926509276285268486543 361389763914427902729815)
        ·
          refine ⟨542084645871641854094723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361389763914427902729815 542084645871641854094723)
          ·
            refine ⟨813126968807462781142085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542084645871641854094723 813126968807462781142085)
            ·
              refine ⟨152461306651399271464141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 813126968807462781142085 152461306651399271464141)
              ·
                refine ⟨57172989994274726799053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152461306651399271464141 57172989994274726799053)
                ·
                  rfl

theorem cell19_187893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_187893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187893 prefixEnd_187893 := by exact prefixLift 187893
  have htrace : WordTrace (prefixWord ++ tailWord_187893) baseStart_187893 baseEnd_187893 := by
    simpa [prefixWord, tailWord_187893, baseEnd_187893] using wordTrace_append hprefix tailTrace_187893
  have hstable : (prefixWord ++ tailWord_187893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187893).length < 2 ^ (prefixWord ++ tailWord_187893).sum := by decide
  have hdescent : baseEnd_187893 < baseStart_187893 := by decide
  rcases family_descends (prefixWord ++ tailWord_187893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187899 : List Nat := [1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_187899 : Nat := 118140960795 + 187899 * 2 ^ 59
def prefixEnd_187899 : Nat := 4983230072969 + 3 ^ 40 * 187899 * 2
def baseEnd_187899 : Nat := 57174815703268490665703

theorem tailTrace_187899 : CollatzResearch.WordTrace tailWord_187899 prefixEnd_187899 57174815703268490665703 := by
  unfold tailWord_187899
  simp only [CollatzResearch.WordTrace]
  refine ⟨6853239546281488439446751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4568826364187658959631167 6853239546281488439446751)
  ·
    refine ⟨10279859319422232659170127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6853239546281488439446751 10279859319422232659170127)
    ·
      refine ⟨15419788979133348988755191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10279859319422232659170127 15419788979133348988755191)
      ·
        refine ⟨23129683468700023483132787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15419788979133348988755191 23129683468700023483132787)
        ·
          refine ⟨34694525203050035224699181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23129683468700023483132787 34694525203050035224699181)
          ·
            refine ⟨13010446951143763209262193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34694525203050035224699181 13010446951143763209262193)
            ·
              refine ⟨9757835213357822406946645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13010446951143763209262193 9757835213357822406946645)
              ·
                refine ⟨57174815703268490665703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9757835213357822406946645 57174815703268490665703)
                ·
                  rfl

theorem cell19_187899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_187899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187899 prefixEnd_187899 := by exact prefixLift 187899
  have htrace : WordTrace (prefixWord ++ tailWord_187899) baseStart_187899 baseEnd_187899 := by
    simpa [prefixWord, tailWord_187899, baseEnd_187899] using wordTrace_append hprefix tailTrace_187899
  have hstable : (prefixWord ++ tailWord_187899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187899).length < 2 ^ (prefixWord ++ tailWord_187899).sum := by decide
  have hdescent : baseEnd_187899 < baseStart_187899 := by decide
  rcases family_descends (prefixWord ++ tailWord_187899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187975 : List Nat := [1, 1, 4, 1, 12]
def baseStart_187975 : Nat := 118140960795 + 187975 * 2 ^ 59
def prefixEnd_187975 : Nat := 4983230072969 + 3 ^ 40 * 187975 * 2
def baseEnd_187975 : Nat := 2118442272241586406541

theorem tailTrace_187975 : CollatzResearch.WordTrace tailWord_187975 prefixEnd_187975 2118442272241586406541 := by
  unfold tailWord_187975
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856011494006153419213379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4570674329337435612808919 6856011494006153419213379)
  ·
    refine ⟨10284017241009230128820069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6856011494006153419213379 10284017241009230128820069)
    ·
      refine ⟨1928253232689230649153763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10284017241009230128820069 1928253232689230649153763)
      ·
        refine ⟨2892379849033845973730645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928253232689230649153763 2892379849033845973730645)
        ·
          refine ⟨2118442272241586406541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2892379849033845973730645 2118442272241586406541)
          ·
            rfl

theorem cell19_187975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 12].length) (baseStart_187975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_187975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_187975 prefixEnd_187975 := by exact prefixLift 187975
  have htrace : WordTrace (prefixWord ++ tailWord_187975) baseStart_187975 baseEnd_187975 := by
    simpa [prefixWord, tailWord_187975, baseEnd_187975] using wordTrace_append hprefix tailTrace_187975
  have hstable : (prefixWord ++ tailWord_187975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187975).length < 2 ^ (prefixWord ++ tailWord_187975).sum := by decide
  have hdescent : baseEnd_187975 < baseStart_187975 := by decide
  rcases family_descends (prefixWord ++ tailWord_187975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188032 : List Nat := [2, 1, 1, 2, 1, 4, 8]
def baseStart_188032 : Nat := 118140960795 + 188032 * 2 ^ 59
def prefixEnd_188032 : Nat := 4983230072969 + 3 ^ 40 * 188032 * 2
def baseEnd_188032 : Nat := 19071761861987863236595

theorem tailTrace_188032 : CollatzResearch.WordTrace tailWord_188032 prefixEnd_188032 19071761861987863236595 := by
  unfold tailWord_188032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429045227399826077019175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4572060303199768102692233 3429045227399826077019175)
  ·
    refine ⟨5143567841099739115528763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3429045227399826077019175 5143567841099739115528763)
    ·
      refine ⟨7715351761649608673293145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143567841099739115528763 7715351761649608673293145)
      ·
        refine ⟨5786513821237206504969859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7715351761649608673293145 5786513821237206504969859)
        ·
          refine ⟨8679770731855809757454789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5786513821237206504969859 8679770731855809757454789)
          ·
            refine ⟨1627457012222964329522773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8679770731855809757454789 1627457012222964329522773)
            ·
              refine ⟨19071761861987863236595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1627457012222964329522773 19071761861987863236595)
              ·
                rfl

theorem cell19_188032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_188032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188032 prefixEnd_188032 := by exact prefixLift 188032
  have htrace : WordTrace (prefixWord ++ tailWord_188032) baseStart_188032 baseEnd_188032 := by
    simpa [prefixWord, tailWord_188032, baseEnd_188032] using wordTrace_append hprefix tailTrace_188032
  have hstable : (prefixWord ++ tailWord_188032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188032).length < 2 ^ (prefixWord ++ tailWord_188032).sum := by decide
  have hdescent : baseEnd_188032 < baseStart_188032 := by decide
  rcases family_descends (prefixWord ++ tailWord_188032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188068 : List Nat := [2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_188068 : Nat := 118140960795 + 188068 * 2 ^ 59
def prefixEnd_188068 : Nat := 4983230072969 + 3 ^ 40 * 188068 * 2
def baseEnd_188068 : Nat := 57226239839926172909687

theorem tailTrace_188068 : CollatzResearch.WordTrace tailWord_188068 prefixEnd_188068 57226239839926172909687 := by
  unfold tailWord_188068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429701741334615151174429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4572935655112820201565905 3429701741334615151174429)
  ·
    refine ⟨1286138153000480681690411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3429701741334615151174429 1286138153000480681690411)
    ·
      refine ⟨1929207229500721022535617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286138153000480681690411 1929207229500721022535617)
      ·
        refine ⟨1446905422125540766901713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1929207229500721022535617 1446905422125540766901713)
        ·
          refine ⟨1085179066594155575176285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1446905422125540766901713 1085179066594155575176285)
          ·
            refine ⟨406942149972808340691107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1085179066594155575176285 406942149972808340691107)
            ·
              refine ⟨610413224959212511036661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406942149972808340691107 610413224959212511036661)
              ·
                refine ⟨57226239839926172909687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610413224959212511036661 57226239839926172909687)
                ·
                  rfl

theorem cell19_188068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_188068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188068 prefixEnd_188068 := by exact prefixLift 188068
  have htrace : WordTrace (prefixWord ++ tailWord_188068) baseStart_188068 baseEnd_188068 := by
    simpa [prefixWord, tailWord_188068, baseEnd_188068] using wordTrace_append hprefix tailTrace_188068
  have hstable : (prefixWord ++ tailWord_188068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188068).length < 2 ^ (prefixWord ++ tailWord_188068).sum := by decide
  have hdescent : baseEnd_188068 < baseStart_188068 := by decide
  rcases family_descends (prefixWord ++ tailWord_188068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188085 : List Nat := [1, 3, 3, 3, 2, 2, 5]
def baseStart_188085 : Nat := 118140960795 + 188085 * 2 ^ 59
def prefixEnd_188085 : Nat := 4983230072969 + 3 ^ 40 * 188085 * 2
def baseEnd_188085 : Nat := 19077137560691723510621

theorem tailTrace_188085 : CollatzResearch.WordTrace tailWord_188085 prefixEnd_188085 19077137560691723510621 := by
  unfold tailWord_188085
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860023523607642205717709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4573349015738428137145139 6860023523607642205717709)
  ·
    refine ⟨2572508821352865827144141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6860023523607642205717709 2572508821352865827144141)
    ·
      refine ⟨964690808007324685179053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2572508821352865827144141 964690808007324685179053)
      ·
        refine ⟨361759053002746756942145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 964690808007324685179053 361759053002746756942145)
        ·
          refine ⟨271319289752060067706609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361759053002746756942145 271319289752060067706609)
          ·
            refine ⟨203489467314045050779957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271319289752060067706609 203489467314045050779957)
            ·
              refine ⟨19077137560691723510621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203489467314045050779957 19077137560691723510621)
              ·
                rfl

theorem cell19_188085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_188085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188085 prefixEnd_188085 := by exact prefixLift 188085
  have htrace : WordTrace (prefixWord ++ tailWord_188085) baseStart_188085 baseEnd_188085 := by
    simpa [prefixWord, tailWord_188085, baseEnd_188085] using wordTrace_append hprefix tailTrace_188085
  have hstable : (prefixWord ++ tailWord_188085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188085).length < 2 ^ (prefixWord ++ tailWord_188085).sum := by decide
  have hdescent : baseEnd_188085 < baseStart_188085 := by decide
  rcases family_descends (prefixWord ++ tailWord_188085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188087 : List Nat := [1, 1, 3, 1, 5, 3, 5]
def baseStart_188087 : Nat := 118140960795 + 188087 * 2 ^ 59
def prefixEnd_188087 : Nat := 4983230072969 + 3 ^ 40 * 188087 * 2
def baseEnd_188087 : Nat := 19077340417246586162471

theorem tailTrace_188087 : CollatzResearch.WordTrace tailWord_188087 prefixEnd_188087 19077340417246586162471 := by
  unfold tailWord_188087
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860096469600396547290515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4573397646400264364860343 6860096469600396547290515)
  ·
    refine ⟨10290144704400594820935773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860096469600396547290515 10290144704400594820935773)
    ·
      refine ⟨3858804264150223057850915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10290144704400594820935773 3858804264150223057850915)
      ·
        refine ⟨5788206396225334586776373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858804264150223057850915 5788206396225334586776373)
        ·
          refine ⟨542644349646125117510285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5788206396225334586776373 542644349646125117510285)
          ·
            refine ⟨203491631117296919066357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 542644349646125117510285 203491631117296919066357)
            ·
              refine ⟨19077340417246586162471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203491631117296919066357 19077340417246586162471)
              ·
                rfl

theorem cell19_188087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_188087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188087 prefixEnd_188087 := by exact prefixLift 188087
  have htrace : WordTrace (prefixWord ++ tailWord_188087) baseStart_188087 baseEnd_188087 := by
    simpa [prefixWord, tailWord_188087, baseEnd_188087] using wordTrace_append hprefix tailTrace_188087
  have hstable : (prefixWord ++ tailWord_188087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188087).length < 2 ^ (prefixWord ++ tailWord_188087).sum := by decide
  have hdescent : baseEnd_188087 < baseStart_188087 := by decide
  rcases family_descends (prefixWord ++ tailWord_188087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188089 : List Nat := [1, 2, 1, 4, 1, 1, 9]
def baseStart_188089 : Nat := 118140960795 + 188089 * 2 ^ 59
def prefixEnd_188089 : Nat := 4983230072969 + 3 ^ 40 * 188089 * 2
def baseEnd_188089 : Nat := 19077543273801448814321

theorem tailTrace_188089 : CollatzResearch.WordTrace tailWord_188089 prefixEnd_188089 19077543273801448814321 := by
  unfold tailWord_188089
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860169415593150888863321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4573446277062100592575547 6860169415593150888863321)
  ·
    refine ⟨5145127061694863166647491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6860169415593150888863321 5145127061694863166647491)
    ·
      refine ⟨7717690592542294749971237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145127061694863166647491 7717690592542294749971237)
      ·
        refine ⟨1447066986101680265619607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7717690592542294749971237 1447066986101680265619607)
        ·
          refine ⟨2170600479152520398429411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447066986101680265619607 2170600479152520398429411)
          ·
            refine ⟨3255900718728780597644117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170600479152520398429411 3255900718728780597644117)
            ·
              refine ⟨19077543273801448814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3255900718728780597644117 19077543273801448814321)
              ·
                rfl

theorem cell19_188089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_188089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188089 prefixEnd_188089 := by exact prefixLift 188089
  have htrace : WordTrace (prefixWord ++ tailWord_188089) baseStart_188089 baseEnd_188089 := by
    simpa [prefixWord, tailWord_188089, baseEnd_188089] using wordTrace_append hprefix tailTrace_188089
  have hstable : (prefixWord ++ tailWord_188089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188089).length < 2 ^ (prefixWord ++ tailWord_188089).sum := by decide
  have hdescent : baseEnd_188089 < baseStart_188089 := by decide
  rcases family_descends (prefixWord ++ tailWord_188089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188102 : List Nat := [6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_188102 : Nat := 118140960795 + 188102 * 2 ^ 59
def prefixEnd_188102 : Nat := 4983230072969 + 3 ^ 40 * 188102 * 2
def baseEnd_188102 : Nat := 57236585524224168154039

theorem tailTrace_188102 : CollatzResearch.WordTrace tailWord_188102 prefixEnd_188102 57236585524224168154039 := by
  unfold tailWord_188102
  simp only [CollatzResearch.WordTrace]
  refine ⟨214395111392064190908955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4573762376364036072724373 214395111392064190908955)
  ·
    refine ⟨321592667088096286363433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214395111392064190908955 321592667088096286363433)
    ·
      refine ⟨241194500316072214772575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321592667088096286363433 241194500316072214772575)
      ·
        refine ⟨361791750474108322158863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241194500316072214772575 361791750474108322158863)
        ·
          refine ⟨542687625711162483238295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361791750474108322158863 542687625711162483238295)
          ·
            refine ⟨814031438566743724857443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542687625711162483238295 814031438566743724857443)
            ·
              refine ⟨1221047157850115587286165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814031438566743724857443 1221047157850115587286165)
              ·
                refine ⟨57236585524224168154039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1221047157850115587286165 57236585524224168154039)
                ·
                  rfl

theorem cell19_188102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_188102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188102 prefixEnd_188102 := by exact prefixLift 188102
  have htrace : WordTrace (prefixWord ++ tailWord_188102) baseStart_188102 baseEnd_188102 := by
    simpa [prefixWord, tailWord_188102, baseEnd_188102] using wordTrace_append hprefix tailTrace_188102
  have hstable : (prefixWord ++ tailWord_188102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188102).length < 2 ^ (prefixWord ++ tailWord_188102).sum := by decide
  have hdescent : baseEnd_188102 < baseStart_188102 := by decide
  rcases family_descends (prefixWord ++ tailWord_188102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188127 : List Nat := [1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_188127 : Nat := 118140960795 + 188127 * 2 ^ 59
def prefixEnd_188127 : Nat := 4983230072969 + 3 ^ 40 * 188127 * 2
def baseEnd_188127 : Nat := 57244192645031517598415

theorem tailTrace_188127 : CollatzResearch.WordTrace tailWord_188127 prefixEnd_188127 57244192645031517598415 := by
  unfold tailWord_188127
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861555389455483378746635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4574370259636988919164423 6861555389455483378746635)
  ·
    refine ⟨10292333084183225068119953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6861555389455483378746635 10292333084183225068119953)
    ·
      refine ⟨7719249813137418801089965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10292333084183225068119953 7719249813137418801089965)
      ·
        refine ⟨2894718679926532050408737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7719249813137418801089965 2894718679926532050408737)
        ·
          refine ⟨2171039009944899037806553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2894718679926532050408737 2171039009944899037806553)
          ·
            refine ⟨1628279257458674278354915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171039009944899037806553 1628279257458674278354915)
            ·
              refine ⟨2442418886188011417532373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628279257458674278354915 2442418886188011417532373)
              ·
                refine ⟨57244192645031517598415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2442418886188011417532373 57244192645031517598415)
                ·
                  rfl

theorem cell19_188127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_188127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188127 prefixEnd_188127 := by exact prefixLift 188127
  have htrace : WordTrace (prefixWord ++ tailWord_188127) baseStart_188127 baseEnd_188127 := by
    simpa [prefixWord, tailWord_188127, baseEnd_188127] using wordTrace_append hprefix tailTrace_188127
  have hstable : (prefixWord ++ tailWord_188127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188127).length < 2 ^ (prefixWord ++ tailWord_188127).sum := by decide
  have hdescent : baseEnd_188127 < baseStart_188127 := by decide
  rcases family_descends (prefixWord ++ tailWord_188127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188178 : List Nat := [3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_188178 : Nat := 118140960795 + 188178 * 2 ^ 59
def prefixEnd_188178 : Nat := 4983230072969 + 3 ^ 40 * 188178 * 2
def baseEnd_188178 : Nat := 57259711171478510464943

theorem tailTrace_188178 : CollatzResearch.WordTrace tailWord_188178 prefixEnd_188178 57259711171478510464943 := by
  unfold tailWord_188178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715853878067679772213297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4575610341513812725902125 1715853878067679772213297)
  ·
    refine ⟨1286890408550759829159973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1715853878067679772213297 1286890408550759829159973)
    ·
      refine ⟨241291951603267467967495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1286890408550759829159973 241291951603267467967495)
      ·
        refine ⟨361937927404901201951243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241291951603267467967495 361937927404901201951243)
        ·
          refine ⟨542906891107351802926865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361937927404901201951243 542906891107351802926865)
          ·
            refine ⟨407180168330513852195149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542906891107351802926865 407180168330513852195149)
            ·
              refine ⟨152692563123942694573181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407180168330513852195149 152692563123942694573181)
              ·
                refine ⟨57259711171478510464943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152692563123942694573181 57259711171478510464943)
                ·
                  rfl

theorem cell19_188178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_188178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188178 prefixEnd_188178 := by exact prefixLift 188178
  have htrace : WordTrace (prefixWord ++ tailWord_188178) baseStart_188178 baseEnd_188178 := by
    simpa [prefixWord, tailWord_188178, baseEnd_188178] using wordTrace_append hprefix tailTrace_188178
  have hstable : (prefixWord ++ tailWord_188178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188178).length < 2 ^ (prefixWord ++ tailWord_188178).sum := by decide
  have hdescent : baseEnd_188178 < baseStart_188178 := by decide
  rcases family_descends (prefixWord ++ tailWord_188178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188184 : List Nat := [2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_188184 : Nat := 118140960795 + 188184 * 2 ^ 59
def prefixEnd_188184 : Nat := 4983230072969 + 3 ^ 40 * 188184 * 2
def baseEnd_188184 : Nat := 57261536880472274331593

theorem tailTrace_188184 : CollatzResearch.WordTrace tailWord_188184 prefixEnd_188184 57261536880472274331593 := by
  unfold tailWord_188184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431817175124491056785803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4575756233499321409047737 3431817175124491056785803)
  ·
    refine ⟨5147725762686736585178705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3431817175124491056785803 5147725762686736585178705)
    ·
      refine ⟨3860794322015052438884029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5147725762686736585178705 3860794322015052438884029)
      ·
        refine ⟨1447797870755644664581511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3860794322015052438884029 1447797870755644664581511)
        ·
          refine ⟨2171696806133466996872267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447797870755644664581511 2171696806133466996872267)
          ·
            refine ⟨3257545209200200495308401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171696806133466996872267 3257545209200200495308401)
            ·
              refine ⟨2443158906900150371481301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257545209200200495308401 2443158906900150371481301)
              ·
                refine ⟨57261536880472274331593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2443158906900150371481301 57261536880472274331593)
                ·
                  rfl

theorem cell19_188184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_188184 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188184 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188184 prefixEnd_188184 := by exact prefixLift 188184
  have htrace : WordTrace (prefixWord ++ tailWord_188184) baseStart_188184 baseEnd_188184 := by
    simpa [prefixWord, tailWord_188184, baseEnd_188184] using wordTrace_append hprefix tailTrace_188184
  have hstable : (prefixWord ++ tailWord_188184).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188184).length < 2 ^ (prefixWord ++ tailWord_188184).sum := by decide
  have hdescent : baseEnd_188184 < baseStart_188184 := by decide
  rcases family_descends (prefixWord ++ tailWord_188184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188237 : List Nat := [1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_188237 : Nat := 118140960795 + 188237 * 2 ^ 59
def prefixEnd_188237 : Nat := 4983230072969 + 3 ^ 40 * 188237 * 2
def baseEnd_188237 : Nat := 57277663976583855153671

theorem tailTrace_188237 : CollatzResearch.WordTrace tailWord_188237 prefixEnd_188237 57277663976583855153671 := by
  unfold tailWord_188237
  simp only [CollatzResearch.WordTrace]
  refine ⟨6865567419056972165250965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4577044946037981443500643 6865567419056972165250965)
  ·
    refine ⟨321823472768295570246139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6865567419056972165250965 321823472768295570246139)
    ·
      refine ⟨482735209152443355369209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321823472768295570246139 482735209152443355369209)
      ·
        refine ⟨362051406864332516526907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482735209152443355369209 362051406864332516526907)
        ·
          refine ⟨543077110296498774790361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362051406864332516526907 543077110296498774790361)
          ·
            refine ⟨407307832722374081092771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543077110296498774790361 407307832722374081092771)
            ·
              refine ⟨610961749083561121639157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407307832722374081092771 610961749083561121639157)
              ·
                refine ⟨57277663976583855153671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 610961749083561121639157 57277663976583855153671)
                ·
                  rfl

theorem cell19_188237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_188237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188237 prefixEnd_188237 := by exact prefixLift 188237
  have htrace : WordTrace (prefixWord ++ tailWord_188237) baseStart_188237 baseEnd_188237 := by
    simpa [prefixWord, tailWord_188237, baseEnd_188237] using wordTrace_append hprefix tailTrace_188237
  have hstable : (prefixWord ++ tailWord_188237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188237).length < 2 ^ (prefixWord ++ tailWord_188237).sum := by decide
  have hdescent : baseEnd_188237 < baseStart_188237 := by decide
  rcases family_descends (prefixWord ++ tailWord_188237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188258 : List Nat := [3, 3, 2, 1, 2, 1, 7]
def baseStart_188258 : Nat := 118140960795 + 188258 * 2 ^ 59
def prefixEnd_188258 : Nat := 4983230072969 + 3 ^ 40 * 188258 * 2
def baseEnd_188258 : Nat := 19094684652687342895649

theorem tailTrace_188258 : CollatzResearch.WordTrace tailWord_188258 prefixEnd_188258 19094684652687342895649 := by
  unfold tailWord_188258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716583337995223187941357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4577555567987261834510285 1716583337995223187941357)
  ·
    refine ⟨643718751748208695478009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1716583337995223187941357 643718751748208695478009)
    ·
      refine ⟨482789063811156521608507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643718751748208695478009 482789063811156521608507)
      ·
        refine ⟨724183595716734782412761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482789063811156521608507 724183595716734782412761)
        ·
          refine ⟨543137696787551086809571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724183595716734782412761 543137696787551086809571)
          ·
            refine ⟨814706545181326630214357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543137696787551086809571 814706545181326630214357)
            ·
              refine ⟨19094684652687342895649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 814706545181326630214357 19094684652687342895649)
              ·
                rfl

theorem cell19_188258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_188258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188258 prefixEnd_188258 := by exact prefixLift 188258
  have htrace : WordTrace (prefixWord ++ tailWord_188258) baseStart_188258 baseEnd_188258 := by
    simpa [prefixWord, tailWord_188258, baseEnd_188258] using wordTrace_append hprefix tailTrace_188258
  have hstable : (prefixWord ++ tailWord_188258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188258).length < 2 ^ (prefixWord ++ tailWord_188258).sum := by decide
  have hdescent : baseEnd_188258 < baseStart_188258 := by decide
  rcases family_descends (prefixWord ++ tailWord_188258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188277 : List Nat := [1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_188277 : Nat := 118140960795 + 188277 * 2 ^ 59
def prefixEnd_188277 : Nat := 4983230072969 + 3 ^ 40 * 188277 * 2
def baseEnd_188277 : Nat := 57289835369875614264673

theorem tailTrace_188277 : CollatzResearch.WordTrace tailWord_188277 prefixEnd_188277 57289835369875614264673 := by
  unfold tailWord_188277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867026338912058996707085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4578017559274705997804723 6867026338912058996707085)
  ·
    refine ⟨2575134877092022123765157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6867026338912058996707085 2575134877092022123765157)
    ·
      refine ⟨482837789454754148205967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2575134877092022123765157 482837789454754148205967)
      ·
        refine ⟨724256684182131222308951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482837789454754148205967 724256684182131222308951)
        ·
          refine ⟨1086385026273196833463427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724256684182131222308951 1086385026273196833463427)
          ·
            refine ⟨1629577539409795250195141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086385026273196833463427 1629577539409795250195141)
            ·
              refine ⟨305545788639336609411589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1629577539409795250195141 305545788639336609411589)
              ·
                refine ⟨57289835369875614264673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305545788639336609411589 57289835369875614264673)
                ·
                  rfl

theorem cell19_188277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_188277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188277 prefixEnd_188277 := by exact prefixLift 188277
  have htrace : WordTrace (prefixWord ++ tailWord_188277) baseStart_188277 baseEnd_188277 := by
    simpa [prefixWord, tailWord_188277, baseEnd_188277] using wordTrace_append hprefix tailTrace_188277
  have hstable : (prefixWord ++ tailWord_188277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188277).length < 2 ^ (prefixWord ++ tailWord_188277).sum := by decide
  have hdescent : baseEnd_188277 < baseStart_188277 := by decide
  rcases family_descends (prefixWord ++ tailWord_188277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188317 : List Nat := [1, 4, 2, 1, 2, 9]
def baseStart_188317 : Nat := 118140960795 + 188317 * 2 ^ 59
def prefixEnd_188317 : Nat := 4983230072969 + 3 ^ 40 * 188317 * 2
def baseEnd_188317 : Nat := 6366889640351930375075

theorem tailTrace_188317 : CollatzResearch.WordTrace tailWord_188317 prefixEnd_188317 6366889640351930375075 := by
  unfold tailWord_188317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868485258767145828163205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4578990172511430552108803 6868485258767145828163205)
  ·
    refine ⟨1287840986018839842780601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6868485258767145828163205 1287840986018839842780601)
    ·
      refine ⟨965880739514129882085451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1287840986018839842780601 965880739514129882085451)
      ·
        refine ⟨1448821109271194823128177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965880739514129882085451 1448821109271194823128177)
        ·
          refine ⟨1086615831953396117346133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448821109271194823128177 1086615831953396117346133)
          ·
            refine ⟨6366889640351930375075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1086615831953396117346133 6366889640351930375075)
            ·
              rfl

theorem cell19_188317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_188317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188317 prefixEnd_188317 := by exact prefixLift 188317
  have htrace : WordTrace (prefixWord ++ tailWord_188317) baseStart_188317 baseEnd_188317 := by
    simpa [prefixWord, tailWord_188317, baseEnd_188317] using wordTrace_append hprefix tailTrace_188317
  have hstable : (prefixWord ++ tailWord_188317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188317).length < 2 ^ (prefixWord ++ tailWord_188317).sum := by decide
  have hdescent : baseEnd_188317 < baseStart_188317 := by decide
  rcases family_descends (prefixWord ++ tailWord_188317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188328 : List Nat := [2, 1, 6, 2, 2, 1, 1, 4]
def baseStart_188328 : Nat := 118140960795 + 188328 * 2 ^ 59
def prefixEnd_188328 : Nat := 4983230072969 + 3 ^ 40 * 188328 * 2
def baseEnd_188328 : Nat := 57305353896322607131201

theorem tailTrace_188328 : CollatzResearch.WordTrace tailWord_188328 prefixEnd_188328 57305353896322607131201 := by
  unfold tailWord_188328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434443230863647353406819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4579257641151529804542425 3434443230863647353406819)
  ·
    refine ⟨5151664846295471030110229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3434443230863647353406819 5151664846295471030110229)
    ·
      refine ⟨241484289670100204536417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5151664846295471030110229 241484289670100204536417)
      ·
        refine ⟨181113217252575153402313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241484289670100204536417 181113217252575153402313)
        ·
          refine ⟨135834912939431365051735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181113217252575153402313 135834912939431365051735)
          ·
            refine ⟨203752369409147047577603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135834912939431365051735 203752369409147047577603)
            ·
              refine ⟨305628554113720571366405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203752369409147047577603 305628554113720571366405)
              ·
                refine ⟨57305353896322607131201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305628554113720571366405 57305353896322607131201)
                ·
                  rfl

theorem cell19_188328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_188328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188328 prefixEnd_188328 := by exact prefixLift 188328
  have htrace : WordTrace (prefixWord ++ tailWord_188328) baseStart_188328 baseEnd_188328 := by
    simpa [prefixWord, tailWord_188328, baseEnd_188328] using wordTrace_append hprefix tailTrace_188328
  have hstable : (prefixWord ++ tailWord_188328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188328).length < 2 ^ (prefixWord ++ tailWord_188328).sum := by decide
  have hdescent : baseEnd_188328 < baseStart_188328 := by decide
  rcases family_descends (prefixWord ++ tailWord_188328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188406 : List Nat := [5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_188406 : Nat := 118140960795 + 188406 * 2 ^ 59
def prefixEnd_188406 : Nat := 4983230072969 + 3 ^ 40 * 188406 * 2
def baseEnd_188406 : Nat := 57329088113241537397655

theorem tailTrace_188406 : CollatzResearch.WordTrace tailWord_188406 prefixEnd_188406 57329088113241537397655 := by
  unfold tailWord_188406
  simp only [CollatzResearch.WordTrace]
  refine ⟨429483209715294626759567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4581154236963142685435381 429483209715294626759567)
  ·
    refine ⟨644224814572941940139351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429483209715294626759567 644224814572941940139351)
    ·
      refine ⟨966337221859412910209027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644224814572941940139351 966337221859412910209027)
      ·
        refine ⟨1449505832789119365313541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966337221859412910209027 1449505832789119365313541)
        ·
          refine ⟨271782343647959880996289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1449505832789119365313541 271782343647959880996289)
          ·
            refine ⟨203836757735969910747217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271782343647959880996289 203836757735969910747217)
            ·
              refine ⟨152877568301977433060413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203836757735969910747217 152877568301977433060413)
              ·
                refine ⟨57329088113241537397655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152877568301977433060413 57329088113241537397655)
                ·
                  rfl

theorem cell19_188406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_188406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188406 prefixEnd_188406 := by exact prefixLift 188406
  have htrace : WordTrace (prefixWord ++ tailWord_188406) baseStart_188406 baseEnd_188406 := by
    simpa [prefixWord, tailWord_188406, baseEnd_188406] using wordTrace_append hprefix tailTrace_188406
  have hstable : (prefixWord ++ tailWord_188406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188406).length < 2 ^ (prefixWord ++ tailWord_188406).sum := by decide
  have hdescent : baseEnd_188406 < baseStart_188406 := by decide
  rcases family_descends (prefixWord ++ tailWord_188406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188412 : List Nat := [2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_188412 : Nat := 118140960795 + 188412 * 2 ^ 59
def prefixEnd_188412 : Nat := 4983230072969 + 3 ^ 40 * 188412 * 2
def baseEnd_188412 : Nat := 57330913822235301264305

theorem tailTrace_188412 : CollatzResearch.WordTrace tailWord_188412 prefixEnd_188412 57330913822235301264305 := by
  unfold tailWord_188412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435975096711488526435745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4581300128948651368580993 3435975096711488526435745)
  ·
    refine ⟨2576981322533616394826809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3435975096711488526435745 2576981322533616394826809)
    ·
      refine ⟨1932735991900212296120107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576981322533616394826809 1932735991900212296120107)
      ·
        refine ⟨2899103987850318444180161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932735991900212296120107 2899103987850318444180161)
        ·
          refine ⟨2174327990887738833135121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2899103987850318444180161 2174327990887738833135121)
          ·
            refine ⟨1630745993165804124851341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2174327990887738833135121 1630745993165804124851341)
            ·
              refine ⟨611529747437176546819253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1630745993165804124851341 611529747437176546819253)
              ·
                refine ⟨57330913822235301264305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 611529747437176546819253 57330913822235301264305)
                ·
                  rfl

theorem cell19_188412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_188412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188412 prefixEnd_188412 := by exact prefixLift 188412
  have htrace : WordTrace (prefixWord ++ tailWord_188412) baseStart_188412 baseEnd_188412 := by
    simpa [prefixWord, tailWord_188412, baseEnd_188412] using wordTrace_append hprefix tailTrace_188412
  have hstable : (prefixWord ++ tailWord_188412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188412).length < 2 ^ (prefixWord ++ tailWord_188412).sum := by decide
  have hdescent : baseEnd_188412 < baseStart_188412 := by decide
  rcases family_descends (prefixWord ++ tailWord_188412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188469 : List Nat := [1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_188469 : Nat := 118140960795 + 188469 * 2 ^ 59
def prefixEnd_188469 : Nat := 4983230072969 + 3 ^ 40 * 188469 * 2
def baseEnd_188469 : Nat := 57348258057676057997483

theorem tailTrace_188469 : CollatzResearch.WordTrace tailWord_188469 prefixEnd_188469 57348258057676057997483 := by
  unfold tailWord_188469
  simp only [CollatzResearch.WordTrace]
  refine ⟨6874029154216475787696461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4582686102810983858464307 6874029154216475787696461)
  ·
    refine ⟨2577760932831178420386173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6874029154216475787696461 2577760932831178420386173)
    ·
      refine ⟨966660349811691907644815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2577760932831178420386173 966660349811691907644815)
      ·
        refine ⟨1449990524717537861467223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966660349811691907644815 1449990524717537861467223)
        ·
          refine ⟨2174985787076306792200835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449990524717537861467223 2174985787076306792200835)
          ·
            refine ⟨3262478680614460188301253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174985787076306792200835 3262478680614460188301253)
            ·
              refine ⟨611714752615211285306485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3262478680614460188301253 611714752615211285306485)
              ·
                refine ⟨57348258057676057997483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 611714752615211285306485 57348258057676057997483)
                ·
                  rfl

theorem cell19_188469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_188469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188469 prefixEnd_188469 := by exact prefixLift 188469
  have htrace : WordTrace (prefixWord ++ tailWord_188469) baseStart_188469 baseEnd_188469 := by
    simpa [prefixWord, tailWord_188469, baseEnd_188469] using wordTrace_append hprefix tailTrace_188469
  have hstable : (prefixWord ++ tailWord_188469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188469).length < 2 ^ (prefixWord ++ tailWord_188469).sum := by decide
  have hdescent : baseEnd_188469 < baseStart_188469 := by decide
  rcases family_descends (prefixWord ++ tailWord_188469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188522 : List Nat := [3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_188522 : Nat := 118140960795 + 188522 * 2 ^ 59
def prefixEnd_188522 : Nat := 4983230072969 + 3 ^ 40 * 188522 * 2
def baseEnd_188522 : Nat := 57364385153787638819561

theorem tailTrace_188522 : CollatzResearch.WordTrace tailWord_188522 prefixEnd_188522 57364385153787638819561 := by
  unfold tailWord_188522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718990555756116459843955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4583974815349643892917213 1718990555756116459843955)
  ·
    refine ⟨2578485833634174689765933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1718990555756116459843955 2578485833634174689765933)
    ·
      refine ⟨966932187612815508662225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2578485833634174689765933 966932187612815508662225)
      ·
        refine ⟨725199140709611631496669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 966932187612815508662225 725199140709611631496669)
        ·
          refine ⟨271949677766104361811251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 725199140709611631496669 271949677766104361811251)
          ·
            refine ⟨407924516649156542716877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271949677766104361811251 407924516649156542716877)
            ·
              refine ⟨152971693743433703518829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407924516649156542716877 152971693743433703518829)
              ·
                refine ⟨57364385153787638819561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152971693743433703518829 57364385153787638819561)
                ·
                  rfl

theorem cell19_188522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_188522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188522 prefixEnd_188522 := by exact prefixLift 188522
  have htrace : WordTrace (prefixWord ++ tailWord_188522) baseStart_188522 baseEnd_188522 := by
    simpa [prefixWord, tailWord_188522, baseEnd_188522] using wordTrace_append hprefix tailTrace_188522
  have hstable : (prefixWord ++ tailWord_188522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188522).length < 2 ^ (prefixWord ++ tailWord_188522).sum := by decide
  have hdescent : baseEnd_188522 < baseStart_188522 := by decide
  rcases family_descends (prefixWord ++ tailWord_188522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188524 : List Nat := [2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_188524 : Nat := 118140960795 + 188524 * 2 ^ 59
def prefixEnd_188524 : Nat := 4983230072969 + 3 ^ 40 * 188524 * 2
def baseEnd_188524 : Nat := 57364993723452226775111

theorem tailTrace_188524 : CollatzResearch.WordTrace tailWord_188524 prefixEnd_188524 57364993723452226775111 := by
  unfold tailWord_188524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438017584508610090474313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4584023446011480120632417 3438017584508610090474313)
  ·
    refine ⟨2578513188381457567855735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3438017584508610090474313 2578513188381457567855735)
    ·
      refine ⟨3867769782572186351783603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2578513188381457567855735 3867769782572186351783603)
      ·
        refine ⟨5801654673858279527675405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3867769782572186351783603 5801654673858279527675405)
        ·
          refine ⟨2175620502696854822878277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5801654673858279527675405 2175620502696854822878277)
          ·
            refine ⟨407928844255660279289677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2175620502696854822878277 407928844255660279289677)
            ·
              refine ⟨152973316595872604733629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407928844255660279289677 152973316595872604733629)
              ·
                refine ⟨57364993723452226775111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152973316595872604733629 57364993723452226775111)
                ·
                  rfl

theorem cell19_188524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_188524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188524 prefixEnd_188524 := by exact prefixLift 188524
  have htrace : WordTrace (prefixWord ++ tailWord_188524) baseStart_188524 baseEnd_188524 := by
    simpa [prefixWord, tailWord_188524, baseEnd_188524] using wordTrace_append hprefix tailTrace_188524
  have hstable : (prefixWord ++ tailWord_188524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188524).length < 2 ^ (prefixWord ++ tailWord_188524).sum := by decide
  have hdescent : baseEnd_188524 < baseStart_188524 := by decide
  rcases family_descends (prefixWord ++ tailWord_188524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188661 : List Nat := [1, 3, 15]
def baseStart_188661 : Nat := 118140960795 + 188661 * 2 ^ 59
def prefixEnd_188661 : Nat := 4983230072969 + 3 ^ 40 * 188661 * 2
def baseEnd_188661 : Nat := 236241484549286015351

theorem tailTrace_188661 : CollatzResearch.WordTrace tailWord_188661 prefixEnd_188661 236241484549286015351 := by
  unfold tailWord_188661
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881031969520892578685837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4587354646347261719123891 6881031969520892578685837)
  ·
    refine ⟨2580386988570334717007189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6881031969520892578685837 2580386988570334717007189)
    ·
      refine ⟨236241484549286015351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 2580386988570334717007189 236241484549286015351)
      ·
        rfl

theorem cell19_188661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 15].length) (baseStart_188661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188661 prefixEnd_188661 := by exact prefixLift 188661
  have htrace : WordTrace (prefixWord ++ tailWord_188661) baseStart_188661 baseEnd_188661 := by
    simpa [prefixWord, tailWord_188661, baseEnd_188661] using wordTrace_append hprefix tailTrace_188661
  have hstable : (prefixWord ++ tailWord_188661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188661).length < 2 ^ (prefixWord ++ tailWord_188661).sum := by decide
  have hdescent : baseEnd_188661 < baseStart_188661 := by decide
  rcases family_descends (prefixWord ++ tailWord_188661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188674 : List Nat := [3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_188674 : Nat := 118140960795 + 188674 * 2 ^ 59
def prefixEnd_188674 : Nat := 4983230072969 + 3 ^ 40 * 188674 * 2
def baseEnd_188674 : Nat := 57410636448296323441369

theorem tailTrace_188674 : CollatzResearch.WordTrace tailWord_188674 prefixEnd_188674 57410636448296323441369 := by
  unfold tailWord_188674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720376529618448949727269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4587670745649197199272717 1720376529618448949727269)
  ·
    refine ⟨322570599303459178073863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1720376529618448949727269 322570599303459178073863)
    ·
      refine ⟨483855898955188767110795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322570599303459178073863 483855898955188767110795)
      ·
        refine ⟨725783848432783150666193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483855898955188767110795 725783848432783150666193)
        ·
          refine ⟨544337886324587362999645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725783848432783150666193 544337886324587362999645)
          ·
            refine ⟨204126707371720261124867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 544337886324587362999645 204126707371720261124867)
            ·
              refine ⟨306190061057580391687301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204126707371720261124867 306190061057580391687301)
              ·
                refine ⟨57410636448296323441369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306190061057580391687301 57410636448296323441369)
                ·
                  rfl

theorem cell19_188674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_188674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188674 prefixEnd_188674 := by exact prefixLift 188674
  have htrace : WordTrace (prefixWord ++ tailWord_188674) baseStart_188674 baseEnd_188674 := by
    simpa [prefixWord, tailWord_188674, baseEnd_188674] using wordTrace_append hprefix tailTrace_188674
  have hstable : (prefixWord ++ tailWord_188674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188674).length < 2 ^ (prefixWord ++ tailWord_188674).sum := by decide
  have hdescent : baseEnd_188674 < baseStart_188674 := by decide
  rcases family_descends (prefixWord ++ tailWord_188674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188695 : List Nat := [1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_188695 : Nat := 118140960795 + 188695 * 2 ^ 59
def prefixEnd_188695 : Nat := 4983230072969 + 3 ^ 40 * 188695 * 2
def baseEnd_188695 : Nat := 57417026429774496974645

theorem tailTrace_188695 : CollatzResearch.WordTrace tailWord_188695 prefixEnd_188695 57417026429774496974645 := by
  unfold tailWord_188695
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882272051397716385423539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4588181367598477590282359 6882272051397716385423539)
  ·
    refine ⟨10323408077096574578135309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6882272051397716385423539 10323408077096574578135309)
    ·
      refine ⟨3871278028911215466800741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10323408077096574578135309 3871278028911215466800741)
      ·
        refine ⟨725864630420852900025139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3871278028911215466800741 725864630420852900025139)
        ·
          refine ⟨1088796945631279350037709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725864630420852900025139 1088796945631279350037709)
          ·
            refine ⟨408298854611729756264141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1088796945631279350037709 408298854611729756264141)
            ·
              refine ⟨153112070479398658599053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408298854611729756264141 153112070479398658599053)
              ·
                refine ⟨57417026429774496974645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153112070479398658599053 57417026429774496974645)
                ·
                  rfl

theorem cell19_188695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_188695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188695 prefixEnd_188695 := by exact prefixLift 188695
  have htrace : WordTrace (prefixWord ++ tailWord_188695) baseStart_188695 baseEnd_188695 := by
    simpa [prefixWord, tailWord_188695, baseEnd_188695] using wordTrace_append hprefix tailTrace_188695
  have hstable : (prefixWord ++ tailWord_188695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188695).length < 2 ^ (prefixWord ++ tailWord_188695).sum := by decide
  have hdescent : baseEnd_188695 < baseStart_188695 := by decide
  rcases family_descends (prefixWord ++ tailWord_188695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188699 : List Nat := [1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_188699 : Nat := 118140960795 + 188699 * 2 ^ 59
def prefixEnd_188699 : Nat := 4983230072969 + 3 ^ 40 * 188699 * 2
def baseEnd_188699 : Nat := 57418243569103672885745

theorem tailTrace_188699 : CollatzResearch.WordTrace tailWord_188699 prefixEnd_188699 57418243569103672885745 := by
  unfold tailWord_188699
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882417943383225068569151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4588278628922150045712767 6882417943383225068569151)
  ·
    refine ⟨10323626915074837602853727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6882417943383225068569151 10323626915074837602853727)
    ·
      refine ⟨15485440372612256404280591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10323626915074837602853727 15485440372612256404280591)
      ·
        refine ⟨23228160558918384606420887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15485440372612256404280591 23228160558918384606420887)
        ·
          refine ⟨34842240838377576909631331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23228160558918384606420887 34842240838377576909631331)
          ·
            refine ⟨52263361257566365364446997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34842240838377576909631331 52263361257566365364446997)
            ·
              refine ⟨2449845058948423376458453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52263361257566365364446997 2449845058948423376458453)
              ·
                refine ⟨57418243569103672885745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2449845058948423376458453 57418243569103672885745)
                ·
                  rfl

theorem cell19_188699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_188699 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188699 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188699 prefixEnd_188699 := by exact prefixLift 188699
  have htrace : WordTrace (prefixWord ++ tailWord_188699) baseStart_188699 baseEnd_188699 := by
    simpa [prefixWord, tailWord_188699, baseEnd_188699] using wordTrace_append hprefix tailTrace_188699
  have hstable : (prefixWord ++ tailWord_188699).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188699).length < 2 ^ (prefixWord ++ tailWord_188699).sum := by decide
  have hdescent : baseEnd_188699 < baseStart_188699 := by decide
  rcases family_descends (prefixWord ++ tailWord_188699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188714 : List Nat := [3, 1, 4, 2, 2, 1, 6]
def baseStart_188714 : Nat := 118140960795 + 188714 * 2 ^ 59
def prefixEnd_188714 : Nat := 4983230072969 + 3 ^ 40 * 188714 * 2
def baseEnd_188714 : Nat := 19140935947196027517457

theorem tailTrace_188714 : CollatzResearch.WordTrace tailWord_188714 prefixEnd_188714 19140935947196027517457 := by
  unfold tailWord_188714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720741259582220657591299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4588643358885921753576797 1720741259582220657591299)
  ·
    refine ⟨2581111889373330986386949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1720741259582220657591299 2581111889373330986386949)
    ·
      refine ⟨483958479257499559947553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2581111889373330986386949 483958479257499559947553)
      ·
        refine ⟨362968859443124669960665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483958479257499559947553 362968859443124669960665)
        ·
          refine ⟨272226644582343502470499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362968859443124669960665 272226644582343502470499)
          ·
            refine ⟨408339966873515253705749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272226644582343502470499 408339966873515253705749)
            ·
              refine ⟨19140935947196027517457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 408339966873515253705749 19140935947196027517457)
              ·
                rfl

theorem cell19_188714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_188714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188714 prefixEnd_188714 := by exact prefixLift 188714
  have htrace : WordTrace (prefixWord ++ tailWord_188714) baseStart_188714 baseEnd_188714 := by
    simpa [prefixWord, tailWord_188714, baseEnd_188714] using wordTrace_append hprefix tailTrace_188714
  have hstable : (prefixWord ++ tailWord_188714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188714).length < 2 ^ (prefixWord ++ tailWord_188714).sum := by decide
  have hdescent : baseEnd_188714 < baseStart_188714 := by decide
  rcases family_descends (prefixWord ++ tailWord_188714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188752 : List Nat := [2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_188752 : Nat := 118140960795 + 188752 * 2 ^ 59
def prefixEnd_188752 : Nat := 4983230072969 + 3 ^ 40 * 188752 * 2
def baseEnd_188752 : Nat := 57434370665215253707823

theorem tailTrace_188752 : CollatzResearch.WordTrace tailWord_188752 prefixEnd_188752 57434370665215253707823 := by
  unfold tailWord_188752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442175506095607560124255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4589567341460810080165673 3442175506095607560124255)
  ·
    refine ⟨5163263259143411340186383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3442175506095607560124255 5163263259143411340186383)
    ·
      refine ⟨7744894888715117010279575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163263259143411340186383 7744894888715117010279575)
      ·
        refine ⟨11617342333072675515419363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744894888715117010279575 11617342333072675515419363)
        ·
          refine ⟨17426013499609013273129045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11617342333072675515419363 17426013499609013273129045)
          ·
            refine ⟨204211095698543124294481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 17426013499609013273129045 204211095698543124294481)
            ·
              refine ⟨153158321773907343220861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204211095698543124294481 153158321773907343220861)
              ·
                refine ⟨57434370665215253707823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153158321773907343220861 57434370665215253707823)
                ·
                  rfl

theorem cell19_188752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_188752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188752 prefixEnd_188752 := by exact prefixLift 188752
  have htrace : WordTrace (prefixWord ++ tailWord_188752) baseStart_188752 baseEnd_188752 := by
    simpa [prefixWord, tailWord_188752, baseEnd_188752] using wordTrace_append hprefix tailTrace_188752
  have hstable : (prefixWord ++ tailWord_188752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188752).length < 2 ^ (prefixWord ++ tailWord_188752).sum := by decide
  have hdescent : baseEnd_188752 < baseStart_188752 := by decide
  rcases family_descends (prefixWord ++ tailWord_188752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188773 : List Nat := [1, 3, 1, 3, 1, 5, 5]
def baseStart_188773 : Nat := 118140960795 + 188773 * 2 ^ 59
def prefixEnd_188773 : Nat := 4983230072969 + 3 ^ 40 * 188773 * 2
def baseEnd_188773 : Nat := 19146920215564475747033

theorem tailTrace_188773 : CollatzResearch.WordTrace tailWord_188773 prefixEnd_188773 19146920215564475747033 := by
  unfold tailWord_188773
  simp only [CollatzResearch.WordTrace]
  refine ⟨6885116945115135706762973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4590077963410090471175315 6885116945115135706762973)
  ·
    refine ⟨2581918854418175890036115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6885116945115135706762973 2581918854418175890036115)
    ·
      refine ⟨3872878281627263835054173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581918854418175890036115 3872878281627263835054173)
      ·
        refine ⟨1452329355610223938145315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3872878281627263835054173 1452329355610223938145315)
        ·
          refine ⟨2178494033415335907217973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452329355610223938145315 2178494033415335907217973)
          ·
            refine ⟨204233815632687741301685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2178494033415335907217973 204233815632687741301685)
            ·
              refine ⟨19146920215564475747033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204233815632687741301685 19146920215564475747033)
              ·
                rfl

theorem cell19_188773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_188773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188773 prefixEnd_188773 := by exact prefixLift 188773
  have htrace : WordTrace (prefixWord ++ tailWord_188773) baseStart_188773 baseEnd_188773 := by
    simpa [prefixWord, tailWord_188773, baseEnd_188773] using wordTrace_append hprefix tailTrace_188773
  have hstable : (prefixWord ++ tailWord_188773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188773).length < 2 ^ (prefixWord ++ tailWord_188773).sum := by decide
  have hdescent : baseEnd_188773 < baseStart_188773 := by decide
  rcases family_descends (prefixWord ++ tailWord_188773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188832 : List Nat := [2, 1, 1, 4, 1, 10]
def baseStart_188832 : Nat := 118140960795 + 188832 * 2 ^ 59
def prefixEnd_188832 : Nat := 4983230072969 + 3 ^ 40 * 188832 * 2
def baseEnd_188832 : Nat := 6384301494644307992203

theorem tailTrace_188832 : CollatzResearch.WordTrace tailWord_188832 prefixEnd_188832 6384301494644307992203 := by
  unfold tailWord_188832
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443634425950694391580375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4591512567934259188773833 3443634425950694391580375)
  ·
    refine ⟨5165451638926041587370563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3443634425950694391580375 5165451638926041587370563)
    ·
      refine ⟨7748177458389062381055845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165451638926041587370563 7748177458389062381055845)
      ·
        refine ⟨1452783273447949196447971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7748177458389062381055845 1452783273447949196447971)
        ·
          refine ⟨2179174910171923794671957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452783273447949196447971 2179174910171923794671957)
          ·
            refine ⟨6384301494644307992203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2179174910171923794671957 6384301494644307992203)
            ·
              rfl

theorem cell19_188832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_188832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188832 prefixEnd_188832 := by exact prefixLift 188832
  have htrace : WordTrace (prefixWord ++ tailWord_188832) baseStart_188832 baseEnd_188832 := by
    simpa [prefixWord, tailWord_188832, baseEnd_188832] using wordTrace_append hprefix tailTrace_188832
  have hstable : (prefixWord ++ tailWord_188832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188832).length < 2 ^ (prefixWord ++ tailWord_188832).sum := by decide
  have hdescent : baseEnd_188832 < baseStart_188832 := by decide
  rcases family_descends (prefixWord ++ tailWord_188832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188845 : List Nat := [1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_188845 : Nat := 118140960795 + 188845 * 2 ^ 59
def prefixEnd_188845 : Nat := 4983230072969 + 3 ^ 40 * 188845 * 2
def baseEnd_188845 : Nat := 57462669154618593640903

theorem tailTrace_188845 : CollatzResearch.WordTrace tailWord_188845 prefixEnd_188845 57462669154618593640903 := by
  unfold tailWord_188845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887743000854292003383989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4591828667236194668922659 6887743000854292003383989)
  ·
    refine ⟨645725906330089875317249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6887743000854292003383989 645725906330089875317249)
    ·
      refine ⟨484294429747567406487937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 645725906330089875317249 484294429747567406487937)
      ·
        refine ⟨363220822310675554865953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484294429747567406487937 363220822310675554865953)
        ·
          refine ⟨272415616733006666149465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363220822310675554865953 272415616733006666149465)
          ·
            refine ⟨204311712549754999612099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272415616733006666149465 204311712549754999612099)
            ·
              refine ⟨306467568824632499418149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204311712549754999612099 306467568824632499418149)
              ·
                refine ⟨57462669154618593640903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306467568824632499418149 57462669154618593640903)
                ·
                  rfl

theorem cell19_188845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_188845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188845 prefixEnd_188845 := by exact prefixLift 188845
  have htrace : WordTrace (prefixWord ++ tailWord_188845) baseStart_188845 baseEnd_188845 := by
    simpa [prefixWord, tailWord_188845, baseEnd_188845] using wordTrace_append hprefix tailTrace_188845
  have hstable : (prefixWord ++ tailWord_188845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188845).length < 2 ^ (prefixWord ++ tailWord_188845).sum := by decide
  have hdescent : baseEnd_188845 < baseStart_188845 := by decide
  rcases family_descends (prefixWord ++ tailWord_188845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188849 : List Nat := [1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_188849 : Nat := 118140960795 + 188849 * 2 ^ 59
def prefixEnd_188849 : Nat := 4983230072969 + 3 ^ 40 * 188849 * 2
def baseEnd_188849 : Nat := 57463886293947769552003

theorem tailTrace_188849 : CollatzResearch.WordTrace tailWord_188849 prefixEnd_188849 57463886293947769552003 := by
  unfold tailWord_188849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887888892839800686529601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4591925928559867124353067 6887888892839800686529601)
  ·
    refine ⟨5165916669629850514897201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6887888892839800686529601 5165916669629850514897201)
    ·
      refine ⟨3874437502222387886172901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5165916669629850514897201 3874437502222387886172901)
      ·
        refine ⟨726457031666697728657419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3874437502222387886172901 726457031666697728657419)
        ·
          refine ⟨1089685547500046592986129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726457031666697728657419 1089685547500046592986129)
          ·
            refine ⟨817264160625034944739597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089685547500046592986129 817264160625034944739597)
            ·
              refine ⟨306474060234388104277349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817264160625034944739597 306474060234388104277349)
              ·
                refine ⟨57463886293947769552003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306474060234388104277349 57463886293947769552003)
                ·
                  rfl

theorem cell19_188849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_188849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188849 prefixEnd_188849 := by exact prefixLift 188849
  have htrace : WordTrace (prefixWord ++ tailWord_188849) baseStart_188849 baseEnd_188849 := by
    simpa [prefixWord, tailWord_188849, baseEnd_188849] using wordTrace_append hprefix tailTrace_188849
  have hstable : (prefixWord ++ tailWord_188849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188849).length < 2 ^ (prefixWord ++ tailWord_188849).sum := by decide
  have hdescent : baseEnd_188849 < baseStart_188849 := by decide
  rcases family_descends (prefixWord ++ tailWord_188849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188889 : List Nat := [1, 2, 1, 2, 4, 1, 8]
def baseStart_188889 : Nat := 118140960795 + 188889 * 2 ^ 59
def prefixEnd_188889 : Nat := 4983230072969 + 3 ^ 40 * 188889 * 2
def baseEnd_188889 : Nat := 19158685895746509554335

theorem tailTrace_188889 : CollatzResearch.WordTrace tailWord_188889 prefixEnd_188889 19158685895746509554335 := by
  unfold tailWord_188889
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889347812694887517985721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4592898541796591678657147 6889347812694887517985721)
  ·
    refine ⟨5167010859521165638489291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6889347812694887517985721 5167010859521165638489291)
    ·
      refine ⟨7750516289281748457733937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5167010859521165638489291 7750516289281748457733937)
      ·
        refine ⟨5812887216961311343300453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7750516289281748457733937 5812887216961311343300453)
        ·
          refine ⟨1089916353180245876868835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5812887216961311343300453 1089916353180245876868835)
          ·
            refine ⟨1634874529770368815303253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089916353180245876868835 1634874529770368815303253)
            ·
              refine ⟨19158685895746509554335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1634874529770368815303253 19158685895746509554335)
              ·
                rfl

theorem cell19_188889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_188889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188889 prefixEnd_188889 := by exact prefixLift 188889
  have htrace : WordTrace (prefixWord ++ tailWord_188889) baseStart_188889 baseEnd_188889 := by
    simpa [prefixWord, tailWord_188889, baseEnd_188889] using wordTrace_append hprefix tailTrace_188889
  have hstable : (prefixWord ++ tailWord_188889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188889).length < 2 ^ (prefixWord ++ tailWord_188889).sum := by decide
  have hdescent : baseEnd_188889 < baseStart_188889 := by decide
  rcases family_descends (prefixWord ++ tailWord_188889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188908 : List Nat := [2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_188908 : Nat := 118140960795 + 188908 * 2 ^ 59
def prefixEnd_188908 : Nat := 4983230072969 + 3 ^ 40 * 188908 * 2
def baseEnd_188908 : Nat := 57481839099053114240731

theorem tailTrace_188908 : CollatzResearch.WordTrace tailWord_188908 prefixEnd_188908 57481839099053114240731 := by
  unfold tailWord_188908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445020399813026881463689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4593360533084035841951585 3445020399813026881463689)
  ·
    refine ⟨2583765299859770161097767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3445020399813026881463689 2583765299859770161097767)
    ·
      refine ⟨3875647949789655241646651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2583765299859770161097767 3875647949789655241646651)
      ·
        refine ⟨5813471924684482862469977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3875647949789655241646651 5813471924684482862469977)
        ·
          refine ⟨4360103943513362146852483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5813471924684482862469977 4360103943513362146852483)
          ·
            refine ⟨6540155915270043220278725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360103943513362146852483 6540155915270043220278725)
            ·
              refine ⟨1226279234113133103802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6540155915270043220278725 1226279234113133103802261)
              ·
                refine ⟨57481839099053114240731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1226279234113133103802261 57481839099053114240731)
                ·
                  rfl

theorem cell19_188908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_188908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188908 prefixEnd_188908 := by exact prefixLift 188908
  have htrace : WordTrace (prefixWord ++ tailWord_188908) baseStart_188908 baseEnd_188908 := by
    simpa [prefixWord, tailWord_188908, baseEnd_188908] using wordTrace_append hprefix tailTrace_188908
  have hstable : (prefixWord ++ tailWord_188908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188908).length < 2 ^ (prefixWord ++ tailWord_188908).sum := by decide
  have hdescent : baseEnd_188908 < baseStart_188908 := by decide
  rcases family_descends (prefixWord ++ tailWord_188908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188927 : List Nat := [1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_188927 : Nat := 118140960795 + 188927 * 2 ^ 59
def prefixEnd_188927 : Nat := 4983230072969 + 3 ^ 40 * 188927 * 2
def baseEnd_188927 : Nat := 57487620510866699818457

theorem tailTrace_188927 : CollatzResearch.WordTrace tailWord_188927 prefixEnd_188927 57487620510866699818457 := by
  unfold tailWord_188927
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890733786557220007869035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4593822524371480005246023 6890733786557220007869035)
  ·
    refine ⟨10336100679835830011803553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6890733786557220007869035 10336100679835830011803553)
    ·
      refine ⟨7752075509876872508852665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10336100679835830011803553 7752075509876872508852665)
      ·
        refine ⟨5814056632407654381639499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7752075509876872508852665 5814056632407654381639499)
        ·
          refine ⟨8721084948611481572459249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814056632407654381639499 8721084948611481572459249)
          ·
            refine ⟨6540813711458611179344437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8721084948611481572459249 6540813711458611179344437)
            ·
              refine ⟨613201285449244798063541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6540813711458611179344437 613201285449244798063541)
              ·
                refine ⟨57487620510866699818457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 613201285449244798063541 57487620510866699818457)
                ·
                  rfl

theorem cell19_188927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_188927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188927 prefixEnd_188927 := by exact prefixLift 188927
  have htrace : WordTrace (prefixWord ++ tailWord_188927) baseStart_188927 baseEnd_188927 := by
    simpa [prefixWord, tailWord_188927, baseEnd_188927] using wordTrace_append hprefix tailTrace_188927
  have hstable : (prefixWord ++ tailWord_188927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188927).length < 2 ^ (prefixWord ++ tailWord_188927).sum := by decide
  have hdescent : baseEnd_188927 < baseStart_188927 := by decide
  rcases family_descends (prefixWord ++ tailWord_188927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188963 : List Nat := [1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_188963 : Nat := 118140960795 + 188963 * 2 ^ 59
def prefixEnd_188963 : Nat := 4983230072969 + 3 ^ 40 * 188963 * 2
def baseEnd_188963 : Nat := 57498574764829283018359

theorem tailTrace_188963 : CollatzResearch.WordTrace tailWord_188963 prefixEnd_188963 57498574764829283018359 := by
  unfold tailWord_188963
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892046814426798156179543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4594697876284532104119695 6892046814426798156179543)
  ·
    refine ⟨10338070221640197234269315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892046814426798156179543 10338070221640197234269315)
    ·
      refine ⟨15507105332460295851403973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338070221640197234269315 15507105332460295851403973)
      ·
        refine ⟨2907582249836305472138245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15507105332460295851403973 2907582249836305472138245)
        ·
          refine ⟨545171671844307276025921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2907582249836305472138245 545171671844307276025921)
          ·
            refine ⟨408878753883230457019441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545171671844307276025921 408878753883230457019441)
            ·
              refine ⟨306659065412422842764581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408878753883230457019441 306659065412422842764581)
              ·
                refine ⟨57498574764829283018359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306659065412422842764581 57498574764829283018359)
                ·
                  rfl

theorem cell19_188963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_188963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188963 prefixEnd_188963 := by exact prefixLift 188963
  have htrace : WordTrace (prefixWord ++ tailWord_188963) baseStart_188963 baseEnd_188963 := by
    simpa [prefixWord, tailWord_188963, baseEnd_188963] using wordTrace_append hprefix tailTrace_188963
  have hstable : (prefixWord ++ tailWord_188963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188963).length < 2 ^ (prefixWord ++ tailWord_188963).sum := by decide
  have hdescent : baseEnd_188963 < baseStart_188963 := by decide
  rcases family_descends (prefixWord ++ tailWord_188963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188965 : List Nat := [1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_188965 : Nat := 118140960795 + 188965 * 2 ^ 59
def prefixEnd_188965 : Nat := 4983230072969 + 3 ^ 40 * 188965 * 2
def baseEnd_188965 : Nat := 57499183334493870973909

theorem tailTrace_188965 : CollatzResearch.WordTrace tailWord_188965 prefixEnd_188965 57499183334493870973909 := by
  unfold tailWord_188965
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892119760419552497752349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4594746506946368331834899 6892119760419552497752349)
  ·
    refine ⟨2584544910157332186657131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6892119760419552497752349 2584544910157332186657131)
    ·
      refine ⟨3876817365235998279985697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584544910157332186657131 3876817365235998279985697)
      ·
        refine ⟨2907613023926998709989273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3876817365235998279985697 2907613023926998709989273)
        ·
          refine ⟨2180709767945249032491955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907613023926998709989273 2180709767945249032491955)
          ·
            refine ⟨3271064651917873548737933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180709767945249032491955 3271064651917873548737933)
            ·
              refine ⟨1226649244469202580776725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3271064651917873548737933 1226649244469202580776725)
              ·
                refine ⟨57499183334493870973909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1226649244469202580776725 57499183334493870973909)
                ·
                  rfl

theorem cell19_188965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_188965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188965 prefixEnd_188965 := by exact prefixLift 188965
  have htrace : WordTrace (prefixWord ++ tailWord_188965) baseStart_188965 baseEnd_188965 := by
    simpa [prefixWord, tailWord_188965, baseEnd_188965] using wordTrace_append hprefix tailTrace_188965
  have hstable : (prefixWord ++ tailWord_188965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188965).length < 2 ^ (prefixWord ++ tailWord_188965).sum := by decide
  have hdescent : baseEnd_188965 < baseStart_188965 := by decide
  rcases family_descends (prefixWord ++ tailWord_188965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188984 : List Nat := [2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_188984 : Nat := 118140960795 + 188984 * 2 ^ 59
def prefixEnd_188984 : Nat := 4983230072969 + 3 ^ 40 * 188984 * 2
def baseEnd_188984 : Nat := 57504964746307456551635

theorem tailTrace_188984 : CollatzResearch.WordTrace tailWord_188984 prefixEnd_188984 57504964746307456551635 := by
  unfold tailWord_188984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446406373675359371347003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4595208498233812495129337 3446406373675359371347003)
  ·
    refine ⟨5169609560513039057020505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3446406373675359371347003 5169609560513039057020505)
    ·
      refine ⟨3877207170384779292765379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5169609560513039057020505 3877207170384779292765379)
      ·
        refine ⟨5815810755577168939148069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877207170384779292765379 5815810755577168939148069)
        ·
          refine ⟨1090464516670719176090263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5815810755577168939148069 1090464516670719176090263)
          ·
            refine ⟨1635696775006078764135395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090464516670719176090263 1635696775006078764135395)
            ·
              refine ⟨2453545162509118146203093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635696775006078764135395 2453545162509118146203093)
              ·
                refine ⟨57504964746307456551635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2453545162509118146203093 57504964746307456551635)
                ·
                  rfl

theorem cell19_188984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_188984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_188984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_188984 prefixEnd_188984 := by exact prefixLift 188984
  have htrace : WordTrace (prefixWord ++ tailWord_188984) baseStart_188984 baseEnd_188984 := by
    simpa [prefixWord, tailWord_188984, baseEnd_188984] using wordTrace_append hprefix tailTrace_188984
  have hstable : (prefixWord ++ tailWord_188984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188984).length < 2 ^ (prefixWord ++ tailWord_188984).sum := by decide
  have hdescent : baseEnd_188984 < baseStart_188984 := by decide
  rcases family_descends (prefixWord ++ tailWord_188984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189037 : List Nat := [1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_189037 : Nat := 118140960795 + 189037 * 2 ^ 59
def prefixEnd_189037 : Nat := 4983230072969 + 3 ^ 40 * 189037 * 2
def baseEnd_189037 : Nat := 57521091842419037373713

theorem tailTrace_189037 : CollatzResearch.WordTrace tailWord_189037 prefixEnd_189037 57521091842419037373713 := by
  unfold tailWord_189037
  simp only [CollatzResearch.WordTrace]
  refine ⟨6894745816158708794373365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4596497210772472529582243 6894745816158708794373365)
  ·
    refine ⟨646382420264878949472503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6894745816158708794373365 646382420264878949472503)
    ·
      refine ⟨969573630397318424208755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646382420264878949472503 969573630397318424208755)
      ·
        refine ⟨1454360445595977636313133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969573630397318424208755 1454360445595977636313133)
        ·
          refine ⟨545385167098491613617425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1454360445595977636313133 545385167098491613617425)
          ·
            refine ⟨409038875323868710213069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545385167098491613617425 409038875323868710213069)
            ·
              refine ⟨153389578246450766329901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409038875323868710213069 153389578246450766329901)
              ·
                refine ⟨57521091842419037373713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153389578246450766329901 57521091842419037373713)
                ·
                  rfl

theorem cell19_189037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_189037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189037 prefixEnd_189037 := by exact prefixLift 189037
  have htrace : WordTrace (prefixWord ++ tailWord_189037) baseStart_189037 baseEnd_189037 := by
    simpa [prefixWord, tailWord_189037, baseEnd_189037] using wordTrace_append hprefix tailTrace_189037
  have hstable : (prefixWord ++ tailWord_189037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189037).length < 2 ^ (prefixWord ++ tailWord_189037).sum := by decide
  have hdescent : baseEnd_189037 < baseStart_189037 := by decide
  rcases family_descends (prefixWord ++ tailWord_189037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189079 : List Nat := [1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_189079 : Nat := 118140960795 + 189079 * 2 ^ 59
def prefixEnd_189079 : Nat := 4983230072969 + 3 ^ 40 * 189079 * 2
def baseEnd_189079 : Nat := 57533871805375384440265

theorem tailTrace_189079 : CollatzResearch.WordTrace tailWord_189079 prefixEnd_189079 57533871805375384440265 := by
  unfold tailWord_189079
  simp only [CollatzResearch.WordTrace]
  refine ⟨6896277682006549967402291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4597518454671033311601527 6896277682006549967402291)
  ·
    refine ⟨10344416523009824951103437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6896277682006549967402291 10344416523009824951103437)
    ·
      refine ⟨3879156196128684356663789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10344416523009824951103437 3879156196128684356663789)
      ·
        refine ⟨1454683573548256633748921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3879156196128684356663789 1454683573548256633748921)
        ·
          refine ⟨1091012680161192475311691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454683573548256633748921 1091012680161192475311691)
          ·
            refine ⟨1636519020241788712967537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091012680161192475311691 1636519020241788712967537)
            ·
              refine ⟨1227389265181341534725653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636519020241788712967537 1227389265181341534725653)
              ·
                refine ⟨57533871805375384440265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1227389265181341534725653 57533871805375384440265)
                ·
                  rfl

theorem cell19_189079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_189079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189079 prefixEnd_189079 := by exact prefixLift 189079
  have htrace : WordTrace (prefixWord ++ tailWord_189079) baseStart_189079 baseEnd_189079 := by
    simpa [prefixWord, tailWord_189079, baseEnd_189079] using wordTrace_append hprefix tailTrace_189079
  have hstable : (prefixWord ++ tailWord_189079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189079).length < 2 ^ (prefixWord ++ tailWord_189079).sum := by decide
  have hdescent : baseEnd_189079 < baseStart_189079 := by decide
  rcases family_descends (prefixWord ++ tailWord_189079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189117 : List Nat := [1, 4, 1, 2, 1, 3, 7]
def baseStart_189117 : Nat := 118140960795 + 189117 * 2 ^ 59
def prefixEnd_189117 : Nat := 4983230072969 + 3 ^ 40 * 189117 * 2
def baseEnd_189117 : Nat := 19181811543000851865239

theorem tailTrace_189117 : CollatzResearch.WordTrace tailWord_189117 prefixEnd_189117 19181811543000851865239 := by
  unfold tailWord_189117
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897663655868882457285605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4598442437245921638190403 6897663655868882457285605)
  ·
    refine ⟨1293311935475415460741051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6897663655868882457285605 1293311935475415460741051)
    ·
      refine ⟨1939967903213123191111577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293311935475415460741051 1939967903213123191111577)
      ·
        refine ⟨1454975927409842393333683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1939967903213123191111577 1454975927409842393333683)
        ·
          refine ⟨2182463891114763590000525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454975927409842393333683 2182463891114763590000525)
          ·
            refine ⟨818423959168036346250197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2182463891114763590000525 818423959168036346250197)
            ·
              refine ⟨19181811543000851865239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 818423959168036346250197 19181811543000851865239)
              ·
                rfl

theorem cell19_189117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_189117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189117 prefixEnd_189117 := by exact prefixLift 189117
  have htrace : WordTrace (prefixWord ++ tailWord_189117) baseStart_189117 baseEnd_189117 := by
    simpa [prefixWord, tailWord_189117, baseEnd_189117] using wordTrace_append hprefix tailTrace_189117
  have hstable : (prefixWord ++ tailWord_189117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189117).length < 2 ^ (prefixWord ++ tailWord_189117).sum := by decide
  have hdescent : baseEnd_189117 < baseStart_189117 := by decide
  rcases family_descends (prefixWord ++ tailWord_189117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189134 : List Nat := [4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_189134 : Nat := 118140960795 + 189134 * 2 ^ 59
def prefixEnd_189134 : Nat := 4983230072969 + 3 ^ 40 * 189134 * 2
def baseEnd_189134 : Nat := 57550607471151553217893

theorem tailTrace_189134 : CollatzResearch.WordTrace tailWord_189134 prefixEnd_189134 57550607471151553217893 := by
  unfold tailWord_189134
  simp only [CollatzResearch.WordTrace]
  refine ⟨862285462100911795081807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4598855797871529573769637 862285462100911795081807)
  ·
    refine ⟨1293428193151367692622711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 862285462100911795081807 1293428193151367692622711)
    ·
      refine ⟨1940142289727051538934067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293428193151367692622711 1940142289727051538934067)
      ·
        refine ⟨2910213434590577308401101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940142289727051538934067 2910213434590577308401101)
        ·
          refine ⟨1091330037971466490650413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2910213434590577308401101 1091330037971466490650413)
          ·
            refine ⟨409248764239299933993905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1091330037971466490650413 409248764239299933993905)
            ·
              refine ⟨306936573179474950495429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409248764239299933993905 306936573179474950495429)
              ·
                refine ⟨57550607471151553217893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306936573179474950495429 57550607471151553217893)
                ·
                  rfl

theorem cell19_189134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_189134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189134 prefixEnd_189134 := by exact prefixLift 189134
  have htrace : WordTrace (prefixWord ++ tailWord_189134) baseStart_189134 baseEnd_189134 := by
    simpa [prefixWord, tailWord_189134, baseEnd_189134] using wordTrace_append hprefix tailTrace_189134
  have hstable : (prefixWord ++ tailWord_189134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189134).length < 2 ^ (prefixWord ++ tailWord_189134).sum := by decide
  have hdescent : baseEnd_189134 < baseStart_189134 := by decide
  rcases family_descends (prefixWord ++ tailWord_189134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189191 : List Nat := [1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_189191 : Nat := 118140960795 + 189191 * 2 ^ 59
def prefixEnd_189191 : Nat := 4983230072969 + 3 ^ 40 * 189191 * 2
def baseEnd_189191 : Nat := 57567951706592309951071

theorem tailTrace_189191 : CollatzResearch.WordTrace tailWord_189191 prefixEnd_189191 57567951706592309951071 := by
  unfold tailWord_189191
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900362657600793095479427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4600241771733862063652951 6900362657600793095479427)
  ·
    refine ⟨10350543986401189643219141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900362657600793095479427 10350543986401189643219141)
    ·
      refine ⟨1940726997450223058103589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10350543986401189643219141 1940726997450223058103589)
      ·
        refine ⟨363886312021916823394423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1940726997450223058103589 363886312021916823394423)
        ·
          refine ⟨545829468032875235091635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363886312021916823394423 545829468032875235091635)
          ·
            refine ⟨818744202049312852637453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545829468032875235091635 818744202049312852637453)
            ·
              refine ⟨307029075768492319739045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818744202049312852637453 307029075768492319739045)
              ·
                refine ⟨57567951706592309951071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307029075768492319739045 57567951706592309951071)
                ·
                  rfl

theorem cell19_189191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_189191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189191 prefixEnd_189191 := by exact prefixLift 189191
  have htrace : WordTrace (prefixWord ++ tailWord_189191) baseStart_189191 baseEnd_189191 := by
    simpa [prefixWord, tailWord_189191, baseEnd_189191] using wordTrace_append hprefix tailTrace_189191
  have hstable : (prefixWord ++ tailWord_189191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189191).length < 2 ^ (prefixWord ++ tailWord_189191).sum := by decide
  have hdescent : baseEnd_189191 < baseStart_189191 := by decide
  rcases family_descends (prefixWord ++ tailWord_189191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189193 : List Nat := [1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_189193 : Nat := 118140960795 + 189193 * 2 ^ 59
def prefixEnd_189193 : Nat := 4983230072969 + 3 ^ 40 * 189193 * 2
def baseEnd_189193 : Nat := 57568560276256897906621

theorem tailTrace_189193 : CollatzResearch.WordTrace tailWord_189193 prefixEnd_189193 57568560276256897906621 := by
  unfold tailWord_189193
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900435603593547437052233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4600290402395698291368155 6900435603593547437052233)
  ·
    refine ⟨5175326702695160577789175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6900435603593547437052233 5175326702695160577789175)
    ·
      refine ⟨7762990054042740866683763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5175326702695160577789175 7762990054042740866683763)
      ·
        refine ⟨11644485081064111300025645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762990054042740866683763 11644485081064111300025645)
        ·
          refine ⟨4366681905399041737509617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11644485081064111300025645 4366681905399041737509617)
          ·
            refine ⟨3275011429049281303132213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4366681905399041737509617 3275011429049281303132213)
            ·
              refine ⟨307032321473370122168645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3275011429049281303132213 307032321473370122168645)
              ·
                refine ⟨57568560276256897906621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307032321473370122168645 57568560276256897906621)
                ·
                  rfl

theorem cell19_189193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_189193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189193 prefixEnd_189193 := by exact prefixLift 189193
  have htrace : WordTrace (prefixWord ++ tailWord_189193) baseStart_189193 baseEnd_189193 := by
    simpa [prefixWord, tailWord_189193, baseEnd_189193] using wordTrace_append hprefix tailTrace_189193
  have hstable : (prefixWord ++ tailWord_189193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189193).length < 2 ^ (prefixWord ++ tailWord_189193).sum := by decide
  have hdescent : baseEnd_189193 < baseStart_189193 := by decide
  rcases family_descends (prefixWord ++ tailWord_189193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189210 : List Nat := [3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_189210 : Nat := 118140960795 + 189210 * 2 ^ 59
def prefixEnd_189210 : Nat := 4983230072969 + 3 ^ 40 * 189210 * 2
def baseEnd_189210 : Nat := 57573733118405895528797

theorem tailTrace_189210 : CollatzResearch.WordTrace tailWord_189210 prefixEnd_189210 57573733118405895528797 := by
  unfold tailWord_189210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725263911132989835105271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4600703763021306226947389 1725263911132989835105271)
  ·
    refine ⟨2587895866699484752657907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1725263911132989835105271 2587895866699484752657907)
    ·
      refine ⟨3881843800049227128986861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587895866699484752657907 3881843800049227128986861)
      ·
        refine ⟨1455691425018460173370073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3881843800049227128986861 1455691425018460173370073)
        ·
          refine ⟨1091768568763845130027555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455691425018460173370073 1091768568763845130027555)
          ·
            refine ⟨1637652853145767695041333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091768568763845130027555 1637652853145767695041333)
            ·
              refine ⟨153529954982415721410125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1637652853145767695041333 153529954982415721410125)
              ·
                refine ⟨57573733118405895528797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153529954982415721410125 57573733118405895528797)
                ·
                  rfl

theorem cell19_189210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_189210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189210 prefixEnd_189210 := by exact prefixLift 189210
  have htrace : WordTrace (prefixWord ++ tailWord_189210) baseStart_189210 baseEnd_189210 := by
    simpa [prefixWord, tailWord_189210, baseEnd_189210] using wordTrace_append hprefix tailTrace_189210
  have hstable : (prefixWord ++ tailWord_189210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189210).length < 2 ^ (prefixWord ++ tailWord_189210).sum := by decide
  have hdescent : baseEnd_189210 < baseStart_189210 := by decide
  rcases family_descends (prefixWord ++ tailWord_189210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189261 : List Nat := [1, 6, 1, 2, 3, 1, 2, 3]
def baseStart_189261 : Nat := 118140960795 + 189261 * 2 ^ 59
def prefixEnd_189261 : Nat := 4983230072969 + 3 ^ 40 * 189261 * 2
def baseEnd_189261 : Nat := 57589251644852888395325

theorem tailTrace_189261 : CollatzResearch.WordTrace tailWord_189261 prefixEnd_189261 57589251644852888395325 := by
  unfold tailWord_189261
  simp only [CollatzResearch.WordTrace]
  refine ⟨6902915767347195050527637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4601943844898130033685091 6902915767347195050527637)
  ·
    refine ⟨323574176594399767993483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6902915767347195050527637 323574176594399767993483)
    ·
      refine ⟨485361264891599651990225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323574176594399767993483 485361264891599651990225)
      ·
        refine ⟨364020948668699738992669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485361264891599651990225 364020948668699738992669)
        ·
          refine ⟨136507855750762402122251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364020948668699738992669 136507855750762402122251)
          ·
            refine ⟨204761783626143603183377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136507855750762402122251 204761783626143603183377)
            ·
              refine ⟨153571337719607702387533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204761783626143603183377 153571337719607702387533)
              ·
                refine ⟨57589251644852888395325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153571337719607702387533 57589251644852888395325)
                ·
                  rfl

theorem cell19_189261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_189261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189261 prefixEnd_189261 := by exact prefixLift 189261
  have htrace : WordTrace (prefixWord ++ tailWord_189261) baseStart_189261 baseEnd_189261 := by
    simpa [prefixWord, tailWord_189261, baseEnd_189261] using wordTrace_append hprefix tailTrace_189261
  have hstable : (prefixWord ++ tailWord_189261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189261).length < 2 ^ (prefixWord ++ tailWord_189261).sum := by decide
  have hdescent : baseEnd_189261 < baseStart_189261 := by decide
  rcases family_descends (prefixWord ++ tailWord_189261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189265 : List Nat := [1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_189265 : Nat := 118140960795 + 189265 * 2 ^ 59
def prefixEnd_189265 : Nat := 4983230072969 + 3 ^ 40 * 189265 * 2
def baseEnd_189265 : Nat := 57590468784182064306425

theorem tailTrace_189265 : CollatzResearch.WordTrace tailWord_189265 prefixEnd_189265 57590468784182064306425 := by
  unfold tailWord_189265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903061659332703733673249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4602041106221802489115499 6903061659332703733673249)
  ·
    refine ⟨5177296244499527800254937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6903061659332703733673249 5177296244499527800254937)
    ·
      refine ⟨3882972183374645850191203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5177296244499527800254937 3882972183374645850191203)
      ·
        refine ⟨5824458275061968775286805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882972183374645850191203 5824458275061968775286805)
        ·
          refine ⟨273021481643529786341569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5824458275061968775286805 273021481643529786341569)
          ·
            refine ⟨204766111232647339756177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273021481643529786341569 204766111232647339756177)
            ·
              refine ⟨153574583424485504817133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204766111232647339756177 153574583424485504817133)
              ·
                refine ⟨57590468784182064306425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153574583424485504817133 57590468784182064306425)
                ·
                  rfl

theorem cell19_189265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_189265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189265 prefixEnd_189265 := by exact prefixLift 189265
  have htrace : WordTrace (prefixWord ++ tailWord_189265) baseStart_189265 baseEnd_189265 := by
    simpa [prefixWord, tailWord_189265, baseEnd_189265] using wordTrace_append hprefix tailTrace_189265
  have hstable : (prefixWord ++ tailWord_189265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189265).length < 2 ^ (prefixWord ++ tailWord_189265).sum := by decide
  have hdescent : baseEnd_189265 < baseStart_189265 := by decide
  rcases family_descends (prefixWord ++ tailWord_189265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189269 : List Nat := [1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_189269 : Nat := 118140960795 + 189269 * 2 ^ 59
def prefixEnd_189269 : Nat := 4983230072969 + 3 ^ 40 * 189269 * 2
def baseEnd_189269 : Nat := 57591685923511240217525

theorem tailTrace_189269 : CollatzResearch.WordTrace tailWord_189269 prefixEnd_189269 57591685923511240217525 := by
  unfold tailWord_189269
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903207551318212416818861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4602138367545474944545907 6903207551318212416818861)
  ·
    refine ⟨2588702831744329656307073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6903207551318212416818861 2588702831744329656307073)
    ·
      refine ⟨1941527123808247242230305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2588702831744329656307073 1941527123808247242230305)
      ·
        refine ⟨1456145342856185431672729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1941527123808247242230305 1456145342856185431672729)
        ·
          refine ⟨1092109007142139073754547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456145342856185431672729 1092109007142139073754547)
          ·
            refine ⟨1638163510713208610631821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092109007142139073754547 1638163510713208610631821)
            ·
              refine ⟨614311316517453228986933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638163510713208610631821 614311316517453228986933)
              ·
                refine ⟨57591685923511240217525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 614311316517453228986933 57591685923511240217525)
                ·
                  rfl

theorem cell19_189269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_189269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189269 prefixEnd_189269 := by exact prefixLift 189269
  have htrace : WordTrace (prefixWord ++ tailWord_189269) baseStart_189269 baseEnd_189269 := by
    simpa [prefixWord, tailWord_189269, baseEnd_189269] using wordTrace_append hprefix tailTrace_189269
  have hstable : (prefixWord ++ tailWord_189269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189269).length < 2 ^ (prefixWord ++ tailWord_189269).sum := by decide
  have hdescent : baseEnd_189269 < baseStart_189269 := by decide
  rcases family_descends (prefixWord ++ tailWord_189269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189288 : List Nat := [2, 1, 4, 2, 1, 2, 7]
def baseStart_189288 : Nat := 118140960795 + 189288 * 2 ^ 59
def prefixEnd_189288 : Nat := 4983230072969 + 3 ^ 40 * 189288 * 2
def baseEnd_189288 : Nat := 19199155778441608598417

theorem tailTrace_189288 : CollatzResearch.WordTrace tailWord_189288 prefixEnd_189288 19199155778441608598417 := by
  unfold tailWord_189288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451950269124689330880259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4602600358832919107840345 3451950269124689330880259)
  ·
    refine ⟨5177925403687033996320389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3451950269124689330880259 5177925403687033996320389)
    ·
      refine ⟨970861013191318874310073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5177925403687033996320389 970861013191318874310073)
      ·
        refine ⟨728145759893489155732555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 970861013191318874310073 728145759893489155732555)
        ·
          refine ⟨1092218639840233733598833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728145759893489155732555 1092218639840233733598833)
          ·
            refine ⟨819163979880175300199125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092218639840233733598833 819163979880175300199125)
            ·
              refine ⟨19199155778441608598417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 819163979880175300199125 19199155778441608598417)
              ·
                rfl

theorem cell19_189288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_189288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189288 prefixEnd_189288 := by exact prefixLift 189288
  have htrace : WordTrace (prefixWord ++ tailWord_189288) baseStart_189288 baseEnd_189288 := by
    simpa [prefixWord, tailWord_189288, baseEnd_189288] using wordTrace_append hprefix tailTrace_189288
  have hstable : (prefixWord ++ tailWord_189288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189288).length < 2 ^ (prefixWord ++ tailWord_189288).sum := by decide
  have hdescent : baseEnd_189288 < baseStart_189288 := by decide
  rcases family_descends (prefixWord ++ tailWord_189288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189345 : List Nat := [1, 2, 3, 4, 1, 8]
def baseStart_189345 : Nat := 118140960795 + 189345 * 2 ^ 59
def prefixEnd_189345 : Nat := 4983230072969 + 3 ^ 40 * 189345 * 2
def baseEnd_189345 : Nat := 6401645730085064725381

theorem tailTrace_189345 : CollatzResearch.WordTrace tailWord_189345 prefixEnd_189345 6401645730085064725381 := by
  unfold tailWord_189345
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905979499042877396585489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4603986332695251597723659 6905979499042877396585489)
  ·
    refine ⟨5179484624282158047439117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6905979499042877396585489 5179484624282158047439117)
    ·
      refine ⟨1942306734105809267789669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5179484624282158047439117 1942306734105809267789669)
      ·
        refine ⟨364182512644839237710563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1942306734105809267789669 364182512644839237710563)
        ·
          refine ⟨546273768967258856565845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364182512644839237710563 546273768967258856565845)
          ·
            refine ⟨6401645730085064725381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 546273768967258856565845 6401645730085064725381)
            ·
              rfl

theorem cell19_189345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_189345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189345 prefixEnd_189345 := by exact prefixLift 189345
  have htrace : WordTrace (prefixWord ++ tailWord_189345) baseStart_189345 baseEnd_189345 := by
    simpa [prefixWord, tailWord_189345, baseEnd_189345] using wordTrace_append hprefix tailTrace_189345
  have hstable : (prefixWord ++ tailWord_189345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189345).length < 2 ^ (prefixWord ++ tailWord_189345).sum := by decide
  have hdescent : baseEnd_189345 < baseStart_189345 := by decide
  rcases family_descends (prefixWord ++ tailWord_189345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189402 : List Nat := [3, 1, 1, 2, 4, 2, 6]
def baseStart_189402 : Nat := 118140960795 + 189402 * 2 ^ 59
def prefixEnd_189402 : Nat := 4983230072969 + 3 ^ 40 * 189402 * 2
def baseEnd_189402 : Nat := 19210718602068779753869

theorem tailTrace_189402 : CollatzResearch.WordTrace tailWord_189402 prefixEnd_189402 19210718602068779753869 := by
  unfold tailWord_189402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727014614959094032852615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4605372306557584087606973 1727014614959094032852615)
  ·
    refine ⟨2590521922438641049278923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727014614959094032852615 2590521922438641049278923)
    ·
      refine ⟨3885782883657961573918385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590521922438641049278923 3885782883657961573918385)
      ·
        refine ⟨2914337162743471180438789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3885782883657961573918385 2914337162743471180438789)
        ·
          refine ⟨546438218014400846332273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2914337162743471180438789 546438218014400846332273)
          ·
            refine ⟨409828663510800634749205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546438218014400846332273 409828663510800634749205)
            ·
              refine ⟨19210718602068779753869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 409828663510800634749205 19210718602068779753869)
              ·
                rfl

theorem cell19_189402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_189402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189402 prefixEnd_189402 := by exact prefixLift 189402
  have htrace : WordTrace (prefixWord ++ tailWord_189402) baseStart_189402 baseEnd_189402 := by
    simpa [prefixWord, tailWord_189402, baseEnd_189402] using wordTrace_append hprefix tailTrace_189402
  have hstable : (prefixWord ++ tailWord_189402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189402).length < 2 ^ (prefixWord ++ tailWord_189402).sum := by decide
  have hdescent : baseEnd_189402 < baseStart_189402 := by decide
  rcases family_descends (prefixWord ++ tailWord_189402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189428 : List Nat := [2, 6, 2, 1, 2, 1, 2, 3]
def baseStart_189428 : Nat := 118140960795 + 189428 * 2 ^ 59
def prefixEnd_189428 : Nat := 4983230072969 + 3 ^ 40 * 189428 * 2
def baseEnd_189428 : Nat := 57640067211845982683759

theorem tailTrace_189428 : CollatzResearch.WordTrace tailWord_189428 prefixEnd_189428 57640067211845982683759 := by
  unfold tailWord_189428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454503378871091285928469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4606004505161455047904625 3454503378871091285928469)
  ·
    refine ⟨161929845884582404027897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3454503378871091285928469 161929845884582404027897)
    ·
      refine ⟨121447384413436803020923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161929845884582404027897 121447384413436803020923)
      ·
        refine ⟨182171076620155204531385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121447384413436803020923 182171076620155204531385)
        ·
          refine ⟨136628307465116403398539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182171076620155204531385 136628307465116403398539)
          ·
            refine ⟨204942461197674605097809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136628307465116403398539 204942461197674605097809)
            ·
              refine ⟨153706845898255953823357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204942461197674605097809 153706845898255953823357)
              ·
                refine ⟨57640067211845982683759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153706845898255953823357 57640067211845982683759)
                ·
                  rfl

theorem cell19_189428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_189428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189428 prefixEnd_189428 := by exact prefixLift 189428
  have htrace : WordTrace (prefixWord ++ tailWord_189428) baseStart_189428 baseEnd_189428 := by
    simpa [prefixWord, tailWord_189428, baseEnd_189428] using wordTrace_append hprefix tailTrace_189428
  have hstable : (prefixWord ++ tailWord_189428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189428).length < 2 ^ (prefixWord ++ tailWord_189428).sum := by decide
  have hdescent : baseEnd_189428 < baseStart_189428 := by decide
  rcases family_descends (prefixWord ++ tailWord_189428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189476 : List Nat := [2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_189476 : Nat := 118140960795 + 189476 * 2 ^ 59
def prefixEnd_189476 : Nat := 4983230072969 + 3 ^ 40 * 189476 * 2
def baseEnd_189476 : Nat := 57654672883796093616961

theorem tailTrace_189476 : CollatzResearch.WordTrace tailWord_189476 prefixEnd_189476 57654672883796093616961 := by
  unfold tailWord_189476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455378730784143384802141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4607171641045524513069521 3455378730784143384802141)
  ·
    refine ⟨1295767024044053769300803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3455378730784143384802141 1295767024044053769300803)
    ·
      refine ⟨1943650536066080653951205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295767024044053769300803 1943650536066080653951205)
      ·
        refine ⟨364434475512390122615851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1943650536066080653951205 364434475512390122615851)
        ·
          refine ⟨546651713268585183923777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364434475512390122615851 546651713268585183923777)
          ·
            refine ⟨409988784951438887942833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546651713268585183923777 409988784951438887942833)
            ·
              refine ⟨307491588713579165957125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409988784951438887942833 307491588713579165957125)
              ·
                refine ⟨57654672883796093616961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307491588713579165957125 57654672883796093616961)
                ·
                  rfl

theorem cell19_189476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_189476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189476 prefixEnd_189476 := by exact prefixLift 189476
  have htrace : WordTrace (prefixWord ++ tailWord_189476) baseStart_189476 baseEnd_189476 := by
    simpa [prefixWord, tailWord_189476, baseEnd_189476] using wordTrace_append hprefix tailTrace_189476
  have hstable : (prefixWord ++ tailWord_189476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189476).length < 2 ^ (prefixWord ++ tailWord_189476).sum := by decide
  have hdescent : baseEnd_189476 < baseStart_189476 := by decide
  rcases family_descends (prefixWord ++ tailWord_189476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189497 : List Nat := [1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_189497 : Nat := 118140960795 + 189497 * 2 ^ 59
def prefixEnd_189497 : Nat := 4983230072969 + 3 ^ 40 * 189497 * 2
def baseEnd_189497 : Nat := 57661062865274267150237

theorem tailTrace_189497 : CollatzResearch.WordTrace tailWord_189497 prefixEnd_189497 57661062865274267150237 := by
  unfold tailWord_189497
  simp only [CollatzResearch.WordTrace]
  refine ⟨6911523394492207356118745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4607682262994804904079163 6911523394492207356118745)
  ·
    refine ⟨5183642545869155517089059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6911523394492207356118745 5183642545869155517089059)
    ·
      refine ⟨7775463818803733275633589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183642545869155517089059 7775463818803733275633589)
      ·
        refine ⟨728949733012849994590649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7775463818803733275633589 728949733012849994590649)
        ·
          refine ⟨546712299759637495942987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728949733012849994590649 546712299759637495942987)
          ·
            refine ⟨820068449639456243914481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546712299759637495942987 820068449639456243914481)
            ·
              refine ⟨615051337229592182935861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820068449639456243914481 615051337229592182935861)
              ·
                refine ⟨57661062865274267150237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615051337229592182935861 57661062865274267150237)
                ·
                  rfl

theorem cell19_189497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_189497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189497 prefixEnd_189497 := by exact prefixLift 189497
  have htrace : WordTrace (prefixWord ++ tailWord_189497) baseStart_189497 baseEnd_189497 := by
    simpa [prefixWord, tailWord_189497, baseEnd_189497] using wordTrace_append hprefix tailTrace_189497
  have hstable : (prefixWord ++ tailWord_189497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189497).length < 2 ^ (prefixWord ++ tailWord_189497).sum := by decide
  have hdescent : baseEnd_189497 < baseStart_189497 := by decide
  rcases family_descends (prefixWord ++ tailWord_189497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189573 : List Nat := [1, 3, 1, 1, 6, 1, 6]
def baseStart_189573 : Nat := 118140960795 + 189573 * 2 ^ 59
def prefixEnd_189573 : Nat := 4983230072969 + 3 ^ 40 * 189573 * 2
def baseEnd_189573 : Nat := 19228062837509536487047

theorem tailTrace_189573 : CollatzResearch.WordTrace tailWord_189573 prefixEnd_189573 19228062837509536487047 := by
  unfold tailWord_189573
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914295342216872335885373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4609530228144581557256915 6914295342216872335885373)
  ·
    refine ⟨2592860753331327125957015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6914295342216872335885373 2592860753331327125957015)
    ·
      refine ⟨3889291129996990688935523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592860753331327125957015 3889291129996990688935523)
      ·
        refine ⟨5833936694995486033403285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889291129996990688935523 5833936694995486033403285)
        ·
          refine ⟨273465782577913407815779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5833936694995486033403285 273465782577913407815779)
          ·
            refine ⟨410198673866870111723669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273465782577913407815779 410198673866870111723669)
            ·
              refine ⟨19228062837509536487047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 410198673866870111723669 19228062837509536487047)
              ·
                rfl

theorem cell19_189573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_189573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189573 prefixEnd_189573 := by exact prefixLift 189573
  have htrace : WordTrace (prefixWord ++ tailWord_189573) baseStart_189573 baseEnd_189573 := by
    simpa [prefixWord, tailWord_189573, baseEnd_189573] using wordTrace_append hprefix tailTrace_189573
  have hstable : (prefixWord ++ tailWord_189573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189573).length < 2 ^ (prefixWord ++ tailWord_189573).sum := by decide
  have hdescent : baseEnd_189573 < baseStart_189573 := by decide
  rcases family_descends (prefixWord ++ tailWord_189573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189607 : List Nat := [1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_189607 : Nat := 118140960795 + 189607 * 2 ^ 59
def prefixEnd_189607 : Nat := 4983230072969 + 3 ^ 40 * 189607 * 2
def baseEnd_189607 : Nat := 57694534196826604705493

theorem tailTrace_189607 : CollatzResearch.WordTrace tailWord_189607 prefixEnd_189607 57694534196826604705493 := by
  unfold tailWord_189607
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915535424093696142623075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4610356949395797428415383 6915535424093696142623075)
  ·
    refine ⟨10373303136140544213934613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915535424093696142623075 10373303136140544213934613)
    ·
      refine ⟨486248584506588010028185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10373303136140544213934613 486248584506588010028185)
      ·
        refine ⟨364686438379941007521139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486248584506588010028185 364686438379941007521139)
        ·
          refine ⟨547029657569911511281709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364686438379941007521139 547029657569911511281709)
          ·
            refine ⟨205136121588716816730641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547029657569911511281709 205136121588716816730641)
            ·
              refine ⟨153852091191537612547981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205136121588716816730641 153852091191537612547981)
              ·
                refine ⟨57694534196826604705493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153852091191537612547981 57694534196826604705493)
                ·
                  rfl

theorem cell19_189607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_189607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189607 prefixEnd_189607 := by exact prefixLift 189607
  have htrace : WordTrace (prefixWord ++ tailWord_189607) baseStart_189607 baseEnd_189607 := by
    simpa [prefixWord, tailWord_189607, baseEnd_189607] using wordTrace_append hprefix tailTrace_189607
  have hstable : (prefixWord ++ tailWord_189607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189607).length < 2 ^ (prefixWord ++ tailWord_189607).sum := by decide
  have hdescent : baseEnd_189607 < baseStart_189607 := by decide
  rcases family_descends (prefixWord ++ tailWord_189607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189630 : List Nat := [4, 2, 1, 1, 3, 1, 7]
def baseStart_189630 : Nat := 118140960795 + 189630 * 2 ^ 59
def prefixEnd_189630 : Nat := 4983230072969 + 3 ^ 40 * 189630 * 2
def baseEnd_189630 : Nat := 19233844249323122064773

theorem tailTrace_189630 : CollatzResearch.WordTrace tailWord_189630 prefixEnd_189630 19233844249323122064773 := by
  unfold tailWord_189630
  simp only [CollatzResearch.WordTrace]
  refine ⟨864546787876296383838793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4610916202006914047140229 864546787876296383838793)
  ·
    refine ⟨648410090907222287879095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 864546787876296383838793 648410090907222287879095)
    ·
      refine ⟨972615136360833431818643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 648410090907222287879095 972615136360833431818643)
      ·
        refine ⟨1458922704541250147727965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972615136360833431818643 1458922704541250147727965)
        ·
          refine ⟨547096014202968805397987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1458922704541250147727965 547096014202968805397987)
          ·
            refine ⟨820644021304453208096981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547096014202968805397987 820644021304453208096981)
            ·
              refine ⟨19233844249323122064773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 820644021304453208096981 19233844249323122064773)
              ·
                rfl

theorem cell19_189630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_189630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189630 prefixEnd_189630 := by exact prefixLift 189630
  have htrace : WordTrace (prefixWord ++ tailWord_189630) baseStart_189630 baseEnd_189630 := by
    simpa [prefixWord, tailWord_189630, baseEnd_189630] using wordTrace_append hprefix tailTrace_189630
  have hstable : (prefixWord ++ tailWord_189630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189630).length < 2 ^ (prefixWord ++ tailWord_189630).sum := by decide
  have hdescent : baseEnd_189630 < baseStart_189630 := by decide
  rcases family_descends (prefixWord ++ tailWord_189630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189704 : List Nat := [2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_189704 : Nat := 118140960795 + 189704 * 2 ^ 59
def prefixEnd_189704 : Nat := 4983230072969 + 3 ^ 40 * 189704 * 2
def baseEnd_189704 : Nat := 57724049825559120549673

theorem tailTrace_189704 : CollatzResearch.WordTrace tailWord_189704 prefixEnd_189704 57724049825559120549673 := by
  unfold tailWord_189704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459536652371140854452083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4612715536494854472602777 3459536652371140854452083)
  ·
    refine ⟨5189304978556711281678125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3459536652371140854452083 5189304978556711281678125)
    ·
      refine ⟨1945989366958766730629297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5189304978556711281678125 1945989366958766730629297)
      ·
        refine ⟨1459492025219075047971973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1945989366958766730629297 1459492025219075047971973)
        ·
          refine ⟨273654754728576571494745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1459492025219075047971973 273654754728576571494745)
          ·
            refine ⟨205241066046432428621059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273654754728576571494745 205241066046432428621059)
            ·
              refine ⟨307861599069648642931589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205241066046432428621059 307861599069648642931589)
              ·
                refine ⟨57724049825559120549673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307861599069648642931589 57724049825559120549673)
                ·
                  rfl

theorem cell19_189704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_189704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189704 prefixEnd_189704 := by exact prefixLift 189704
  have htrace : WordTrace (prefixWord ++ tailWord_189704) baseStart_189704 baseEnd_189704 := by
    simpa [prefixWord, tailWord_189704, baseEnd_189704] using wordTrace_append hprefix tailTrace_189704
  have hstable : (prefixWord ++ tailWord_189704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189704).length < 2 ^ (prefixWord ++ tailWord_189704).sum := by decide
  have hdescent : baseEnd_189704 < baseStart_189704 := by decide
  rcases family_descends (prefixWord ++ tailWord_189704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189784 : List Nat := [2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_189784 : Nat := 118140960795 + 189784 * 2 ^ 59
def prefixEnd_189784 : Nat := 4983230072969 + 3 ^ 40 * 189784 * 2
def baseEnd_189784 : Nat := 57748392612142638771677

theorem tailTrace_189784 : CollatzResearch.WordTrace tailWord_189784 prefixEnd_189784 57748392612142638771677 := by
  unfold tailWord_189784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460995572226227685908203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4614660762968303581210937 3460995572226227685908203)
  ·
    refine ⟨5191493358339341528862305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3460995572226227685908203 5191493358339341528862305)
    ·
      refine ⟨3893620018754506146646729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5191493358339341528862305 3893620018754506146646729)
      ·
        refine ⟨2920215014065879609985047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3893620018754506146646729 2920215014065879609985047)
        ·
          refine ⟨4380322521098819414977571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920215014065879609985047 4380322521098819414977571)
          ·
            refine ⟨6570483781648229122466357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380322521098819414977571 6570483781648229122466357)
            ·
              refine ⟨615982854529521480231221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6570483781648229122466357 615982854529521480231221)
              ·
                refine ⟨57748392612142638771677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615982854529521480231221 57748392612142638771677)
                ·
                  rfl

theorem cell19_189784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_189784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189784 prefixEnd_189784 := by exact prefixLift 189784
  have htrace : WordTrace (prefixWord ++ tailWord_189784) baseStart_189784 baseEnd_189784 := by
    simpa [prefixWord, tailWord_189784, baseEnd_189784] using wordTrace_append hprefix tailTrace_189784
  have hstable : (prefixWord ++ tailWord_189784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189784).length < 2 ^ (prefixWord ++ tailWord_189784).sum := by decide
  have hdescent : baseEnd_189784 < baseStart_189784 := by decide
  rcases family_descends (prefixWord ++ tailWord_189784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189799 : List Nat := [1, 1, 5, 1, 5, 1, 5]
def baseStart_189799 : Nat := 118140960795 + 189799 * 2 ^ 59
def prefixEnd_189799 : Nat := 4983230072969 + 3 ^ 40 * 189799 * 2
def baseEnd_189799 : Nat := 19250985628209016146101

theorem tailTrace_189799 : CollatzResearch.WordTrace tailWord_189799 prefixEnd_189799 19250985628209016146101 := by
  unfold tailWord_189799
  simp only [CollatzResearch.WordTrace]
  refine ⟨6922538239398112933612451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4615025492932075289074967 6922538239398112933612451)
  ·
    refine ⟨10383807359097169400418677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6922538239398112933612451 10383807359097169400418677)
    ·
      refine ⟨973481939915359631289251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10383807359097169400418677 973481939915359631289251)
      ·
        refine ⟨1460222909873039446933877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973481939915359631289251 1460222909873039446933877)
        ·
          refine ⟨136895897800597448150051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1460222909873039446933877 136895897800597448150051)
          ·
            refine ⟨205343846700896172225077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136895897800597448150051 205343846700896172225077)
            ·
              refine ⟨19250985628209016146101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205343846700896172225077 19250985628209016146101)
              ·
                rfl

theorem cell19_189799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_189799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189799 prefixEnd_189799 := by exact prefixLift 189799
  have htrace : WordTrace (prefixWord ++ tailWord_189799) baseStart_189799 baseEnd_189799 := by
    simpa [prefixWord, tailWord_189799, baseEnd_189799] using wordTrace_append hprefix tailTrace_189799
  have hstable : (prefixWord ++ tailWord_189799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189799).length < 2 ^ (prefixWord ++ tailWord_189799).sum := by decide
  have hdescent : baseEnd_189799 < baseStart_189799 := by decide
  rcases family_descends (prefixWord ++ tailWord_189799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189877 : List Nat := [1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_189877 : Nat := 118140960795 + 189877 * 2 ^ 59
def prefixEnd_189877 : Nat := 4983230072969 + 3 ^ 40 * 189877 * 2
def baseEnd_189877 : Nat := 57776691101545978704757

theorem tailTrace_189877 : CollatzResearch.WordTrace tailWord_189877 prefixEnd_189877 57776691101545978704757 := by
  unfold tailWord_189877
  simp only [CollatzResearch.WordTrace]
  refine ⟨6925383133115532254951885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4616922088743688169967923 6925383133115532254951885)
  ·
    refine ⟨2597018674918324595606957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6925383133115532254951885 2597018674918324595606957)
    ·
      refine ⟨973882003094371723352609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2597018674918324595606957 973882003094371723352609)
      ·
        refine ⟨730411502320778792514457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 973882003094371723352609 730411502320778792514457)
        ·
          refine ⟨547808626740584094385843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730411502320778792514457 547808626740584094385843)
          ·
            refine ⟨821712940110876141578765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547808626740584094385843 821712940110876141578765)
            ·
              refine ⟨308142352541578553092037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821712940110876141578765 308142352541578553092037)
              ·
                refine ⟨57776691101545978704757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308142352541578553092037 57776691101545978704757)
                ·
                  rfl

theorem cell19_189877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_189877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189877 prefixEnd_189877 := by exact prefixLift 189877
  have htrace : WordTrace (prefixWord ++ tailWord_189877) baseStart_189877 baseEnd_189877 := by
    simpa [prefixWord, tailWord_189877, baseEnd_189877] using wordTrace_append hprefix tailTrace_189877
  have hstable : (prefixWord ++ tailWord_189877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189877).length < 2 ^ (prefixWord ++ tailWord_189877).sum := by decide
  have hdescent : baseEnd_189877 < baseStart_189877 := by decide
  rcases family_descends (prefixWord ++ tailWord_189877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189896 : List Nat := [2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_189896 : Nat := 118140960795 + 189896 * 2 ^ 59
def prefixEnd_189896 : Nat := 4983230072969 + 3 ^ 40 * 189896 * 2
def baseEnd_189896 : Nat := 57782472513359564282483

theorem tailTrace_189896 : CollatzResearch.WordTrace tailWord_189896 prefixEnd_189896 57782472513359564282483 := by
  unfold tailWord_189896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463038060023349249946771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4617384080031132333262361 3463038060023349249946771)
  ·
    refine ⟨5194557090035023874920157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3463038060023349249946771 5194557090035023874920157)
    ·
      refine ⟨1947958908763133953095059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5194557090035023874920157 1947958908763133953095059)
      ·
        refine ⟨2921938363144700929642589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947958908763133953095059 2921938363144700929642589)
        ·
          refine ⟨1095726886179262848615971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2921938363144700929642589 1095726886179262848615971)
          ·
            refine ⟨1643590329268894272923957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095726886179262848615971 1643590329268894272923957)
            ·
              refine ⟨154086593368958838086621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1643590329268894272923957 154086593368958838086621)
              ·
                refine ⟨57782472513359564282483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154086593368958838086621 57782472513359564282483)
                ·
                  rfl

theorem cell19_189896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_189896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189896 prefixEnd_189896 := by exact prefixLift 189896
  have htrace : WordTrace (prefixWord ++ tailWord_189896) baseStart_189896 baseEnd_189896 := by
    simpa [prefixWord, tailWord_189896, baseEnd_189896] using wordTrace_append hprefix tailTrace_189896
  have hstable : (prefixWord ++ tailWord_189896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189896).length < 2 ^ (prefixWord ++ tailWord_189896).sum := by decide
  have hdescent : baseEnd_189896 < baseStart_189896 := by decide
  rcases family_descends (prefixWord ++ tailWord_189896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189953 : List Nat := [1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_189953 : Nat := 118140960795 + 189953 * 2 ^ 59
def prefixEnd_189953 : Nat := 4983230072969 + 3 ^ 40 * 189953 * 2
def baseEnd_189953 : Nat := 57799816748800321015661

theorem tailTrace_189953 : CollatzResearch.WordTrace tailWord_189953 prefixEnd_189953 57799816748800321015661 := by
  unfold tailWord_189953
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928155080840197234718513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4618770053893464823145675 6928155080840197234718513)
  ·
    refine ⟨5196116310630147926038885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6928155080840197234718513 5196116310630147926038885)
    ·
      refine ⟨974271808243152736132291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5196116310630147926038885 974271808243152736132291)
      ·
        refine ⟨1461407712364729104198437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974271808243152736132291 1461407712364729104198437)
        ·
          refine ⟨274013946068386707037207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1461407712364729104198437 274013946068386707037207)
          ·
            refine ⟨411020919102580060555811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274013946068386707037207 411020919102580060555811)
            ·
              refine ⟨616531378653870090833717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411020919102580060555811 616531378653870090833717)
              ·
                refine ⟨57799816748800321015661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616531378653870090833717 57799816748800321015661)
                ·
                  rfl

theorem cell19_189953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_189953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_189953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_189953 prefixEnd_189953 := by exact prefixLift 189953
  have htrace : WordTrace (prefixWord ++ tailWord_189953) baseStart_189953 baseEnd_189953 := by
    simpa [prefixWord, tailWord_189953, baseEnd_189953] using wordTrace_append hprefix tailTrace_189953
  have hstable : (prefixWord ++ tailWord_189953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189953).length < 2 ^ (prefixWord ++ tailWord_189953).sum := by decide
  have hdescent : baseEnd_189953 < baseStart_189953 := by decide
  rcases family_descends (prefixWord ++ tailWord_189953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190029 : List Nat := [1, 6, 1, 1, 3, 7]
def baseStart_190029 : Nat := 118140960795 + 190029 * 2 ^ 59
def prefixEnd_190029 : Nat := 4983230072969 + 3 ^ 40 * 190029 * 2
def baseEnd_190029 : Nat := 6424771377339407036285

theorem tailTrace_190029 : CollatzResearch.WordTrace tailWord_190029 prefixEnd_190029 6424771377339407036285 := by
  unfold tailWord_190029
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930927028564862214485141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4620618019043241476323427 6930927028564862214485141)
  ·
    refine ⟨324887204463977916303991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6930927028564862214485141 324887204463977916303991)
    ·
      refine ⟨487330806695966874455987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324887204463977916303991 487330806695966874455987)
      ·
        refine ⟨730996210043950311683981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487330806695966874455987 730996210043950311683981)
        ·
          refine ⟨274123578766481366881493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730996210043950311683981 274123578766481366881493)
          ·
            refine ⟨6424771377339407036285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 274123578766481366881493 6424771377339407036285)
            ·
              rfl

theorem cell19_190029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_190029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190029 prefixEnd_190029 := by exact prefixLift 190029
  have htrace : WordTrace (prefixWord ++ tailWord_190029) baseStart_190029 baseEnd_190029 := by
    simpa [prefixWord, tailWord_190029, baseEnd_190029] using wordTrace_append hprefix tailTrace_190029
  have hstable : (prefixWord ++ tailWord_190029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190029).length < 2 ^ (prefixWord ++ tailWord_190029).sum := by decide
  have hdescent : baseEnd_190029 < baseStart_190029 := by decide
  rcases family_descends (prefixWord ++ tailWord_190029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190120 : List Nat := [2, 1, 7, 1, 1, 1, 1, 5]
def baseStart_190120 : Nat := 118140960795 + 190120 * 2 ^ 59
def prefixEnd_190120 : Nat := 4983230072969 + 3 ^ 40 * 190120 * 2
def baseEnd_190120 : Nat := 57850632315793415304095

theorem tailTrace_190120 : CollatzResearch.WordTrace tailWord_190120 prefixEnd_190120 57850632315793415304095 := by
  unfold tailWord_190120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3467123035617592378023907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4622830714156789837365209 3467123035617592378023907)
  ·
    refine ⟨5200684553426388567035861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3467123035617592378023907 5200684553426388567035861)
    ·
      refine ⟨121891044220930982039903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5200684553426388567035861 121891044220930982039903)
      ·
        refine ⟨182836566331396473059855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121891044220930982039903 182836566331396473059855)
        ·
          refine ⟨274254849497094709589783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182836566331396473059855 274254849497094709589783)
          ·
            refine ⟨411382274245642064384675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274254849497094709589783 411382274245642064384675)
            ·
              refine ⟨617073411368463096577013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411382274245642064384675 617073411368463096577013)
              ·
                refine ⟨57850632315793415304095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617073411368463096577013 57850632315793415304095)
                ·
                  rfl

theorem cell19_190120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_190120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190120 prefixEnd_190120 := by exact prefixLift 190120
  have htrace : WordTrace (prefixWord ++ tailWord_190120) baseStart_190120 baseEnd_190120 := by
    simpa [prefixWord, tailWord_190120, baseEnd_190120] using wordTrace_append hprefix tailTrace_190120
  have hstable : (prefixWord ++ tailWord_190120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190120).length < 2 ^ (prefixWord ++ tailWord_190120).sum := by decide
  have hdescent : baseEnd_190120 < baseStart_190120 := by decide
  rcases family_descends (prefixWord ++ tailWord_190120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190162 : List Nat := [3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_190162 : Nat := 118140960795 + 190162 * 2 ^ 59
def prefixEnd_190162 : Nat := 4983230072969 + 3 ^ 40 * 190162 * 2
def baseEnd_190162 : Nat := 57863412278749762370647

theorem tailTrace_190162 : CollatzResearch.WordTrace tailWord_190162 prefixEnd_190162 57863412278749762370647 := by
  unfold tailWord_190162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733944484270756482269185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4623851958055350619384493 1733944484270756482269185)
  ·
    refine ⟨1300458363203067361701889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1733944484270756482269185 1300458363203067361701889)
    ·
      refine ⟨975343772402300521276417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1300458363203067361701889 975343772402300521276417)
      ·
        refine ⟨731507829301725390957313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975343772402300521276417 731507829301725390957313)
        ·
          refine ⟨548630871976294043217985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731507829301725390957313 548630871976294043217985)
          ·
            refine ⟨411473153982220532413489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548630871976294043217985 411473153982220532413489)
            ·
              refine ⟨308604865486665399310117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411473153982220532413489 308604865486665399310117)
              ·
                refine ⟨57863412278749762370647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308604865486665399310117 57863412278749762370647)
                ·
                  rfl

theorem cell19_190162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_190162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190162 prefixEnd_190162 := by exact prefixLift 190162
  have htrace : WordTrace (prefixWord ++ tailWord_190162) baseStart_190162 baseEnd_190162 := by
    simpa [prefixWord, tailWord_190162, baseEnd_190162] using wordTrace_append hprefix tailTrace_190162
  have hstable : (prefixWord ++ tailWord_190162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190162).length < 2 ^ (prefixWord ++ tailWord_190162).sum := by decide
  have hdescent : baseEnd_190162 < baseStart_190162 := by decide
  rcases family_descends (prefixWord ++ tailWord_190162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190223 : List Nat := [1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_190223 : Nat := 118140960795 + 190223 * 2 ^ 59
def prefixEnd_190223 : Nat := 4983230072969 + 3 ^ 40 * 190223 * 2
def baseEnd_190223 : Nat := 57881973653519695014925

theorem tailTrace_190223 : CollatzResearch.WordTrace tailWord_190223 prefixEnd_190223 57881973653519695014925 := by
  unfold tailWord_190223
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938002789862033347047323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4625335193241355564698215 6938002789862033347047323)
  ·
    refine ⟨10407004184793050020570985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6938002789862033347047323 10407004184793050020570985)
    ·
      refine ⟨7805253138594787515428239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10407004184793050020570985 7805253138594787515428239)
      ·
        refine ⟨11707879707892181273142359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805253138594787515428239 11707879707892181273142359)
        ·
          refine ⟨17561819561838271909713539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11707879707892181273142359 17561819561838271909713539)
          ·
            refine ⟨26342729342757407864570309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17561819561838271909713539 26342729342757407864570309)
            ·
              refine ⟨4939261751767013974606933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26342729342757407864570309 4939261751767013974606933)
              ·
                refine ⟨57881973653519695014925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4939261751767013974606933 57881973653519695014925)
                ·
                  rfl

theorem cell19_190223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_190223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190223 prefixEnd_190223 := by exact prefixLift 190223
  have htrace : WordTrace (prefixWord ++ tailWord_190223) baseStart_190223 baseEnd_190223 := by
    simpa [prefixWord, tailWord_190223, baseEnd_190223] using wordTrace_append hprefix tailTrace_190223
  have hstable : (prefixWord ++ tailWord_190223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190223).length < 2 ^ (prefixWord ++ tailWord_190223).sum := by decide
  have hdescent : baseEnd_190223 < baseStart_190223 := by decide
  rcases family_descends (prefixWord ++ tailWord_190223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190259 : List Nat := [1, 1, 1, 2, 7, 1, 6]
def baseStart_190259 : Nat := 118140960795 + 190259 * 2 ^ 59
def prefixEnd_190259 : Nat := 4983230072969 + 3 ^ 40 * 190259 * 2
def baseEnd_190259 : Nat := 19297642635827426071609

theorem tailTrace_190259 : CollatzResearch.WordTrace tailWord_190259 prefixEnd_190259 19297642635827426071609 := by
  unfold tailWord_190259
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939315817731611495357831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4626210545154407663571887 6939315817731611495357831)
  ·
    refine ⟨10408973726597417243036747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6939315817731611495357831 10408973726597417243036747)
    ·
      refine ⟨15613460589896125864555121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10408973726597417243036747 15613460589896125864555121)
      ·
        refine ⟨11710095442422094398416341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15613460589896125864555121 11710095442422094398416341)
        ·
          refine ⟨274455361931767837462883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11710095442422094398416341 274455361931767837462883)
          ·
            refine ⟨411683042897651756194325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274455361931767837462883 411683042897651756194325)
            ·
              refine ⟨19297642635827426071609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411683042897651756194325 19297642635827426071609)
              ·
                rfl

theorem cell19_190259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_190259 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190259 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190259 prefixEnd_190259 := by exact prefixLift 190259
  have htrace : WordTrace (prefixWord ++ tailWord_190259) baseStart_190259 baseEnd_190259 := by
    simpa [prefixWord, tailWord_190259, baseEnd_190259] using wordTrace_append hprefix tailTrace_190259
  have hstable : (prefixWord ++ tailWord_190259).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190259).length < 2 ^ (prefixWord ++ tailWord_190259).sum := by decide
  have hdescent : baseEnd_190259 < baseStart_190259 := by decide
  rcases family_descends (prefixWord ++ tailWord_190259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190316 : List Nat := [2, 2, 1, 1, 4, 4, 5]
def baseStart_190316 : Nat := 118140960795 + 190316 * 2 ^ 59
def prefixEnd_190316 : Nat := 4983230072969 + 3 ^ 40 * 190316 * 2
def baseEnd_190316 : Nat := 19303424047641011649335

theorem tailTrace_190316 : CollatzResearch.WordTrace tailWord_190316 prefixEnd_190316 19303424047641011649335 := by
  unfold tailWord_190316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3470697389262555115091401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4627596519016740153455201 3470697389262555115091401)
  ·
    refine ⟨2603023041946916336318551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3470697389262555115091401 2603023041946916336318551)
    ·
      refine ⟨3904534562920374504477827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603023041946916336318551 3904534562920374504477827)
      ·
        refine ⟨5856801844380561756716741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904534562920374504477827 5856801844380561756716741)
        ·
          refine ⟨1098150345821355329384389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5856801844380561756716741 1098150345821355329384389)
          ·
            refine ⟨205903189841504124259573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1098150345821355329384389 205903189841504124259573)
            ·
              refine ⟨19303424047641011649335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205903189841504124259573 19303424047641011649335)
              ·
                rfl

theorem cell19_190316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_190316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190316 prefixEnd_190316 := by exact prefixLift 190316
  have htrace : WordTrace (prefixWord ++ tailWord_190316) baseStart_190316 baseEnd_190316 := by
    simpa [prefixWord, tailWord_190316, baseEnd_190316] using wordTrace_append hprefix tailTrace_190316
  have hstable : (prefixWord ++ tailWord_190316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190316).length < 2 ^ (prefixWord ++ tailWord_190316).sum := by decide
  have hdescent : baseEnd_190316 < baseStart_190316 := by decide
  rcases family_descends (prefixWord ++ tailWord_190316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190394 : List Nat := [3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_190394 : Nat := 118140960795 + 190394 * 2 ^ 59
def prefixEnd_190394 : Nat := 4983230072969 + 3 ^ 40 * 190394 * 2
def baseEnd_190394 : Nat := 57934006359841965214459

theorem tailTrace_190394 : CollatzResearch.WordTrace tailWord_190394 prefixEnd_190394 57934006359841965214459 := by
  unfold tailWord_190394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736059918060632387880559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4629493114828353034348157 1736059918060632387880559)
  ·
    refine ⟨2604089877090948581820839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1736059918060632387880559 2604089877090948581820839)
    ·
      refine ⟨3906134815636422872731259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604089877090948581820839 3906134815636422872731259)
      ·
        refine ⟨5859202223454634309096889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3906134815636422872731259 5859202223454634309096889)
        ·
          refine ⟨4394401667590975731822667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5859202223454634309096889 4394401667590975731822667)
          ·
            refine ⟨6591602501386463597734001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394401667590975731822667 6591602501386463597734001)
            ·
              refine ⟨4943701876039847698300501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591602501386463597734001 4943701876039847698300501)
              ·
                refine ⟨57934006359841965214459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4943701876039847698300501 57934006359841965214459)
                ·
                  rfl

theorem cell19_190394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_190394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190394 prefixEnd_190394 := by exact prefixLift 190394
  have htrace : WordTrace (prefixWord ++ tailWord_190394) baseStart_190394 baseEnd_190394 := by
    simpa [prefixWord, tailWord_190394, baseEnd_190394] using wordTrace_append hprefix tailTrace_190394
  have hstable : (prefixWord ++ tailWord_190394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190394).length < 2 ^ (prefixWord ++ tailWord_190394).sum := by decide
  have hdescent : baseEnd_190394 < baseStart_190394 := by decide
  rcases family_descends (prefixWord ++ tailWord_190394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190411 : List Nat := [1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_190411 : Nat := 118140960795 + 190411 * 2 ^ 59
def prefixEnd_190411 : Nat := 4983230072969 + 3 ^ 40 * 190411 * 2
def baseEnd_190411 : Nat := 57939179201990962836635

theorem tailTrace_190411 : CollatzResearch.WordTrace tailWord_190411 prefixEnd_190411 57939179201990962836635 := by
  unfold tailWord_190411
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944859713180941454891087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4629906475453960969927391 6944859713180941454891087)
  ·
    refine ⟨10417289569771412182336631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944859713180941454891087 10417289569771412182336631)
    ·
      refine ⟨15625934354657118273504947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417289569771412182336631 15625934354657118273504947)
      ·
        refine ⟨23438901531985677410257421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15625934354657118273504947 23438901531985677410257421)
        ·
          refine ⟨8789588074494629028846533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23438901531985677410257421 8789588074494629028846533)
          ·
            refine ⟨1648047763967742942908725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8789588074494629028846533 1648047763967742942908725)
            ·
              refine ⟨154504477871975900897693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1648047763967742942908725 154504477871975900897693)
              ·
                refine ⟨57939179201990962836635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154504477871975900897693 57939179201990962836635)
                ·
                  rfl

theorem cell19_190411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_190411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190411 prefixEnd_190411 := by exact prefixLift 190411
  have htrace : WordTrace (prefixWord ++ tailWord_190411) baseStart_190411 baseEnd_190411 := by
    simpa [prefixWord, tailWord_190411, baseEnd_190411] using wordTrace_append hprefix tailTrace_190411
  have hstable : (prefixWord ++ tailWord_190411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190411).length < 2 ^ (prefixWord ++ tailWord_190411).sum := by decide
  have hdescent : baseEnd_190411 < baseStart_190411 := by decide
  rcases family_descends (prefixWord ++ tailWord_190411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190485 : List Nat := [1, 3, 2, 1, 6, 1, 5]
def baseStart_190485 : Nat := 118140960795 + 190485 * 2 ^ 59
def prefixEnd_190485 : Nat := 4983230072969 + 3 ^ 40 * 190485 * 2
def baseEnd_190485 : Nat := 19320565426526905730663

theorem tailTrace_190485 : CollatzResearch.WordTrace tailWord_190485 prefixEnd_190485 19320565426526905730663 := by
  unfold tailWord_190485
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947558714912852093084909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631705809941901395389939 6947558714912852093084909)
  ·
    refine ⟨2605334518092319534906841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6947558714912852093084909 2605334518092319534906841)
    ·
      refine ⟨1954000888569239651180131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2605334518092319534906841 1954000888569239651180131)
      ·
        refine ⟨2931001332853859476770197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954000888569239651180131 2931001332853859476770197)
        ·
          refine ⟨137390687477524662973603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2931001332853859476770197 137390687477524662973603)
          ·
            refine ⟨206086031216286994460405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137390687477524662973603 206086031216286994460405)
            ·
              refine ⟨19320565426526905730663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206086031216286994460405 19320565426526905730663)
              ·
                rfl

theorem cell19_190485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_190485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190485 prefixEnd_190485 := by exact prefixLift 190485
  have htrace : WordTrace (prefixWord ++ tailWord_190485) baseStart_190485 baseEnd_190485 := by
    simpa [prefixWord, tailWord_190485, baseEnd_190485] using wordTrace_append hprefix tailTrace_190485
  have hstable : (prefixWord ++ tailWord_190485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190485).length < 2 ^ (prefixWord ++ tailWord_190485).sum := by decide
  have hdescent : baseEnd_190485 < baseStart_190485 := by decide
  rcases family_descends (prefixWord ++ tailWord_190485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190506 : List Nat := [3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_190506 : Nat := 118140960795 + 190506 * 2 ^ 59
def prefixEnd_190506 : Nat := 4983230072969 + 3 ^ 40 * 190506 * 2
def baseEnd_190506 : Nat := 57968086261058890725265

theorem tailTrace_190506 : CollatzResearch.WordTrace tailWord_190506 prefixEnd_190506 57968086261058890725265 := by
  unfold tailWord_190506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737081161959193169899843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4632216431891181786399581 1737081161959193169899843)
  ·
    refine ⟨2605621742938789754849765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737081161959193169899843 2605621742938789754849765)
    ·
      refine ⟨488554076801023079034331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2605621742938789754849765 488554076801023079034331)
      ·
        refine ⟨732831115201534618551497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488554076801023079034331 732831115201534618551497)
        ·
          refine ⟨549623336401150963913623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732831115201534618551497 549623336401150963913623)
          ·
            refine ⟨824435004601726445870435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549623336401150963913623 824435004601726445870435)
            ·
              refine ⟨1236652506902589668805653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824435004601726445870435 1236652506902589668805653)
              ·
                refine ⟨57968086261058890725265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1236652506902589668805653 57968086261058890725265)
                ·
                  rfl

theorem cell19_190506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_190506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190506 prefixEnd_190506 := by exact prefixLift 190506
  have htrace : WordTrace (prefixWord ++ tailWord_190506) baseStart_190506 baseEnd_190506 := by
    simpa [prefixWord, tailWord_190506, baseEnd_190506] using wordTrace_append hprefix tailTrace_190506
  have hstable : (prefixWord ++ tailWord_190506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190506).length < 2 ^ (prefixWord ++ tailWord_190506).sum := by decide
  have hdescent : baseEnd_190506 < baseStart_190506 := by decide
  rcases family_descends (prefixWord ++ tailWord_190506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190527 : List Nat := [1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_190527 : Nat := 118140960795 + 190527 * 2 ^ 59
def prefixEnd_190527 : Nat := 4983230072969 + 3 ^ 40 * 190527 * 2
def baseEnd_190527 : Nat := 57974476242537064258541

theorem tailTrace_190527 : CollatzResearch.WordTrace tailWord_190527 prefixEnd_190527 57974476242537064258541 := by
  unfold tailWord_190527
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949090580760693266113835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4632727053840462177409223 6949090580760693266113835)
  ·
    refine ⟨10423635871141039899170753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6949090580760693266113835 10423635871141039899170753)
    ·
      refine ⟨7817726903355779924378065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10423635871141039899170753 7817726903355779924378065)
      ·
        refine ⟨5863295177516834943283549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7817726903355779924378065 5863295177516834943283549)
        ·
          refine ⟨2198735691568813103731331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5863295177516834943283549 2198735691568813103731331)
          ·
            refine ⟨3298103537353219655596997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198735691568813103731331 3298103537353219655596997)
            ·
              refine ⟨618394413253728685424437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3298103537353219655596997 618394413253728685424437)
              ·
                refine ⟨57974476242537064258541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 618394413253728685424437 57974476242537064258541)
                ·
                  rfl

theorem cell19_190527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_190527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190527 prefixEnd_190527 := by exact prefixLift 190527
  have htrace : WordTrace (prefixWord ++ tailWord_190527) baseStart_190527 baseEnd_190527 := by
    simpa [prefixWord, tailWord_190527, baseEnd_190527] using wordTrace_append hprefix tailTrace_190527
  have hstable : (prefixWord ++ tailWord_190527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190527).length < 2 ^ (prefixWord ++ tailWord_190527).sum := by decide
  have hdescent : baseEnd_190527 < baseStart_190527 := by decide
  rcases family_descends (prefixWord ++ tailWord_190527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190546 : List Nat := [3, 2, 2, 1, 11]
def baseStart_190546 : Nat := 118140960795 + 190546 * 2 ^ 59
def prefixEnd_190546 : Nat := 4983230072969 + 3 ^ 40 * 190546 * 2
def baseEnd_190546 : Nat := 2147416950161135179121

theorem tailTrace_190546 : CollatzResearch.WordTrace tailWord_190546 prefixEnd_190546 2147416950161135179121 := by
  unfold tailWord_190546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737445891922964877763873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4633189045127906340703661 1737445891922964877763873)
  ·
    refine ⟨1303084418942223658322905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1737445891922964877763873 1303084418942223658322905)
    ·
      refine ⟨977313314206667743742179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1303084418942223658322905 977313314206667743742179)
      ·
        refine ⟨1465969971310001615613269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977313314206667743742179 1465969971310001615613269)
        ·
          refine ⟨2147416950161135179121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1465969971310001615613269 2147416950161135179121)
          ·
            rfl

theorem cell19_190546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 11].length) (baseStart_190546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190546 prefixEnd_190546 := by exact prefixLift 190546
  have htrace : WordTrace (prefixWord ++ tailWord_190546) baseStart_190546 baseEnd_190546 := by
    simpa [prefixWord, tailWord_190546, baseEnd_190546] using wordTrace_append hprefix tailTrace_190546
  have hstable : (prefixWord ++ tailWord_190546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190546).length < 2 ^ (prefixWord ++ tailWord_190546).sum := by decide
  have hdescent : baseEnd_190546 < baseStart_190546 := by decide
  rcases family_descends (prefixWord ++ tailWord_190546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190637 : List Nat := [1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_190637 : Nat := 118140960795 + 190637 * 2 ^ 59
def prefixEnd_190637 : Nat := 4983230072969 + 3 ^ 40 * 190637 * 2
def baseEnd_190637 : Nat := 58007947574089401813797

theorem tailTrace_190637 : CollatzResearch.WordTrace tailWord_190637 prefixEnd_190637 58007947574089401813797 := by
  unfold tailWord_190637
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953102610362182052618165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4635401740241454701745443 6953102610362182052618165)
  ·
    refine ⟨651853369721454567432953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6953102610362182052618165 651853369721454567432953)
    ·
      refine ⟨488890027291090925574715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 651853369721454567432953 488890027291090925574715)
      ·
        refine ⟨733335040936636388362073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488890027291090925574715 733335040936636388362073)
        ·
          refine ⟨550001280702477291271555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733335040936636388362073 550001280702477291271555)
          ·
            refine ⟨825001921053715936907333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550001280702477291271555 825001921053715936907333)
            ·
              refine ⟨154687860197571738170125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 825001921053715936907333 154687860197571738170125)
              ·
                refine ⟨58007947574089401813797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154687860197571738170125 58007947574089401813797)
                ·
                  rfl

theorem cell19_190637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_190637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190637 prefixEnd_190637 := by exact prefixLift 190637
  have htrace : WordTrace (prefixWord ++ tailWord_190637) baseStart_190637 baseEnd_190637 := by
    simpa [prefixWord, tailWord_190637, baseEnd_190637] using wordTrace_append hprefix tailTrace_190637
  have hstable : (prefixWord ++ tailWord_190637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190637).length < 2 ^ (prefixWord ++ tailWord_190637).sum := by decide
  have hdescent : baseEnd_190637 < baseStart_190637 := by decide
  rcases family_descends (prefixWord ++ tailWord_190637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190698 : List Nat := [3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_190698 : Nat := 118140960795 + 190698 * 2 ^ 59
def prefixEnd_190698 : Nat := 4983230072969 + 3 ^ 40 * 190698 * 2
def baseEnd_190698 : Nat := 58026508948859334458075

theorem tailTrace_190698 : CollatzResearch.WordTrace tailWord_190698 prefixEnd_190698 58026508948859334458075 := by
  unfold tailWord_190698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738831865785297367647187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4636884975427459647059165 1738831865785297367647187)
  ·
    refine ⟨2608247798677946051470781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1738831865785297367647187 2608247798677946051470781)
    ·
      refine ⟨978092924504229769301543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2608247798677946051470781 978092924504229769301543)
      ·
        refine ⟨1467139386756344653952315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978092924504229769301543 1467139386756344653952315)
        ·
          refine ⟨2200709080134516980928473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467139386756344653952315 2200709080134516980928473)
          ·
            refine ⟨1650531810100887735696355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200709080134516980928473 1650531810100887735696355)
            ·
              refine ⟨2475797715151331603544533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650531810100887735696355 2475797715151331603544533)
              ·
                refine ⟨58026508948859334458075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2475797715151331603544533 58026508948859334458075)
                ·
                  rfl

theorem cell19_190698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_190698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190698 prefixEnd_190698 := by exact prefixLift 190698
  have htrace : WordTrace (prefixWord ++ tailWord_190698) baseStart_190698 baseEnd_190698 := by
    simpa [prefixWord, tailWord_190698, baseEnd_190698] using wordTrace_append hprefix tailTrace_190698
  have hstable : (prefixWord ++ tailWord_190698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190698).length < 2 ^ (prefixWord ++ tailWord_190698).sum := by decide
  have hdescent : baseEnd_190698 < baseStart_190698 := by decide
  rcases family_descends (prefixWord ++ tailWord_190698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190772 : List Nat := [2, 5, 1, 1, 1, 3, 6]
def baseStart_190772 : Nat := 118140960795 + 190772 * 2 ^ 59
def prefixEnd_190772 : Nat := 4983230072969 + 3 ^ 40 * 190772 * 2
def baseEnd_190772 : Nat := 19349675342149696271143

theorem tailTrace_190772 : CollatzResearch.WordTrace tailWord_190772 prefixEnd_190772 19349675342149696271143 := by
  unfold tailWord_190772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479013232436550054391285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4638684309915400072521713 3479013232436550054391285)
  ·
    refine ⟨326157490540926567599183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3479013232436550054391285 326157490540926567599183)
    ·
      refine ⟨489236235811389851398775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326157490540926567599183 489236235811389851398775)
      ·
        refine ⟨733854353717084777098163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489236235811389851398775 733854353717084777098163)
        ·
          refine ⟨1100781530575627165647245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733854353717084777098163 1100781530575627165647245)
          ·
            refine ⟨412793073965860187117717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1100781530575627165647245 412793073965860187117717)
            ·
              refine ⟨19349675342149696271143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 412793073965860187117717 19349675342149696271143)
              ·
                rfl

theorem cell19_190772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_190772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190772 prefixEnd_190772 := by exact prefixLift 190772
  have htrace : WordTrace (prefixWord ++ tailWord_190772) baseStart_190772 baseEnd_190772 := by
    simpa [prefixWord, tailWord_190772, baseEnd_190772] using wordTrace_append hprefix tailTrace_190772
  have hstable : (prefixWord ++ tailWord_190772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190772).length < 2 ^ (prefixWord ++ tailWord_190772).sum := by decide
  have hdescent : baseEnd_190772 < baseStart_190772 := by decide
  rcases family_descends (prefixWord ++ tailWord_190772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190905 : List Nat := [1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_190905 : Nat := 118140960795 + 190905 * 2 ^ 59
def prefixEnd_190905 : Nat := 4983230072969 + 3 ^ 40 * 190905 * 2
def baseEnd_190905 : Nat := 58089495909144187857511

theorem tailTrace_190905 : CollatzResearch.WordTrace tailWord_190905 prefixEnd_190905 58089495909144187857511 := by
  unfold tailWord_190905
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962877373391263823374169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4641918248927509215582779 6962877373391263823374169)
  ·
    refine ⟨5222158030043447867530627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6962877373391263823374169 5222158030043447867530627)
    ·
      refine ⟨7833237045065171801295941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222158030043447867530627 7833237045065171801295941)
      ·
        refine ⟨1468731945949719712742989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7833237045065171801295941 1468731945949719712742989)
        ·
          refine ⟨550774479731144892278621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1468731945949719712742989 550774479731144892278621)
          ·
            refine ⟨206540429899179334604483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 550774479731144892278621 206540429899179334604483)
            ·
              refine ⟨309810644848769001906725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206540429899179334604483 309810644848769001906725)
              ·
                refine ⟨58089495909144187857511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309810644848769001906725 58089495909144187857511)
                ·
                  rfl

theorem cell19_190905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_190905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_190905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_190905 prefixEnd_190905 := by exact prefixLift 190905
  have htrace : WordTrace (prefixWord ++ tailWord_190905) baseStart_190905 baseEnd_190905 := by
    simpa [prefixWord, tailWord_190905, baseEnd_190905] using wordTrace_append hprefix tailTrace_190905
  have hstable : (prefixWord ++ tailWord_190905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190905).length < 2 ^ (prefixWord ++ tailWord_190905).sum := by decide
  have hdescent : baseEnd_190905 < baseStart_190905 := by decide
  rcases family_descends (prefixWord ++ tailWord_190905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191070 : List Nat := [4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_191070 : Nat := 118140960795 + 191070 * 2 ^ 59
def prefixEnd_191070 : Nat := 4983230072969 + 3 ^ 40 * 191070 * 2
def baseEnd_191070 : Nat := 58139702906472694190395

theorem tailTrace_191070 : CollatzResearch.WordTrace tailWord_191070 prefixEnd_191070 58139702906472694190395 := by
  unfold tailWord_191070
  simp only [CollatzResearch.WordTrace]
  refine ⟨871111927224187125391333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4645930278528998002087109 871111927224187125391333)
  ·
    refine ⟨163333486354535086010875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 871111927224187125391333 163333486354535086010875)
    ·
      refine ⟨245000229531802629016313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163333486354535086010875 245000229531802629016313)
      ·
        refine ⟨183750172148851971762235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245000229531802629016313 183750172148851971762235)
        ·
          refine ⟨275625258223277957643353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183750172148851971762235 275625258223277957643353)
          ·
            refine ⟨206718943667458468232515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275625258223277957643353 206718943667458468232515)
            ·
              refine ⟨310078415501187702348773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206718943667458468232515 310078415501187702348773)
              ·
                refine ⟨58139702906472694190395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310078415501187702348773 58139702906472694190395)
                ·
                  rfl

theorem cell19_191070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_191070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191070 prefixEnd_191070 := by exact prefixLift 191070
  have htrace : WordTrace (prefixWord ++ tailWord_191070) baseStart_191070 baseEnd_191070 := by
    simpa [prefixWord, tailWord_191070, baseEnd_191070] using wordTrace_append hprefix tailTrace_191070
  have hstable : (prefixWord ++ tailWord_191070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191070).length < 2 ^ (prefixWord ++ tailWord_191070).sum := by decide
  have hdescent : baseEnd_191070 < baseStart_191070 := by decide
  rcases family_descends (prefixWord ++ tailWord_191070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191093 : List Nat := [1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_191093 : Nat := 118140960795 + 191093 * 2 ^ 59
def prefixEnd_191093 : Nat := 4983230072969 + 3 ^ 40 * 191093 * 2
def baseEnd_191093 : Nat := 58146701457615455679221

theorem tailTrace_191093 : CollatzResearch.WordTrace tailWord_191093 prefixEnd_191093 58146701457615455679221 := by
  unfold tailWord_191093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6969734296710171931217933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4646489531140114620811955 6969734296710171931217933)
  ·
    refine ⟨2613650361266314474206725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6969734296710171931217933 2613650361266314474206725)
    ·
      refine ⟨490059442737433963913761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2613650361266314474206725 490059442737433963913761)
      ·
        refine ⟨367544582053075472935321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490059442737433963913761 367544582053075472935321)
        ·
          refine ⟨275658436539806604701491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367544582053075472935321 275658436539806604701491)
          ·
            refine ⟨413487654809709907052237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275658436539806604701491 413487654809709907052237)
            ·
              refine ⟨155057870553641215144589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413487654809709907052237 155057870553641215144589)
              ·
                refine ⟨58146701457615455679221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155057870553641215144589 58146701457615455679221)
                ·
                  rfl

theorem cell19_191093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_191093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191093 prefixEnd_191093 := by exact prefixLift 191093
  have htrace : WordTrace (prefixWord ++ tailWord_191093) baseStart_191093 baseEnd_191093 := by
    simpa [prefixWord, tailWord_191093, baseEnd_191093] using wordTrace_append hprefix tailTrace_191093
  have hstable : (prefixWord ++ tailWord_191093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191093).length < 2 ^ (prefixWord ++ tailWord_191093).sum := by decide
  have hdescent : baseEnd_191093 < baseStart_191093 := by decide
  rcases family_descends (prefixWord ++ tailWord_191093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191146 : List Nat := [3, 1, 5, 2, 2, 1, 2, 3]
def baseStart_191146 : Nat := 118140960795 + 191146 * 2 ^ 59
def prefixEnd_191146 : Nat := 4983230072969 + 3 ^ 40 * 191146 * 2
def baseEnd_191146 : Nat := 58162828553727036501299

theorem tailTrace_191146 : CollatzResearch.WordTrace tailWord_191146 prefixEnd_191146 58162828553727036501299 := by
  unfold tailWord_191146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742916841379540495724323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4647778243678774655264861 1742916841379540495724323)
  ·
    refine ⟨2614375262069310743586485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1742916841379540495724323 2614375262069310743586485)
    ·
      refine ⟨245097680818997882211233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2614375262069310743586485 245097680818997882211233)
      ·
        refine ⟨183823260614248411658425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245097680818997882211233 183823260614248411658425)
        ·
          refine ⟨137867445460686308743819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183823260614248411658425 137867445460686308743819)
          ·
            refine ⟨206801168191029463115729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137867445460686308743819 206801168191029463115729)
            ·
              refine ⟨155100876143272097336797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206801168191029463115729 155100876143272097336797)
              ·
                refine ⟨58162828553727036501299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155100876143272097336797 58162828553727036501299)
                ·
                  rfl

theorem cell19_191146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_191146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191146 prefixEnd_191146 := by exact prefixLift 191146
  have htrace : WordTrace (prefixWord ++ tailWord_191146) baseStart_191146 baseEnd_191146 := by
    simpa [prefixWord, tailWord_191146, baseEnd_191146] using wordTrace_append hprefix tailTrace_191146
  have hstable : (prefixWord ++ tailWord_191146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191146).length < 2 ^ (prefixWord ++ tailWord_191146).sum := by decide
  have hdescent : baseEnd_191146 < baseStart_191146 := by decide
  rcases family_descends (prefixWord ++ tailWord_191146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191150 : List Nat := [4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_191150 : Nat := 118140960795 + 191150 * 2 ^ 59
def prefixEnd_191150 : Nat := 4983230072969 + 3 ^ 40 * 191150 * 2
def baseEnd_191150 : Nat := 58164045693056212412399

theorem tailTrace_191150 : CollatzResearch.WordTrace tailWord_191150 prefixEnd_191150 58164045693056212412399 := by
  unfold tailWord_191150
  simp only [CollatzResearch.WordTrace]
  refine ⟨871476657187958833255363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4647875505002447110695269 871476657187958833255363)
  ·
    refine ⟨1307214985781938249883045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 871476657187958833255363 1307214985781938249883045)
    ·
      refine ⟨245102809834113421853071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1307214985781938249883045 245102809834113421853071)
      ·
        refine ⟨367654214751170132779607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245102809834113421853071 367654214751170132779607)
        ·
          refine ⟨551481322126755199169411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367654214751170132779607 551481322126755199169411)
          ·
            refine ⟨827221983190132798754117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551481322126755199169411 827221983190132798754117)
            ·
              refine ⟨155104121848149899766397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 827221983190132798754117 155104121848149899766397)
              ·
                refine ⟨58164045693056212412399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155104121848149899766397 58164045693056212412399)
                ·
                  rfl

theorem cell19_191150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_191150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191150 prefixEnd_191150 := by exact prefixLift 191150
  have htrace : WordTrace (prefixWord ++ tailWord_191150) baseStart_191150 baseEnd_191150 := by
    simpa [prefixWord, tailWord_191150, baseEnd_191150] using wordTrace_append hprefix tailTrace_191150
  have hstable : (prefixWord ++ tailWord_191150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191150).length < 2 ^ (prefixWord ++ tailWord_191150).sum := by decide
  have hdescent : baseEnd_191150 < baseStart_191150 := by decide
  rcases family_descends (prefixWord ++ tailWord_191150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191169 : List Nat := [1, 2, 6, 2, 1, 2, 5]
def baseStart_191169 : Nat := 118140960795 + 191169 * 2 ^ 59
def prefixEnd_191169 : Nat := 4983230072969 + 3 ^ 40 * 191169 * 2
def baseEnd_191169 : Nat := 19389942368289932663375

theorem tailTrace_191169 : CollatzResearch.WordTrace tailWord_191169 prefixEnd_191169 19389942368289932663375 := by
  unfold tailWord_191169
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972506244434836910984561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4648337496289891273989707 6972506244434836910984561)
  ·
    refine ⟨5229379683326127683238421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6972506244434836910984561 5229379683326127683238421)
    ·
      refine ⟨245127172655912235151801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5229379683326127683238421 245127172655912235151801)
      ·
        refine ⟨183845379491934176363851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245127172655912235151801 183845379491934176363851)
        ·
          refine ⟨275768069237901264545777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183845379491934176363851 275768069237901264545777)
          ·
            refine ⟨206826051928425948409333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275768069237901264545777 206826051928425948409333)
            ·
              refine ⟨19389942368289932663375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206826051928425948409333 19389942368289932663375)
              ·
                rfl

theorem cell19_191169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_191169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191169 prefixEnd_191169 := by exact prefixLift 191169
  have htrace : WordTrace (prefixWord ++ tailWord_191169) baseStart_191169 baseEnd_191169 := by
    simpa [prefixWord, tailWord_191169, baseEnd_191169] using wordTrace_append hprefix tailTrace_191169
  have hstable : (prefixWord ++ tailWord_191169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191169).length < 2 ^ (prefixWord ++ tailWord_191169).sum := by decide
  have hdescent : baseEnd_191169 < baseStart_191169 := by decide
  rcases family_descends (prefixWord ++ tailWord_191169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191192 : List Nat := [2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_191192 : Nat := 118140960795 + 191192 * 2 ^ 59
def prefixEnd_191192 : Nat := 4983230072969 + 3 ^ 40 * 191192 * 2
def baseEnd_191192 : Nat := 58176825656012559478951

theorem tailTrace_191192 : CollatzResearch.WordTrace tailWord_191192 prefixEnd_191192 58176825656012559478951 := by
  unfold tailWord_191192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486672561675755919535915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4648896748901007892714553 3486672561675755919535915)
  ·
    refine ⟨5230008842513633879303873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486672561675755919535915 5230008842513633879303873)
    ·
      refine ⟨3922506631885225409477905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230008842513633879303873 3922506631885225409477905)
      ·
        refine ⟨2941879973913919057108429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3922506631885225409477905 2941879973913919057108429)
        ·
          refine ⟨1103204990217719646415661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2941879973913919057108429 1103204990217719646415661)
          ·
            refine ⟨413701871331644867405873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1103204990217719646415661 413701871331644867405873)
            ·
              refine ⟨310276403498733650554405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413701871331644867405873 310276403498733650554405)
              ·
                refine ⟨58176825656012559478951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310276403498733650554405 58176825656012559478951)
                ·
                  rfl

theorem cell19_191192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_191192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191192 prefixEnd_191192 := by exact prefixLift 191192
  have htrace : WordTrace (prefixWord ++ tailWord_191192) baseStart_191192 baseEnd_191192 := by
    simpa [prefixWord, tailWord_191192, baseEnd_191192] using wordTrace_append hprefix tailTrace_191192
  have hstable : (prefixWord ++ tailWord_191192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191192).length < 2 ^ (prefixWord ++ tailWord_191192).sum := by decide
  have hdescent : baseEnd_191192 < baseStart_191192 := by decide
  rcases family_descends (prefixWord ++ tailWord_191192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191230 : List Nat := [4, 2, 2, 1, 2, 8]
def baseStart_191230 : Nat := 118140960795 + 191230 * 2 ^ 59
def prefixEnd_191230 : Nat := 4983230072969 + 3 ^ 40 * 191230 * 2
def baseEnd_191230 : Nat := 6465376497737747848267

theorem tailTrace_191230 : CollatzResearch.WordTrace tailWord_191230 prefixEnd_191230 6465376497737747848267 := by
  unfold tailWord_191230
  simp only [CollatzResearch.WordTrace]
  refine ⟨871841387151730541119393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4649820731475896219303429 871841387151730541119393)
  ·
    refine ⟨653881040363797905839545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 871841387151730541119393 653881040363797905839545)
    ·
      refine ⟨490410780272848429379659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 653881040363797905839545 490410780272848429379659)
      ·
        refine ⟨735616170409272644069489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490410780272848429379659 735616170409272644069489)
        ·
          refine ⟨551712127806954483052117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735616170409272644069489 551712127806954483052117)
          ·
            refine ⟨6465376497737747848267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 551712127806954483052117 6465376497737747848267)
            ·
              rfl

theorem cell19_191230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_191230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191230 prefixEnd_191230 := by exact prefixLift 191230
  have htrace : WordTrace (prefixWord ++ tailWord_191230) baseStart_191230 baseEnd_191230 := by
    simpa [prefixWord, tailWord_191230, baseEnd_191230] using wordTrace_append hprefix tailTrace_191230
  have hstable : (prefixWord ++ tailWord_191230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191230).length < 2 ^ (prefixWord ++ tailWord_191230).sum := by decide
  have hdescent : baseEnd_191230 < baseStart_191230 := by decide
  rcases family_descends (prefixWord ++ tailWord_191230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191266 : List Nat := [3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_191266 : Nat := 118140960795 + 191266 * 2 ^ 59
def prefixEnd_191266 : Nat := 4983230072969 + 3 ^ 40 * 191266 * 2
def baseEnd_191266 : Nat := 58199342733602313834305

theorem tailTrace_191266 : CollatzResearch.WordTrace tailWord_191266 prefixEnd_191266 58199342733602313834305 := by
  unfold tailWord_191266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744011031270855619316413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4650696083388948318177101 1744011031270855619316413)
  ·
    refine ⟨654004136726570857243655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1744011031270855619316413 654004136726570857243655)
    ·
      refine ⟨981006205089856285865483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654004136726570857243655 981006205089856285865483)
      ·
        refine ⟨1471509307634784428798225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981006205089856285865483 1471509307634784428798225)
        ·
          refine ⟨1103631980726088321598669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471509307634784428798225 1103631980726088321598669)
          ·
            refine ⟨413861992772283120599501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1103631980726088321598669 413861992772283120599501)
            ·
              refine ⟨155198247289606170224813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413861992772283120599501 155198247289606170224813)
              ·
                refine ⟨58199342733602313834305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155198247289606170224813 58199342733602313834305)
                ·
                  rfl

theorem cell19_191266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_191266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191266 prefixEnd_191266 := by exact prefixLift 191266
  have htrace : WordTrace (prefixWord ++ tailWord_191266) baseStart_191266 baseEnd_191266 := by
    simpa [prefixWord, tailWord_191266, baseEnd_191266] using wordTrace_append hprefix tailTrace_191266
  have hstable : (prefixWord ++ tailWord_191266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191266).length < 2 ^ (prefixWord ++ tailWord_191266).sum := by decide
  have hdescent : baseEnd_191266 < baseStart_191266 := by decide
  rcases family_descends (prefixWord ++ tailWord_191266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191327 : List Nat := [1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_191327 : Nat := 118140960795 + 191327 * 2 ^ 59
def prefixEnd_191327 : Nat := 4983230072969 + 3 ^ 40 * 191327 * 2
def baseEnd_191327 : Nat := 58217904108372246478583

theorem tailTrace_191327 : CollatzResearch.WordTrace tailWord_191327 prefixEnd_191327 58217904108372246478583 := by
  unfold tailWord_191327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978268977862429895236235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4652179318574953263490823 6978268977862429895236235)
  ·
    refine ⟨10467403466793644842854353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6978268977862429895236235 10467403466793644842854353)
    ·
      refine ⟨7850552600095233632140765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10467403466793644842854353 7850552600095233632140765)
      ·
        refine ⟨2943957225035712612052787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7850552600095233632140765 2943957225035712612052787)
        ·
          refine ⟨4415935837553568918079181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943957225035712612052787 4415935837553568918079181)
          ·
            refine ⟨1655975939082588344279693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4415935837553568918079181 1655975939082588344279693)
            ·
              refine ⟨620990977155970629104885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1655975939082588344279693 620990977155970629104885)
              ·
                refine ⟨58217904108372246478583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 620990977155970629104885 58217904108372246478583)
                ·
                  rfl

theorem cell19_191327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_191327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191327 prefixEnd_191327 := by exact prefixLift 191327
  have htrace : WordTrace (prefixWord ++ tailWord_191327) baseStart_191327 baseEnd_191327 := by
    simpa [prefixWord, tailWord_191327, baseEnd_191327] using wordTrace_append hprefix tailTrace_191327
  have hstable : (prefixWord ++ tailWord_191327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191327).length < 2 ^ (prefixWord ++ tailWord_191327).sum := by decide
  have hdescent : baseEnd_191327 < baseStart_191327 := by decide
  rcases family_descends (prefixWord ++ tailWord_191327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191342 : List Nat := [4, 1, 2, 3, 2, 2, 5]
def baseStart_191342 : Nat := 118140960795 + 191342 * 2 ^ 59
def prefixEnd_191342 : Nat := 4983230072969 + 3 ^ 40 * 191342 * 2
def baseEnd_191342 : Nat := 19407489460285552048403

theorem tailTrace_191342 : CollatzResearch.WordTrace tailWord_191342 prefixEnd_191342 19407489460285552048403 := by
  unfold tailWord_191342
  simp only [CollatzResearch.WordTrace]
  refine ⟨872352009101010932129035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4652544048538724971354853 872352009101010932129035)
  ·
    refine ⟨1308528013651516398193553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872352009101010932129035 1308528013651516398193553)
    ·
      refine ⟨981396010238637298645165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308528013651516398193553 981396010238637298645165)
      ·
        refine ⟨368023503839488986991937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 981396010238637298645165 368023503839488986991937)
        ·
          refine ⟨276017627879616740243953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368023503839488986991937 276017627879616740243953)
          ·
            refine ⟨207013220909712555182965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276017627879616740243953 207013220909712555182965)
            ·
              refine ⟨19407489460285552048403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207013220909712555182965 19407489460285552048403)
              ·
                rfl

theorem cell19_191342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_191342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191342 prefixEnd_191342 := by exact prefixLift 191342
  have htrace : WordTrace (prefixWord ++ tailWord_191342) baseStart_191342 baseEnd_191342 := by
    simpa [prefixWord, tailWord_191342, baseEnd_191342] using wordTrace_append hprefix tailTrace_191342
  have hstable : (prefixWord ++ tailWord_191342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191342).length < 2 ^ (prefixWord ++ tailWord_191342).sum := by decide
  have hdescent : baseEnd_191342 < baseStart_191342 := by decide
  rcases family_descends (prefixWord ++ tailWord_191342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191346 : List Nat := [3, 2, 1, 2, 1, 1, 9]
def baseStart_191346 : Nat := 118140960795 + 191346 * 2 ^ 59
def prefixEnd_191346 : Nat := 4983230072969 + 3 ^ 40 * 191346 * 2
def baseEnd_191346 : Nat := 19407895173395277352103

theorem tailTrace_191346 : CollatzResearch.WordTrace tailWord_191346 prefixEnd_191346 19407895173395277352103 := by
  unfold tailWord_191346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744740491198399035044473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4652641309862397426785261 1744740491198399035044473)
  ·
    refine ⟨1308555368398799276283355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1744740491198399035044473 1308555368398799276283355)
    ·
      refine ⟨1962833052598198914425033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308555368398799276283355 1962833052598198914425033)
      ·
        refine ⟨1472124789448649185818775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1962833052598198914425033 1472124789448649185818775)
        ·
          refine ⟨2208187184172973778728163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472124789448649185818775 2208187184172973778728163)
          ·
            refine ⟨3312280776259460668092245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208187184172973778728163 3312280776259460668092245)
            ·
              refine ⟨19407895173395277352103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3312280776259460668092245 19407895173395277352103)
              ·
                rfl

theorem cell19_191346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_191346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191346 prefixEnd_191346 := by exact prefixLift 191346
  have htrace : WordTrace (prefixWord ++ tailWord_191346) baseStart_191346 baseEnd_191346 := by
    simpa [prefixWord, tailWord_191346, baseEnd_191346] using wordTrace_append hprefix tailTrace_191346
  have hstable : (prefixWord ++ tailWord_191346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191346).length < 2 ^ (prefixWord ++ tailWord_191346).sum := by decide
  have hdescent : baseEnd_191346 < baseStart_191346 := by decide
  rcases family_descends (prefixWord ++ tailWord_191346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191365 : List Nat := [1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_191365 : Nat := 118140960795 + 191365 * 2 ^ 59
def prefixEnd_191365 : Nat := 4983230072969 + 3 ^ 40 * 191365 * 2
def baseEnd_191365 : Nat := 58229466931999417634035

theorem tailTrace_191365 : CollatzResearch.WordTrace tailWord_191365 prefixEnd_191365 58229466931999417634035 := by
  unfold tailWord_191365
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979654951724762385119549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4653103301149841590079699 6979654951724762385119549)
  ·
    refine ⟨2617370606896785894419831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6979654951724762385119549 2617370606896785894419831)
    ·
      refine ⟨3926055910345178841629747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2617370606896785894419831 3926055910345178841629747)
      ·
        refine ⟨5889083865517768262444621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3926055910345178841629747 5889083865517768262444621)
        ·
          refine ⟨2208406449569163098416733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5889083865517768262444621 2208406449569163098416733)
          ·
            refine ⟨828152418588436161906275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2208406449569163098416733 828152418588436161906275)
            ·
              refine ⟨1242228627882654242859413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828152418588436161906275 1242228627882654242859413)
              ·
                refine ⟨58229466931999417634035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1242228627882654242859413 58229466931999417634035)
                ·
                  rfl

theorem cell19_191365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_191365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191365 prefixEnd_191365 := by exact prefixLift 191365
  have htrace : WordTrace (prefixWord ++ tailWord_191365) baseStart_191365 baseEnd_191365 := by
    simpa [prefixWord, tailWord_191365, baseEnd_191365] using wordTrace_append hprefix tailTrace_191365
  have hstable : (prefixWord ++ tailWord_191365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191365).length < 2 ^ (prefixWord ++ tailWord_191365).sum := by decide
  have hdescent : baseEnd_191365 < baseStart_191365 := by decide
  rcases family_descends (prefixWord ++ tailWord_191365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191439 : List Nat := [1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_191439 : Nat := 118140960795 + 191439 * 2 ^ 59
def prefixEnd_191439 : Nat := 4983230072969 + 3 ^ 40 * 191439 * 2
def baseEnd_191439 : Nat := 58251984009589171989389

theorem tailTrace_191439 : CollatzResearch.WordTrace tailWord_191439 prefixEnd_191439 58251984009589171989389 := by
  unfold tailWord_191439
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982353953456673023313371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4654902635637782015542247 6982353953456673023313371)
  ·
    refine ⟨10473530930185009534970057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6982353953456673023313371 10473530930185009534970057)
    ·
      refine ⟨7855148197638757151227543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10473530930185009534970057 7855148197638757151227543)
      ·
        refine ⟨11782722296458135726841315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7855148197638757151227543 11782722296458135726841315)
        ·
          refine ⟨17674083444687203590261973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11782722296458135726841315 17674083444687203590261973)
          ·
            refine ⟨414236330734856334146765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17674083444687203590261973 414236330734856334146765)
            ·
              refine ⟨155338624025571125305037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414236330734856334146765 155338624025571125305037)
              ·
                refine ⟨58251984009589171989389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155338624025571125305037 58251984009589171989389)
                ·
                  rfl

theorem cell19_191439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_191439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191439 prefixEnd_191439 := by exact prefixLift 191439
  have htrace : WordTrace (prefixWord ++ tailWord_191439) baseStart_191439 baseEnd_191439 := by
    simpa [prefixWord, tailWord_191439, baseEnd_191439] using wordTrace_append hprefix tailTrace_191439
  have hstable : (prefixWord ++ tailWord_191439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191439).length < 2 ^ (prefixWord ++ tailWord_191439).sum := by decide
  have hdescent : baseEnd_191439 < baseStart_191439 := by decide
  rcases family_descends (prefixWord ++ tailWord_191439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191490 : List Nat := [3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_191490 : Nat := 118140960795 + 191490 * 2 ^ 59
def prefixEnd_191490 : Nat := 4983230072969 + 3 ^ 40 * 191490 * 2
def baseEnd_191490 : Nat := 58267502536036164855917

theorem tailTrace_191490 : CollatzResearch.WordTrace tailWord_191490 prefixEnd_191490 58267502536036164855917 := by
  unfold tailWord_191490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746053519067977183354981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4656142717514605822279949 1746053519067977183354981)
  ·
    refine ⟨327385034825245721879059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1746053519067977183354981 327385034825245721879059)
    ·
      refine ⟨491077552237868582818589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327385034825245721879059 491077552237868582818589)
      ·
        refine ⟨184154082089200718556971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491077552237868582818589 184154082089200718556971)
        ·
          refine ⟨276231123133801077835457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184154082089200718556971 276231123133801077835457)
          ·
            refine ⟨207173342350350808376593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276231123133801077835457 207173342350350808376593)
            ·
              refine ⟨155380006762763106282445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207173342350350808376593 155380006762763106282445)
              ·
                refine ⟨58267502536036164855917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155380006762763106282445 58267502536036164855917)
                ·
                  rfl

theorem cell19_191490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_191490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191490 prefixEnd_191490 := by exact prefixLift 191490
  have htrace : WordTrace (prefixWord ++ tailWord_191490) baseStart_191490 baseEnd_191490 := by
    simpa [prefixWord, tailWord_191490, baseEnd_191490] using wordTrace_append hprefix tailTrace_191490
  have hstable : (prefixWord ++ tailWord_191490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191490).length < 2 ^ (prefixWord ++ tailWord_191490).sum := by decide
  have hdescent : baseEnd_191490 < baseStart_191490 := by decide
  rcases family_descends (prefixWord ++ tailWord_191490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191496 : List Nat := [2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_191496 : Nat := 118140960795 + 191496 * 2 ^ 59
def prefixEnd_191496 : Nat := 4983230072969 + 3 ^ 40 * 191496 * 2
def baseEnd_191496 : Nat := 58269328245029928722567

theorem tailTrace_191496 : CollatzResearch.WordTrace tailWord_191496 prefixEnd_191496 58269328245029928722567 := by
  unfold tailWord_191496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492216457125085879069171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4656288609500114505425561 3492216457125085879069171)
  ·
    refine ⟨5238324685687628818603757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3492216457125085879069171 5238324685687628818603757)
    ·
      refine ⟨1964371757132860806976409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5238324685687628818603757 1964371757132860806976409)
      ·
        refine ⟨1473278817849645605232307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964371757132860806976409 1473278817849645605232307)
        ·
          refine ⟨2209918226774468407848461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473278817849645605232307 2209918226774468407848461)
          ·
            refine ⟨828719335040425652943173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2209918226774468407848461 828719335040425652943173)
            ·
              refine ⟨155384875320079809926845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 828719335040425652943173 155384875320079809926845)
              ·
                refine ⟨58269328245029928722567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155384875320079809926845 58269328245029928722567)
                ·
                  rfl

theorem cell19_191496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_191496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191496 prefixEnd_191496 := by exact prefixLift 191496
  have htrace : WordTrace (prefixWord ++ tailWord_191496) baseStart_191496 baseEnd_191496 := by
    simpa [prefixWord, tailWord_191496, baseEnd_191496] using wordTrace_append hprefix tailTrace_191496
  have hstable : (prefixWord ++ tailWord_191496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191496).length < 2 ^ (prefixWord ++ tailWord_191496).sum := by decide
  have hdescent : baseEnd_191496 < baseStart_191496 := by decide
  rcases family_descends (prefixWord ++ tailWord_191496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191534 : List Nat := [4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_191534 : Nat := 118140960795 + 191534 * 2 ^ 59
def prefixEnd_191534 : Nat := 4983230072969 + 3 ^ 40 * 191534 * 2
def baseEnd_191534 : Nat := 58280891068657099878019

theorem tailTrace_191534 : CollatzResearch.WordTrace tailWord_191534 prefixEnd_191534 58280891068657099878019 := by
  unfold tailWord_191534
  simp only [CollatzResearch.WordTrace]
  refine ⟨873227361014063031002707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4657212592075002832014437 873227361014063031002707)
  ·
    refine ⟨1309841041521094546504061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873227361014063031002707 1309841041521094546504061)
    ·
      refine ⟨491190390570410454939023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1309841041521094546504061 491190390570410454939023)
      ·
        refine ⟨736785585855615682408535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491190390570410454939023 736785585855615682408535)
        ·
          refine ⟨1105178378783423523612803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736785585855615682408535 1105178378783423523612803)
          ·
            refine ⟨1657767568175135285419205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105178378783423523612803 1657767568175135285419205)
            ·
              refine ⟨310831419032837866016101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1657767568175135285419205 310831419032837866016101)
              ·
                refine ⟨58280891068657099878019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310831419032837866016101 58280891068657099878019)
                ·
                  rfl

theorem cell19_191534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_191534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191534 prefixEnd_191534 := by exact prefixLift 191534
  have htrace : WordTrace (prefixWord ++ tailWord_191534) baseStart_191534 baseEnd_191534 := by
    simpa [prefixWord, tailWord_191534, baseEnd_191534] using wordTrace_append hprefix tailTrace_191534
  have hstable : (prefixWord ++ tailWord_191534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191534).length < 2 ^ (prefixWord ++ tailWord_191534).sum := by decide
  have hdescent : baseEnd_191534 < baseStart_191534 := by decide
  rcases family_descends (prefixWord ++ tailWord_191534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191536 : List Nat := [2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_191536 : Nat := 118140960795 + 191536 * 2 ^ 59
def prefixEnd_191536 : Nat := 4983230072969 + 3 ^ 40 * 191536 * 2
def baseEnd_191536 : Nat := 58281499638321687833569

theorem tailTrace_191536 : CollatzResearch.WordTrace tailWord_191536 prefixEnd_191536 58281499638321687833569 := by
  unfold tailWord_191536
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492945917052629294797231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4657261222736839059729641 3492945917052629294797231)
  ·
    refine ⟨5239418875578943942195847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3492945917052629294797231 5239418875578943942195847)
    ·
      refine ⟨7859128313368415913293771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239418875578943942195847 7859128313368415913293771)
      ·
        refine ⟨11788692470052623869940657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859128313368415913293771 11788692470052623869940657)
        ·
          refine ⟨8841519352539467902455493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11788692470052623869940657 8841519352539467902455493)
          ·
            refine ⟨1657784878601150231710405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8841519352539467902455493 1657784878601150231710405)
            ·
              refine ⟨310834664737715668445701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1657784878601150231710405 310834664737715668445701)
              ·
                refine ⟨58281499638321687833569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310834664737715668445701 58281499638321687833569)
                ·
                  rfl

theorem cell19_191536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_191536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191536 prefixEnd_191536 := by exact prefixLift 191536
  have htrace : WordTrace (prefixWord ++ tailWord_191536) baseStart_191536 baseEnd_191536 := by
    simpa [prefixWord, tailWord_191536, baseEnd_191536] using wordTrace_append hprefix tailTrace_191536
  have hstable : (prefixWord ++ tailWord_191536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191536).length < 2 ^ (prefixWord ++ tailWord_191536).sum := by decide
  have hdescent : baseEnd_191536 < baseStart_191536 := by decide
  rcases family_descends (prefixWord ++ tailWord_191536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191591 : List Nat := [1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_191591 : Nat := 118140960795 + 191591 * 2 ^ 59
def prefixEnd_191591 : Nat := 4983230072969 + 3 ^ 40 * 191591 * 2
def baseEnd_191591 : Nat := 58298235304097856611197

theorem tailTrace_191591 : CollatzResearch.WordTrace tailWord_191591 prefixEnd_191591 58298235304097856611197 := by
  unfold tailWord_191591
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987897848906002982846627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4658598565937335321897751 6987897848906002982846627)
  ·
    refine ⟨10481846773359004474269941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987897848906002982846627 10481846773359004474269941)
    ·
      refine ⟨982673135002406669462807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10481846773359004474269941 982673135002406669462807)
      ·
        refine ⟨1474009702503610004194211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982673135002406669462807 1474009702503610004194211)
        ·
          refine ⟨2211014553755415006291317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474009702503610004194211 2211014553755415006291317)
          ·
            refine ⟨207282614414570156839811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2211014553755415006291317 207282614414570156839811)
            ·
              refine ⟨310923921621855235259717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207282614414570156839811 310923921621855235259717)
              ·
                refine ⟨58298235304097856611197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310923921621855235259717 58298235304097856611197)
                ·
                  rfl

theorem cell19_191591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_191591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191591 prefixEnd_191591 := by exact prefixLift 191591
  have htrace : WordTrace (prefixWord ++ tailWord_191591) baseStart_191591 baseEnd_191591 := by
    simpa [prefixWord, tailWord_191591, baseEnd_191591] using wordTrace_append hprefix tailTrace_191591
  have hstable : (prefixWord ++ tailWord_191591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191591).length < 2 ^ (prefixWord ++ tailWord_191591).sum := by decide
  have hdescent : baseEnd_191591 < baseStart_191591 := by decide
  rcases family_descends (prefixWord ++ tailWord_191591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191593 : List Nat := [1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_191593 : Nat := 118140960795 + 191593 * 2 ^ 59
def prefixEnd_191593 : Nat := 4983230072969 + 3 ^ 40 * 191593 * 2
def baseEnd_191593 : Nat := 58298843873762444566747

theorem tailTrace_191593 : CollatzResearch.WordTrace tailWord_191593 prefixEnd_191593 58298843873762444566747 := by
  unfold tailWord_191593
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987970794898757324419433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4658647196599171549612955 6987970794898757324419433)
  ·
    refine ⟨5240978096174067993314575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6987970794898757324419433 5240978096174067993314575)
    ·
      refine ⟨7861467144261101989971863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240978096174067993314575 7861467144261101989971863)
      ·
        refine ⟨11792200716391652984957795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861467144261101989971863 11792200716391652984957795)
        ·
          refine ⟨17688301074587479477436693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11792200716391652984957795 17688301074587479477436693)
          ·
            refine ⟨829139112871288100504845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17688301074587479477436693 829139112871288100504845)
            ·
              refine ⟨310927167326733037689317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829139112871288100504845 310927167326733037689317)
              ·
                refine ⟨58298843873762444566747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310927167326733037689317 58298843873762444566747)
                ·
                  rfl

theorem cell19_191593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_191593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191593 prefixEnd_191593 := by exact prefixLift 191593
  have htrace : WordTrace (prefixWord ++ tailWord_191593) baseStart_191593 baseEnd_191593 := by
    simpa [prefixWord, tailWord_191593, baseEnd_191593] using wordTrace_append hprefix tailTrace_191593
  have hstable : (prefixWord ++ tailWord_191593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191593).length < 2 ^ (prefixWord ++ tailWord_191593).sum := by decide
  have hdescent : baseEnd_191593 < baseStart_191593 := by decide
  rcases family_descends (prefixWord ++ tailWord_191593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191665 : List Nat := [1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_191665 : Nat := 118140960795 + 191665 * 2 ^ 59
def prefixEnd_191665 : Nat := 4983230072969 + 3 ^ 40 * 191665 * 2
def baseEnd_191665 : Nat := 58320752381687610966551

theorem tailTrace_191665 : CollatzResearch.WordTrace tailWord_191665 prefixEnd_191665 58320752381687610966551 := by
  unfold tailWord_191665
  simp only [CollatzResearch.WordTrace]
  refine ⟨6990596850637913621040449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4660397900425275747360299 6990596850637913621040449)
  ·
    refine ⟨5242947637978435215780337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6990596850637913621040449 5242947637978435215780337)
    ·
      refine ⟨3932210728483826411835253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5242947637978435215780337 3932210728483826411835253)
      ·
        refine ⟨368644755795358726109555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3932210728483826411835253 368644755795358726109555)
        ·
          refine ⟨552967133693038089164333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368644755795358726109555 552967133693038089164333)
          ·
            refine ⟨207362675134889283436625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 552967133693038089164333 207362675134889283436625)
            ·
              refine ⟨155522006351166962577469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207362675134889283436625 155522006351166962577469)
              ·
                refine ⟨58320752381687610966551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155522006351166962577469 58320752381687610966551)
                ·
                  rfl

theorem cell19_191665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_191665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191665 prefixEnd_191665 := by exact prefixLift 191665
  have htrace : WordTrace (prefixWord ++ tailWord_191665) baseStart_191665 baseEnd_191665 := by
    simpa [prefixWord, tailWord_191665, baseEnd_191665] using wordTrace_append hprefix tailTrace_191665
  have hstable : (prefixWord ++ tailWord_191665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191665).length < 2 ^ (prefixWord ++ tailWord_191665).sum := by decide
  have hdescent : baseEnd_191665 < baseStart_191665 := by decide
  rcases family_descends (prefixWord ++ tailWord_191665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
