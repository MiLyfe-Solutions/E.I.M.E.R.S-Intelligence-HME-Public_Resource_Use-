import V185TrunkScan22Chunk169

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1517159 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 7]
def baseStart_1517159 : Nat := 118140960795 + 1517159 * 2 ^ 59
def prefixEnd_1517159 : Nat := 4983230072969 + 3 ^ 40 * 1517159 * 2
def baseEnd_1517159 : Nat := 173118176954385520474493

theorem tailTrace_1517159 : CollatzResearch.WordTrace tailWord_1517159 prefixEnd_1517159 173118176954385520474493 := by
  unfold tailWord_1517159
  simp only [CollatzResearch.WordTrace]
  refine ⟨55335334710599527973498531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36890223140399685315665687 55335334710599527973498531)
  ·
    refine ⟨83003002065899291960247797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55335334710599527973498531 83003002065899291960247797)
    ·
      refine ⟨7781531443678058621273231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83003002065899291960247797 7781531443678058621273231)
      ·
        refine ⟨11672297165517087931909847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781531443678058621273231 11672297165517087931909847)
        ·
          refine ⟨17508445748275631897864771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11672297165517087931909847 17508445748275631897864771)
          ·
            refine ⟨26262668622413447846797157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17508445748275631897864771 26262668622413447846797157)
            ·
              refine ⟨4924250366702521471274467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26262668622413447846797157 4924250366702521471274467)
              ·
                refine ⟨7386375550053782206911701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924250366702521471274467 7386375550053782206911701)
                ·
                  refine ⟨173118176954385520474493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7386375550053782206911701 173118176954385520474493)
                  ·
                    rfl

theorem cell22_1517159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 7].length) (baseStart_1517159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517159 prefixEnd_1517159 := by exact prefixLift 1517159
  have htrace : WordTrace (prefixWord ++ tailWord_1517159) baseStart_1517159 baseEnd_1517159 := by
    simpa [prefixWord, tailWord_1517159, baseEnd_1517159] using wordTrace_append hprefix tailTrace_1517159
  have hstable : (prefixWord ++ tailWord_1517159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517159).length < 2 ^ (prefixWord ++ tailWord_1517159).sum := by decide
  have hdescent : baseEnd_1517159 < baseStart_1517159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517214 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1517214 : Nat := 118140960795 + 1517214 * 2 ^ 59
def prefixEnd_1517214 : Nat := 4983230072969 + 3 ^ 40 * 1517214 * 2
def baseEnd_1517214 : Nat := 519373358487154751298311

theorem tailTrace_1517214 : CollatzResearch.WordTrace tailWord_1517214 prefixEnd_1517214 519373358487154751298311 := by
  unfold tailWord_1517214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6917167590675034045843837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36891560483600181577833797 6917167590675034045843837)
  ·
    refine ⟨2593937846503137767191439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6917167590675034045843837 2593937846503137767191439)
    ·
      refine ⟨3890906769754706650787159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593937846503137767191439 3890906769754706650787159)
      ·
        refine ⟨5836360154632059976180739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3890906769754706650787159 5836360154632059976180739)
        ·
          refine ⟨8754540231948089964271109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836360154632059976180739 8754540231948089964271109)
          ·
            refine ⟨1641476293490266868300833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8754540231948089964271109 1641476293490266868300833)
            ·
              refine ⟨1231107220117700151225625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641476293490266868300833 1231107220117700151225625)
              ·
                refine ⟨923330415088275113419219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231107220117700151225625 923330415088275113419219)
                ·
                  refine ⟨1384995622632412670128829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923330415088275113419219 1384995622632412670128829)
                  ·
                    refine ⟨519373358487154751298311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384995622632412670128829 519373358487154751298311)
                    ·
                      rfl

theorem cell22_1517214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1517214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517214 prefixEnd_1517214 := by exact prefixLift 1517214
  have htrace : WordTrace (prefixWord ++ tailWord_1517214) baseStart_1517214 baseEnd_1517214 := by
    simpa [prefixWord, tailWord_1517214, baseEnd_1517214] using wordTrace_append hprefix tailTrace_1517214
  have hstable : (prefixWord ++ tailWord_1517214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517214).length < 2 ^ (prefixWord ++ tailWord_1517214).sum := by decide
  have hdescent : baseEnd_1517214 < baseStart_1517214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517219 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_1517219 : Nat := 118140960795 + 1517219 * 2 ^ 59
def prefixEnd_1517219 : Nat := 4983230072969 + 3 ^ 40 * 1517219 * 2
def baseEnd_1517219 : Nat := 519375070089336404923295

theorem tailTrace_1517219 : CollatzResearch.WordTrace tailWord_1517219 prefixEnd_1517219 519375070089336404923295 := by
  unfold tailWord_1517219
  simp only [CollatzResearch.WordTrace]
  refine ⟨55337523090382158220682711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36891682060254772147121807 55337523090382158220682711)
  ·
    refine ⟨83006284635573237331024067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55337523090382158220682711 83006284635573237331024067)
    ·
      refine ⟨124509426953359855996536101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83006284635573237331024067 124509426953359855996536101)
      ·
        refine ⟨23345517553754972999350519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124509426953359855996536101 23345517553754972999350519)
        ·
          refine ⟨35018276330632459499025779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23345517553754972999350519 35018276330632459499025779)
          ·
            refine ⟨52527414495948689248538669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35018276330632459499025779 52527414495948689248538669)
            ·
              refine ⟨19697780435980758468202001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52527414495948689248538669 19697780435980758468202001)
              ·
                refine ⟨14773335326985568851151501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19697780435980758468202001 14773335326985568851151501)
                ·
                  refine ⟨5540000747619588319181813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14773335326985568851151501 5540000747619588319181813)
                  ·
                    refine ⟨519375070089336404923295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5540000747619588319181813 519375070089336404923295)
                    ·
                      rfl

theorem cell22_1517219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_1517219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517219 prefixEnd_1517219 := by exact prefixLift 1517219
  have htrace : WordTrace (prefixWord ++ tailWord_1517219) baseStart_1517219 baseEnd_1517219 := by
    simpa [prefixWord, tailWord_1517219, baseEnd_1517219] using wordTrace_append hprefix tailTrace_1517219
  have hstable : (prefixWord ++ tailWord_1517219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517219).length < 2 ^ (prefixWord ++ tailWord_1517219).sum := by decide
  have hdescent : baseEnd_1517219 < baseStart_1517219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517238 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_1517238 : Nat := 118140960795 + 1517238 * 2 ^ 59
def prefixEnd_1517238 : Nat := 4983230072969 + 3 ^ 40 * 1517238 * 2
def baseEnd_1517238 : Nat := 173127191392542229566079

theorem tailTrace_1517238 : CollatzResearch.WordTrace tailWord_1517238 prefixEnd_1517238 173127191392542229566079 := by
  unfold tailWord_1517238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458638504832082779101523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36892144051542216310416245 3458638504832082779101523)
  ·
    refine ⟨5187957757248124168652285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3458638504832082779101523 5187957757248124168652285)
    ·
      refine ⟨1945484158968046563244607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5187957757248124168652285 1945484158968046563244607)
      ·
        refine ⟨2918226238452069844866911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945484158968046563244607 2918226238452069844866911)
        ·
          refine ⟨4377339357678104767300367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918226238452069844866911 4377339357678104767300367)
          ·
            refine ⟨6566009036517157150950551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377339357678104767300367 6566009036517157150950551)
            ·
              refine ⟨9849013554775735726425827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566009036517157150950551 9849013554775735726425827)
              ·
                refine ⟨14773520332163603589638741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9849013554775735726425827 14773520332163603589638741)
                ·
                  refine ⟨173127191392542229566079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14773520332163603589638741 173127191392542229566079)
                  ·
                    rfl

theorem cell22_1517238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_1517238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517238 prefixEnd_1517238 := by exact prefixLift 1517238
  have htrace : WordTrace (prefixWord ++ tailWord_1517238) baseStart_1517238 baseEnd_1517238 := by
    simpa [prefixWord, tailWord_1517238, baseEnd_1517238] using wordTrace_append hprefix tailTrace_1517238
  have hstable : (prefixWord ++ tailWord_1517238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517238).length < 2 ^ (prefixWord ++ tailWord_1517238).sum := by decide
  have hdescent : baseEnd_1517238 < baseStart_1517238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517266 : List Nat := [3, 2, 2, 2, 2, 2, 9]
def baseStart_1517266 : Nat := 118140960795 + 1517266 * 2 ^ 59
def prefixEnd_1517266 : Nat := 4983230072969 + 3 ^ 40 * 1517266 * 2
def baseEnd_1517266 : Nat := 19236709598142368481413

theorem tailTrace_1517266 : CollatzResearch.WordTrace tailWord_1517266 prefixEnd_1517266 19236709598142368481413 := by
  unfold tailWord_1517266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834809330302971311910913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36892824880807923498429101 13834809330302971311910913)
  ·
    refine ⟨10376106997727228483933185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13834809330302971311910913 10376106997727228483933185)
    ·
      refine ⟨7782080248295421362949889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10376106997727228483933185 7782080248295421362949889)
      ·
        refine ⟨5836560186221566022212417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7782080248295421362949889 5836560186221566022212417)
        ·
          refine ⟨4377420139666174516659313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836560186221566022212417 4377420139666174516659313)
          ·
            refine ⟨3283065104749630887494485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377420139666174516659313 3283065104749630887494485)
            ·
              refine ⟨19236709598142368481413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3283065104749630887494485 19236709598142368481413)
              ·
                rfl

theorem cell22_1517266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 9].length) (baseStart_1517266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517266 prefixEnd_1517266 := by exact prefixLift 1517266
  have htrace : WordTrace (prefixWord ++ tailWord_1517266) baseStart_1517266 baseEnd_1517266 := by
    simpa [prefixWord, tailWord_1517266, baseEnd_1517266] using wordTrace_append hprefix tailTrace_1517266
  have hstable : (prefixWord ++ tailWord_1517266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517266).length < 2 ^ (prefixWord ++ tailWord_1517266).sum := by decide
  have hdescent : baseEnd_1517266 < baseStart_1517266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517287 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1517287 : Nat := 118140960795 + 1517287 * 2 ^ 59
def prefixEnd_1517287 : Nat := 4983230072969 + 3 ^ 40 * 1517287 * 2
def baseEnd_1517287 : Nat := 519398347879006894223087

theorem tailTrace_1517287 : CollatzResearch.WordTrace tailWord_1517287 prefixEnd_1517287 519398347879006894223087 := by
  unfold tailWord_1517287
  simp only [CollatzResearch.WordTrace]
  refine ⟨55340003254135805834158115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36893335502757203889438743 55340003254135805834158115)
  ·
    refine ⟨83010004881203708751237173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55340003254135805834158115 83010004881203708751237173)
    ·
      refine ⟨7782187957612847695428485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83010004881203708751237173 7782187957612847695428485)
      ·
        refine ⟨1459160242052408942892841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7782187957612847695428485 1459160242052408942892841)
        ·
          refine ⟨1094370181539306707169631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1459160242052408942892841 1094370181539306707169631)
          ·
            refine ⟨1641555272308960060754447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094370181539306707169631 1641555272308960060754447)
            ·
              refine ⟨2462332908463440091131671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641555272308960060754447 2462332908463440091131671)
              ·
                refine ⟨3693499362695160136697507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462332908463440091131671 3693499362695160136697507)
                ·
                  refine ⟨5540249044042740205046261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693499362695160136697507 5540249044042740205046261)
                  ·
                    refine ⟨519398347879006894223087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5540249044042740205046261 519398347879006894223087)
                    ·
                      rfl

theorem cell22_1517287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1517287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517287 prefixEnd_1517287 := by exact prefixLift 1517287
  have htrace : WordTrace (prefixWord ++ tailWord_1517287) baseStart_1517287 baseEnd_1517287 := by
    simpa [prefixWord, tailWord_1517287, baseEnd_1517287] using wordTrace_append hprefix tailTrace_1517287
  have hstable : (prefixWord ++ tailWord_1517287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517287).length < 2 ^ (prefixWord ++ tailWord_1517287).sum := by decide
  have hdescent : baseEnd_1517287 < baseStart_1517287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517298 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_1517298 : Nat := 118140960795 + 1517298 * 2 ^ 59
def prefixEnd_1517298 : Nat := 4983230072969 + 3 ^ 40 * 1517298 * 2
def baseEnd_1517298 : Nat := 519402113403806532198053

theorem tailTrace_1517298 : CollatzResearch.WordTrace tailWord_1517298 prefixEnd_1517298 519402113403806532198053 := by
  unfold tailWord_1517298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13835101114273988678202137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36893602971397303141872365 13835101114273988678202137)
  ·
    refine ⟨10376325835705491508651603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13835101114273988678202137 10376325835705491508651603)
    ·
      refine ⟨15564488753558237262977405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10376325835705491508651603 15564488753558237262977405)
      ·
        refine ⟨5836683282584338973616527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15564488753558237262977405 5836683282584338973616527)
        ·
          refine ⟨8755024923876508460424791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836683282584338973616527 8755024923876508460424791)
          ·
            refine ⟨13132537385814762690637187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8755024923876508460424791 13132537385814762690637187)
            ·
              refine ⟨19698806078722144035955781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13132537385814762690637187 19698806078722144035955781)
              ·
                refine ⟨3693526139760402006741709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19698806078722144035955781 3693526139760402006741709)
                ·
                  refine ⟨1385072302410150752528141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3693526139760402006741709 1385072302410150752528141)
                  ·
                    refine ⟨519402113403806532198053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385072302410150752528141 519402113403806532198053)
                    ·
                      rfl

theorem cell22_1517298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_1517298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517298 prefixEnd_1517298 := by exact prefixLift 1517298
  have htrace : WordTrace (prefixWord ++ tailWord_1517298) baseStart_1517298 baseEnd_1517298 := by
    simpa [prefixWord, tailWord_1517298, baseEnd_1517298] using wordTrace_append hprefix tailTrace_1517298
  have hstable : (prefixWord ++ tailWord_1517298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517298).length < 2 ^ (prefixWord ++ tailWord_1517298).sum := by decide
  have hdescent : baseEnd_1517298 < baseStart_1517298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517300 : List Nat := [2, 6, 1, 1, 1, 2, 1, 8]
def baseStart_1517300 : Nat := 118140960795 + 1517300 * 2 ^ 59
def prefixEnd_1517300 : Nat := 4983230072969 + 3 ^ 40 * 1517300 * 2
def baseEnd_1517300 : Nat := 57711422004964354849783

theorem tailTrace_1517300 : CollatzResearch.WordTrace tailWord_1517300 prefixEnd_1517300 57711422004964354849783 := by
  unfold tailWord_1517300
  simp only [CollatzResearch.WordTrace]
  refine ⟨27670238701544354527190677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36893651602059139369587569 27670238701544354527190677)
  ·
    refine ⟨1297042439134891618462063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27670238701544354527190677 1297042439134891618462063)
    ·
      refine ⟨1945563658702337427693095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1297042439134891618462063 1945563658702337427693095)
      ·
        refine ⟨2918345488053506141539643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945563658702337427693095 2918345488053506141539643)
        ·
          refine ⟨4377518232080259212309465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918345488053506141539643 4377518232080259212309465)
          ·
            refine ⟨3283138674060194409232099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377518232080259212309465 3283138674060194409232099)
            ·
              refine ⟨4924708011090291613848149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283138674060194409232099 4924708011090291613848149)
              ·
                refine ⟨57711422004964354849783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4924708011090291613848149 57711422004964354849783)
                ·
                  rfl

theorem cell22_1517300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 8].length) (baseStart_1517300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517300 prefixEnd_1517300 := by exact prefixLift 1517300
  have htrace : WordTrace (prefixWord ++ tailWord_1517300) baseStart_1517300 baseEnd_1517300 := by
    simpa [prefixWord, tailWord_1517300, baseEnd_1517300] using wordTrace_append hprefix tailTrace_1517300
  have hstable : (prefixWord ++ tailWord_1517300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517300).length < 2 ^ (prefixWord ++ tailWord_1517300).sum := by decide
  have hdescent : baseEnd_1517300 < baseStart_1517300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517315 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 1, 3]
def baseStart_1517315 : Nat := 118140960795 + 1517315 * 2 ^ 59
def prefixEnd_1517315 : Nat := 4983230072969 + 3 ^ 40 * 1517315 * 2
def baseEnd_1517315 : Nat := 519407932851224154523001

theorem tailTrace_1517315 : CollatzResearch.WordTrace tailWord_1517315 prefixEnd_1517315 519407932851224154523001 := by
  unfold tailWord_1517315
  simp only [CollatzResearch.WordTrace]
  refine ⟨55341024498034366616177399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36894016332022911077451599 55341024498034366616177399)
  ·
    refine ⟨83011536747051549924266099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55341024498034366616177399 83011536747051549924266099)
    ·
      refine ⟨124517305120577324886399149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83011536747051549924266099 124517305120577324886399149)
      ·
        refine ⟨46693989420216496832399681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124517305120577324886399149 46693989420216496832399681)
        ·
          refine ⟨35020492065162372624299761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46693989420216496832399681 35020492065162372624299761)
          ·
            refine ⟨26265369048871779468224821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35020492065162372624299761 26265369048871779468224821)
            ·
              refine ⟨2462378348331729325146077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26265369048871779468224821 2462378348331729325146077)
              ·
                refine ⟨923391880624398496929779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2462378348331729325146077 923391880624398496929779)
                ·
                  refine ⟨1385087820936597745394669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923391880624398496929779 1385087820936597745394669)
                  ·
                    refine ⟨519407932851224154523001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385087820936597745394669 519407932851224154523001)
                    ·
                      rfl

theorem cell22_1517315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 3].length) (baseStart_1517315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517315 prefixEnd_1517315 := by exact prefixLift 1517315
  have htrace : WordTrace (prefixWord ++ tailWord_1517315) baseStart_1517315 baseEnd_1517315 := by
    simpa [prefixWord, tailWord_1517315, baseEnd_1517315] using wordTrace_append hprefix tailTrace_1517315
  have hstable : (prefixWord ++ tailWord_1517315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517315).length < 2 ^ (prefixWord ++ tailWord_1517315).sum := by decide
  have hdescent : baseEnd_1517315 < baseStart_1517315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517326 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1517326 : Nat := 118140960795 + 1517326 * 2 ^ 59
def prefixEnd_1517326 : Nat := 4983230072969 + 3 ^ 40 * 1517326 * 2
def baseEnd_1517326 : Nat := 519411698376023792497967

theorem tailTrace_1517326 : CollatzResearch.WordTrace tailWord_1517326 prefixEnd_1517326 519411698376023792497967 := by
  unfold tailWord_1517326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6917678212624314436853479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36894283800663010329885221 6917678212624314436853479)
  ·
    refine ⟨10376517318936471655280219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6917678212624314436853479 10376517318936471655280219)
    ·
      refine ⟨15564775978404707482920329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10376517318936471655280219 15564775978404707482920329)
      ·
        refine ⟨11673581983803530612190247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15564775978404707482920329 11673581983803530612190247)
        ·
          refine ⟨17510372975705295918285371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673581983803530612190247 17510372975705295918285371)
          ·
            refine ⟨26265559463557943877428057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17510372975705295918285371 26265559463557943877428057)
            ·
              refine ⟨19699169597668457908071043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26265559463557943877428057 19699169597668457908071043)
              ·
                refine ⟨29548754396502686862106565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19699169597668457908071043 29548754396502686862106565)
                ·
                  refine ⟨5540391449344253786644981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29548754396502686862106565 5540391449344253786644981)
                  ·
                    refine ⟨519411698376023792497967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5540391449344253786644981 519411698376023792497967)
                    ·
                      rfl

theorem cell22_1517326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1517326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517326 prefixEnd_1517326 := by exact prefixLift 1517326
  have htrace : WordTrace (prefixWord ++ tailWord_1517326) baseStart_1517326 baseEnd_1517326 := by
    simpa [prefixWord, tailWord_1517326, baseEnd_1517326] using wordTrace_append hprefix tailTrace_1517326
  have hstable : (prefixWord ++ tailWord_1517326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517326).length < 2 ^ (prefixWord ++ tailWord_1517326).sum := by decide
  have hdescent : baseEnd_1517326 < baseStart_1517326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517345 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 5]
def baseStart_1517345 : Nat := 118140960795 + 1517345 * 2 ^ 59
def prefixEnd_1517345 : Nat := 4983230072969 + 3 ^ 40 * 1517345 * 2
def baseEnd_1517345 : Nat := 173139400821438025424303

theorem tailTrace_1517345 : CollatzResearch.WordTrace tailWord_1517345 prefixEnd_1517345 173139400821438025424303 := by
  unfold tailWord_1517345
  simp only [CollatzResearch.WordTrace]
  refine ⟨55342118687925681739769489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36894745791950454493179659 55342118687925681739769489)
  ·
    refine ⟨41506589015944261304827117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55342118687925681739769489 41506589015944261304827117)
    ·
      refine ⟨15564970880979097989310169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41506589015944261304827117 15564970880979097989310169)
      ·
        refine ⟨11673728160734323491982627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15564970880979097989310169 11673728160734323491982627)
        ·
          refine ⟨17510592241101485237973941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673728160734323491982627 17510592241101485237973941)
          ·
            refine ⟨1641618022603264241060057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17510592241101485237973941 1641618022603264241060057)
            ·
              refine ⟨1231213516952448180795043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641618022603264241060057 1231213516952448180795043)
              ·
                refine ⟨1846820275428672271192565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231213516952448180795043 1846820275428672271192565)
                ·
                  refine ⟨173139400821438025424303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1846820275428672271192565 173139400821438025424303)
                  ·
                    rfl

theorem cell22_1517345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_1517345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517345 prefixEnd_1517345 := by exact prefixLift 1517345
  have htrace : WordTrace (prefixWord ++ tailWord_1517345) baseStart_1517345 baseEnd_1517345 := by
    simpa [prefixWord, tailWord_1517345, baseEnd_1517345] using wordTrace_append hprefix tailTrace_1517345
  have hstable : (prefixWord ++ tailWord_1517345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517345).length < 2 ^ (prefixWord ++ tailWord_1517345).sum := by decide
  have hdescent : baseEnd_1517345 < baseStart_1517345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517420 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_1517420 : Nat := 118140960795 + 1517420 * 2 ^ 59
def prefixEnd_1517420 : Nat := 4983230072969 + 3 ^ 40 * 1517420 * 2
def baseEnd_1517420 : Nat := 519443876497038880647679

theorem tailTrace_1517420 : CollatzResearch.WordTrace tailWord_1517420 prefixEnd_1517420 519443876497038880647679 := by
  unfold tailWord_1517420
  simp only [CollatzResearch.WordTrace]
  refine ⟨27672427081326984774374857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36896569441769313032499809 27672427081326984774374857)
  ·
    refine ⟨20754320310995238580781143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27672427081326984774374857 20754320310995238580781143)
    ·
      refine ⟨31131480466492857871171715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20754320310995238580781143 31131480466492857871171715)
      ·
        refine ⟨46697220699739286806757573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31131480466492857871171715 46697220699739286806757573)
        ·
          refine ⟨8755728881201116276267045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46697220699739286806757573 8755728881201116276267045)
          ·
            refine ⟨1641699165225209301800071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8755728881201116276267045 1641699165225209301800071)
            ·
              refine ⟨2462548747837813952700107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641699165225209301800071 2462548747837813952700107)
              ·
                refine ⟨3693823121756720929050161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462548747837813952700107 3693823121756720929050161)
                ·
                  refine ⟨2770367341317540696787621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3693823121756720929050161 2770367341317540696787621)
                  ·
                    refine ⟨519443876497038880647679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2770367341317540696787621 519443876497038880647679)
                    ·
                      rfl

theorem cell22_1517420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_1517420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517420 prefixEnd_1517420 := by exact prefixLift 1517420
  have htrace : WordTrace (prefixWord ++ tailWord_1517420) baseStart_1517420 baseEnd_1517420 := by
    simpa [prefixWord, tailWord_1517420, baseEnd_1517420] using wordTrace_append hprefix tailTrace_1517420
  have hstable : (prefixWord ++ tailWord_1517420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517420).length < 2 ^ (prefixWord ++ tailWord_1517420).sum := by decide
  have hdescent : baseEnd_1517420 < baseStart_1517420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517433 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_1517433 : Nat := 118140960795 + 1517433 * 2 ^ 59
def prefixEnd_1517433 : Nat := 4983230072969 + 3 ^ 40 * 1517433 * 2
def baseEnd_1517433 : Nat := 519448326662711180072639

theorem tailTrace_1517433 : CollatzResearch.WordTrace tailWord_1517433 prefixEnd_1517433 519448326662711180072639 := by
  unfold tailWord_1517433
  simp only [CollatzResearch.WordTrace]
  refine ⟨55345328311606872768972953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36896885541071248512648635 55345328311606872768972953)
  ·
    refine ⟨41508996233705154576729715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55345328311606872768972953 41508996233705154576729715)
    ·
      refine ⟨62263494350557731865094573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41508996233705154576729715 62263494350557731865094573)
      ·
        refine ⟨23348810381459149449410465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62263494350557731865094573 23348810381459149449410465)
        ·
          refine ⟨17511607786094362087057849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23348810381459149449410465 17511607786094362087057849)
          ·
            refine ⟨13133705839570771565293387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17511607786094362087057849 13133705839570771565293387)
            ·
              refine ⟨19700558759356157347940081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13133705839570771565293387 19700558759356157347940081)
              ·
                refine ⟨14775419069517118010955061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19700558759356157347940081 14775419069517118010955061)
                ·
                  refine ⟨1385195537767229813527037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14775419069517118010955061 1385195537767229813527037)
                  ·
                    refine ⟨519448326662711180072639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385195537767229813527037 519448326662711180072639)
                    ·
                      rfl

theorem cell22_1517433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_1517433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517433 prefixEnd_1517433 := by exact prefixLift 1517433
  have htrace : WordTrace (prefixWord ++ tailWord_1517433) baseStart_1517433 baseEnd_1517433 := by
    simpa [prefixWord, tailWord_1517433, baseEnd_1517433] using wordTrace_append hprefix tailTrace_1517433
  have hstable : (prefixWord ++ tailWord_1517433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517433).length < 2 ^ (prefixWord ++ tailWord_1517433).sum := by decide
  have hdescent : baseEnd_1517433 < baseStart_1517433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517553 : List Nat := [1, 2, 2, 2, 5, 10]
def baseStart_1517553 : Nat := 118140960795 + 1517553 * 2 ^ 59
def prefixEnd_1517553 : Nat := 4983230072969 + 3 ^ 40 * 1517553 * 2
def baseEnd_1517553 : Nat := 6413449445865072432991

theorem tailTrace_1517553 : CollatzResearch.WordTrace tailWord_1517553 prefixEnd_1517553 6413449445865072432991 := by
  unfold tailWord_1517553
  simp only [CollatzResearch.WordTrace]
  refine ⟨55349705071172133263341313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36899803380781422175560875 55349705071172133263341313)
  ·
    refine ⟨41512278803379099947505985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55349705071172133263341313 41512278803379099947505985)
    ·
      refine ⟨31134209102534324960629489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41512278803379099947505985 31134209102534324960629489)
      ·
        refine ⟨23350656826900743720472117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31134209102534324960629489 23350656826900743720472117)
        ·
          refine ⟨2189124077521944723794261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23350656826900743720472117 2189124077521944723794261)
          ·
            refine ⟨6413449445865072432991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2189124077521944723794261 6413449445865072432991)
            ·
              rfl

theorem cell22_1517553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 10].length) (baseStart_1517553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517553 prefixEnd_1517553 := by exact prefixLift 1517553
  have htrace : WordTrace (prefixWord ++ tailWord_1517553) baseStart_1517553 baseEnd_1517553 := by
    simpa [prefixWord, tailWord_1517553, baseEnd_1517553] using wordTrace_append hprefix tailTrace_1517553
  have hstable : (prefixWord ++ tailWord_1517553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517553).length < 2 ^ (prefixWord ++ tailWord_1517553).sum := by decide
  have hdescent : baseEnd_1517553 < baseStart_1517553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517589 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_1517589 : Nat := 118140960795 + 1517589 * 2 ^ 59
def prefixEnd_1517589 : Nat := 4983230072969 + 3 ^ 40 * 1517589 * 2
def baseEnd_1517589 : Nat := 519501728650778773172161

theorem tailTrace_1517589 : CollatzResearch.WordTrace tailWord_1517589 prefixEnd_1517589 519501728650778773172161 := by
  unfold tailWord_1517589
  simp only [CollatzResearch.WordTrace]
  refine ⟨55351018099041711411651821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36900678732694474274434547 55351018099041711411651821)
  ·
    refine ⟨20756631787140641779369433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55351018099041711411651821 20756631787140641779369433)
    ·
      refine ⟨15567473840355481334527075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20756631787140641779369433 15567473840355481334527075)
      ·
        refine ⟨23351210760533222001790613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15567473840355481334527075 23351210760533222001790613)
        ·
          refine ⟨1094588004399994781333935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23351210760533222001790613 1094588004399994781333935)
          ·
            refine ⟨1641882006599992172000903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094588004399994781333935 1641882006599992172000903)
            ·
              refine ⟨2462823009899988258001355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641882006599992172000903 2462823009899988258001355)
              ·
                refine ⟨3694234514849982387002033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462823009899988258001355 3694234514849982387002033)
                ·
                  refine ⟨2770675886137486790251525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694234514849982387002033 2770675886137486790251525)
                  ·
                    refine ⟨519501728650778773172161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2770675886137486790251525 519501728650778773172161)
                    ·
                      rfl

theorem cell22_1517589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_1517589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517589 prefixEnd_1517589 := by exact prefixLift 1517589
  have htrace : WordTrace (prefixWord ++ tailWord_1517589) baseStart_1517589 baseEnd_1517589 := by
    simpa [prefixWord, tailWord_1517589, baseEnd_1517589] using wordTrace_append hprefix tailTrace_1517589
  have hstable : (prefixWord ++ tailWord_1517589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517589).length < 2 ^ (prefixWord ++ tailWord_1517589).sum := by decide
  have hdescent : baseEnd_1517589 < baseStart_1517589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517608 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1517608 : Nat := 118140960795 + 1517608 * 2 ^ 59
def prefixEnd_1517608 : Nat := 4983230072969 + 3 ^ 40 * 1517608 * 2
def baseEnd_1517608 : Nat := 519508232739069056947103

theorem tailTrace_1517608 : CollatzResearch.WordTrace tailWord_1517608 prefixEnd_1517608 519508232739069056947103 := by
  unfold tailWord_1517608
  simp only [CollatzResearch.WordTrace]
  refine ⟨27675855542986438828296739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36901140723981918437728985 27675855542986438828296739)
  ·
    refine ⟨41513783314479658242445109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27675855542986438828296739 41513783314479658242445109)
    ·
      refine ⟨3891917185732467960229229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41513783314479658242445109 3891917185732467960229229)
      ·
        refine ⟨1459468944649675485085961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3891917185732467960229229 1459468944649675485085961)
        ·
          refine ⟨1094601708487256613814471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1459468944649675485085961 1094601708487256613814471)
          ·
            refine ⟨1641902562730884920721707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094601708487256613814471 1641902562730884920721707)
            ·
              refine ⟨2462853844096327381082561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641902562730884920721707 2462853844096327381082561)
              ·
                refine ⟨1847140383072245535811921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462853844096327381082561 1847140383072245535811921)
                ·
                  refine ⟨1385355287304184151858941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847140383072245535811921 1385355287304184151858941)
                  ·
                    refine ⟨519508232739069056947103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385355287304184151858941 519508232739069056947103)
                    ·
                      rfl

theorem cell22_1517608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1517608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517608 prefixEnd_1517608 := by exact prefixLift 1517608
  have htrace : WordTrace (prefixWord ++ tailWord_1517608) baseStart_1517608 baseEnd_1517608 := by
    simpa [prefixWord, tailWord_1517608, baseEnd_1517608] using wordTrace_append hprefix tailTrace_1517608
  have hstable : (prefixWord ++ tailWord_1517608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517608).length < 2 ^ (prefixWord ++ tailWord_1517608).sum := by decide
  have hdescent : baseEnd_1517608 < baseStart_1517608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517632 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 5]
def baseStart_1517632 : Nat := 118140960795 + 1517632 * 2 ^ 59
def prefixEnd_1517632 : Nat := 4983230072969 + 3 ^ 40 * 1517632 * 2
def baseEnd_1517632 : Nat := 173172149476513664782343

theorem tailTrace_1517632 : CollatzResearch.WordTrace tailWord_1517632 prefixEnd_1517632 173172149476513664782343 := by
  unfold tailWord_1517632
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676293218942964877733575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36901724291923953170311433 27676293218942964877733575)
  ·
    refine ⟨41514439828414447316600363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27676293218942964877733575 41514439828414447316600363)
    ·
      refine ⟨62271659742621670974900545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41514439828414447316600363 62271659742621670974900545)
      ·
        refine ⟨46703744806966253231175409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62271659742621670974900545 46703744806966253231175409)
        ·
          refine ⟨35027808605224689923381557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46703744806966253231175409 35027808605224689923381557)
          ·
            refine ⟨3283857056739814680317021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35027808605224689923381557 3283857056739814680317021)
            ·
              refine ⟨1231446396277430505118883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3283857056739814680317021 1231446396277430505118883)
              ·
                refine ⟨1847169594416145757678325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231446396277430505118883 1847169594416145757678325)
                ·
                  refine ⟨173172149476513664782343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1847169594416145757678325 173172149476513664782343)
                  ·
                    rfl

theorem cell22_1517632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_1517632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517632 prefixEnd_1517632 := by exact prefixLift 1517632
  have htrace : WordTrace (prefixWord ++ tailWord_1517632) baseStart_1517632 baseEnd_1517632 := by
    simpa [prefixWord, tailWord_1517632, baseEnd_1517632] using wordTrace_append hprefix tailTrace_1517632
  have hstable : (prefixWord ++ tailWord_1517632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517632).length < 2 ^ (prefixWord ++ tailWord_1517632).sum := by decide
  have hdescent : baseEnd_1517632 < baseStart_1517632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517722 : List Nat := [3, 1, 1, 5, 3, 9]
def baseStart_1517722 : Nat := 118140960795 + 1517722 * 2 ^ 59
def prefixEnd_1517722 : Nat := 4983230072969 + 3 ^ 40 * 1517722 * 2
def baseEnd_1517722 : Nat := 6414163669985318019713

theorem tailTrace_1517722 : CollatzResearch.WordTrace tailWord_1517722 prefixEnd_1517722 6414163669985318019713 := by
  unfold tailWord_1517722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13838967251889968781560855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36903912671706583417495613 13838967251889968781560855)
  ·
    refine ⟨20758450877834953172341283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13838967251889968781560855 20758450877834953172341283)
    ·
      refine ⟨31137676316752429758511925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20758450877834953172341283 31137676316752429758511925)
      ·
        refine ⟨2919157154695540289860493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31137676316752429758511925 2919157154695540289860493)
        ·
          refine ⟨1094683933010827608697685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2919157154695540289860493 1094683933010827608697685)
          ·
            refine ⟨6414163669985318019713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1094683933010827608697685 6414163669985318019713)
            ·
              rfl

theorem cell22_1517722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 9].length) (baseStart_1517722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517722 prefixEnd_1517722 := by exact prefixLift 1517722
  have htrace : WordTrace (prefixWord ++ tailWord_1517722) baseStart_1517722 baseEnd_1517722 := by
    simpa [prefixWord, tailWord_1517722, baseEnd_1517722] using wordTrace_append hprefix tailTrace_1517722
  have hstable : (prefixWord ++ tailWord_1517722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517722).length < 2 ^ (prefixWord ++ tailWord_1517722).sum := by decide
  have hdescent : baseEnd_1517722 < baseStart_1517722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517784 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 5]
def baseStart_1517784 : Nat := 118140960795 + 1517784 * 2 ^ 59
def prefixEnd_1517784 : Nat := 4983230072969 + 3 ^ 40 * 1517784 * 2
def baseEnd_1517784 : Nat := 173189493711954421515521

theorem tailTrace_1517784 : CollatzResearch.WordTrace tailWord_1517784 prefixEnd_1517784 173189493711954421515521 := by
  unfold tailWord_1517784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27679065166667629857500203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36905420222223506476666937 27679065166667629857500203)
  ·
    refine ⟨41518597750001444786250305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27679065166667629857500203 41518597750001444786250305)
    ·
      refine ⟨31138948312501083589687729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41518597750001444786250305 31138948312501083589687729)
      ·
        refine ⟨23354211234375812692265797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31138948312501083589687729 23354211234375812692265797)
        ·
          refine ⟨4378914606445464879799837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23354211234375812692265797 4378914606445464879799837)
          ·
            refine ⟨1642092977417049329924939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4378914606445464879799837 1642092977417049329924939)
            ·
              refine ⟨2463139466125573994887409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642092977417049329924939 2463139466125573994887409)
              ·
                refine ⟨1847354599594180496165557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463139466125573994887409 1847354599594180496165557)
                ·
                  refine ⟨173189493711954421515521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1847354599594180496165557 173189493711954421515521)
                  ·
                    rfl

theorem cell22_1517784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_1517784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517784 prefixEnd_1517784 := by exact prefixLift 1517784
  have htrace : WordTrace (prefixWord ++ tailWord_1517784) baseStart_1517784 baseEnd_1517784 := by
    simpa [prefixWord, tailWord_1517784, baseEnd_1517784] using wordTrace_append hprefix tailTrace_1517784
  have hstable : (prefixWord ++ tailWord_1517784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517784).length < 2 ^ (prefixWord ++ tailWord_1517784).sum := by decide
  have hdescent : baseEnd_1517784 < baseStart_1517784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517788 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1517788 : Nat := 118140960795 + 1517788 * 2 ^ 59
def prefixEnd_1517788 : Nat := 4983230072969 + 3 ^ 40 * 1517788 * 2
def baseEnd_1517788 : Nat := 519569850417608587446551

theorem tailTrace_1517788 : CollatzResearch.WordTrace tailWord_1517788 prefixEnd_1517788 519569850417608587446551 := by
  unfold tailWord_1517788
  simp only [CollatzResearch.WordTrace]
  refine ⟨27679138112660384199073009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36905517483547178932097345 27679138112660384199073009)
  ·
    refine ⟨20759353584495288149304757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27679138112660384199073009 20759353584495288149304757)
    ·
      refine ⟨1946189398546433263997321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20759353584495288149304757 1946189398546433263997321)
      ·
        refine ⟨1459642048909824947997991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1946189398546433263997321 1459642048909824947997991)
        ·
          refine ⟨2189463073364737421996987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459642048909824947997991 2189463073364737421996987)
          ·
            refine ⟨3284194610047106132995481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189463073364737421996987 3284194610047106132995481)
            ·
              refine ⟨2463145957535329599746611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284194610047106132995481 2463145957535329599746611)
              ·
                refine ⟨3694718936302994399619917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463145957535329599746611 3694718936302994399619917)
                ·
                  refine ⟨1385519601113622899857469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3694718936302994399619917 1385519601113622899857469)
                  ·
                    refine ⟨519569850417608587446551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385519601113622899857469 519569850417608587446551)
                    ·
                      rfl

theorem cell22_1517788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1517788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517788 prefixEnd_1517788 := by exact prefixLift 1517788
  have htrace : WordTrace (prefixWord ++ tailWord_1517788) baseStart_1517788 baseEnd_1517788 := by
    simpa [prefixWord, tailWord_1517788, baseEnd_1517788] using wordTrace_append hprefix tailTrace_1517788
  have hstable : (prefixWord ++ tailWord_1517788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517788).length < 2 ^ (prefixWord ++ tailWord_1517788).sum := by decide
  have hdescent : baseEnd_1517788 < baseStart_1517788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517814 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_1517814 : Nat := 118140960795 + 1517814 * 2 ^ 59
def prefixEnd_1517814 : Nat := 4983230072969 + 3 ^ 40 * 1517814 * 2
def baseEnd_1517814 : Nat := 519578750748953186296471

theorem tailTrace_1517814 : CollatzResearch.WordTrace tailWord_1517814 prefixEnd_1517814 519578750748953186296471 := by
  unfold tailWord_1517814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459951532701660927412031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36906149682151049892394997 3459951532701660927412031)
  ·
    refine ⟨5189927299052491391118047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3459951532701660927412031 5189927299052491391118047)
    ·
      refine ⟨7784890948578737086677071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5189927299052491391118047 7784890948578737086677071)
      ·
        refine ⟨11677336422868105630015607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7784890948578737086677071 11677336422868105630015607)
        ·
          refine ⟨17516004634302158445023411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11677336422868105630015607 17516004634302158445023411)
          ·
            refine ⟨26274006951453237667535117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17516004634302158445023411 26274006951453237667535117)
            ·
              refine ⟨9852752606794964125325669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26274006951453237667535117 9852752606794964125325669)
              ·
                refine ⟨1847391113774055773498563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9852752606794964125325669 1847391113774055773498563)
                ·
                  refine ⟨2771086670661083660247845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847391113774055773498563 2771086670661083660247845)
                  ·
                    refine ⟨519578750748953186296471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2771086670661083660247845 519578750748953186296471)
                    ·
                      rfl

theorem cell22_1517814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_1517814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517814 prefixEnd_1517814 := by exact prefixLift 1517814
  have htrace : WordTrace (prefixWord ++ tailWord_1517814) baseStart_1517814 baseEnd_1517814 := by
    simpa [prefixWord, tailWord_1517814, baseEnd_1517814] using wordTrace_append hprefix tailTrace_1517814
  have hstable : (prefixWord ++ tailWord_1517814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517814).length < 2 ^ (prefixWord ++ tailWord_1517814).sum := by decide
  have hdescent : baseEnd_1517814 < baseStart_1517814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517827 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 6, 3]
def baseStart_1517827 : Nat := 118140960795 + 1517827 * 2 ^ 59
def prefixEnd_1517827 : Nat := 4983230072969 + 3 ^ 40 * 1517827 * 2
def baseEnd_1517827 : Nat := 519583200914625485721431

theorem tailTrace_1517827 : CollatzResearch.WordTrace tailWord_1517827 prefixEnd_1517827 519583200914625485721431 := by
  unfold tailWord_1517827
  simp only [CollatzResearch.WordTrace]
  refine ⟨55359698672179478058815735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36906465781452985372543823 55359698672179478058815735)
  ·
    refine ⟨83039548008269217088223603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55359698672179478058815735 83039548008269217088223603)
    ·
      refine ⟨124559322012403825632335405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83039548008269217088223603 124559322012403825632335405)
      ·
        refine ⟨46709745754651434612125777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124559322012403825632335405 46709745754651434612125777)
        ·
          refine ⟨35032309315988575959094333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46709745754651434612125777 35032309315988575959094333)
          ·
            refine ⟨13137115993495715984660375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35032309315988575959094333 13137115993495715984660375)
            ·
              refine ⟨19705673990243573976990563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13137115993495715984660375 19705673990243573976990563)
              ·
                refine ⟨29558510985365360965485845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19705673990243573976990563 29558510985365360965485845)
                ·
                  refine ⟨1385555202439001295257149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29558510985365360965485845 1385555202439001295257149)
                  ·
                    refine ⟨519583200914625485721431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385555202439001295257149 519583200914625485721431)
                    ·
                      rfl

theorem cell22_1517827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 3].length) (baseStart_1517827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517827 prefixEnd_1517827 := by exact prefixLift 1517827
  have htrace : WordTrace (prefixWord ++ tailWord_1517827) baseStart_1517827 baseEnd_1517827 := by
    simpa [prefixWord, tailWord_1517827, baseEnd_1517827] using wordTrace_append hprefix tailTrace_1517827
  have hstable : (prefixWord ++ tailWord_1517827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517827).length < 2 ^ (prefixWord ++ tailWord_1517827).sum := by decide
  have hdescent : baseEnd_1517827 < baseStart_1517827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517861 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_1517861 : Nat := 118140960795 + 1517861 * 2 ^ 59
def prefixEnd_1517861 : Nat := 4983230072969 + 3 ^ 40 * 1517861 * 2
def baseEnd_1517861 : Nat := 519594839809460730371327

theorem tailTrace_1517861 : CollatzResearch.WordTrace tailWord_1517861 prefixEnd_1517861 519594839809460730371327 := by
  unfold tailWord_1517861
  simp only [CollatzResearch.WordTrace]
  refine ⟨55360938754056301865553437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36907292502704201243702291 55360938754056301865553437)
  ·
    refine ⟨20760352032771113199582539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55360938754056301865553437 20760352032771113199582539)
    ·
      refine ⟨31140528049156669799373809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20760352032771113199582539 31140528049156669799373809)
      ·
        refine ⟨23355396036867502349530357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31140528049156669799373809 23355396036867502349530357)
        ·
          refine ⟨2189568378456328345268471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23355396036867502349530357 2189568378456328345268471)
          ·
            refine ⟨3284352567684492517902707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189568378456328345268471 3284352567684492517902707)
            ·
              refine ⟨4926528851526738776854061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284352567684492517902707 4926528851526738776854061)
              ·
                refine ⟨1847448319322527041320273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4926528851526738776854061 1847448319322527041320273)
                ·
                  refine ⟨1385586239491895280990205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847448319322527041320273 1385586239491895280990205)
                  ·
                    refine ⟨519594839809460730371327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385586239491895280990205 519594839809460730371327)
                    ·
                      rfl

theorem cell22_1517861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_1517861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517861 prefixEnd_1517861 := by exact prefixLift 1517861
  have htrace : WordTrace (prefixWord ++ tailWord_1517861) baseStart_1517861 baseEnd_1517861 := by
    simpa [prefixWord, tailWord_1517861, baseEnd_1517861] using wordTrace_append hprefix tailTrace_1517861
  have hstable : (prefixWord ++ tailWord_1517861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517861).length < 2 ^ (prefixWord ++ tailWord_1517861).sum := by decide
  have hdescent : baseEnd_1517861 < baseStart_1517861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517876 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1517876 : Nat := 118140960795 + 1517876 * 2 ^ 59
def prefixEnd_1517876 : Nat := 4983230072969 + 3 ^ 40 * 1517876 * 2
def baseEnd_1517876 : Nat := 519599974616005691246281

theorem tailTrace_1517876 : CollatzResearch.WordTrace tailWord_1517876 prefixEnd_1517876 519599974616005691246281 := by
  unfold tailWord_1517876
  simp only [CollatzResearch.WordTrace]
  refine ⟨27680742924500979713674741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36907657232667972951566321 27680742924500979713674741)
  ·
    refine ⟨2595069649171966848157007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27680742924500979713674741 2595069649171966848157007)
    ·
      refine ⟨3892604473757950272235511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595069649171966848157007 3892604473757950272235511)
      ·
        refine ⟨5838906710636925408353267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3892604473757950272235511 5838906710636925408353267)
        ·
          refine ⟨8758360065955388112529901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5838906710636925408353267 8758360065955388112529901)
          ·
            refine ⟨3284385024733270542198713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8758360065955388112529901 3284385024733270542198713)
            ·
              refine ⟨2463288768549952906649035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284385024733270542198713 2463288768549952906649035)
              ·
                refine ⟨3694933152824929359973553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463288768549952906649035 3694933152824929359973553)
                ·
                  refine ⟨2771199864618697019980165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694933152824929359973553 2771199864618697019980165)
                  ·
                    refine ⟨519599974616005691246281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2771199864618697019980165 519599974616005691246281)
                    ·
                      rfl

theorem cell22_1517876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1517876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517876 prefixEnd_1517876 := by exact prefixLift 1517876
  have htrace : WordTrace (prefixWord ++ tailWord_1517876) baseStart_1517876 baseEnd_1517876 := by
    simpa [prefixWord, tailWord_1517876, baseEnd_1517876] using wordTrace_append hprefix tailTrace_1517876
  have hstable : (prefixWord ++ tailWord_1517876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517876).length < 2 ^ (prefixWord ++ tailWord_1517876).sum := by decide
  have hdescent : baseEnd_1517876 < baseStart_1517876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517964 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_1517964 : Nat := 118140960795 + 1517964 * 2 ^ 59
def prefixEnd_1517964 : Nat := 4983230072969 + 3 ^ 40 * 1517964 * 2
def baseEnd_1517964 : Nat := 173210032938134265015337

theorem tailTrace_1517964 : CollatzResearch.WordTrace tailWord_1517964 prefixEnd_1517964 173210032938134265015337 := by
  unfold tailWord_1517964
  simp only [CollatzResearch.WordTrace]
  refine ⟨27682347736341575228276473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36909796981788766971035297 27682347736341575228276473)
  ·
    refine ⟨20761760802256181421207355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27682347736341575228276473 20761760802256181421207355)
    ·
      refine ⟨31142641203384272131811033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20761760802256181421207355 31142641203384272131811033)
      ·
        refine ⟨23356980902538204098858275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31142641203384272131811033 23356980902538204098858275)
        ·
          refine ⟨35035471353807306148287413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23356980902538204098858275 35035471353807306148287413)
          ·
            refine ⟨3284575439419434951401945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35035471353807306148287413 3284575439419434951401945)
            ·
              refine ⟨2463431579564576213551459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284575439419434951401945 2463431579564576213551459)
              ·
                refine ⟨3695147369346864320327189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463431579564576213551459 3695147369346864320327189)
                ·
                  refine ⟨173210032938134265015337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3695147369346864320327189 173210032938134265015337)
                  ·
                    rfl

theorem cell22_1517964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_1517964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517964 prefixEnd_1517964 := by exact prefixLift 1517964
  have htrace : WordTrace (prefixWord ++ tailWord_1517964) baseStart_1517964 baseEnd_1517964 := by
    simpa [prefixWord, tailWord_1517964, baseEnd_1517964] using wordTrace_append hprefix tailTrace_1517964
  have hstable : (prefixWord ++ tailWord_1517964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517964).length < 2 ^ (prefixWord ++ tailWord_1517964).sum := by decide
  have hdescent : baseEnd_1517964 < baseStart_1517964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517977 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_1517977 : Nat := 118140960795 + 1517977 * 2 ^ 59
def prefixEnd_1517977 : Nat := 4983230072969 + 3 ^ 40 * 1517977 * 2
def baseEnd_1517977 : Nat := 519634548980075094470971

theorem tailTrace_1517977 : CollatzResearch.WordTrace tailWord_1517977 prefixEnd_1517977 519634548980075094470971 := by
  unfold tailWord_1517977
  simp only [CollatzResearch.WordTrace]
  refine ⟨55365169621636053676776185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36910113081090702451184123 55365169621636053676776185)
  ·
    refine ⟨41523877216227040257582139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55365169621636053676776185 41523877216227040257582139)
    ·
      refine ⟨62285815824340560386373209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41523877216227040257582139 62285815824340560386373209)
      ·
        refine ⟨46714361868255420289779907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62285815824340560386373209 46714361868255420289779907)
        ·
          refine ⟨70071542802383130434669861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46714361868255420289779907 70071542802383130434669861)
          ·
            refine ⟨13138414275446836956500599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70071542802383130434669861 13138414275446836956500599)
            ·
              refine ⟨19707621413170255434750899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13138414275446836956500599 19707621413170255434750899)
              ·
                refine ⟨29561432119755383152126349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19707621413170255434750899 29561432119755383152126349)
                ·
                  refine ⟨11085537044908268682047381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29561432119755383152126349 11085537044908268682047381)
                  ·
                    refine ⟨519634548980075094470971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11085537044908268682047381 519634548980075094470971)
                    ·
                      rfl

theorem cell22_1517977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_1517977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517977 prefixEnd_1517977 := by exact prefixLift 1517977
  have htrace : WordTrace (prefixWord ++ tailWord_1517977) baseStart_1517977 baseEnd_1517977 := by
    simpa [prefixWord, tailWord_1517977, baseEnd_1517977] using wordTrace_append hprefix tailTrace_1517977
  have hstable : (prefixWord ++ tailWord_1517977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517977).length < 2 ^ (prefixWord ++ tailWord_1517977).sum := by decide
  have hdescent : baseEnd_1517977 < baseStart_1517977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518009 : List Nat := [1, 2, 1, 4, 3, 3, 8]
def baseStart_1518009 : Nat := 118140960795 + 1518009 * 2 ^ 59
def prefixEnd_1518009 : Nat := 4983230072969 + 3 ^ 40 * 1518009 * 2
def baseEnd_1518009 : Nat := 19246129749408802876699

theorem tailTrace_1518009 : CollatzResearch.WordTrace tailWord_1518009 prefixEnd_1518009 19246129749408802876699 := by
  unfold tailWord_1518009
  simp only [CollatzResearch.WordTrace]
  refine ⟨55366336757520123141941081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36910891171680082094627387 55366336757520123141941081)
  ·
    refine ⟨41524752568140092356455811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55366336757520123141941081 41524752568140092356455811)
    ·
      refine ⟨62287128852210138534683717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41524752568140092356455811 62287128852210138534683717)
      ·
        refine ⟨11678836659789400975253197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62287128852210138534683717 11678836659789400975253197)
        ·
          refine ⟨4379563747421025365719949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11678836659789400975253197 4379563747421025365719949)
          ·
            refine ⟨1642336405282884512144981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4379563747421025365719949 1642336405282884512144981)
            ·
              refine ⟨19246129749408802876699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1642336405282884512144981 19246129749408802876699)
              ·
                rfl

theorem cell22_1518009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 8].length) (baseStart_1518009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518009 prefixEnd_1518009 := by exact prefixLift 1518009
  have htrace : WordTrace (prefixWord ++ tailWord_1518009) baseStart_1518009 baseEnd_1518009 := by
    simpa [prefixWord, tailWord_1518009, baseEnd_1518009] using wordTrace_append hprefix tailTrace_1518009
  have hstable : (prefixWord ++ tailWord_1518009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518009).length < 2 ^ (prefixWord ++ tailWord_1518009).sum := by decide
  have hdescent : baseEnd_1518009 < baseStart_1518009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518099 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 6]
def baseStart_1518099 : Nat := 118140960795 + 1518099 * 2 ^ 59
def prefixEnd_1518099 : Nat := 4983230072969 + 3 ^ 40 * 1518099 * 2
def baseEnd_1518099 : Nat := 173225437357769147640199

theorem tailTrace_1518099 : CollatzResearch.WordTrace tailWord_1518099 prefixEnd_1518099 173225437357769147640199 := by
  unfold tailWord_1518099
  simp only [CollatzResearch.WordTrace]
  refine ⟨55369619327194068512717351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36913079551462712341811567 55369619327194068512717351)
  ·
    refine ⟨83054428990791102769076027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55369619327194068512717351 83054428990791102769076027)
    ·
      refine ⟨124581643486186654153614041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83054428990791102769076027 124581643486186654153614041)
      ·
        refine ⟨93436232614639990615210531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124581643486186654153614041 93436232614639990615210531)
        ·
          refine ⟨140154348921959985922815797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93436232614639990615210531 140154348921959985922815797)
          ·
            refine ⟨13139470211433748680263981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140154348921959985922815797 13139470211433748680263981)
            ·
              refine ⟨4927301329287655755098993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13139470211433748680263981 4927301329287655755098993)
              ·
                refine ⟨3695475996965741816324245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927301329287655755098993 3695475996965741816324245)
                ·
                  refine ⟨173225437357769147640199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3695475996965741816324245 173225437357769147640199)
                  ·
                    rfl

theorem cell22_1518099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_1518099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518099 prefixEnd_1518099 := by exact prefixLift 1518099
  have htrace : WordTrace (prefixWord ++ tailWord_1518099) baseStart_1518099 baseEnd_1518099 := by
    simpa [prefixWord, tailWord_1518099, baseEnd_1518099] using wordTrace_append hprefix tailTrace_1518099
  have hstable : (prefixWord ++ tailWord_1518099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518099).length < 2 ^ (prefixWord ++ tailWord_1518099).sum := by decide
  have hdescent : baseEnd_1518099 < baseStart_1518099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518101 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1518101 : Nat := 118140960795 + 1518101 * 2 ^ 59
def prefixEnd_1518101 : Nat := 4983230072969 + 3 ^ 40 * 1518101 * 2
def baseEnd_1518101 : Nat := 519676996714180104370591

theorem tailTrace_1518101 : CollatzResearch.WordTrace tailWord_1518101 prefixEnd_1518101 519676996714180104370591 := by
  unfold tailWord_1518101
  simp only [CollatzResearch.WordTrace]
  refine ⟨55369692273186822854290157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36913128182124548569526771 55369692273186822854290157)
  ·
    refine ⟨20763634602445058570358809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55369692273186822854290157 20763634602445058570358809)
    ·
      refine ⟨15572725951833793927769107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20763634602445058570358809 15572725951833793927769107)
      ·
        refine ⟨23359088927750690891653661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15572725951833793927769107 23359088927750690891653661)
        ·
          refine ⟨8759658347906509084370123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23359088927750690891653661 8759658347906509084370123)
          ·
            refine ⟨13139487521859763626555185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8759658347906509084370123 13139487521859763626555185)
            ·
              refine ⟨9854615641394822719916389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13139487521859763626555185 9854615641394822719916389)
              ·
                refine ⟨1847740432761529259984323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9854615641394822719916389 1847740432761529259984323)
                ·
                  refine ⟨2771610649142293889976485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847740432761529259984323 2771610649142293889976485)
                  ·
                    refine ⟨519676996714180104370591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2771610649142293889976485 519676996714180104370591)
                    ·
                      rfl

theorem cell22_1518101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1518101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518101 prefixEnd_1518101 := by exact prefixLift 1518101
  have htrace : WordTrace (prefixWord ++ tailWord_1518101) baseStart_1518101 baseEnd_1518101 := by
    simpa [prefixWord, tailWord_1518101, baseEnd_1518101] using wordTrace_append hprefix tailTrace_1518101
  have hstable : (prefixWord ++ tailWord_1518101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518101).length < 2 ^ (prefixWord ++ tailWord_1518101).sum := by decide
  have hdescent : baseEnd_1518101 < baseStart_1518101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518131 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 4, 3]
def baseStart_1518131 : Nat := 118140960795 + 1518131 * 2 ^ 59
def prefixEnd_1518131 : Nat := 4983230072969 + 3 ^ 40 * 1518131 * 2
def baseEnd_1518131 : Nat := 519687266327270026120499

theorem tailTrace_1518131 : CollatzResearch.WordTrace tailWord_1518131 prefixEnd_1518131 519687266327270026120499 := by
  unfold tailWord_1518131
  simp only [CollatzResearch.WordTrace]
  refine ⟨55370786463078137977882247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36913857642052091985254831 55370786463078137977882247)
  ·
    refine ⟨83056179694617206966823371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55370786463078137977882247 83056179694617206966823371)
    ·
      refine ⟨124584269541925810450235057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83056179694617206966823371 124584269541925810450235057)
      ·
        refine ⟨93438202156444357837676293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124584269541925810450235057 93438202156444357837676293)
        ·
          refine ⟨17519662904333317094564305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93438202156444357837676293 17519662904333317094564305)
          ·
            refine ⟨13139747178249987820923229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17519662904333317094564305 13139747178249987820923229)
            ·
              refine ⟨4927405191843745432846211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13139747178249987820923229 4927405191843745432846211)
              ·
                refine ⟨7391107787765618149269317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927405191843745432846211 7391107787765618149269317)
                ·
                  refine ⟨1385832710206053402987997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7391107787765618149269317 1385832710206053402987997)
                  ·
                    refine ⟨519687266327270026120499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385832710206053402987997 519687266327270026120499)
                    ·
                      rfl

theorem cell22_1518131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 3].length) (baseStart_1518131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518131 prefixEnd_1518131 := by exact prefixLift 1518131
  have htrace : WordTrace (prefixWord ++ tailWord_1518131) baseStart_1518131 baseEnd_1518131 := by
    simpa [prefixWord, tailWord_1518131, baseEnd_1518131] using wordTrace_append hprefix tailTrace_1518131
  have hstable : (prefixWord ++ tailWord_1518131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518131).length < 2 ^ (prefixWord ++ tailWord_1518131).sum := by decide
  have hdescent : baseEnd_1518131 < baseStart_1518131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518161 : List Nat := [1, 2, 2, 1, 3, 3, 4, 6]
def baseStart_1518161 : Nat := 118140960795 + 1518161 * 2 ^ 59
def prefixEnd_1518161 : Nat := 4983230072969 + 3 ^ 40 * 1518161 * 2
def baseEnd_1518161 : Nat := 57744170660039994207823

theorem tailTrace_1518161 : CollatzResearch.WordTrace tailWord_1518161 prefixEnd_1518161 57744170660039994207823 := by
  unfold tailWord_1518161
  simp only [CollatzResearch.WordTrace]
  refine ⟨55371880652969453101474337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36914587101979635400982891 55371880652969453101474337)
  ·
    refine ⟨41528910489727089826105753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55371880652969453101474337 41528910489727089826105753)
    ·
      refine ⟨31146682867295317369579315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41528910489727089826105753 31146682867295317369579315)
      ·
        refine ⟨46720024300942976054368973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31146682867295317369579315 46720024300942976054368973)
        ·
          refine ⟨17520009112853616020388365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46720024300942976054368973 17520009112853616020388365)
          ·
            refine ⟨6570003417320106007645637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17520009112853616020388365 6570003417320106007645637)
            ·
              refine ⟨1231875640747519876433557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6570003417320106007645637 1231875640747519876433557)
              ·
                refine ⟨57744170660039994207823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1231875640747519876433557 57744170660039994207823)
                ·
                  rfl

theorem cell22_1518161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 6].length) (baseStart_1518161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518161 prefixEnd_1518161 := by exact prefixLift 1518161
  have htrace : WordTrace (prefixWord ++ tailWord_1518161) baseStart_1518161 baseEnd_1518161 := by
    simpa [prefixWord, tailWord_1518161, baseEnd_1518161] using wordTrace_append hprefix tailTrace_1518161
  have hstable : (prefixWord ++ tailWord_1518161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518161).length < 2 ^ (prefixWord ++ tailWord_1518161).sum := by decide
  have hdescent : baseEnd_1518161 < baseStart_1518161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518176 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_1518176 : Nat := 118140960795 + 1518176 * 2 ^ 59
def prefixEnd_1518176 : Nat := 4983230072969 + 3 ^ 40 * 1518176 * 2
def baseEnd_1518176 : Nat := 519702670746904908745361

theorem tailTrace_1518176 : CollatzResearch.WordTrace tailWord_1518176 prefixEnd_1518176 519702670746904908745361 := by
  unfold tailWord_1518176
  simp only [CollatzResearch.WordTrace]
  refine ⟨27686213873957555331635191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36914951831943407108846921 27686213873957555331635191)
  ·
    refine ⟨41529320810936332997452787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27686213873957555331635191 41529320810936332997452787)
    ·
      refine ⟨62293981216404499496179181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41529320810936332997452787 62293981216404499496179181)
      ·
        refine ⟨23360242956151687311067193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62293981216404499496179181 23360242956151687311067193)
        ·
          refine ⟨17520182217113765483300395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23360242956151687311067193 17520182217113765483300395)
          ·
            refine ⟨26280273325670648224950593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17520182217113765483300395 26280273325670648224950593)
            ·
              refine ⟨19710204994252986168712945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26280273325670648224950593 19710204994252986168712945)
              ·
                refine ⟨14782653745689739626534709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19710204994252986168712945 14782653745689739626534709)
                ·
                  refine ⟨1385873788658413089987629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14782653745689739626534709 1385873788658413089987629)
                  ·
                    refine ⟨519702670746904908745361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385873788658413089987629 519702670746904908745361)
                    ·
                      rfl

theorem cell22_1518176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_1518176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518176 prefixEnd_1518176 := by exact prefixLift 1518176
  have htrace : WordTrace (prefixWord ++ tailWord_1518176) baseStart_1518176 baseEnd_1518176 := by
    simpa [prefixWord, tailWord_1518176, baseEnd_1518176] using wordTrace_append hprefix tailTrace_1518176
  have hstable : (prefixWord ++ tailWord_1518176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518176).length < 2 ^ (prefixWord ++ tailWord_1518176).sum := by decide
  have hdescent : baseEnd_1518176 < baseStart_1518176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518238 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1518238 : Nat := 118140960795 + 1518238 * 2 ^ 59
def prefixEnd_1518238 : Nat := 4983230072969 + 3 ^ 40 * 1518238 * 2
def baseEnd_1518238 : Nat := 519723894613957413695171

theorem tailTrace_1518238 : CollatzResearch.WordTrace tailWord_1518238 prefixEnd_1518238 519723894613957413695171 := by
  unfold tailWord_1518238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921836134211311906503421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36916459382460330168018245 6921836134211311906503421)
  ·
    refine ⟨2595688550329241964938783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6921836134211311906503421 2595688550329241964938783)
    ·
      refine ⟨3893532825493862947408175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595688550329241964938783 3893532825493862947408175)
      ·
        refine ⟨5840299238240794421112263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893532825493862947408175 5840299238240794421112263)
        ·
          refine ⟨8760448857361191631668395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840299238240794421112263 8760448857361191631668395)
          ·
            refine ⟨13140673286041787447502593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760448857361191631668395 13140673286041787447502593)
            ·
              refine ⟨9855504964531340585626945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13140673286041787447502593 9855504964531340585626945)
              ·
                refine ⟨7391628723398505439220209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855504964531340585626945 7391628723398505439220209)
                ·
                  refine ⟨5543721542548879079415157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7391628723398505439220209 5543721542548879079415157)
                  ·
                    refine ⟨519723894613957413695171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5543721542548879079415157 519723894613957413695171)
                    ·
                      rfl

theorem cell22_1518238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1518238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518238 prefixEnd_1518238 := by exact prefixLift 1518238
  have htrace : WordTrace (prefixWord ++ tailWord_1518238) baseStart_1518238 baseEnd_1518238 := by
    simpa [prefixWord, tailWord_1518238, baseEnd_1518238] using wordTrace_append hprefix tailTrace_1518238
  have hstable : (prefixWord ++ tailWord_1518238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518238).length < 2 ^ (prefixWord ++ tailWord_1518238).sum := by decide
  have hdescent : baseEnd_1518238 < baseStart_1518238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518253 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1518253 : Nat := 118140960795 + 1518253 * 2 ^ 59
def prefixEnd_1518253 : Nat := 4983230072969 + 3 ^ 40 * 1518253 * 2
def baseEnd_1518253 : Nat := 519729029420502374570125

theorem tailTrace_1518253 : CollatzResearch.WordTrace tailWord_1518253 prefixEnd_1518253 519729029420502374570125 := by
  unfold tailWord_1518253
  simp only [CollatzResearch.WordTrace]
  refine ⟨55375236168636152813823413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36916824112424101875882275 55375236168636152813823413)
  ·
    refine ⟨5191428390809639326295945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55375236168636152813823413 5191428390809639326295945)
    ·
      refine ⟨3893571293107229494721959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5191428390809639326295945 3893571293107229494721959)
      ·
        refine ⟨5840356939660844242082939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893571293107229494721959 5840356939660844242082939)
        ·
          refine ⟨8760535409491266363124409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840356939660844242082939 8760535409491266363124409)
          ·
            refine ⟨6570401557118449772343307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8760535409491266363124409 6570401557118449772343307)
            ·
              refine ⟨9855602335677674658514961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570401557118449772343307 9855602335677674658514961)
              ·
                refine ⟨7391701751758255993886221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855602335677674658514961 7391701751758255993886221)
                ·
                  refine ⟨2771888156909345997707333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7391701751758255993886221 2771888156909345997707333)
                  ·
                    refine ⟨519729029420502374570125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2771888156909345997707333 519729029420502374570125)
                    ·
                      rfl

theorem cell22_1518253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1518253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518253 prefixEnd_1518253 := by exact prefixLift 1518253
  have htrace : WordTrace (prefixWord ++ tailWord_1518253) baseStart_1518253 baseEnd_1518253 := by
    simpa [prefixWord, tailWord_1518253, baseEnd_1518253] using wordTrace_append hprefix tailTrace_1518253
  have hstable : (prefixWord ++ tailWord_1518253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518253).length < 2 ^ (prefixWord ++ tailWord_1518253).sum := by decide
  have hdescent : baseEnd_1518253 < baseStart_1518253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518296 : List Nat := [2, 1, 2, 2, 3, 3, 9]
def baseStart_1518296 : Nat := 118140960795 + 1518296 * 2 ^ 59
def prefixEnd_1518296 : Nat := 4983230072969 + 3 ^ 40 * 1518296 * 2
def baseEnd_1518296 : Nat := 19249768488861651694259

theorem tailTrace_1518296 : CollatzResearch.WordTrace tailWord_1518296 prefixEnd_1518296 19249768488861651694259 := by
  unfold tailWord_1518296
  simp only [CollatzResearch.WordTrace]
  refine ⟨27688402253740185578819371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36917869671653580771759161 27688402253740185578819371)
  ·
    refine ⟨41532603380610278368229057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27688402253740185578819371 41532603380610278368229057)
    ·
      refine ⟨31149452535457708776171793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41532603380610278368229057 31149452535457708776171793)
      ·
        refine ⟨23362089401593281582128845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31149452535457708776171793 23362089401593281582128845)
        ·
          refine ⟨8760783525597480593298317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23362089401593281582128845 8760783525597480593298317)
          ·
            refine ⟨3285293822099055222486869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8760783525597480593298317 3285293822099055222486869)
            ·
              refine ⟨19249768488861651694259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3285293822099055222486869 19249768488861651694259)
              ·
                rfl

theorem cell22_1518296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 9].length) (baseStart_1518296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518296 prefixEnd_1518296 := by exact prefixLift 1518296
  have htrace : WordTrace (prefixWord ++ tailWord_1518296) baseStart_1518296 baseEnd_1518296 := by
    simpa [prefixWord, tailWord_1518296, baseEnd_1518296] using wordTrace_append hprefix tailTrace_1518296
  have hstable : (prefixWord ++ tailWord_1518296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518296).length < 2 ^ (prefixWord ++ tailWord_1518296).sum := by decide
  have hdescent : baseEnd_1518296 < baseStart_1518296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518317 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_1518317 : Nat := 118140960795 + 1518317 * 2 ^ 59
def prefixEnd_1518317 : Nat := 4983230072969 + 3 ^ 40 * 1518317 * 2
def baseEnd_1518317 : Nat := 519750937928427540969929

theorem tailTrace_1518317 : CollatzResearch.WordTrace tailWord_1518317 prefixEnd_1518317 519750937928427540969929 := by
  unfold tailWord_1518317
  simp only [CollatzResearch.WordTrace]
  refine ⟨55377570440404291744153205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36918380293602861162768803 55377570440404291744153205)
  ·
    refine ⟨5191647228787902351014363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55377570440404291744153205 5191647228787902351014363)
    ·
      refine ⟨7787470843181853526521545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191647228787902351014363 7787470843181853526521545)
      ·
        refine ⟨5840603132386390144891159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7787470843181853526521545 5840603132386390144891159)
        ·
          refine ⟨8760904698579585217336739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840603132386390144891159 8760904698579585217336739)
          ·
            refine ⟨13141357047869377826005109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760904698579585217336739 13141357047869377826005109)
            ·
              refine ⟨1232002223237754171187979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13141357047869377826005109 1232002223237754171187979)
              ·
                refine ⟨1848003334856631256781969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232002223237754171187979 1848003334856631256781969)
                ·
                  refine ⟨1386002501142473442586477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848003334856631256781969 1386002501142473442586477)
                  ·
                    refine ⟨519750937928427540969929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386002501142473442586477 519750937928427540969929)
                    ·
                      rfl

theorem cell22_1518317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_1518317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518317 prefixEnd_1518317 := by exact prefixLift 1518317
  have htrace : WordTrace (prefixWord ++ tailWord_1518317) baseStart_1518317 baseEnd_1518317 := by
    simpa [prefixWord, tailWord_1518317, baseEnd_1518317] using wordTrace_append hprefix tailTrace_1518317
  have hstable : (prefixWord ++ tailWord_1518317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518317).length < 2 ^ (prefixWord ++ tailWord_1518317).sum := by decide
  have hdescent : baseEnd_1518317 < baseStart_1518317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518328 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_1518328 : Nat := 118140960795 + 1518328 * 2 ^ 59
def prefixEnd_1518328 : Nat := 4983230072969 + 3 ^ 40 * 1518328 * 2
def baseEnd_1518328 : Nat := 519754703453227178944895

theorem tailTrace_1518328 : CollatzResearch.WordTrace tailWord_1518328 prefixEnd_1518328 519754703453227178944895 := by
  unfold tailWord_1518328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27688985821682220311401819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36918647762242960415202425 27688985821682220311401819)
  ·
    refine ⟨41533478732523330467102729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27688985821682220311401819 41533478732523330467102729)
    ·
      refine ⟨31150109049392497850327047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41533478732523330467102729 31150109049392497850327047)
      ·
        refine ⟨46725163574088746775490571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31150109049392497850327047 46725163574088746775490571)
        ·
          refine ⟨70087745361133120163235857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46725163574088746775490571 70087745361133120163235857)
          ·
            refine ⟨52565809020849840122426893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70087745361133120163235857 52565809020849840122426893)
            ·
              refine ⟨19712178382818690045910085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52565809020849840122426893 19712178382818690045910085)
              ·
                refine ⟨3696033446778504383608141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19712178382818690045910085 3696033446778504383608141)
                ·
                  refine ⟨1386012542541939143853053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3696033446778504383608141 1386012542541939143853053)
                  ·
                    refine ⟨519754703453227178944895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386012542541939143853053 519754703453227178944895)
                    ·
                      rfl

theorem cell22_1518328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_1518328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518328 prefixEnd_1518328 := by exact prefixLift 1518328
  have htrace : WordTrace (prefixWord ++ tailWord_1518328) baseStart_1518328 baseEnd_1518328 := by
    simpa [prefixWord, tailWord_1518328, baseEnd_1518328] using wordTrace_append hprefix tailTrace_1518328
  have hstable : (prefixWord ++ tailWord_1518328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518328).length < 2 ^ (prefixWord ++ tailWord_1518328).sum := by decide
  have hdescent : baseEnd_1518328 < baseStart_1518328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518371 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_1518371 : Nat := 118140960795 + 1518371 * 2 ^ 59
def prefixEnd_1518371 : Nat := 4983230072969 + 3 ^ 40 * 1518371 * 2
def baseEnd_1518371 : Nat := 519769423231989400119763

theorem tailTrace_1518371 : CollatzResearch.WordTrace tailWord_1518371 prefixEnd_1518371 519769423231989400119763 := by
  unfold tailWord_1518371
  simp only [CollatzResearch.WordTrace]
  refine ⟨55379539982208658966618967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36919693321472439311079311 55379539982208658966618967)
  ·
    refine ⟨83069309973312988449928451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55379539982208658966618967 83069309973312988449928451)
    ·
      refine ⟨124603964959969482674892677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83069309973312988449928451 124603964959969482674892677)
      ·
        refine ⟨23363243429994278001542377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124603964959969482674892677 23363243429994278001542377)
        ·
          refine ⟨17522432572495708501156783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23363243429994278001542377 17522432572495708501156783)
          ·
            refine ⟨26283648858743562751735175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17522432572495708501156783 26283648858743562751735175)
            ·
              refine ⟨39425473288115344127602763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26283648858743562751735175 39425473288115344127602763)
              ·
                refine ⟨59138209932173016191404145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39425473288115344127602763 59138209932173016191404145)
                ·
                  refine ⟨44353657449129762143553109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59138209932173016191404145 44353657449129762143553109)
                  ·
                    refine ⟨519769423231989400119763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44353657449129762143553109 519769423231989400119763)
                    ·
                      rfl

theorem cell22_1518371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_1518371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518371 prefixEnd_1518371 := by exact prefixLift 1518371
  have htrace : WordTrace (prefixWord ++ tailWord_1518371) baseStart_1518371 baseEnd_1518371 := by
    simpa [prefixWord, tailWord_1518371, baseEnd_1518371] using wordTrace_append hprefix tailTrace_1518371
  have hstable : (prefixWord ++ tailWord_1518371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518371).length < 2 ^ (prefixWord ++ tailWord_1518371).sum := by decide
  have hdescent : baseEnd_1518371 < baseStart_1518371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518413 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1518413 : Nat := 118140960795 + 1518413 * 2 ^ 59
def prefixEnd_1518413 : Nat := 4983230072969 + 3 ^ 40 * 1518413 * 2
def baseEnd_1518413 : Nat := 519783800690315290569635

theorem tailTrace_1518413 : CollatzResearch.WordTrace tailWord_1518413 prefixEnd_1518413 519783800690315290569635 := by
  unfold tailWord_1518413
  simp only [CollatzResearch.WordTrace]
  refine ⟨55381071848056500139647893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36920714565371000093098595 55381071848056500139647893)
  ·
    refine ⟨2595987742877648444045995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55381071848056500139647893 2595987742877648444045995)
    ·
      refine ⟨3893981614316472666068993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595987742877648444045995 3893981614316472666068993)
      ·
        refine ⟨2920486210737354499551745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3893981614316472666068993 2920486210737354499551745)
        ·
          refine ⟨2190364658053015874663809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2920486210737354499551745 2190364658053015874663809)
          ·
            refine ⟨1642773493539761905997857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190364658053015874663809 1642773493539761905997857)
            ·
              refine ⟨1232080120154821429498393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642773493539761905997857 1232080120154821429498393)
              ·
                refine ⟨924060090116116072123795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232080120154821429498393 924060090116116072123795)
                ·
                  refine ⟨1386090135174174108185693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924060090116116072123795 1386090135174174108185693)
                  ·
                    refine ⟨519783800690315290569635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386090135174174108185693 519783800690315290569635)
                    ·
                      rfl

theorem cell22_1518413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1518413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518413 prefixEnd_1518413 := by exact prefixLift 1518413
  have htrace : WordTrace (prefixWord ++ tailWord_1518413) baseStart_1518413 baseEnd_1518413 := by
    simpa [prefixWord, tailWord_1518413, baseEnd_1518413] using wordTrace_append hprefix tailTrace_1518413
  have hstable : (prefixWord ++ tailWord_1518413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518413).length < 2 ^ (prefixWord ++ tailWord_1518413).sum := by decide
  have hdescent : baseEnd_1518413 < baseStart_1518413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518418 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1518418 : Nat := 118140960795 + 1518418 * 2 ^ 59
def prefixEnd_1518418 : Nat := 4983230072969 + 3 ^ 40 * 1518418 * 2
def baseEnd_1518418 : Nat := 519785512292496944194619

theorem tailTrace_1518418 : CollatzResearch.WordTrace tailWord_1518418 prefixEnd_1518418 519785512292496944194619 := by
  unfold tailWord_1518418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845313553259596498394977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36920836142025590662386605 13845313553259596498394977)
  ·
    refine ⟨10383985164944697373796233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13845313553259596498394977 10383985164944697373796233)
    ·
      refine ⟨7787988873708523030347175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10383985164944697373796233 7787988873708523030347175)
      ·
        refine ⟨11681983310562784545520763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7787988873708523030347175 11681983310562784545520763)
        ·
          refine ⟨17522974965844176818281145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11681983310562784545520763 17522974965844176818281145)
          ·
            refine ⟨13142231224383132613710859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17522974965844176818281145 13142231224383132613710859)
            ·
              refine ⟨19713346836574698920566289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13142231224383132613710859 19713346836574698920566289)
              ·
                refine ⟨14785010127431024190424717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19713346836574698920566289 14785010127431024190424717)
                ·
                  refine ⟨5544378797786634071409269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14785010127431024190424717 5544378797786634071409269)
                  ·
                    refine ⟨519785512292496944194619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5544378797786634071409269 519785512292496944194619)
                    ·
                      rfl

theorem cell22_1518418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1518418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518418 prefixEnd_1518418 := by exact prefixLift 1518418
  have htrace : WordTrace (prefixWord ++ tailWord_1518418) baseStart_1518418 baseEnd_1518418 := by
    simpa [prefixWord, tailWord_1518418, baseEnd_1518418] using wordTrace_append hprefix tailTrace_1518418
  have hstable : (prefixWord ++ tailWord_1518418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518418).length < 2 ^ (prefixWord ++ tailWord_1518418).sum := by decide
  have hdescent : baseEnd_1518418 < baseStart_1518418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518435 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 1, 5]
def baseStart_1518435 : Nat := 118140960795 + 1518435 * 2 ^ 59
def prefixEnd_1518435 : Nat := 4983230072969 + 3 ^ 40 * 1518435 * 2
def baseEnd_1518435 : Nat := 519791331739914566519567

theorem tailTrace_1518435 : CollatzResearch.WordTrace tailWord_1518435 prefixEnd_1518435 519791331739914566519567 := by
  unfold tailWord_1518435
  simp only [CollatzResearch.WordTrace]
  refine ⟨55381874253976797896948759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36921249502651198597965839 55381874253976797896948759)
  ·
    refine ⟨83072811380965196845423139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55381874253976797896948759 83072811380965196845423139)
    ·
      refine ⟨124609217071447795268134709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83072811380965196845423139 124609217071447795268134709)
      ·
        refine ⟨11682114100448230806387629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124609217071447795268134709 11682114100448230806387629)
        ·
          refine ⟨4380792787668086552395361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11682114100448230806387629 4380792787668086552395361)
          ·
            refine ⟨3285594590751064914296521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380792787668086552395361 3285594590751064914296521)
            ·
              refine ⟨2464195943063298685722391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285594590751064914296521 2464195943063298685722391)
              ·
                refine ⟨3696293914594948028583587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464195943063298685722391 3696293914594948028583587)
                ·
                  refine ⟨5544440871892422042875381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696293914594948028583587 5544440871892422042875381)
                  ·
                    refine ⟨519791331739914566519567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5544440871892422042875381 519791331739914566519567)
                    ·
                      rfl

theorem cell22_1518435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].length) (baseStart_1518435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518435 prefixEnd_1518435 := by exact prefixLift 1518435
  have htrace : WordTrace (prefixWord ++ tailWord_1518435) baseStart_1518435 baseEnd_1518435 := by
    simpa [prefixWord, tailWord_1518435, baseEnd_1518435] using wordTrace_append hprefix tailTrace_1518435
  have hstable : (prefixWord ++ tailWord_1518435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518435).length < 2 ^ (prefixWord ++ tailWord_1518435).sum := by decide
  have hdescent : baseEnd_1518435 < baseStart_1518435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518450 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1518450 : Nat := 118140960795 + 1518450 * 2 ^ 59
def prefixEnd_1518450 : Nat := 4983230072969 + 3 ^ 40 * 1518450 * 2
def baseEnd_1518450 : Nat := 519796466546459527394521

theorem tailTrace_1518450 : CollatzResearch.WordTrace tailWord_1518450 prefixEnd_1518450 519796466546459527394521 := by
  unfold tailWord_1518450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845605337230613864686201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36921614232614970305829869 13845605337230613864686201)
  ·
    refine ⟨10384204002922960398514651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13845605337230613864686201 10384204002922960398514651)
    ·
      refine ⟨15576306004384440597771977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10384204002922960398514651 15576306004384440597771977)
      ·
        refine ⟨11682229503288330448328983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15576306004384440597771977 11682229503288330448328983)
        ·
          refine ⟨17523344254932495672493475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11682229503288330448328983 17523344254932495672493475)
          ·
            refine ⟨26285016382398743508740213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17523344254932495672493475 26285016382398743508740213)
            ·
              refine ⟨2464220285849882203944395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26285016382398743508740213 2464220285849882203944395)
              ·
                refine ⟨3696330428774823305916593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464220285849882203944395 3696330428774823305916593)
                ·
                  refine ⟨2772247821581117479437445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3696330428774823305916593 2772247821581117479437445)
                  ·
                    refine ⟨519796466546459527394521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772247821581117479437445 519796466546459527394521)
                    ·
                      rfl

theorem cell22_1518450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1518450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518450 prefixEnd_1518450 := by exact prefixLift 1518450
  have htrace : WordTrace (prefixWord ++ tailWord_1518450) baseStart_1518450 baseEnd_1518450 := by
    simpa [prefixWord, tailWord_1518450, baseEnd_1518450] using wordTrace_append hprefix tailTrace_1518450
  have hstable : (prefixWord ++ tailWord_1518450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518450).length < 2 ^ (prefixWord ++ tailWord_1518450).sum := by decide
  have hdescent : baseEnd_1518450 < baseStart_1518450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518454 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1518454 : Nat := 118140960795 + 1518454 * 2 ^ 59
def prefixEnd_1518454 : Nat := 4983230072969 + 3 ^ 40 * 1518454 * 2
def baseEnd_1518454 : Nat := 173265945276068283431503

theorem tailTrace_1518454 : CollatzResearch.WordTrace tailWord_1518454 prefixEnd_1518454 173265945276068283431503 := by
  unfold tailWord_1518454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461410452556747758868151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36921711493938642761260277 3461410452556747758868151)
  ·
    refine ⟨5192115678835121638302227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461410452556747758868151 5192115678835121638302227)
    ·
      refine ⟨7788173518252682457453341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192115678835121638302227 7788173518252682457453341)
      ·
        refine ⟨2920565069344755921545003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7788173518252682457453341 2920565069344755921545003)
        ·
          refine ⟨4380847604017133882317505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920565069344755921545003 4380847604017133882317505)
          ·
            refine ⟨3285635703012850411738129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380847604017133882317505 3285635703012850411738129)
            ·
              refine ⟨2464226777259637808803597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285635703012850411738129 2464226777259637808803597)
              ·
                refine ⟨924085041472364178301349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2464226777259637808803597 924085041472364178301349)
                ·
                  refine ⟨173265945276068283431503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924085041472364178301349 173265945276068283431503)
                  ·
                    rfl

theorem cell22_1518454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1518454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518454 prefixEnd_1518454 := by exact prefixLift 1518454
  have htrace : WordTrace (prefixWord ++ tailWord_1518454) baseStart_1518454 baseEnd_1518454 := by
    simpa [prefixWord, tailWord_1518454, baseEnd_1518454] using wordTrace_append hprefix tailTrace_1518454
  have hstable : (prefixWord ++ tailWord_1518454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518454).length < 2 ^ (prefixWord ++ tailWord_1518454).sum := by decide
  have hdescent : baseEnd_1518454 < baseStart_1518454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518486 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1518486 : Nat := 118140960795 + 1518486 * 2 ^ 59
def prefixEnd_1518486 : Nat := 4983230072969 + 3 ^ 40 * 1518486 * 2
def baseEnd_1518486 : Nat := 519808790082167433494411

theorem tailTrace_1518486 : CollatzResearch.WordTrace tailWord_1518486 prefixEnd_1518486 519808790082167433494411 := by
  unfold tailWord_1518486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461483398549502100440957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36922489584528022404703541 3461483398549502100440957)
  ·
    refine ⟨1298056274456063287665359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3461483398549502100440957 1298056274456063287665359)
    ·
      refine ⟨1947084411684094931498039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298056274456063287665359 1947084411684094931498039)
      ·
        refine ⟨2920626617526142397247059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947084411684094931498039 2920626617526142397247059)
        ·
          refine ⟨4380939926289213595870589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920626617526142397247059 4380939926289213595870589)
          ·
            refine ⟨1642852472358455098451471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4380939926289213595870589 1642852472358455098451471)
            ·
              refine ⟨2464278708537682647677207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642852472358455098451471 2464278708537682647677207)
              ·
                refine ⟨3696418062806523971515811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464278708537682647677207 3696418062806523971515811)
                ·
                  refine ⟨5544627094209785957273717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696418062806523971515811 5544627094209785957273717)
                  ·
                    refine ⟨519808790082167433494411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5544627094209785957273717 519808790082167433494411)
                    ·
                      rfl

theorem cell22_1518486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1518486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518486 prefixEnd_1518486 := by exact prefixLift 1518486
  have htrace : WordTrace (prefixWord ++ tailWord_1518486) baseStart_1518486 baseEnd_1518486 := by
    simpa [prefixWord, tailWord_1518486, baseEnd_1518486] using wordTrace_append hprefix tailTrace_1518486
  have hstable : (prefixWord ++ tailWord_1518486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518486).length < 2 ^ (prefixWord ++ tailWord_1518486).sum := by decide
  have hdescent : baseEnd_1518486 < baseStart_1518486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518497 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_1518497 : Nat := 118140960795 + 1518497 * 2 ^ 59
def prefixEnd_1518497 : Nat := 4983230072969 + 3 ^ 40 * 1518497 * 2
def baseEnd_1518497 : Nat := 519812555606967071469377

theorem tailTrace_1518497 : CollatzResearch.WordTrace tailWord_1518497 prefixEnd_1518497 519812555606967071469377 := by
  unfold tailWord_1518497
  simp only [CollatzResearch.WordTrace]
  refine ⟨55384135579752182485705745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36922757053168121657137163 55384135579752182485705745)
  ·
    refine ⟨41538101684814136864279309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55384135579752182485705745 41538101684814136864279309)
    ·
      refine ⟨15576788131805301324104741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41538101684814136864279309 15576788131805301324104741)
      ·
        refine ⟨2920647774713493998269639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15576788131805301324104741 2920647774713493998269639)
        ·
          refine ⟨4380971662070240997404459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920647774713493998269639 4380971662070240997404459)
          ·
            refine ⟨6571457493105361496106689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380971662070240997404459 6571457493105361496106689)
            ·
              refine ⟨4928593119829021122080017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571457493105361496106689 4928593119829021122080017)
              ·
                refine ⟨3696444839871765841560013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928593119829021122080017 3696444839871765841560013)
                ·
                  refine ⟨1386166814951912190585005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3696444839871765841560013 1386166814951912190585005)
                  ·
                    refine ⟨519812555606967071469377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386166814951912190585005 519812555606967071469377)
                    ·
                      rfl

theorem cell22_1518497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_1518497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518497 prefixEnd_1518497 := by exact prefixLift 1518497
  have htrace : WordTrace (prefixWord ++ tailWord_1518497) baseStart_1518497 baseEnd_1518497 := by
    simpa [prefixWord, tailWord_1518497, baseEnd_1518497] using wordTrace_append hprefix tailTrace_1518497
  have hstable : (prefixWord ++ tailWord_1518497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518497).length < 2 ^ (prefixWord ++ tailWord_1518497).sum := by decide
  have hdescent : baseEnd_1518497 < baseStart_1518497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518540 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1518540 : Nat := 118140960795 + 1518540 * 2 ^ 59
def prefixEnd_1518540 : Nat := 4983230072969 + 3 ^ 40 * 1518540 * 2
def baseEnd_1518540 : Nat := 519827275385729292644245

theorem tailTrace_1518540 : CollatzResearch.WordTrace tailWord_1518540 prefixEnd_1518540 519827275385729292644245 := by
  unfold tailWord_1518540
  simp only [CollatzResearch.WordTrace]
  refine ⟨27692851959298200414760537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36923802612397600553014049 27692851959298200414760537)
  ·
    refine ⟨20769638969473650311070403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27692851959298200414760537 20769638969473650311070403)
    ·
      refine ⟨31154458454210475466605605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20769638969473650311070403 31154458454210475466605605)
      ·
        refine ⟨5841460960164464149988551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31154458454210475466605605 5841460960164464149988551)
        ·
          refine ⟨8762191440246696224982827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841460960164464149988551 8762191440246696224982827)
          ·
            refine ⟨13143287160370044337474241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762191440246696224982827 13143287160370044337474241)
            ·
              refine ⟨9857465370277533253105681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13143287160370044337474241 9857465370277533253105681)
              ·
                refine ⟨7393099027708149939829261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9857465370277533253105681 7393099027708149939829261)
                ·
                  refine ⟨2772412135390556227435973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7393099027708149939829261 2772412135390556227435973)
                  ·
                    refine ⟨519827275385729292644245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772412135390556227435973 519827275385729292644245)
                    ·
                      rfl

theorem cell22_1518540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1518540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518540 prefixEnd_1518540 := by exact prefixLift 1518540
  have htrace : WordTrace (prefixWord ++ tailWord_1518540) baseStart_1518540 baseEnd_1518540 := by
    simpa [prefixWord, tailWord_1518540, baseEnd_1518540] using wordTrace_append hprefix tailTrace_1518540
  have hstable : (prefixWord ++ tailWord_1518540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518540).length < 2 ^ (prefixWord ++ tailWord_1518540).sum := by decide
  have hdescent : baseEnd_1518540 < baseStart_1518540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518557 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1518557 : Nat := 118140960795 + 1518557 * 2 ^ 59
def prefixEnd_1518557 : Nat := 4983230072969 + 3 ^ 40 * 1518557 * 2
def baseEnd_1518557 : Nat := 519833094833146914969193

theorem tailTrace_1518557 : CollatzResearch.WordTrace tailWord_1518557 prefixEnd_1518557 519833094833146914969193 := by
  unfold tailWord_1518557
  simp only [CollatzResearch.WordTrace]
  refine ⟨55386323959534812732889925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36924215973023208488593283 55386323959534812732889925)
  ·
    refine ⟨10384935742412777387416861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55386323959534812732889925 10384935742412777387416861)
    ·
      refine ⟨3894350903404791520281323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10384935742412777387416861 3894350903404791520281323)
      ·
        refine ⟨5841526355107187280421985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894350903404791520281323 5841526355107187280421985)
        ·
          refine ⟨4381144766330390460316489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841526355107187280421985 4381144766330390460316489)
          ·
            refine ⟨3285858574747792845237367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381144766330390460316489 3285858574747792845237367)
            ·
              refine ⟨4928787862121689267856051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285858574747792845237367 4928787862121689267856051)
              ·
                refine ⟨7393181793182533901784077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928787862121689267856051 7393181793182533901784077)
                ·
                  refine ⟨2772443172443450213169029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7393181793182533901784077 2772443172443450213169029)
                  ·
                    refine ⟨519833094833146914969193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772443172443450213169029 519833094833146914969193)
                    ·
                      rfl

theorem cell22_1518557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1518557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518557 prefixEnd_1518557 := by exact prefixLift 1518557
  have htrace : WordTrace (prefixWord ++ tailWord_1518557) baseStart_1518557 baseEnd_1518557 := by
    simpa [prefixWord, tailWord_1518557, baseEnd_1518557] using wordTrace_append hprefix tailTrace_1518557
  have hstable : (prefixWord ++ tailWord_1518557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518557).length < 2 ^ (prefixWord ++ tailWord_1518557).sum := by decide
  have hdescent : baseEnd_1518557 < baseStart_1518557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518570 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1518570 : Nat := 118140960795 + 1518570 * 2 ^ 59
def prefixEnd_1518570 : Nat := 4983230072969 + 3 ^ 40 * 1518570 * 2
def baseEnd_1518570 : Nat := 519837544998819214394153

theorem tailTrace_1518570 : CollatzResearch.WordTrace tailWord_1518570 prefixEnd_1518570 519837544998819214394153 := by
  unfold tailWord_1518570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13846699527121928988278291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36924532072325143968742109 13846699527121928988278291)
  ·
    refine ⟨20770049290682893482417437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13846699527121928988278291 20770049290682893482417437)
    ·
      refine ⟨7788768484006085055906539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20770049290682893482417437 7788768484006085055906539)
      ·
        refine ⟨11683152726009127583859809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7788768484006085055906539 11683152726009127583859809)
        ·
          refine ⟨8762364544506845687894857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11683152726009127583859809 8762364544506845687894857)
          ·
            refine ⟨6571773408380134265921143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8762364544506845687894857 6571773408380134265921143)
            ·
              refine ⟨9857660112570201398881715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571773408380134265921143 9857660112570201398881715)
              ·
                refine ⟨14786490168855302098322573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9857660112570201398881715 14786490168855302098322573)
                ·
                  refine ⟨5544933813320738286870965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14786490168855302098322573 5544933813320738286870965)
                  ·
                    refine ⟨519837544998819214394153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5544933813320738286870965 519837544998819214394153)
                    ·
                      rfl

theorem cell22_1518570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1518570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518570 prefixEnd_1518570 := by exact prefixLift 1518570
  have htrace : WordTrace (prefixWord ++ tailWord_1518570) baseStart_1518570 baseEnd_1518570 := by
    simpa [prefixWord, tailWord_1518570, baseEnd_1518570] using wordTrace_append hprefix tailTrace_1518570
  have hstable : (prefixWord ++ tailWord_1518570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518570).length < 2 ^ (prefixWord ++ tailWord_1518570).sum := by decide
  have hdescent : baseEnd_1518570 < baseStart_1518570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518585 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_1518585 : Nat := 118140960795 + 1518585 * 2 ^ 59
def prefixEnd_1518585 : Nat := 4983230072969 + 3 ^ 40 * 1518585 * 2
def baseEnd_1518585 : Nat := 519842679805364175269107

theorem tailTrace_1518585 : CollatzResearch.WordTrace tailWord_1518585 prefixEnd_1518585 519842679805364175269107 := by
  unfold tailWord_1518585
  simp only [CollatzResearch.WordTrace]
  refine ⟨55387345203433373514909209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36924896802288915676606139 55387345203433373514909209)
  ·
    refine ⟨41540508902575030136181907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55387345203433373514909209 41540508902575030136181907)
    ·
      refine ⟨62310763353862545204272861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41540508902575030136181907 62310763353862545204272861)
      ·
        refine ⟨23366536257698454451602323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62310763353862545204272861 23366536257698454451602323)
        ·
          refine ⟨35049804386547681677403485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23366536257698454451602323 35049804386547681677403485)
          ·
            refine ⟨13143676644955380629026307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35049804386547681677403485 13143676644955380629026307)
            ·
              refine ⟨19715514967433070943539461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13143676644955380629026307 19715514967433070943539461)
              ·
                refine ⟨3696659056393700801913649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19715514967433070943539461 3696659056393700801913649)
                ·
                  refine ⟨2772494292295275601435237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3696659056393700801913649 2772494292295275601435237)
                  ·
                    refine ⟨519842679805364175269107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772494292295275601435237 519842679805364175269107)
                    ·
                      rfl

theorem cell22_1518585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_1518585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518585 prefixEnd_1518585 := by exact prefixLift 1518585
  have htrace : WordTrace (prefixWord ++ tailWord_1518585) baseStart_1518585 baseEnd_1518585 := by
    simpa [prefixWord, tailWord_1518585, baseEnd_1518585] using wordTrace_append hprefix tailTrace_1518585
  have hstable : (prefixWord ++ tailWord_1518585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518585).length < 2 ^ (prefixWord ++ tailWord_1518585).sum := by decide
  have hdescent : baseEnd_1518585 < baseStart_1518585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518600 : List Nat := [2, 1, 3, 2, 1, 3, 3, 7]
def baseStart_1518600 : Nat := 118140960795 + 1518600 * 2 ^ 59
def prefixEnd_1518600 : Nat := 4983230072969 + 3 ^ 40 * 1518600 * 2
def baseEnd_1518600 : Nat := 57760868290212126238229

theorem tailTrace_1518600 : CollatzResearch.WordTrace tailWord_1518600 prefixEnd_1518600 57760868290212126238229 := by
  unfold tailWord_1518600
  simp only [CollatzResearch.WordTrace]
  refine ⟨27693946149189515538352627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36925261532252687384470169 27693946149189515538352627)
  ·
    refine ⟨41540919223784273307528941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27693946149189515538352627 41540919223784273307528941)
    ·
      refine ⟨15577844708919102490323353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41540919223784273307528941 15577844708919102490323353)
      ·
        refine ⟨11683383531689326867742515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15577844708919102490323353 11683383531689326867742515)
        ·
          refine ⟨17525075297533990301613773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11683383531689326867742515 17525075297533990301613773)
          ·
            refine ⟨6571903236575246363105165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17525075297533990301613773 6571903236575246363105165)
            ·
              refine ⟨2464463713715717386164437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6571903236575246363105165 2464463713715717386164437)
              ·
                refine ⟨57760868290212126238229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2464463713715717386164437 57760868290212126238229)
                ·
                  rfl

theorem cell22_1518600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_1518600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518600 prefixEnd_1518600 := by exact prefixLift 1518600
  have htrace : WordTrace (prefixWord ++ tailWord_1518600) baseStart_1518600 baseEnd_1518600 := by
    simpa [prefixWord, tailWord_1518600, baseEnd_1518600] using wordTrace_append hprefix tailTrace_1518600
  have hstable : (prefixWord ++ tailWord_1518600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518600).length < 2 ^ (prefixWord ++ tailWord_1518600).sum := by decide
  have hdescent : baseEnd_1518600 < baseStart_1518600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518649 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_1518649 : Nat := 118140960795 + 1518649 * 2 ^ 59
def prefixEnd_1518649 : Nat := 4983230072969 + 3 ^ 40 * 1518649 * 2
def baseEnd_1518649 : Nat := 519864588313289341668911

theorem tailTrace_1518649 : CollatzResearch.WordTrace tailWord_1518649 prefixEnd_1518649 519864588313289341668911 := by
  unfold tailWord_1518649
  simp only [CollatzResearch.WordTrace]
  refine ⟨55389679475201512445239001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36926452983467674963492667 55389679475201512445239001)
  ·
    refine ⟨41542259606401134333929251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55389679475201512445239001 41542259606401134333929251)
    ·
      refine ⟨62313389409601701500893877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41542259606401134333929251 62313389409601701500893877)
      ·
        refine ⟨5841880257150159515708801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62313389409601701500893877 5841880257150159515708801)
        ·
          refine ⟨4381410192862619636781601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841880257150159515708801 4381410192862619636781601)
          ·
            refine ⟨3286057644646964727586201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381410192862619636781601 3286057644646964727586201)
            ·
              refine ⟨2464543233485223545689651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286057644646964727586201 2464543233485223545689651)
              ·
                refine ⟨3696814850227835318534477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464543233485223545689651 3696814850227835318534477)
                ·
                  refine ⟨1386305568835438244450429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3696814850227835318534477 1386305568835438244450429)
                  ·
                    refine ⟨519864588313289341668911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386305568835438244450429 519864588313289341668911)
                    ·
                      rfl

theorem cell22_1518649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_1518649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518649 prefixEnd_1518649 := by exact prefixLift 1518649
  have htrace : WordTrace (prefixWord ++ tailWord_1518649) baseStart_1518649 baseEnd_1518649 := by
    simpa [prefixWord, tailWord_1518649, baseEnd_1518649] using wordTrace_append hprefix tailTrace_1518649
  have hstable : (prefixWord ++ tailWord_1518649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518649).length < 2 ^ (prefixWord ++ tailWord_1518649).sum := by decide
  have hdescent : baseEnd_1518649 < baseStart_1518649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518705 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1518705 : Nat := 118140960795 + 1518705 * 2 ^ 59
def prefixEnd_1518705 : Nat := 4983230072969 + 3 ^ 40 * 1518705 * 2
def baseEnd_1518705 : Nat := 519883758257723862268739

theorem tailTrace_1518705 : CollatzResearch.WordTrace tailWord_1518705 prefixEnd_1518705 519883758257723862268739 := by
  unfold tailWord_1518705
  simp only [CollatzResearch.WordTrace]
  refine ⟨55391721962998634009277569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36927814641999089339518379 55391721962998634009277569)
  ·
    refine ⟨41543791472248975506958177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55391721962998634009277569 41543791472248975506958177)
    ·
      refine ⟨31157843604186731630218633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41543791472248975506958177 31157843604186731630218633)
      ·
        refine ⟨23368382703140048722663975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31157843604186731630218633 23368382703140048722663975)
        ·
          refine ⟨35052574054710073083995963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23368382703140048722663975 35052574054710073083995963)
          ·
            refine ⟨52578861082065109625993945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35052574054710073083995963 52578861082065109625993945)
            ·
              refine ⟨39434145811548832219495459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52578861082065109625993945 39434145811548832219495459)
              ·
                refine ⟨59151218717323248329243189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39434145811548832219495459 59151218717323248329243189)
                ·
                  refine ⟨5545426754749054530866549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59151218717323248329243189 5545426754749054530866549)
                  ·
                    refine ⟨519883758257723862268739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5545426754749054530866549 519883758257723862268739)
                    ·
                      rfl

theorem cell22_1518705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1518705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518705 prefixEnd_1518705 := by exact prefixLift 1518705
  have htrace : WordTrace (prefixWord ++ tailWord_1518705) baseStart_1518705 baseEnd_1518705 := by
    simpa [prefixWord, tailWord_1518705, baseEnd_1518705] using wordTrace_append hprefix tailTrace_1518705
  have hstable : (prefixWord ++ tailWord_1518705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518705).length < 2 ^ (prefixWord ++ tailWord_1518705).sum := by decide
  have hdescent : baseEnd_1518705 < baseStart_1518705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518720 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_1518720 : Nat := 118140960795 + 1518720 * 2 ^ 59
def prefixEnd_1518720 : Nat := 4983230072969 + 3 ^ 40 * 1518720 * 2
def baseEnd_1518720 : Nat := 519888893064268823143693

theorem tailTrace_1518720 : CollatzResearch.WordTrace tailWord_1518720 prefixEnd_1518720 519888893064268823143693 := by
  unfold tailWord_1518720
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696134528972145785536807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36928179371962861047382409 27696134528972145785536807)
  ·
    refine ⟨41544201793458218678305211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27696134528972145785536807 41544201793458218678305211)
    ·
      refine ⟨62316302690187328017457817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41544201793458218678305211 62316302690187328017457817)
      ·
        refine ⟨46737227017640496013093363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62316302690187328017457817 46737227017640496013093363)
        ·
          refine ⟨70105840526460744019640045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46737227017640496013093363 70105840526460744019640045)
          ·
            refine ⟨26289690197422779007365017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70105840526460744019640045 26289690197422779007365017)
            ·
              refine ⟨19717267648067084255523763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26289690197422779007365017 19717267648067084255523763)
              ·
                refine ⟨29575901472100626383285645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19717267648067084255523763 29575901472100626383285645)
                ·
                  refine ⟨11090963052037734893732117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29575901472100626383285645 11090963052037734893732117)
                  ·
                    refine ⟨519888893064268823143693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11090963052037734893732117 519888893064268823143693)
                    ·
                      rfl

theorem cell22_1518720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_1518720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518720 prefixEnd_1518720 := by exact prefixLift 1518720
  have htrace : WordTrace (prefixWord ++ tailWord_1518720) baseStart_1518720 baseEnd_1518720 := by
    simpa [prefixWord, tailWord_1518720, baseEnd_1518720] using wordTrace_append hprefix tailTrace_1518720
  have hstable : (prefixWord ++ tailWord_1518720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518720).length < 2 ^ (prefixWord ++ tailWord_1518720).sum := by decide
  have hdescent : baseEnd_1518720 < baseStart_1518720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518756 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1518756 : Nat := 118140960795 + 1518756 * 2 ^ 59
def prefixEnd_1518756 : Nat := 4983230072969 + 3 ^ 40 * 1518756 * 2
def baseEnd_1518756 : Nat := 519901216599976729243583

theorem tailTrace_1518756 : CollatzResearch.WordTrace tailWord_1518756 prefixEnd_1518756 519901216599976729243583 := by
  unfold tailWord_1518756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696791042906934859692061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36929054723875913146256081 27696791042906934859692061)
  ·
    refine ⟨10386296641090100572384523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27696791042906934859692061 10386296641090100572384523)
    ·
      refine ⟨15579444961635150858576785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10386296641090100572384523 15579444961635150858576785)
      ·
        refine ⟨11684583721226363143932589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15579444961635150858576785 11684583721226363143932589)
        ·
          refine ⟨4381718895459886178974721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11684583721226363143932589 4381718895459886178974721)
          ·
            refine ⟨3286289171594914634231041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381718895459886178974721 3286289171594914634231041)
            ·
              refine ⟨2464716878696185975673281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286289171594914634231041 2464716878696185975673281)
              ·
                refine ⟨1848537659022139481754961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464716878696185975673281 1848537659022139481754961)
                ·
                  refine ⟨1386403244266604611316221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848537659022139481754961 1386403244266604611316221)
                  ·
                    refine ⟨519901216599976729243583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386403244266604611316221 519901216599976729243583)
                    ·
                      rfl

theorem cell22_1518756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1518756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518756 prefixEnd_1518756 := by exact prefixLift 1518756
  have htrace : WordTrace (prefixWord ++ tailWord_1518756) baseStart_1518756 baseEnd_1518756 := by
    simpa [prefixWord, tailWord_1518756, baseEnd_1518756] using wordTrace_append hprefix tailTrace_1518756
  have hstable : (prefixWord ++ tailWord_1518756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518756).length < 2 ^ (prefixWord ++ tailWord_1518756).sum := by decide
  have hdescent : baseEnd_1518756 < baseStart_1518756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518769 : List Nat := [1, 2, 2, 5, 1, 3, 1, 7]
def baseStart_1518769 : Nat := 118140960795 + 1518769 * 2 ^ 59
def prefixEnd_1518769 : Nat := 4983230072969 + 3 ^ 40 * 1518769 * 2
def baseEnd_1518769 : Nat := 57767296307294336518727

theorem tailTrace_1518769 : CollatzResearch.WordTrace tailWord_1518769 prefixEnd_1518769 57767296307294336518727 := by
  unfold tailWord_1518769
  simp only [CollatzResearch.WordTrace]
  refine ⟨55394056234766772939607361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36929370823177848626404907 55394056234766772939607361)
  ·
    refine ⟨41545542176075079704705521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55394056234766772939607361 41545542176075079704705521)
    ·
      refine ⟨31159156632056309778529141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41545542176075079704705521 31159156632056309778529141)
      ·
        refine ⟨2921170934255279041737107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31159156632056309778529141 2921170934255279041737107)
        ·
          refine ⟨4381756401382918562605661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921170934255279041737107 4381756401382918562605661)
          ·
            refine ⟨1643158650518594460977123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4381756401382918562605661 1643158650518594460977123)
            ·
              refine ⟨2464737975777891691465685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643158650518594460977123 2464737975777891691465685)
              ·
                refine ⟨57767296307294336518727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2464737975777891691465685 57767296307294336518727)
                ·
                  rfl

theorem cell22_1518769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 7].length) (baseStart_1518769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518769 prefixEnd_1518769 := by exact prefixLift 1518769
  have htrace : WordTrace (prefixWord ++ tailWord_1518769) baseStart_1518769 baseEnd_1518769 := by
    simpa [prefixWord, tailWord_1518769, baseEnd_1518769] using wordTrace_append hprefix tailTrace_1518769
  have hstable : (prefixWord ++ tailWord_1518769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518769).length < 2 ^ (prefixWord ++ tailWord_1518769).sum := by decide
  have hdescent : baseEnd_1518769 < baseStart_1518769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518788 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1518788 : Nat := 118140960795 + 1518788 * 2 ^ 59
def prefixEnd_1518788 : Nat := 4983230072969 + 3 ^ 40 * 1518788 * 2
def baseEnd_1518788 : Nat := 519912170853939312443485

theorem tailTrace_1518788 : CollatzResearch.WordTrace tailWord_1518788 prefixEnd_1518788 519912170853939312443485 := by
  unfold tailWord_1518788
  simp only [CollatzResearch.WordTrace]
  refine ⟨27697374610848969592274509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36929832814465292789699345 27697374610848969592274509)
  ·
    refine ⟨10386515479068363597102941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27697374610848969592274509 10386515479068363597102941)
    ·
      refine ⟨3894943304650636348913603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10386515479068363597102941 3894943304650636348913603)
      ·
        refine ⟨5842414956975954523370405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894943304650636348913603 5842414956975954523370405)
        ·
          refine ⟨1095452804432991473131951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5842414956975954523370405 1095452804432991473131951)
          ·
            refine ⟨1643179206649487209697927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095452804432991473131951 1643179206649487209697927)
            ·
              refine ⟨2464768809974230814546891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643179206649487209697927 2464768809974230814546891)
              ·
                refine ⟨3697153214961346221820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464768809974230814546891 3697153214961346221820337)
                ·
                  refine ⟨2772864911221009666365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697153214961346221820337 2772864911221009666365253)
                  ·
                    refine ⟨519912170853939312443485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772864911221009666365253 519912170853939312443485)
                    ·
                      rfl

theorem cell22_1518788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1518788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518788 prefixEnd_1518788 := by exact prefixLift 1518788
  have htrace : WordTrace (prefixWord ++ tailWord_1518788) baseStart_1518788 baseEnd_1518788 := by
    simpa [prefixWord, tailWord_1518788, baseEnd_1518788] using wordTrace_append hprefix tailTrace_1518788
  have hstable : (prefixWord ++ tailWord_1518788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518788).length < 2 ^ (prefixWord ++ tailWord_1518788).sum := by decide
  have hdescent : baseEnd_1518788 < baseStart_1518788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518829 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1518829 : Nat := 118140960795 + 1518829 * 2 ^ 59
def prefixEnd_1518829 : Nat := 4983230072969 + 3 ^ 40 * 1518829 * 2
def baseEnd_1518829 : Nat := 519926205991828872168359

theorem tailTrace_1518829 : CollatzResearch.WordTrace tailWord_1518829 prefixEnd_1518829 519926205991828872168359 := by
  unfold tailWord_1518829
  simp only [CollatzResearch.WordTrace]
  refine ⟨55396244614549403186791541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36930829743032935457861027 55396244614549403186791541)
  ·
    refine ⟨5193397932614006548761707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55396244614549403186791541 5193397932614006548761707)
    ·
      refine ⟨7790096898921009823142561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5193397932614006548761707 7790096898921009823142561)
      ·
        refine ⟨5842572674190757367356921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7790096898921009823142561 5842572674190757367356921)
        ·
          refine ⟨4381929505643068025517691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5842572674190757367356921 4381929505643068025517691)
          ·
            refine ⟨6572894258464602038276537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381929505643068025517691 6572894258464602038276537)
            ·
              refine ⟨4929670693848451528707403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572894258464602038276537 4929670693848451528707403)
              ·
                refine ⟨7394506040772677293061105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929670693848451528707403 7394506040772677293061105)
                ·
                  refine ⟨5545879530579507969795829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7394506040772677293061105 5545879530579507969795829)
                  ·
                    refine ⟨519926205991828872168359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5545879530579507969795829 519926205991828872168359)
                    ·
                      rfl

theorem cell22_1518829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1518829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518829 prefixEnd_1518829 := by exact prefixLift 1518829
  have htrace : WordTrace (prefixWord ++ tailWord_1518829) baseStart_1518829 baseEnd_1518829 := by
    simpa [prefixWord, tailWord_1518829, baseEnd_1518829] using wordTrace_append hprefix tailTrace_1518829
  have hstable : (prefixWord ++ tailWord_1518829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518829).length < 2 ^ (prefixWord ++ tailWord_1518829).sum := by decide
  have hdescent : baseEnd_1518829 < baseStart_1518829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518831 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 5]
def baseStart_1518831 : Nat := 118140960795 + 1518831 * 2 ^ 59
def prefixEnd_1518831 : Nat := 4983230072969 + 3 ^ 40 * 1518831 * 2
def baseEnd_1518831 : Nat := 173308963544233844539451

theorem tailTrace_1518831 : CollatzResearch.WordTrace tailWord_1518831 prefixEnd_1518831 173308963544233844539451 := by
  unfold tailWord_1518831
  simp only [CollatzResearch.WordTrace]
  refine ⟨55396317560542157528364347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36930878373694771685576231 55396317560542157528364347)
  ·
    refine ⟨83094476340813236292546521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55396317560542157528364347 83094476340813236292546521)
    ·
      refine ⟨62320857255609927219409891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83094476340813236292546521 62320857255609927219409891)
      ·
        refine ⟨93481285883414890829114837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62320857255609927219409891 93481285883414890829114837)
        ·
          refine ⟨2190967637892536503807379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93481285883414890829114837 2190967637892536503807379)
          ·
            refine ⟨3286451456838804755711069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190967637892536503807379 3286451456838804755711069)
            ·
              refine ⟨1232419296314551783391651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3286451456838804755711069 1232419296314551783391651)
              ·
                refine ⟨1848628944471827675087477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232419296314551783391651 1848628944471827675087477)
                ·
                  refine ⟨173308963544233844539451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848628944471827675087477 173308963544233844539451)
                  ·
                    rfl

theorem cell22_1518831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 5].length) (baseStart_1518831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518831 prefixEnd_1518831 := by exact prefixLift 1518831
  have htrace : WordTrace (prefixWord ++ tailWord_1518831) baseStart_1518831 baseEnd_1518831 := by
    simpa [prefixWord, tailWord_1518831, baseEnd_1518831] using wordTrace_append hprefix tailTrace_1518831
  have hstable : (prefixWord ++ tailWord_1518831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518831).length < 2 ^ (prefixWord ++ tailWord_1518831).sum := by decide
  have hdescent : baseEnd_1518831 < baseStart_1518831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518842 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_1518842 : Nat := 118140960795 + 1518842 * 2 ^ 59
def prefixEnd_1518842 : Nat := 4983230072969 + 3 ^ 40 * 1518842 * 2
def baseEnd_1518842 : Nat := 173310218719167057197773

theorem tailTrace_1518842 : CollatzResearch.WordTrace tailWord_1518842 prefixEnd_1518842 173310218719167057197773 := by
  unfold tailWord_1518842
  simp only [CollatzResearch.WordTrace]
  refine ⟨13849179690875576601753695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36931145842334870938009853 13849179690875576601753695)
  ·
    refine ⟨20773769536313364902630543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13849179690875576601753695 20773769536313364902630543)
    ·
      refine ⟨31160654304470047353945815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20773769536313364902630543 31160654304470047353945815)
      ·
        refine ⟨46740981456705071030918723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31160654304470047353945815 46740981456705071030918723)
        ·
          refine ⟨70111472185057606546378085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46740981456705071030918723 70111472185057606546378085)
          ·
            refine ⟨13145901034698301227445891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70111472185057606546378085 13145901034698301227445891)
            ·
              refine ⟨19718851552047451841168837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13145901034698301227445891 19718851552047451841168837)
              ·
                refine ⟨3697284666008897220219157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19718851552047451841168837 3697284666008897220219157)
                ·
                  refine ⟨173310218719167057197773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3697284666008897220219157 173310218719167057197773)
                  ·
                    rfl

theorem cell22_1518842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_1518842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518842 prefixEnd_1518842 := by exact prefixLift 1518842
  have htrace : WordTrace (prefixWord ++ tailWord_1518842) baseStart_1518842 baseEnd_1518842 := by
    simpa [prefixWord, tailWord_1518842, baseEnd_1518842] using wordTrace_append hprefix tailTrace_1518842
  have hstable : (prefixWord ++ tailWord_1518842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518842).length < 2 ^ (prefixWord ++ tailWord_1518842).sum := by decide
  have hdescent : baseEnd_1518842 < baseStart_1518842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518857 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_1518857 : Nat := 118140960795 + 1518857 * 2 ^ 59
def prefixEnd_1518857 : Nat := 4983230072969 + 3 ^ 40 * 1518857 * 2
def baseEnd_1518857 : Nat := 519935790964046132468273

theorem tailTrace_1518857 : CollatzResearch.WordTrace tailWord_1518857 prefixEnd_1518857 519935790964046132468273 := by
  unfold tailWord_1518857
  simp only [CollatzResearch.WordTrace]
  refine ⟨55397265858447963968810825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36931510572298642645873883 55397265858447963968810825)
  ·
    refine ⟨41547949393835972976608119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55397265858447963968810825 41547949393835972976608119)
    ·
      refine ⟨62321924090753959464912179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41547949393835972976608119 62321924090753959464912179)
      ·
        refine ⟨93482886136130939197368269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62321924090753959464912179 93482886136130939197368269)
        ·
          refine ⟨35056082301049102199013101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93482886136130939197368269 35056082301049102199013101)
          ·
            refine ⟨13146030862893413324629913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35056082301049102199013101 13146030862893413324629913)
            ·
              refine ⟨9859523147170059993472435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13146030862893413324629913 9859523147170059993472435)
              ·
                refine ⟨14789284720755089990208653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9859523147170059993472435 14789284720755089990208653)
                ·
                  refine ⟨5545981770283158746328245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14789284720755089990208653 5545981770283158746328245)
                  ·
                    refine ⟨519935790964046132468273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5545981770283158746328245 519935790964046132468273)
                    ·
                      rfl

theorem cell22_1518857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_1518857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518857 prefixEnd_1518857 := by exact prefixLift 1518857
  have htrace : WordTrace (prefixWord ++ tailWord_1518857) baseStart_1518857 baseEnd_1518857 := by
    simpa [prefixWord, tailWord_1518857, baseEnd_1518857] using wordTrace_append hprefix tailTrace_1518857
  have hstable : (prefixWord ++ tailWord_1518857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518857).length < 2 ^ (prefixWord ++ tailWord_1518857).sum := by decide
  have hdescent : baseEnd_1518857 < baseStart_1518857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518917 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_1518917 : Nat := 118140960795 + 1518917 * 2 ^ 59
def prefixEnd_1518917 : Nat := 4983230072969 + 3 ^ 40 * 1518917 * 2
def baseEnd_1518917 : Nat := 519956330190225975968089

theorem tailTrace_1518917 : CollatzResearch.WordTrace tailWord_1518917 prefixEnd_1518917 519956330190225975968089 := by
  unfold tailWord_1518917
  simp only [CollatzResearch.WordTrace]
  refine ⟨55399454238230594215995005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36932969492153729477330003 55399454238230594215995005)
  ·
    refine ⟨20774795339336472830998127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55399454238230594215995005 20774795339336472830998127)
    ·
      refine ⟨31162193009004709246497191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20774795339336472830998127 31162193009004709246497191)
      ·
        refine ⟨46743289513507063869745787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31162193009004709246497191 46743289513507063869745787)
        ·
          refine ⟨70114934270260595804618681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46743289513507063869745787 70114934270260595804618681)
          ·
            refine ⟨52586200702695446853464011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70114934270260595804618681 52586200702695446853464011)
            ·
              refine ⟨78879301054043170280196017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52586200702695446853464011 78879301054043170280196017)
              ·
                refine ⟨59159475790532377710147013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78879301054043170280196017 59159475790532377710147013)
                ·
                  refine ⟨11092401710724820820652565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59159475790532377710147013 11092401710724820820652565)
                  ·
                    refine ⟨519956330190225975968089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11092401710724820820652565 519956330190225975968089)
                    ·
                      rfl

theorem cell22_1518917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_1518917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518917 prefixEnd_1518917 := by exact prefixLift 1518917
  have htrace : WordTrace (prefixWord ++ tailWord_1518917) baseStart_1518917 baseEnd_1518917 := by
    simpa [prefixWord, tailWord_1518917, baseEnd_1518917] using wordTrace_append hprefix tailTrace_1518917
  have hstable : (prefixWord ++ tailWord_1518917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518917).length < 2 ^ (prefixWord ++ tailWord_1518917).sum := by decide
  have hdescent : baseEnd_1518917 < baseStart_1518917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518949 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 5]
def baseStart_1518949 : Nat := 118140960795 + 1518949 * 2 ^ 59
def prefixEnd_1518949 : Nat := 4983230072969 + 3 ^ 40 * 1518949 * 2
def baseEnd_1518949 : Nat := 173322428148062853055997

theorem tailTrace_1518949 : CollatzResearch.WordTrace tailWord_1518949 prefixEnd_1518949 173322428148062853055997 := by
  unfold tailWord_1518949
  simp only [CollatzResearch.WordTrace]
  refine ⟨55400621374114663681159901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36933747582743109120773267 55400621374114663681159901)
  ·
    refine ⟨20775233015292998880434963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55400621374114663681159901 20775233015292998880434963)
    ·
      refine ⟨31162849522939498320652445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20775233015292998880434963 31162849522939498320652445)
      ·
        refine ⟨11686068571102311870244667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31162849522939498320652445 11686068571102311870244667)
        ·
          refine ⟨17529102856653467805367001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11686068571102311870244667 17529102856653467805367001)
          ·
            refine ⟨13146827142490100854025251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17529102856653467805367001 13146827142490100854025251)
            ·
              refine ⟨19720240713735151281037877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13146827142490100854025251 19720240713735151281037877)
              ·
                refine ⟨1848772566912670432597301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19720240713735151281037877 1848772566912670432597301)
                ·
                  refine ⟨173322428148062853055997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848772566912670432597301 173322428148062853055997)
                  ·
                    rfl

theorem cell22_1518949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_1518949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1518949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1518949 prefixEnd_1518949 := by exact prefixLift 1518949
  have htrace : WordTrace (prefixWord ++ tailWord_1518949) baseStart_1518949 baseEnd_1518949 := by
    simpa [prefixWord, tailWord_1518949, baseEnd_1518949] using wordTrace_append hprefix tailTrace_1518949
  have hstable : (prefixWord ++ tailWord_1518949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518949).length < 2 ^ (prefixWord ++ tailWord_1518949).sum := by decide
  have hdescent : baseEnd_1518949 < baseStart_1518949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519060 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1519060 : Nat := 118140960795 + 1519060 * 2 ^ 59
def prefixEnd_1519060 : Nat := 4983230072969 + 3 ^ 40 * 1519060 * 2
def baseEnd_1519060 : Nat := 520005282012621269642651

theorem tailTrace_1519060 : CollatzResearch.WordTrace tailWord_1519060 prefixEnd_1519060 520005282012621269642651 := by
  unfold tailWord_1519060
  simp only [CollatzResearch.WordTrace]
  refine ⟨27702334938356264819225317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36936446584475019758967089 27702334938356264819225317)
  ·
    refine ⟨5194187800941799653604747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27702334938356264819225317 5194187800941799653604747)
    ·
      refine ⟨7791281701412699480407121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5194187800941799653604747 7791281701412699480407121)
      ·
        refine ⟨5843461276059524610305341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7791281701412699480407121 5843461276059524610305341)
        ·
          refine ⟨2191297978522321728864503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5843461276059524610305341 2191297978522321728864503)
          ·
            refine ⟨3286946967783482593296755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191297978522321728864503 3286946967783482593296755)
            ·
              refine ⟨4930420451675223889945133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286946967783482593296755 4930420451675223889945133)
              ·
                refine ⟨1848907669378208958729425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4930420451675223889945133 1848907669378208958729425)
                ·
                  refine ⟨1386680752033656719047069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848907669378208958729425 1386680752033656719047069)
                  ·
                    refine ⟨520005282012621269642651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386680752033656719047069 520005282012621269642651)
                    ·
                      rfl

theorem cell22_1519060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1519060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519060 prefixEnd_1519060 := by exact prefixLift 1519060
  have htrace : WordTrace (prefixWord ++ tailWord_1519060) baseStart_1519060 baseEnd_1519060 := by
    simpa [prefixWord, tailWord_1519060, baseEnd_1519060] using wordTrace_append hprefix tailTrace_1519060
  have hstable : (prefixWord ++ tailWord_1519060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519060).length < 2 ^ (prefixWord ++ tailWord_1519060).sum := by decide
  have hdescent : baseEnd_1519060 < baseStart_1519060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519071 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 5, 3]
def baseStart_1519071 : Nat := 118140960795 + 1519071 * 2 ^ 59
def prefixEnd_1519071 : Nat := 4983230072969 + 3 ^ 40 * 1519071 * 2
def baseEnd_1519071 : Nat := 520009047537420907617617

theorem tailTrace_1519071 : CollatzResearch.WordTrace tailWord_1519071 prefixEnd_1519071 520009047537420907617617 := by
  unfold tailWord_1519071
  simp only [CollatzResearch.WordTrace]
  refine ⟨55405071079672678517101067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36936714053115119011400711 55405071079672678517101067)
  ·
    refine ⟨83107606619509017775651601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55405071079672678517101067 83107606619509017775651601)
    ·
      refine ⟨62330704964631763331738701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83107606619509017775651601 62330704964631763331738701)
      ·
        refine ⟨23374014361736911249402013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62330704964631763331738701 23374014361736911249402013)
        ·
          refine ⟨8765255385651341718525755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23374014361736911249402013 8765255385651341718525755)
          ·
            refine ⟨13147883078477012577788633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765255385651341718525755 13147883078477012577788633)
            ·
              refine ⟨9860912308857759433341475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13147883078477012577788633 9860912308857759433341475)
              ·
                refine ⟨14791368463286639150012213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9860912308857759433341475 14791368463286639150012213)
                ·
                  refine ⟨1386690793433122420313645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14791368463286639150012213 1386690793433122420313645)
                  ·
                    refine ⟨520009047537420907617617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386690793433122420313645 520009047537420907617617)
                    ·
                      rfl

theorem cell22_1519071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_1519071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519071 prefixEnd_1519071 := by exact prefixLift 1519071
  have htrace : WordTrace (prefixWord ++ tailWord_1519071) baseStart_1519071 baseEnd_1519071 := by
    simpa [prefixWord, tailWord_1519071, baseEnd_1519071] using wordTrace_append hprefix tailTrace_1519071
  have hstable : (prefixWord ++ tailWord_1519071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519071).length < 2 ^ (prefixWord ++ tailWord_1519071).sum := by decide
  have hdescent : baseEnd_1519071 < baseStart_1519071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519084 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_1519084 : Nat := 118140960795 + 1519084 * 2 ^ 59
def prefixEnd_1519084 : Nat := 4983230072969 + 3 ^ 40 * 1519084 * 2
def baseEnd_1519084 : Nat := 173337832567697735680859

theorem tailTrace_1519084 : CollatzResearch.WordTrace tailWord_1519084 prefixEnd_1519084 173337832567697735680859 := by
  unfold tailWord_1519084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27702772614312790868662153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36937030152417054491549537 27702772614312790868662153)
  ·
    refine ⟨20777079460734593151496615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27702772614312790868662153 20777079460734593151496615)
    ·
      refine ⟨31165619191101889727244923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20777079460734593151496615 31165619191101889727244923)
      ·
        refine ⟨46748428786652834590867385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31165619191101889727244923 46748428786652834590867385)
        ·
          refine ⟨35061321589989625943150539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46748428786652834590867385 35061321589989625943150539)
          ·
            refine ⟨52591982384984438914725809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35061321589989625943150539 52591982384984438914725809)
            ·
              refine ⟨39443986788738329186044357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52591982384984438914725809 39443986788738329186044357)
              ·
                refine ⟨7395747522888436722383317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39443986788738329186044357 7395747522888436722383317)
                ·
                  refine ⟨173337832567697735680859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7395747522888436722383317 173337832567697735680859)
                  ·
                    rfl

theorem cell22_1519084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_1519084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519084 prefixEnd_1519084 := by exact prefixLift 1519084
  have htrace : WordTrace (prefixWord ++ tailWord_1519084) baseStart_1519084 baseEnd_1519084 := by
    simpa [prefixWord, tailWord_1519084, baseEnd_1519084] using wordTrace_append hprefix tailTrace_1519084
  have hstable : (prefixWord ++ tailWord_1519084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519084).length < 2 ^ (prefixWord ++ tailWord_1519084).sum := by decide
  have hdescent : baseEnd_1519084 < baseStart_1519084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519099 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_1519099 : Nat := 118140960795 + 1519099 * 2 ^ 59
def prefixEnd_1519099 : Nat := 4983230072969 + 3 ^ 40 * 1519099 * 2
def baseEnd_1519099 : Nat := 520018632509638167917531

theorem tailTrace_1519099 : CollatzResearch.WordTrace tailWord_1519099 prefixEnd_1519099 520018632509638167917531 := by
  unfold tailWord_1519099
  simp only [CollatzResearch.WordTrace]
  refine ⟨55406092323571239299120351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36937394882380826199413567 55406092323571239299120351)
  ·
    refine ⟨83109138485356858948680527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55406092323571239299120351 83109138485356858948680527)
    ·
      refine ⟨124663707728035288423020791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83109138485356858948680527 124663707728035288423020791)
      ·
        refine ⟨186995561592052932634531187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124663707728035288423020791 186995561592052932634531187)
        ·
          refine ⟨280493342388079398951796781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186995561592052932634531187 280493342388079398951796781)
          ·
            refine ⟨105185003395529774606923793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280493342388079398951796781 105185003395529774606923793)
            ·
              refine ⟨78888752546647330955192845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105185003395529774606923793 78888752546647330955192845)
              ·
                refine ⟨29583282204992749108197317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78888752546647330955192845 29583282204992749108197317)
                ·
                  refine ⟨5546865413436140457786997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29583282204992749108197317 5546865413436140457786997)
                  ·
                    refine ⟨520018632509638167917531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5546865413436140457786997 520018632509638167917531)
                    ·
                      rfl

theorem cell22_1519099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_1519099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519099 prefixEnd_1519099 := by exact prefixLift 1519099
  have htrace : WordTrace (prefixWord ++ tailWord_1519099) baseStart_1519099 baseEnd_1519099 := by
    simpa [prefixWord, tailWord_1519099, baseEnd_1519099] using wordTrace_append hprefix tailTrace_1519099
  have hstable : (prefixWord ++ tailWord_1519099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519099).length < 2 ^ (prefixWord ++ tailWord_1519099).sum := by decide
  have hdescent : baseEnd_1519099 < baseStart_1519099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519101 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 5]
def baseStart_1519101 : Nat := 118140960795 + 1519101 * 2 ^ 59
def prefixEnd_1519101 : Nat := 4983230072969 + 3 ^ 40 * 1519101 * 2
def baseEnd_1519101 : Nat := 173339772383503609789175

theorem tailTrace_1519101 : CollatzResearch.WordTrace tailWord_1519101 prefixEnd_1519101 173339772383503609789175 := by
  unfold tailWord_1519101
  simp only [CollatzResearch.WordTrace]
  refine ⟨55406165269563993640693157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36937443513042662427128771 55406165269563993640693157)
  ·
    refine ⟨10388655988043248807629967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55406165269563993640693157 10388655988043248807629967)
    ·
      refine ⟨15582983982064873211444951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10388655988043248807629967 15582983982064873211444951)
      ·
        refine ⟨23374475973097309817167427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15582983982064873211444951 23374475973097309817167427)
        ·
          refine ⟨35061713959645964725751141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23374475973097309817167427 35061713959645964725751141)
          ·
            refine ⟨6574071367433618386078339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35061713959645964725751141 6574071367433618386078339)
            ·
              refine ⟨9861107051150427579117509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574071367433618386078339 9861107051150427579117509)
              ·
                refine ⟨1848957572090705171084533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9861107051150427579117509 1848957572090705171084533)
                ·
                  refine ⟨173339772383503609789175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848957572090705171084533 173339772383503609789175)
                  ·
                    rfl

theorem cell22_1519101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_1519101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519101 prefixEnd_1519101 := by exact prefixLift 1519101
  have htrace : WordTrace (prefixWord ++ tailWord_1519101) baseStart_1519101 baseEnd_1519101 := by
    simpa [prefixWord, tailWord_1519101, baseEnd_1519101] using wordTrace_append hprefix tailTrace_1519101
  have hstable : (prefixWord ++ tailWord_1519101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519101).length < 2 ^ (prefixWord ++ tailWord_1519101).sum := by decide
  have hdescent : baseEnd_1519101 < baseStart_1519101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519146 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_1519146 : Nat := 118140960795 + 1519146 * 2 ^ 59
def prefixEnd_1519146 : Nat := 4983230072969 + 3 ^ 40 * 1519146 * 2
def baseEnd_1519146 : Nat := 173344907190048570664129

theorem tailTrace_1519146 : CollatzResearch.WordTrace tailWord_1519146 prefixEnd_1519146 173344907190048570664129 := by
  unfold tailWord_1519146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13851951638600241581520323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36938537702933977550720861 13851951638600241581520323)
  ·
    refine ⟨20777927457900362372280485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13851951638600241581520323 20777927457900362372280485)
    ·
      refine ⟨3895861398356317944802591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20777927457900362372280485 3895861398356317944802591)
      ·
        refine ⟨5843792097534476917203887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895861398356317944802591 5843792097534476917203887)
        ·
          refine ⟨8765688146301715375805831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843792097534476917203887 8765688146301715375805831)
          ·
            refine ⟨13148532219452573063708747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765688146301715375805831 13148532219452573063708747)
            ·
              refine ⟨19722798329178859595563121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13148532219452573063708747 19722798329178859595563121)
              ·
                refine ⟨14792098746884144696672341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19722798329178859595563121 14792098746884144696672341)
                ·
                  refine ⟨173344907190048570664129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14792098746884144696672341 173344907190048570664129)
                  ·
                    rfl

theorem cell22_1519146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_1519146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519146 prefixEnd_1519146 := by exact prefixLift 1519146
  have htrace : WordTrace (prefixWord ++ tailWord_1519146) baseStart_1519146 baseEnd_1519146 := by
    simpa [prefixWord, tailWord_1519146, baseEnd_1519146] using wordTrace_append hprefix tailTrace_1519146
  have hstable : (prefixWord ++ tailWord_1519146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519146).length < 2 ^ (prefixWord ++ tailWord_1519146).sum := by decide
  have hdescent : baseEnd_1519146 < baseStart_1519146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519191 : List Nat := [1, 1, 3, 2, 2, 4, 1, 8]
def baseStart_1519191 : Nat := 118140960795 + 1519191 * 2 ^ 59
def prefixEnd_1519191 : Nat := 4983230072969 + 3 ^ 40 * 1519191 * 2
def baseEnd_1519191 : Nat := 57783347332197843846361

theorem tailTrace_1519191 : CollatzResearch.WordTrace tailWord_1519191 prefixEnd_1519191 57783347332197843846361 := by
  unfold tailWord_1519191
  simp only [CollatzResearch.WordTrace]
  refine ⟨55409447839237939011469427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36939631892825292674312951 55409447839237939011469427)
  ·
    refine ⟨83114171758856908517204141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55409447839237939011469427 83114171758856908517204141)
    ·
      refine ⟨31167814409571340693951553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83114171758856908517204141 31167814409571340693951553)
      ·
        refine ⟨23375860807178505520463665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31167814409571340693951553 23375860807178505520463665)
        ·
          refine ⟨17531895605383879140347749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23375860807178505520463665 17531895605383879140347749)
          ·
            refine ⟨3287230426009477338815203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17531895605383879140347749 3287230426009477338815203)
            ·
              refine ⟨4930845639014216008222805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287230426009477338815203 4930845639014216008222805)
              ·
                refine ⟨57783347332197843846361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4930845639014216008222805 57783347332197843846361)
                ·
                  rfl

theorem cell22_1519191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 8].length) (baseStart_1519191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519191 prefixEnd_1519191 := by exact prefixLift 1519191
  have htrace : WordTrace (prefixWord ++ tailWord_1519191) baseStart_1519191 baseEnd_1519191 := by
    simpa [prefixWord, tailWord_1519191, baseEnd_1519191] using wordTrace_append hprefix tailTrace_1519191
  have hstable : (prefixWord ++ tailWord_1519191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519191).length < 2 ^ (prefixWord ++ tailWord_1519191).sum := by decide
  have hdescent : baseEnd_1519191 < baseStart_1519191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519208 : List Nat := [2, 1, 4, 3, 1, 3, 8]
def baseStart_1519208 : Nat := 118140960795 + 1519208 * 2 ^ 59
def prefixEnd_1519208 : Nat := 4983230072969 + 3 ^ 40 * 1519208 * 2
def baseEnd_1519208 : Nat := 19261331312488822849711

theorem tailTrace_1519208 : CollatzResearch.WordTrace tailWord_1519208 prefixEnd_1519208 19261331312488822849711 := by
  unfold tailWord_1519208
  simp only [CollatzResearch.WordTrace]
  refine ⟨27705033940088175457419139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36940045253450900609892185 27705033940088175457419139)
  ·
    refine ⟨41557550910132263186128709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27705033940088175457419139 41557550910132263186128709)
    ·
      refine ⟨7792040795649799347399133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41557550910132263186128709 7792040795649799347399133)
      ·
        refine ⟨2922015298368674755274675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7792040795649799347399133 2922015298368674755274675)
        ·
          refine ⟨4383022947553012132912013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922015298368674755274675 4383022947553012132912013)
          ·
            refine ⟨1643633605332379549842005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4383022947553012132912013 1643633605332379549842005)
            ·
              refine ⟨19261331312488822849711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1643633605332379549842005 19261331312488822849711)
              ·
                rfl

theorem cell22_1519208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 8].length) (baseStart_1519208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519208 prefixEnd_1519208 := by exact prefixLift 1519208
  have htrace : WordTrace (prefixWord ++ tailWord_1519208) baseStart_1519208 baseEnd_1519208 := by
    simpa [prefixWord, tailWord_1519208, baseEnd_1519208] using wordTrace_append hprefix tailTrace_1519208
  have hstable : (prefixWord ++ tailWord_1519208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519208).length < 2 ^ (prefixWord ++ tailWord_1519208).sum := by decide
  have hdescent : baseEnd_1519208 < baseStart_1519208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519285 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1519285 : Nat := 118140960795 + 1519285 * 2 ^ 59
def prefixEnd_1519285 : Nat := 4983230072969 + 3 ^ 40 * 1519285 * 2
def baseEnd_1519285 : Nat := 520082304110795682766961

theorem tailTrace_1519285 : CollatzResearch.WordTrace tailWord_1519285 prefixEnd_1519285 520082304110795682766961 := by
  unfold tailWord_1519285
  simp only [CollatzResearch.WordTrace]
  refine ⟨55412876300897393065391309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36941917533931595376927539 55412876300897393065391309)
  ·
    refine ⟨20779828612836522399521741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55412876300897393065391309 20779828612836522399521741)
    ·
      refine ⟨7792435729813695899820653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20779828612836522399521741 7792435729813695899820653)
      ·
        refine ⟨2922163398680135962432745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7792435729813695899820653 2922163398680135962432745)
        ·
          refine ⟨2191622549010101971824559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922163398680135962432745 2191622549010101971824559)
          ·
            refine ⟨3287433823515152957736839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191622549010101971824559 3287433823515152957736839)
            ·
              refine ⟨4931150735272729436605259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287433823515152957736839 4931150735272729436605259)
              ·
                refine ⟨7396726102909094154907889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931150735272729436605259 7396726102909094154907889)
                ·
                  refine ⟨5547544577181820616180917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7396726102909094154907889 5547544577181820616180917)
                  ·
                    refine ⟨520082304110795682766961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5547544577181820616180917 520082304110795682766961)
                    ·
                      rfl

theorem cell22_1519285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1519285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519285 prefixEnd_1519285 := by exact prefixLift 1519285
  have htrace : WordTrace (prefixWord ++ tailWord_1519285) baseStart_1519285 baseEnd_1519285 := by
    simpa [prefixWord, tailWord_1519285, baseEnd_1519285] using wordTrace_append hprefix tailTrace_1519285
  have hstable : (prefixWord ++ tailWord_1519285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519285).length < 2 ^ (prefixWord ++ tailWord_1519285).sum := by decide
  have hdescent : baseEnd_1519285 < baseStart_1519285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519300 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1519300 : Nat := 118140960795 + 1519300 * 2 ^ 59
def prefixEnd_1519300 : Nat := 4983230072969 + 3 ^ 40 * 1519300 * 2
def baseEnd_1519300 : Nat := 520087438917340643641915

theorem tailTrace_1519300 : CollatzResearch.WordTrace tailWord_1519300 prefixEnd_1519300 520087438917340643641915 := by
  unfold tailWord_1519300
  simp only [CollatzResearch.WordTrace]
  refine ⟨27706711697921525313593677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36942282263895367084791569 27706711697921525313593677)
  ·
    refine ⟨10390016886720571992597629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27706711697921525313593677 10390016886720571992597629)
    ·
      refine ⟨3896256332520214497224111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10390016886720571992597629 3896256332520214497224111)
      ·
        refine ⟨5844384498780321745836167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896256332520214497224111 5844384498780321745836167)
        ·
          refine ⟨8766576748170482618754251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5844384498780321745836167 8766576748170482618754251)
          ·
            refine ⟨13149865122255723928131377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766576748170482618754251 13149865122255723928131377)
            ·
              refine ⟨9862398841691792946098533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13149865122255723928131377 9862398841691792946098533)
              ·
                refine ⟨1849199782817211177393475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9862398841691792946098533 1849199782817211177393475)
                ·
                  refine ⟨2773799674225816766090213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849199782817211177393475 2773799674225816766090213)
                  ·
                    refine ⟨520087438917340643641915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773799674225816766090213 520087438917340643641915)
                    ·
                      rfl

theorem cell22_1519300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1519300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519300 prefixEnd_1519300 := by exact prefixLift 1519300
  have htrace : WordTrace (prefixWord ++ tailWord_1519300) baseStart_1519300 baseEnd_1519300 := by
    simpa [prefixWord, tailWord_1519300, baseEnd_1519300] using wordTrace_append hprefix tailTrace_1519300
  have hstable : (prefixWord ++ tailWord_1519300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519300).length < 2 ^ (prefixWord ++ tailWord_1519300).sum := by decide
  have hdescent : baseEnd_1519300 < baseStart_1519300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519313 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_1519313 : Nat := 118140960795 + 1519313 * 2 ^ 59
def prefixEnd_1519313 : Nat := 4983230072969 + 3 ^ 40 * 1519313 * 2
def baseEnd_1519313 : Nat := 520091889083012943066875

theorem tailTrace_1519313 : CollatzResearch.WordTrace tailWord_1519313 prefixEnd_1519313 520091889083012943066875 := by
  unfold tailWord_1519313
  simp only [CollatzResearch.WordTrace]
  refine ⟨55413897544795953847410593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36942598363197302564940395 55413897544795953847410593)
  ·
    refine ⟨41560423158596965385557945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55413897544795953847410593 41560423158596965385557945)
    ·
      refine ⟨31170317368947724039168459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41560423158596965385557945 31170317368947724039168459)
      ·
        refine ⟨46755476053421586058752689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31170317368947724039168459 46755476053421586058752689)
        ·
          refine ⟨35066607040066189544064517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46755476053421586058752689 35066607040066189544064517)
          ·
            refine ⟨6574988820012410539512097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35066607040066189544064517 6574988820012410539512097)
            ·
              refine ⟨4931241615009307904634073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6574988820012410539512097 4931241615009307904634073)
              ·
                refine ⟨3698431211256980928475555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931241615009307904634073 3698431211256980928475555)
                ·
                  refine ⟨5547646816885471392713333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698431211256980928475555 5547646816885471392713333)
                  ·
                    refine ⟨520091889083012943066875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5547646816885471392713333 520091889083012943066875)
                    ·
                      rfl

theorem cell22_1519313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_1519313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519313 prefixEnd_1519313 := by exact prefixLift 1519313
  have htrace : WordTrace (prefixWord ++ tailWord_1519313) baseStart_1519313 baseEnd_1519313 := by
    simpa [prefixWord, tailWord_1519313, baseEnd_1519313] using wordTrace_append hprefix tailTrace_1519313
  have hstable : (prefixWord ++ tailWord_1519313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519313).length < 2 ^ (prefixWord ++ tailWord_1519313).sum := by decide
  have hdescent : baseEnd_1519313 < baseStart_1519313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519328 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_1519328 : Nat := 118140960795 + 1519328 * 2 ^ 59
def prefixEnd_1519328 : Nat := 4983230072969 + 3 ^ 40 * 1519328 * 2
def baseEnd_1519328 : Nat := 520097023889557903941829

theorem tailTrace_1519328 : CollatzResearch.WordTrace tailWord_1519328 prefixEnd_1519328 520097023889557903941829 := by
  unfold tailWord_1519328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27707222319870805704603319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36942963093161074272804425 27707222319870805704603319)
  ·
    refine ⟨41560833479806208556904979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27707222319870805704603319 41560833479806208556904979)
    ·
      refine ⟨62341250219709312835357469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41560833479806208556904979 62341250219709312835357469)
      ·
        refine ⟨23377968832390992313259051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62341250219709312835357469 23377968832390992313259051)
        ·
          refine ⟨35066953248586488469888577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23377968832390992313259051 35066953248586488469888577)
          ·
            refine ⟨26300214936439866352416433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35066953248586488469888577 26300214936439866352416433)
            ·
              refine ⟨19725161202329899764312325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26300214936439866352416433 19725161202329899764312325)
              ·
                refine ⟨3698467725436856205808561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19725161202329899764312325 3698467725436856205808561)
                ·
                  refine ⟨2773850794077642154356421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698467725436856205808561 2773850794077642154356421)
                  ·
                    refine ⟨520097023889557903941829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773850794077642154356421 520097023889557903941829)
                    ·
                      rfl

theorem cell22_1519328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_1519328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519328 prefixEnd_1519328 := by exact prefixLift 1519328
  have htrace : WordTrace (prefixWord ++ tailWord_1519328) baseStart_1519328 baseEnd_1519328 := by
    simpa [prefixWord, tailWord_1519328, baseEnd_1519328] using wordTrace_append hprefix tailTrace_1519328
  have hstable : (prefixWord ++ tailWord_1519328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519328).length < 2 ^ (prefixWord ++ tailWord_1519328).sum := by decide
  have hdescent : baseEnd_1519328 < baseStart_1519328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519388 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_1519388 : Nat := 118140960795 + 1519388 * 2 ^ 59
def prefixEnd_1519388 : Nat := 4983230072969 + 3 ^ 40 * 1519388 * 2
def baseEnd_1519388 : Nat := 173372521038579249147215

theorem tailTrace_1519388 : CollatzResearch.WordTrace tailWord_1519388 prefixEnd_1519388 173372521038579249147215 := by
  unfold tailWord_1519388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27708316509762120828195409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36944422013016161104260545 27708316509762120828195409)
  ·
    refine ⟨20781237382321590621146557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27708316509762120828195409 20781237382321590621146557)
    ·
      refine ⟨7792964018370596482929959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20781237382321590621146557 7792964018370596482929959)
      ·
        refine ⟨11689446027555894724394939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792964018370596482929959 11689446027555894724394939)
        ·
          refine ⟨17534169041333842086592409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11689446027555894724394939 17534169041333842086592409)
          ·
            refine ⟨13150626781000381564944307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17534169041333842086592409 13150626781000381564944307)
            ·
              refine ⟨19725940171500572347416461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13150626781000381564944307 19725940171500572347416461)
              ·
                refine ⟨7397227564312714630281173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19725940171500572347416461 7397227564312714630281173)
                ·
                  refine ⟨173372521038579249147215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7397227564312714630281173 173372521038579249147215)
                  ·
                    rfl

theorem cell22_1519388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_1519388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519388 prefixEnd_1519388 := by exact prefixLift 1519388
  have htrace : WordTrace (prefixWord ++ tailWord_1519388) baseStart_1519388 baseEnd_1519388 := by
    simpa [prefixWord, tailWord_1519388, baseEnd_1519388] using wordTrace_append hprefix tailTrace_1519388
  have hstable : (prefixWord ++ tailWord_1519388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519388).length < 2 ^ (prefixWord ++ tailWord_1519388).sum := by decide
  have hdescent : baseEnd_1519388 < baseStart_1519388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519486 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1519486 : Nat := 118140960795 + 1519486 * 2 ^ 59
def prefixEnd_1519486 : Nat := 4983230072969 + 3 ^ 40 * 1519486 * 2
def baseEnd_1519486 : Nat := 520151110518498158491345

theorem tailTrace_1519486 : CollatzResearch.WordTrace tailWord_1519486 prefixEnd_1519486 520151110518498158491345 := by
  unfold tailWord_1519486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6927525921646150549182289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36946804915446136262305541 6927525921646150549182289)
  ·
    refine ⟨5195644441234612911886717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6927525921646150549182289 5195644441234612911886717)
    ·
      refine ⟨1948366665462979841957519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5195644441234612911886717 1948366665462979841957519)
      ·
        refine ⟨2922549998194469762936279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948366665462979841957519 2922549998194469762936279)
        ·
          refine ⟨4383824997291704644404419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922549998194469762936279 4383824997291704644404419)
          ·
            refine ⟨6575737495937556966606629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383824997291704644404419 6575737495937556966606629)
            ·
              refine ⟨1232950780488291931238743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6575737495937556966606629 1232950780488291931238743)
              ·
                refine ⟨1849426170732437896858115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232950780488291931238743 1849426170732437896858115)
                ·
                  refine ⟨2774139256098656845287173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849426170732437896858115 2774139256098656845287173)
                  ·
                    refine ⟨520151110518498158491345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774139256098656845287173 520151110518498158491345)
                    ·
                      rfl

theorem cell22_1519486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1519486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519486 prefixEnd_1519486 := by exact prefixLift 1519486
  have htrace : WordTrace (prefixWord ++ tailWord_1519486) baseStart_1519486 baseEnd_1519486 := by
    simpa [prefixWord, tailWord_1519486, baseEnd_1519486] using wordTrace_append hprefix tailTrace_1519486
  have hstable : (prefixWord ++ tailWord_1519486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519486).length < 2 ^ (prefixWord ++ tailWord_1519486).sum := by decide
  have hdescent : baseEnd_1519486 < baseStart_1519486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519495 : List Nat := [1, 1, 4, 2, 4, 1, 9]
def baseStart_1519495 : Nat := 118140960795 + 1519495 * 2 ^ 59
def prefixEnd_1519495 : Nat := 4983230072969 + 3 ^ 40 * 1519495 * 2
def baseEnd_1519495 : Nat := 19264970051941671667271

theorem tailTrace_1519495 : CollatzResearch.WordTrace tailWord_1519495 prefixEnd_1519495 19264970051941671667271 := by
  unfold tailWord_1519495
  simp only [CollatzResearch.WordTrace]
  refine ⟨55420535630136598930535939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36947023753424399287023959 55420535630136598930535939)
  ·
    refine ⟨83130803445204898395803909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55420535630136598930535939 83130803445204898395803909)
    ·
      refine ⟨15587025645975918449213233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83130803445204898395803909 15587025645975918449213233)
      ·
        refine ⟨11690269234481938836909925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15587025645975918449213233 11690269234481938836909925)
        ·
          refine ⟨2191925481465363531920611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11690269234481938836909925 2191925481465363531920611)
          ·
            refine ⟨3287888222198045297880917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191925481465363531920611 3287888222198045297880917)
            ·
              refine ⟨19264970051941671667271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3287888222198045297880917 19264970051941671667271)
              ·
                rfl

theorem cell22_1519495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 9].length) (baseStart_1519495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519495 prefixEnd_1519495 := by exact prefixLift 1519495
  have htrace : WordTrace (prefixWord ++ tailWord_1519495) baseStart_1519495 baseEnd_1519495 := by
    simpa [prefixWord, tailWord_1519495, baseEnd_1519495] using wordTrace_append hprefix tailTrace_1519495
  have hstable : (prefixWord ++ tailWord_1519495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519495).length < 2 ^ (prefixWord ++ tailWord_1519495).sum := by decide
  have hdescent : baseEnd_1519495 < baseStart_1519495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519516 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_1519516 : Nat := 118140960795 + 1519516 * 2 ^ 59
def prefixEnd_1519516 : Nat := 4983230072969 + 3 ^ 40 * 1519516 * 2
def baseEnd_1519516 : Nat := 520161380131588080241253

theorem tailTrace_1519516 : CollatzResearch.WordTrace tailWord_1519516 prefixEnd_1519516 520161380131588080241253 := by
  unfold tailWord_1519516
  simp only [CollatzResearch.WordTrace]
  refine ⟨27710650781530259758525201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36947534375373679678033601 27710650781530259758525201)
  ·
    refine ⟨20782988086147694818893901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27710650781530259758525201 20782988086147694818893901)
    ·
      refine ⟨7793620532305385557085213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20782988086147694818893901 7793620532305385557085213)
      ·
        refine ⟨2922607699614519583906955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7793620532305385557085213 2922607699614519583906955)
        ·
          refine ⟨4383911549421779375860433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922607699614519583906955 4383911549421779375860433)
          ·
            refine ⟨3287933662066334531895325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4383911549421779375860433 3287933662066334531895325)
            ·
              refine ⟨1232975123274875449460747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3287933662066334531895325 1232975123274875449460747)
              ·
                refine ⟨1849462684912313174191121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232975123274875449460747 1849462684912313174191121)
                ·
                  refine ⟨1387097013684234880643341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1849462684912313174191121 1387097013684234880643341)
                  ·
                    refine ⟨520161380131588080241253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1387097013684234880643341 520161380131588080241253)
                    ·
                      rfl

theorem cell22_1519516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_1519516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519516 prefixEnd_1519516 := by exact prefixLift 1519516
  have htrace : WordTrace (prefixWord ++ tailWord_1519516) baseStart_1519516 baseEnd_1519516 := by
    simpa [prefixWord, tailWord_1519516, baseEnd_1519516] using wordTrace_append hprefix tailTrace_1519516
  have hstable : (prefixWord ++ tailWord_1519516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519516).length < 2 ^ (prefixWord ++ tailWord_1519516).sum := by decide
  have hdescent : baseEnd_1519516 < baseStart_1519516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519585 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 6]
def baseStart_1519585 : Nat := 118140960795 + 1519585 * 2 ^ 59
def prefixEnd_1519585 : Nat := 4983230072969 + 3 ^ 40 * 1519585 * 2
def baseEnd_1519585 : Nat := 173395000080564966755347

theorem tailTrace_1519585 : CollatzResearch.WordTrace tailWord_1519585 prefixEnd_1519585 173395000080564966755347 := by
  unfold tailWord_1519585
  simp only [CollatzResearch.WordTrace]
  refine ⟨55423818199810544301312209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36949212133207029534208139 55423818199810544301312209)
  ·
    refine ⟨41567863649857908225984157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55423818199810544301312209 41567863649857908225984157)
    ·
      refine ⟨15587948868696715584744059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41567863649857908225984157 15587948868696715584744059)
      ·
        refine ⟨23381923303045073377116089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15587948868696715584744059 23381923303045073377116089)
        ·
          refine ⟨17536442477283805032837067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23381923303045073377116089 17536442477283805032837067)
          ·
            refine ⟨26304663715925707549255601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17536442477283805032837067 26304663715925707549255601)
            ·
              refine ⟨19728497786944280661941701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26304663715925707549255601 19728497786944280661941701)
              ·
                refine ⟨3699093335052052624114069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19728497786944280661941701 3699093335052052624114069)
                ·
                  refine ⟨173395000080564966755347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3699093335052052624114069 173395000080564966755347)
                  ·
                    rfl

theorem cell22_1519585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_1519585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519585 prefixEnd_1519585 := by exact prefixLift 1519585
  have htrace : WordTrace (prefixWord ++ tailWord_1519585) baseStart_1519585 baseEnd_1519585 := by
    simpa [prefixWord, tailWord_1519585, baseEnd_1519585] using wordTrace_append hprefix tailTrace_1519585
  have hstable : (prefixWord ++ tailWord_1519585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519585).length < 2 ^ (prefixWord ++ tailWord_1519585).sum := by decide
  have hdescent : baseEnd_1519585 < baseStart_1519585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519587 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 3, 4]
def baseStart_1519587 : Nat := 118140960795 + 1519587 * 2 ^ 59
def prefixEnd_1519587 : Nat := 4983230072969 + 3 ^ 40 * 1519587 * 2
def baseEnd_1519587 : Nat := 520185684882567561716035

theorem tailTrace_1519587 : CollatzResearch.WordTrace tailWord_1519587 prefixEnd_1519587 520185684882567561716035 := by
  unfold tailWord_1519587
  simp only [CollatzResearch.WordTrace]
  refine ⟨55423891145803298642885015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36949260763868865761923343 55423891145803298642885015)
  ·
    refine ⟨83135836718704947964327523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55423891145803298642885015 83135836718704947964327523)
    ·
      refine ⟨124703755078057421946491285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83135836718704947964327523 124703755078057421946491285)
      ·
        refine ⟨5845488519283941653741779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124703755078057421946491285 5845488519283941653741779)
        ·
          refine ⟨8768232778925912480612669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845488519283941653741779 8768232778925912480612669)
          ·
            refine ⟨3288087292097217180229751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8768232778925912480612669 3288087292097217180229751)
            ·
              refine ⟨4932130938145825770344627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288087292097217180229751 4932130938145825770344627)
              ·
                refine ⟨7398196407218738655516941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932130938145825770344627 7398196407218738655516941)
                ·
                  refine ⟨2774323652707026995818853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7398196407218738655516941 2774323652707026995818853)
                  ·
                    refine ⟨520185684882567561716035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774323652707026995818853 520185684882567561716035)
                    ·
                      rfl

theorem cell22_1519587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_1519587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519587 prefixEnd_1519587 := by exact prefixLift 1519587
  have htrace : WordTrace (prefixWord ++ tailWord_1519587) baseStart_1519587 baseEnd_1519587 := by
    simpa [prefixWord, tailWord_1519587, baseEnd_1519587] using wordTrace_append hprefix tailTrace_1519587
  have hstable : (prefixWord ++ tailWord_1519587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519587).length < 2 ^ (prefixWord ++ tailWord_1519587).sum := by decide
  have hdescent : baseEnd_1519587 < baseStart_1519587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519600 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_1519600 : Nat := 118140960795 + 1519600 * 2 ^ 59
def prefixEnd_1519600 : Nat := 4983230072969 + 3 ^ 40 * 1519600 * 2
def baseEnd_1519600 : Nat := 520190135048239861140995

theorem tailTrace_1519600 : CollatzResearch.WordTrace tailWord_1519600 prefixEnd_1519600 520190135048239861140995 := by
  unfold tailWord_1519600
  simp only [CollatzResearch.WordTrace]
  refine ⟨27712182647378100931554127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36949576863170801242072169 27712182647378100931554127)
  ·
    refine ⟨41568273971067151397331191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27712182647378100931554127 41568273971067151397331191)
    ·
      refine ⟨62352410956600727095996787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41568273971067151397331191 62352410956600727095996787)
      ·
        refine ⟨93528616434901090643995181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62352410956600727095996787 93528616434901090643995181)
        ·
          refine ⟨35073231163087908991498193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93528616434901090643995181 35073231163087908991498193)
          ·
            refine ⟨26304923372315931743623645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35073231163087908991498193 26304923372315931743623645)
            ·
              refine ⟨9864346264618474403858867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26304923372315931743623645 9864346264618474403858867)
              ·
                refine ⟨14796519396927711605788301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9864346264618474403858867 14796519396927711605788301)
                ·
                  refine ⟨5548694773847891852170613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14796519396927711605788301 5548694773847891852170613)
                  ·
                    refine ⟨520190135048239861140995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5548694773847891852170613 520190135048239861140995)
                    ·
                      rfl

theorem cell22_1519600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_1519600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519600 prefixEnd_1519600 := by exact prefixLift 1519600
  have htrace : WordTrace (prefixWord ++ tailWord_1519600) baseStart_1519600 baseEnd_1519600 := by
    simpa [prefixWord, tailWord_1519600, baseEnd_1519600] using wordTrace_append hprefix tailTrace_1519600
  have hstable : (prefixWord ++ tailWord_1519600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519600).length < 2 ^ (prefixWord ++ tailWord_1519600).sum := by decide
  have hdescent : baseEnd_1519600 < baseStart_1519600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519636 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1519636 : Nat := 118140960795 + 1519636 * 2 ^ 59
def prefixEnd_1519636 : Nat := 4983230072969 + 3 ^ 40 * 1519636 * 2
def baseEnd_1519636 : Nat := 173400819527982589080295

theorem tailTrace_1519636 : CollatzResearch.WordTrace tailWord_1519636 prefixEnd_1519636 173400819527982589080295 := by
  unfold tailWord_1519636
  simp only [CollatzResearch.WordTrace]
  refine ⟨27712839161312890005709381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36950452215083853340945841 27712839161312890005709381)
  ·
    refine ⟨5196157342746166876070509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27712839161312890005709381 5196157342746166876070509)
    ·
      refine ⟨1948559003529812578526441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5196157342746166876070509 1948559003529812578526441)
      ·
        refine ⟨1461419252647359433894831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1948559003529812578526441 1461419252647359433894831)
        ·
          refine ⟨2192128878971039150842247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461419252647359433894831 2192128878971039150842247)
          ·
            refine ⟨3288193318456558726263371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192128878971039150842247 3288193318456558726263371)
            ·
              refine ⟨4932289977684838089395057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288193318456558726263371 4932289977684838089395057)
              ·
                refine ⟨3699217483263628567046293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932289977684838089395057 3699217483263628567046293)
                ·
                  refine ⟨173400819527982589080295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3699217483263628567046293 173400819527982589080295)
                  ·
                    rfl

theorem cell22_1519636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1519636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519636 prefixEnd_1519636 := by exact prefixLift 1519636
  have htrace : WordTrace (prefixWord ++ tailWord_1519636) baseStart_1519636 baseEnd_1519636 := by
    simpa [prefixWord, tailWord_1519636, baseEnd_1519636] using wordTrace_append hprefix tailTrace_1519636
  have hstable : (prefixWord ++ tailWord_1519636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519636).length < 2 ^ (prefixWord ++ tailWord_1519636).sum := by decide
  have hdescent : baseEnd_1519636 < baseStart_1519636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519647 : List Nat := [1, 1, 2, 4, 1, 2, 5, 6]
def baseStart_1519647 : Nat := 118140960795 + 1519647 * 2 ^ 59
def prefixEnd_1519647 : Nat := 4983230072969 + 3 ^ 40 * 1519647 * 2
def baseEnd_1519647 : Nat := 57800691567638600579539

theorem tailTrace_1519647 : CollatzResearch.WordTrace tailWord_1519647 prefixEnd_1519647 57800691567638600579539 := by
  unfold tailWord_1519647
  simp only [CollatzResearch.WordTrace]
  refine ⟨55426079525585928890069195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36950719683723952593379463 55426079525585928890069195)
  ·
    refine ⟨83139119288378893335103793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55426079525585928890069195 83139119288378893335103793)
    ·
      refine ⟨62354339466284170001327845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83139119288378893335103793 62354339466284170001327845)
      ·
        refine ⟨11691438649928281875248971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62354339466284170001327845 11691438649928281875248971)
        ·
          refine ⟨17537157974892422812873457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11691438649928281875248971 17537157974892422812873457)
          ·
            refine ⟨13152868481169317109655093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17537157974892422812873457 13152868481169317109655093)
            ·
              refine ⟨1233081420109623479030165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13152868481169317109655093 1233081420109623479030165)
              ·
                refine ⟨57800691567638600579539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1233081420109623479030165 57800691567638600579539)
                ·
                  rfl

theorem cell22_1519647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 6].length) (baseStart_1519647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519647 prefixEnd_1519647 := by exact prefixLift 1519647
  have htrace : WordTrace (prefixWord ++ tailWord_1519647) baseStart_1519647 baseEnd_1519647 := by
    simpa [prefixWord, tailWord_1519647, baseEnd_1519647] using wordTrace_append hprefix tailTrace_1519647
  have hstable : (prefixWord ++ tailWord_1519647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519647).length < 2 ^ (prefixWord ++ tailWord_1519647).sum := by decide
  have hdescent : baseEnd_1519647 < baseStart_1519647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519655 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1519655 : Nat := 118140960795 + 1519655 * 2 ^ 59
def prefixEnd_1519655 : Nat := 4983230072969 + 3 ^ 40 * 1519655 * 2
def baseEnd_1519655 : Nat := 520208962672238051015827

theorem tailTrace_1519655 : CollatzResearch.WordTrace tailWord_1519655 prefixEnd_1519655 520208962672238051015827 := by
  unfold tailWord_1519655
  simp only [CollatzResearch.WordTrace]
  refine ⟨55426371309556946256360419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36950914206371297504240279 55426371309556946256360419)
  ·
    refine ⟨83139556964335419384540629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55426371309556946256360419 83139556964335419384540629)
    ·
      refine ⟨1948583366351611391825171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 83139556964335419384540629 1948583366351611391825171)
      ·
        refine ⟨2922875049527417087737757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948583366351611391825171 2922875049527417087737757)
        ·
          refine ⟨1096078143572781407901659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2922875049527417087737757 1096078143572781407901659)
          ·
            refine ⟨1644117215359172111852489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096078143572781407901659 1644117215359172111852489)
            ·
              refine ⟨1233087911519379083889367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644117215359172111852489 1233087911519379083889367)
              ·
                refine ⟨1849631867279068625834051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233087911519379083889367 1849631867279068625834051)
                ·
                  refine ⟨2774447800918602938751077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849631867279068625834051 2774447800918602938751077)
                  ·
                    refine ⟨520208962672238051015827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774447800918602938751077 520208962672238051015827)
                    ·
                      rfl

theorem cell22_1519655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1519655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519655 prefixEnd_1519655 := by exact prefixLift 1519655
  have htrace : WordTrace (prefixWord ++ tailWord_1519655) baseStart_1519655 baseEnd_1519655 := by
    simpa [prefixWord, tailWord_1519655, baseEnd_1519655] using wordTrace_append hprefix tailTrace_1519655
  have hstable : (prefixWord ++ tailWord_1519655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519655).length < 2 ^ (prefixWord ++ tailWord_1519655).sum := by decide
  have hdescent : baseEnd_1519655 < baseStart_1519655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519660 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1519660 : Nat := 118140960795 + 1519660 * 2 ^ 59
def prefixEnd_1519660 : Nat := 4983230072969 + 3 ^ 40 * 1519660 * 2
def baseEnd_1519660 : Nat := 520210674274419704640811

theorem tailTrace_1519660 : CollatzResearch.WordTrace tailWord_1519660 prefixEnd_1519660 520210674274419704640811 := by
  unfold tailWord_1519660
  simp only [CollatzResearch.WordTrace]
  refine ⟨27713276837269416055146217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36951035783025888073528289 27713276837269416055146217)
  ·
    refine ⟨20784957627952062041359663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27713276837269416055146217 20784957627952062041359663)
    ·
      refine ⟨31177436441928093062039495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20784957627952062041359663 31177436441928093062039495)
      ·
        refine ⟨46766154662892139593059243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31177436441928093062039495 46766154662892139593059243)
        ·
          refine ⟨70149231994338209389588865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46766154662892139593059243 70149231994338209389588865)
          ·
            refine ⟨52611923995753657042191649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70149231994338209389588865 52611923995753657042191649)
            ·
              refine ⟨39458942996815242781643737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52611923995753657042191649 39458942996815242781643737)
              ·
                refine ⟨29594207247611432086232803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39458942996815242781643737 29594207247611432086232803)
                ·
                  refine ⟨44391310871417148129349205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29594207247611432086232803 44391310871417148129349205)
                  ·
                    refine ⟨520210674274419704640811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44391310871417148129349205 520210674274419704640811)
                    ·
                      rfl

theorem cell22_1519660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1519660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519660 prefixEnd_1519660 := by exact prefixLift 1519660
  have htrace : WordTrace (prefixWord ++ tailWord_1519660) baseStart_1519660 baseEnd_1519660 := by
    simpa [prefixWord, tailWord_1519660, baseEnd_1519660] using wordTrace_append hprefix tailTrace_1519660
  have hstable : (prefixWord ++ tailWord_1519660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519660).length < 2 ^ (prefixWord ++ tailWord_1519660).sum := by decide
  have hdescent : baseEnd_1519660 < baseStart_1519660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519675 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 7]
def baseStart_1519675 : Nat := 118140960795 + 1519675 * 2 ^ 59
def prefixEnd_1519675 : Nat := 4983230072969 + 3 ^ 40 * 1519675 * 2
def baseEnd_1519675 : Nat := 173405269693654888505255

theorem tailTrace_1519675 : CollatzResearch.WordTrace tailWord_1519675 prefixEnd_1519675 173405269693654888505255 := by
  unfold tailWord_1519675
  simp only [CollatzResearch.WordTrace]
  refine ⟨55427100769484489672088479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36951400512989659781392319 55427100769484489672088479)
  ·
    refine ⟨83140651154226734508132719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55427100769484489672088479 83140651154226734508132719)
    ·
      refine ⟨124710976731340101762199079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83140651154226734508132719 124710976731340101762199079)
      ·
        refine ⟨187066465097010152643298619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124710976731340101762199079 187066465097010152643298619)
        ·
          refine ⟨280599697645515228964947929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187066465097010152643298619 280599697645515228964947929)
          ·
            refine ⟨210449773234136421723710947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280599697645515228964947929 210449773234136421723710947)
            ·
              refine ⟨315674659851204632585566421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210449773234136421723710947 315674659851204632585566421)
              ·
                refine ⟨7398624840262608576224213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 315674659851204632585566421 7398624840262608576224213)
                ·
                  refine ⟨173405269693654888505255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7398624840262608576224213 173405269693654888505255)
                  ·
                    rfl

theorem cell22_1519675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_1519675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519675 prefixEnd_1519675 := by exact prefixLift 1519675
  have htrace : WordTrace (prefixWord ++ tailWord_1519675) baseStart_1519675 baseEnd_1519675 := by
    simpa [prefixWord, tailWord_1519675, baseEnd_1519675] using wordTrace_append hprefix tailTrace_1519675
  have hstable : (prefixWord ++ tailWord_1519675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519675).length < 2 ^ (prefixWord ++ tailWord_1519675).sum := by decide
  have hdescent : baseEnd_1519675 < baseStart_1519675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519692 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_1519692 : Nat := 118140960795 + 1519692 * 2 ^ 59
def prefixEnd_1519692 : Nat := 4983230072969 + 3 ^ 40 * 1519692 * 2
def baseEnd_1519692 : Nat := 173407209509460762613571

theorem tailTrace_1519692 : CollatzResearch.WordTrace tailWord_1519692 prefixEnd_1519692 173407209509460762613571 := by
  unfold tailWord_1519692
  simp only [CollatzResearch.WordTrace]
  refine ⟨27713860405211450787728665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36951813873615267716971553 27713860405211450787728665)
  ·
    refine ⟨20785395303908588090796499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27713860405211450787728665 20785395303908588090796499)
    ·
      refine ⟨31178092955862882136194749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20785395303908588090796499 31178092955862882136194749)
      ·
        refine ⟨11691784858448580801073031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31178092955862882136194749 11691784858448580801073031)
        ·
          refine ⟨17537677287672871201609547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11691784858448580801073031 17537677287672871201609547)
          ·
            refine ⟨26306515931509306802414321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17537677287672871201609547 26306515931509306802414321)
            ·
              refine ⟨19729886948631980101810741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26306515931509306802414321 19729886948631980101810741)
              ·
                refine ⟨1849676901434248134544757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19729886948631980101810741 1849676901434248134544757)
                ·
                  refine ⟨173407209509460762613571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1849676901434248134544757 173407209509460762613571)
                  ·
                    rfl

theorem cell22_1519692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_1519692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519692 prefixEnd_1519692 := by exact prefixLift 1519692
  have htrace : WordTrace (prefixWord ++ tailWord_1519692) baseStart_1519692 baseEnd_1519692 := by
    simpa [prefixWord, tailWord_1519692, baseEnd_1519692] using wordTrace_append hprefix tailTrace_1519692
  have hstable : (prefixWord ++ tailWord_1519692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519692).length < 2 ^ (prefixWord ++ tailWord_1519692).sum := by decide
  have hdescent : baseEnd_1519692 < baseStart_1519692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519709 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 7]
def baseStart_1519709 : Nat := 118140960795 + 1519709 * 2 ^ 59
def prefixEnd_1519709 : Nat := 4983230072969 + 3 ^ 40 * 1519709 * 2
def baseEnd_1519709 : Nat := 173409149325266636721887

theorem tailTrace_1519709 : CollatzResearch.WordTrace tailWord_1519709 prefixEnd_1519709 173409149325266636721887 := by
  unfold tailWord_1519709
  simp only [CollatzResearch.WordTrace]
  refine ⟨55428340851361313478826181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36952227234240875652550787 55428340851361313478826181)
  ·
    refine ⟨10392813909630246277279909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55428340851361313478826181 10392813909630246277279909)
    ·
      refine ⟨1948652608055671176989983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10392813909630246277279909 1948652608055671176989983)
      ·
        refine ⟨2922978912083506765484975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948652608055671176989983 2922978912083506765484975)
        ·
          refine ⟨4384468368125260148227463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922978912083506765484975 4384468368125260148227463)
          ·
            refine ⟨6576702552187890222341195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384468368125260148227463 6576702552187890222341195)
            ·
              refine ⟨9865053828281835333511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576702552187890222341195 9865053828281835333511793)
              ·
                refine ⟨7398790371211376500133845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9865053828281835333511793 7398790371211376500133845)
                ·
                  refine ⟨173409149325266636721887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7398790371211376500133845 173409149325266636721887)
                  ·
                    rfl

theorem cell22_1519709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_1519709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519709 prefixEnd_1519709 := by exact prefixLift 1519709
  have htrace : WordTrace (prefixWord ++ tailWord_1519709) baseStart_1519709 baseEnd_1519709 := by
    simpa [prefixWord, tailWord_1519709, baseEnd_1519709] using wordTrace_append hprefix tailTrace_1519709
  have hstable : (prefixWord ++ tailWord_1519709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519709).length < 2 ^ (prefixWord ++ tailWord_1519709).sum := by decide
  have hdescent : baseEnd_1519709 < baseStart_1519709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519799 : List Nat := [1, 1, 3, 1, 4, 4, 1, 7]
def baseStart_1519799 : Nat := 118140960795 + 1519799 * 2 ^ 59
def prefixEnd_1519799 : Nat := 4983230072969 + 3 ^ 40 * 1519799 * 2
def baseEnd_1519799 : Nat := 57806472979452186157265

theorem tailTrace_1519799 : CollatzResearch.WordTrace tailWord_1519799 prefixEnd_1519799 57806472979452186157265 := by
  unfold tailWord_1519799
  simp only [CollatzResearch.WordTrace]
  refine ⟨55431623421035258849602451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36954415614023505899734967 55431623421035258849602451)
  ·
    refine ⟨83147435131552888274403677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55431623421035258849602451 83147435131552888274403677)
    ·
      refine ⟨31180288174332333102901379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83147435131552888274403677 31180288174332333102901379)
      ·
        refine ⟨46770432261498499654352069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31180288174332333102901379 46770432261498499654352069)
        ·
          refine ⟨8769456049030968685191013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46770432261498499654352069 8769456049030968685191013)
          ·
            refine ⟨1644273009193306628473315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8769456049030968685191013 1644273009193306628473315)
            ·
              refine ⟨2466409513789959942709973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644273009193306628473315 2466409513789959942709973)
              ·
                refine ⟨57806472979452186157265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2466409513789959942709973 57806472979452186157265)
                ·
                  rfl

theorem cell22_1519799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 7].length) (baseStart_1519799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519799 prefixEnd_1519799 := by exact prefixLift 1519799
  have htrace : WordTrace (prefixWord ++ tailWord_1519799) baseStart_1519799 baseEnd_1519799 := by
    simpa [prefixWord, tailWord_1519799, baseEnd_1519799] using wordTrace_append hprefix tailTrace_1519799
  have hstable : (prefixWord ++ tailWord_1519799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519799).length < 2 ^ (prefixWord ++ tailWord_1519799).sum := by decide
  have hdescent : baseEnd_1519799 < baseStart_1519799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519848 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 1, 3]
def baseStart_1519848 : Nat := 118140960795 + 1519848 * 2 ^ 59
def prefixEnd_1519848 : Nat := 4983230072969 + 3 ^ 40 * 1519848 * 2
def baseEnd_1519848 : Nat := 520275030516449880940235

theorem tailTrace_1519848 : CollatzResearch.WordTrace tailWord_1519848 prefixEnd_1519848 520275030516449880940235 := by
  unfold tailWord_1519848
  simp only [CollatzResearch.WordTrace]
  refine ⟨27716705298928870109068099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36955607065238493478757465 27716705298928870109068099)
  ·
    refine ⟨41575057948393305163602149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27716705298928870109068099 41575057948393305163602149)
    ·
      refine ⟨7795323365323744718175403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41575057948393305163602149 7795323365323744718175403)
      ·
        refine ⟨11692985047985617077263105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795323365323744718175403 11692985047985617077263105)
        ·
          refine ⟨8769738785989212807947329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11692985047985617077263105 8769738785989212807947329)
          ·
            refine ⟨6577304089491909605960497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8769738785989212807947329 6577304089491909605960497)
            ·
              refine ⟨4932978067118932204470373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577304089491909605960497 4932978067118932204470373)
              ·
                refine ⟨924933387584799788338195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4932978067118932204470373 924933387584799788338195)
                ·
                  refine ⟨1387400081377199682507293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924933387584799788338195 1387400081377199682507293)
                  ·
                    refine ⟨520275030516449880940235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1387400081377199682507293 520275030516449880940235)
                    ·
                      rfl

theorem cell22_1519848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_1519848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519848 prefixEnd_1519848 := by exact prefixLift 1519848
  have htrace : WordTrace (prefixWord ++ tailWord_1519848) baseStart_1519848 baseEnd_1519848 := by
    simpa [prefixWord, tailWord_1519848, baseEnd_1519848] using wordTrace_append hprefix tailTrace_1519848
  have hstable : (prefixWord ++ tailWord_1519848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519848).length < 2 ^ (prefixWord ++ tailWord_1519848).sum := by decide
  have hdescent : baseEnd_1519848 < baseStart_1519848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519906 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1519906 : Nat := 118140960795 + 1519906 * 2 ^ 59
def prefixEnd_1519906 : Nat := 4983230072969 + 3 ^ 40 * 1519906 * 2
def baseEnd_1519906 : Nat := 173431628367252354330019

theorem tailTrace_1519906 : CollatzResearch.WordTrace tailWord_1519906 prefixEnd_1519906 173431628367252354330019 := by
  unfold tailWord_1519906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858881507911904030936893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36957017354431744082498381 13858881507911904030936893)
  ·
    refine ⟨5197080565466964011601335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13858881507911904030936893 5197080565466964011601335)
    ·
      refine ⟨7795620848200446017402003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5197080565466964011601335 7795620848200446017402003)
      ·
        refine ⟨11693431272300669026103005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795620848200446017402003 11693431272300669026103005)
        ·
          refine ⟨4385036727112750884788627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11693431272300669026103005 4385036727112750884788627)
          ·
            refine ⟨6577555090669126327182941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385036727112750884788627 6577555090669126327182941)
            ·
              refine ⟨2466583159000922372693603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6577555090669126327182941 2466583159000922372693603)
              ·
                refine ⟨3699874738501383559040405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466583159000922372693603 3699874738501383559040405)
                ·
                  refine ⟨173431628367252354330019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3699874738501383559040405 173431628367252354330019)
                  ·
                    rfl

theorem cell22_1519906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1519906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519906 prefixEnd_1519906 := by exact prefixLift 1519906
  have htrace : WordTrace (prefixWord ++ tailWord_1519906) baseStart_1519906 baseEnd_1519906 := by
    simpa [prefixWord, tailWord_1519906, baseEnd_1519906] using wordTrace_append hprefix tailTrace_1519906
  have hstable : (prefixWord ++ tailWord_1519906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519906).length < 2 ^ (prefixWord ++ tailWord_1519906).sum := by decide
  have hdescent : baseEnd_1519906 < baseStart_1519906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519957 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 4]
def baseStart_1519957 : Nat := 118140960795 + 1519957 * 2 ^ 59
def prefixEnd_1519957 : Nat := 4983230072969 + 3 ^ 40 * 1519957 * 2
def baseEnd_1519957 : Nat := 173437447814669976654967

theorem tailTrace_1519957 : CollatzResearch.WordTrace tailWord_1519957 prefixEnd_1519957 173437447814669976654967 := by
  unfold tailWord_1519957
  simp only [CollatzResearch.WordTrace]
  refine ⟨55437386154462851833854125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36958257436308567889236083 55437386154462851833854125)
  ·
    refine ⟨20789019807923569437695297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55437386154462851833854125 20789019807923569437695297)
    ·
      refine ⟨15591764855942677078271473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20789019807923569437695297 15591764855942677078271473)
      ·
        refine ⟨11693823641957007808703605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15591764855942677078271473 11693823641957007808703605)
        ·
          refine ⟨1096295966433469482065963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11693823641957007808703605 1096295966433469482065963)
          ·
            refine ⟨1644443949650204223098945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096295966433469482065963 1644443949650204223098945)
            ·
              refine ⟨1233332962237653167324209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644443949650204223098945 1233332962237653167324209)
              ·
                refine ⟨924999721678239875493157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233332962237653167324209 924999721678239875493157)
                ·
                  refine ⟨173437447814669976654967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924999721678239875493157 173437447814669976654967)
                  ·
                    rfl

theorem cell22_1519957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_1519957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519957 prefixEnd_1519957 := by exact prefixLift 1519957
  have htrace : WordTrace (prefixWord ++ tailWord_1519957) baseStart_1519957 baseEnd_1519957 := by
    simpa [prefixWord, tailWord_1519957, baseEnd_1519957] using wordTrace_append hprefix tailTrace_1519957
  have hstable : (prefixWord ++ tailWord_1519957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519957).length < 2 ^ (prefixWord ++ tailWord_1519957).sum := by decide
  have hdescent : baseEnd_1519957 < baseStart_1519957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519968 : List Nat := [2, 1, 1, 3, 6, 1, 1, 7]
def baseStart_1519968 : Nat := 118140960795 + 1519968 * 2 ^ 59
def prefixEnd_1519968 : Nat := 4983230072969 + 3 ^ 40 * 1519968 * 2
def baseEnd_1519968 : Nat := 57812900996534396437763

theorem tailTrace_1519968 : CollatzResearch.WordTrace tailWord_1519968 prefixEnd_1519968 57812900996534396437763 := by
  unfold tailWord_1519968
  simp only [CollatzResearch.WordTrace]
  refine ⟨27718893678711500356252279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36958524904948667141669705 27718893678711500356252279)
  ·
    refine ⟨41578340518067250534378419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27718893678711500356252279 41578340518067250534378419)
    ·
      refine ⟨62367510777100875801567629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41578340518067250534378419 62367510777100875801567629)
      ·
        refine ⟨23387816541412828425587861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62367510777100875801567629 23387816541412828425587861)
        ·
          refine ⟨1096303900378726332449431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23387816541412828425587861 1096303900378726332449431)
          ·
            refine ⟨1644455850568089498674147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096303900378726332449431 1644455850568089498674147)
            ·
              refine ⟨2466683775852134248011221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644455850568089498674147 2466683775852134248011221)
              ·
                refine ⟨57812900996534396437763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2466683775852134248011221 57812900996534396437763)
                ·
                  rfl

theorem cell22_1519968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_1519968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519968 prefixEnd_1519968 := by exact prefixLift 1519968
  have htrace : WordTrace (prefixWord ++ tailWord_1519968) baseStart_1519968 baseEnd_1519968 := by
    simpa [prefixWord, tailWord_1519968, baseEnd_1519968] using wordTrace_append hprefix tailTrace_1519968
  have hstable : (prefixWord ++ tailWord_1519968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519968).length < 2 ^ (prefixWord ++ tailWord_1519968).sum := by decide
  have hdescent : baseEnd_1519968 < baseStart_1519968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519994 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_1519994 : Nat := 118140960795 + 1519994 * 2 ^ 59
def prefixEnd_1519994 : Nat := 4983230072969 + 3 ^ 40 * 1519994 * 2
def baseEnd_1519994 : Nat := 520325009300154166789787

theorem tailTrace_1519994 : CollatzResearch.WordTrace tailWord_1519994 prefixEnd_1519994 520325009300154166789787 := by
  unfold tailWord_1519994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859683913832201788237759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36959157103552538101967357 13859683913832201788237759)
  ·
    refine ⟨20789525870748302682356639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13859683913832201788237759 20789525870748302682356639)
    ·
      refine ⟨31184288806122454023534959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20789525870748302682356639 31184288806122454023534959)
      ·
        refine ⟨46776433209183681035302439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31184288806122454023534959 46776433209183681035302439)
        ·
          refine ⟨70164649813775521552953659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46776433209183681035302439 70164649813775521552953659)
          ·
            refine ⟨105246974720663282329430489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70164649813775521552953659 105246974720663282329430489)
            ·
              refine ⟨78935231040497461747072867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105246974720663282329430489 78935231040497461747072867)
              ·
                refine ⟨118402846560746192620609301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78935231040497461747072867 118402846560746192620609301)
                ·
                  refine ⟨5550133432534977779091061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118402846560746192620609301 5550133432534977779091061)
                  ·
                    refine ⟨520325009300154166789787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5550133432534977779091061 520325009300154166789787)
                    ·
                      rfl

theorem cell22_1519994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_1519994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1519994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1519994 prefixEnd_1519994 := by exact prefixLift 1519994
  have htrace : WordTrace (prefixWord ++ tailWord_1519994) baseStart_1519994 baseEnd_1519994 := by
    simpa [prefixWord, tailWord_1519994, baseEnd_1519994] using wordTrace_append hprefix tailTrace_1519994
  have hstable : (prefixWord ++ tailWord_1519994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519994).length < 2 ^ (prefixWord ++ tailWord_1519994).sum := by decide
  have hdescent : baseEnd_1519994 < baseStart_1519994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520071 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1520071 : Nat := 118140960795 + 1520071 * 2 ^ 59
def prefixEnd_1520071 : Nat := 4983230072969 + 3 ^ 40 * 1520071 * 2
def baseEnd_1520071 : Nat := 520351367973751632614551

theorem tailTrace_1520071 : CollatzResearch.WordTrace tailWord_1520071 prefixEnd_1520071 520351367973751632614551 := by
  unfold tailWord_1520071
  simp only [CollatzResearch.WordTrace]
  refine ⟨55441544076049849303504067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36961029384033232869002711 55441544076049849303504067)
  ·
    refine ⟨83162316114074773955256101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55441544076049849303504067 83162316114074773955256101)
    ·
      refine ⟨15592934271389020116610519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83162316114074773955256101 15592934271389020116610519)
      ·
        refine ⟨23389401407083530174915779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15592934271389020116610519 23389401407083530174915779)
        ·
          refine ⟨35084102110625295262373669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23389401407083530174915779 35084102110625295262373669)
          ·
            refine ⟨6578269145742242861695063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35084102110625295262373669 6578269145742242861695063)
            ·
              refine ⟨9867403718613364292542595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6578269145742242861695063 9867403718613364292542595)
              ·
                refine ⟨14801105577920046438813893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9867403718613364292542595 14801105577920046438813893)
                ·
                  refine ⟨2775207295860008707277605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14801105577920046438813893 2775207295860008707277605)
                  ·
                    refine ⟨520351367973751632614551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775207295860008707277605 520351367973751632614551)
                    ·
                      rfl

theorem cell22_1520071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1520071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520071 prefixEnd_1520071 := by exact prefixLift 1520071
  have htrace : WordTrace (prefixWord ++ tailWord_1520071) baseStart_1520071 baseEnd_1520071 := by
    simpa [prefixWord, tailWord_1520071, baseEnd_1520071] using wordTrace_append hprefix tailTrace_1520071
  have hstable : (prefixWord ++ tailWord_1520071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520071).length < 2 ^ (prefixWord ++ tailWord_1520071).sum := by decide
  have hdescent : baseEnd_1520071 < baseStart_1520071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520182 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1520182 : Nat := 118140960795 + 1520182 * 2 ^ 59
def prefixEnd_1520182 : Nat := 4983230072969 + 3 ^ 40 * 1520182 * 2
def baseEnd_1520182 : Nat := 173463121847394781029737

theorem tailTrace_1520182 : CollatzResearch.WordTrace tailWord_1520182 prefixEnd_1520182 173463121847394781029737 := by
  unfold tailWord_1520182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465349536165482203799675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36963728385765143507196533 3465349536165482203799675)
  ·
    refine ⟨5198024304248223305699513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3465349536165482203799675 5198024304248223305699513)
    ·
      refine ⟨3898518228186167479274635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5198024304248223305699513 3898518228186167479274635)
      ·
        refine ⟨5847777342279251218911953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898518228186167479274635 5847777342279251218911953)
        ·
          refine ⟨4385833006709438414183965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5847777342279251218911953 4385833006709438414183965)
          ·
            refine ⟨1644687377516039405318987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4385833006709438414183965 1644687377516039405318987)
            ·
              refine ⟨2467031066274059107978481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644687377516039405318987 2467031066274059107978481)
              ·
                refine ⟨1850273299705544330983861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467031066274059107978481 1850273299705544330983861)
                ·
                  refine ⟨173463121847394781029737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1850273299705544330983861 173463121847394781029737)
                  ·
                    rfl

theorem cell22_1520182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1520182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520182 prefixEnd_1520182 := by exact prefixLift 1520182
  have htrace : WordTrace (prefixWord ++ tailWord_1520182) baseStart_1520182 baseEnd_1520182 := by
    simpa [prefixWord, tailWord_1520182, baseEnd_1520182] using wordTrace_append hprefix tailTrace_1520182
  have hstable : (prefixWord ++ tailWord_1520182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520182).length < 2 ^ (prefixWord ++ tailWord_1520182).sum := by decide
  have hdescent : baseEnd_1520182 < baseStart_1520182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520193 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 6]
def baseStart_1520193 : Nat := 118140960795 + 1520193 * 2 ^ 59
def prefixEnd_1520193 : Nat := 4983230072969 + 3 ^ 40 * 1520193 * 2
def baseEnd_1520193 : Nat := 173464377022327993688059

theorem tailTrace_1520193 : CollatzResearch.WordTrace tailWord_1520193 prefixEnd_1520193 173464377022327993688059 := by
  unfold tailWord_1520193
  simp only [CollatzResearch.WordTrace]
  refine ⟨55445993781607864139445233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36963995854405242759630155 55445993781607864139445233)
  ·
    refine ⟨41584495336205898104583925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55445993781607864139445233 41584495336205898104583925)
    ·
      refine ⟨3898546437769302947304743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41584495336205898104583925 3898546437769302947304743)
      ·
        refine ⟨5847819656653954420957115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898546437769302947304743 5847819656653954420957115)
        ·
          refine ⟨8771729484980931631435673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847819656653954420957115 8771729484980931631435673)
          ·
            refine ⟨6578797113735698723576755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8771729484980931631435673 6578797113735698723576755)
            ·
              refine ⟨9868195670603548085365133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6578797113735698723576755 9868195670603548085365133)
              ·
                refine ⟨3700573376476330532011925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9868195670603548085365133 3700573376476330532011925)
                ·
                  refine ⟨173464377022327993688059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3700573376476330532011925 173464377022327993688059)
                  ·
                    rfl

theorem cell22_1520193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_1520193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520193 prefixEnd_1520193 := by exact prefixLift 1520193
  have htrace : WordTrace (prefixWord ++ tailWord_1520193) baseStart_1520193 baseEnd_1520193 := by
    simpa [prefixWord, tailWord_1520193, baseEnd_1520193] using wordTrace_append hprefix tailTrace_1520193
  have hstable : (prefixWord ++ tailWord_1520193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520193).length < 2 ^ (prefixWord ++ tailWord_1520193).sum := by decide
  have hdescent : baseEnd_1520193 < baseStart_1520193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520238 : List Nat := [4, 1, 2, 2, 2, 1, 10]
def baseStart_1520238 : Nat := 118140960795 + 1520238 * 2 ^ 59
def prefixEnd_1520238 : Nat := 4983230072969 + 3 ^ 40 * 1520238 * 2
def baseEnd_1520238 : Nat := 19274390203208106062557

theorem tailTrace_1520238 : CollatzResearch.WordTrace tailWord_1520238 prefixEnd_1520238 19274390203208106062557 := by
  unfold tailWord_1520238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930954383305604603104171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36965090044296557883222245 6930954383305604603104171)
  ·
    refine ⟨10396431574958406904656257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6930954383305604603104171 10396431574958406904656257)
    ·
      refine ⟨7797323681218805178492193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10396431574958406904656257 7797323681218805178492193)
      ·
        refine ⟨5847992760914103883869145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7797323681218805178492193 5847992760914103883869145)
        ·
          refine ⟨4385994570685577912901859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5847992760914103883869145 4385994570685577912901859)
          ·
            refine ⟨6578991856028366869352789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385994570685577912901859 6578991856028366869352789)
            ·
              refine ⟨19274390203208106062557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6578991856028366869352789 19274390203208106062557)
              ·
                rfl

theorem cell22_1520238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 10].length) (baseStart_1520238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520238 prefixEnd_1520238 := by exact prefixLift 1520238
  have htrace : WordTrace (prefixWord ++ tailWord_1520238) baseStart_1520238 baseEnd_1520238 := by
    simpa [prefixWord, tailWord_1520238, baseEnd_1520238] using wordTrace_append hprefix tailTrace_1520238
  have hstable : (prefixWord ++ tailWord_1520238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520238).length < 2 ^ (prefixWord ++ tailWord_1520238).sum := by decide
  have hdescent : baseEnd_1520238 < baseStart_1520238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520240 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_1520240 : Nat := 118140960795 + 1520240 * 2 ^ 59
def prefixEnd_1520240 : Nat := 4983230072969 + 3 ^ 40 * 1520240 * 2
def baseEnd_1520240 : Nat := 520409220127491525139033

theorem tailTrace_1520240 : CollatzResearch.WordTrace tailWord_1520240 prefixEnd_1520240 520409220127491525139033 := by
  unfold tailWord_1520240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27723854006218795583203087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36965138674958394110937449 27723854006218795583203087)
  ·
    refine ⟨41585781009328193374804631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27723854006218795583203087 41585781009328193374804631)
    ·
      refine ⟨62378671513992290062206947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41585781009328193374804631 62378671513992290062206947)
      ·
        refine ⟨93568007270988435093310421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62378671513992290062206947 93568007270988435093310421)
        ·
          refine ⟨2193000170413791447499463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93568007270988435093310421 2193000170413791447499463)
          ·
            refine ⟨3289500255620687171249195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193000170413791447499463 3289500255620687171249195)
            ·
              refine ⟨4934250383431030756873793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289500255620687171249195 4934250383431030756873793)
              ·
                refine ⟨3700687787573273067655345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934250383431030756873793 3700687787573273067655345)
                ·
                  refine ⟨2775515840679954800741509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3700687787573273067655345 2775515840679954800741509)
                  ·
                    refine ⟨520409220127491525139033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775515840679954800741509 520409220127491525139033)
                    ·
                      rfl

theorem cell22_1520240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_1520240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520240 prefixEnd_1520240 := by exact prefixLift 1520240
  have htrace : WordTrace (prefixWord ++ tailWord_1520240) baseStart_1520240 baseEnd_1520240 := by
    simpa [prefixWord, tailWord_1520240, baseEnd_1520240] using wordTrace_append hprefix tailTrace_1520240
  have hstable : (prefixWord ++ tailWord_1520240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520240).length < 2 ^ (prefixWord ++ tailWord_1520240).sum := by decide
  have hdescent : baseEnd_1520240 < baseStart_1520240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520270 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_1520270 : Nat := 118140960795 + 1520270 * 2 ^ 59
def prefixEnd_1520270 : Nat := 4983230072969 + 3 ^ 40 * 1520270 * 2
def baseEnd_1520270 : Nat := 520419489740581446888941

theorem tailTrace_1520270 : CollatzResearch.WordTrace tailWord_1520270 prefixEnd_1520270 520419489740581446888941 := by
  unfold tailWord_1520270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931100275291113286249783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36965868134885937526665509 6931100275291113286249783)
  ·
    refine ⟨10396650412936669929374675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6931100275291113286249783 10396650412936669929374675)
    ·
      refine ⟨15594975619405004894062013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10396650412936669929374675 15594975619405004894062013)
      ·
        refine ⟨5848115857276876835273255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15594975619405004894062013 5848115857276876835273255)
        ·
          refine ⟨8772173785915315252909883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848115857276876835273255 8772173785915315252909883)
          ·
            refine ⟨13158260678872972879364825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8772173785915315252909883 13158260678872972879364825)
            ·
              refine ⟨9868695509154729659523619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13158260678872972879364825 9868695509154729659523619)
              ·
                refine ⟨14803043263732094489285429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868695509154729659523619 14803043263732094489285429)
                ·
                  refine ⟨1387785305974883858370509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14803043263732094489285429 1387785305974883858370509)
                  ·
                    refine ⟨520419489740581446888941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1387785305974883858370509 520419489740581446888941)
                    ·
                      rfl

theorem cell22_1520270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_1520270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520270 prefixEnd_1520270 := by exact prefixLift 1520270
  have htrace : WordTrace (prefixWord ++ tailWord_1520270) baseStart_1520270 baseEnd_1520270 := by
    simpa [prefixWord, tailWord_1520270, baseEnd_1520270] using wordTrace_append hprefix tailTrace_1520270
  have hstable : (prefixWord ++ tailWord_1520270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520270).length < 2 ^ (prefixWord ++ tailWord_1520270).sum := by decide
  have hdescent : baseEnd_1520270 < baseStart_1520270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520328 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_1520328 : Nat := 118140960795 + 1520328 * 2 ^ 59
def prefixEnd_1520328 : Nat := 4983230072969 + 3 ^ 40 * 1520328 * 2
def baseEnd_1520328 : Nat := 173479781441962876312921

theorem tailTrace_1520328 : CollatzResearch.WordTrace tailWord_1520328 prefixEnd_1520328 173479781441962876312921 := by
  unfold tailWord_1520328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27725458818059391097804819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36967278424079188130406425 27725458818059391097804819)
  ·
    refine ⟨41588188227089086646707229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27725458818059391097804819 41588188227089086646707229)
    ·
      refine ⟨15595570585158407492515211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41588188227089086646707229 15595570585158407492515211)
      ·
        refine ⟨23393355877737611238772817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15595570585158407492515211 23393355877737611238772817)
        ·
          refine ⟨17545016908303208429079613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23393355877737611238772817 17545016908303208429079613)
          ·
            refine ⟨6579381340613703160904855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17545016908303208429079613 6579381340613703160904855)
            ·
              refine ⟨9869072010920554741357283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579381340613703160904855 9869072010920554741357283)
              ·
                refine ⟨14803608016380832112035925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9869072010920554741357283 14803608016380832112035925)
                ·
                  refine ⟨173479781441962876312921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14803608016380832112035925 173479781441962876312921)
                  ·
                    rfl

theorem cell22_1520328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_1520328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520328 prefixEnd_1520328 := by exact prefixLift 1520328
  have htrace : WordTrace (prefixWord ++ tailWord_1520328) baseStart_1520328 baseEnd_1520328 := by
    simpa [prefixWord, tailWord_1520328, baseEnd_1520328] using wordTrace_append hprefix tailTrace_1520328
  have hstable : (prefixWord ++ tailWord_1520328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520328).length < 2 ^ (prefixWord ++ tailWord_1520328).sum := by decide
  have hdescent : baseEnd_1520328 < baseStart_1520328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520330 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1520330 : Nat := 118140960795 + 1520330 * 2 ^ 59
def prefixEnd_1520330 : Nat := 4983230072969 + 3 ^ 40 * 1520330 * 2
def baseEnd_1520330 : Nat := 520440028966761290388757

theorem tailTrace_1520330 : CollatzResearch.WordTrace tailWord_1520330 prefixEnd_1520330 520440028966761290388757 := by
  unfold tailWord_1520330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13862747645527884134295611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36967327054741024358121629 13862747645527884134295611)
  ·
    refine ⟨20794121468291826201443417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13862747645527884134295611 20794121468291826201443417)
    ·
      refine ⟨15595591101218869651082563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20794121468291826201443417 15595591101218869651082563)
      ·
        refine ⟨23393386651828304476623845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15595591101218869651082563 23393386651828304476623845)
        ·
          refine ⟨4386259997217807089366971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23393386651828304476623845 4386259997217807089366971)
          ·
            refine ⟨6579389995826710634050457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386259997217807089366971 6579389995826710634050457)
            ·
              refine ⟨4934542496870032975537843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6579389995826710634050457 4934542496870032975537843)
              ·
                refine ⟨7401813745305049463306765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934542496870032975537843 7401813745305049463306765)
                ·
                  refine ⟨2775680154489393548740037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7401813745305049463306765 2775680154489393548740037)
                  ·
                    refine ⟨520440028966761290388757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2775680154489393548740037 520440028966761290388757)
                    ·
                      rfl

theorem cell22_1520330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1520330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520330 prefixEnd_1520330 := by exact prefixLift 1520330
  have htrace : WordTrace (prefixWord ++ tailWord_1520330) baseStart_1520330 baseEnd_1520330 := by
    simpa [prefixWord, tailWord_1520330, baseEnd_1520330] using wordTrace_append hprefix tailTrace_1520330
  have hstable : (prefixWord ++ tailWord_1520330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520330).length < 2 ^ (prefixWord ++ tailWord_1520330).sum := by decide
  have hdescent : baseEnd_1520330 < baseStart_1520330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520407 : List Nat := [1, 1, 3, 4, 4, 1, 8]
def baseStart_1520407 : Nat := 118140960795 + 1520407 * 2 ^ 59
def prefixEnd_1520407 : Nat := 4983230072969 + 3 ^ 40 * 1520407 * 2
def baseEnd_1520407 : Nat := 19276532875568842822723

theorem tailTrace_1520407 : CollatzResearch.WordTrace tailWord_1520407 prefixEnd_1520407 19276532875568842822723 := by
  unfold tailWord_1520407
  simp only [CollatzResearch.WordTrace]
  refine ⟨55453799002832578687735475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36969199335221719125156983 55453799002832578687735475)
  ·
    refine ⟨83180698504248868031603213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55453799002832578687735475 83180698504248868031603213)
    ·
      refine ⟨31192761939093325511851205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83180698504248868031603213 31192761939093325511851205)
      ·
        refine ⟨5848642863579998533472101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31192761939093325511851205 5848642863579998533472101)
        ·
          refine ⟨1096620536921249725026019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5848642863579998533472101 1096620536921249725026019)
          ·
            refine ⟨1644930805381874587539029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096620536921249725026019 1644930805381874587539029)
            ·
              refine ⟨19276532875568842822723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1644930805381874587539029 19276532875568842822723)
              ·
                rfl

theorem cell22_1520407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 8].length) (baseStart_1520407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520407 prefixEnd_1520407 := by exact prefixLift 1520407
  have htrace : WordTrace (prefixWord ++ tailWord_1520407) baseStart_1520407 baseEnd_1520407 := by
    simpa [prefixWord, tailWord_1520407, baseEnd_1520407] using wordTrace_append hprefix tailTrace_1520407
  have hstable : (prefixWord ++ tailWord_1520407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520407).length < 2 ^ (prefixWord ++ tailWord_1520407).sum := by decide
  have hdescent : baseEnd_1520407 < baseStart_1520407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520480 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_1520480 : Nat := 118140960795 + 1520480 * 2 ^ 59
def prefixEnd_1520480 : Nat := 4983230072969 + 3 ^ 40 * 1520480 * 2
def baseEnd_1520480 : Nat := 173497125677403633046099

theorem tailTrace_1520480 : CollatzResearch.WordTrace tailWord_1520480 prefixEnd_1520480 173497125677403633046099 := by
  unfold tailWord_1520480
  simp only [CollatzResearch.WordTrace]
  refine ⟨27728230765784056077571447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36970974354378741436761929 27728230765784056077571447)
  ·
    refine ⟨41592346148676084116357171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27728230765784056077571447 41592346148676084116357171)
    ·
      refine ⟨62388519223014126174535757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41592346148676084116357171 62388519223014126174535757)
      ·
        refine ⟨23395694708630297315450909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62388519223014126174535757 23395694708630297315450909)
        ·
          refine ⟨8773385515736361493294091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23395694708630297315450909 8773385515736361493294091)
          ·
            refine ⟨13160078273604542239941137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8773385515736361493294091 13160078273604542239941137)
            ·
              refine ⟨9870058705203406679955853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13160078273604542239941137 9870058705203406679955853)
              ·
                refine ⟨3701272014451277504983445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9870058705203406679955853 3701272014451277504983445)
                ·
                  refine ⟨173497125677403633046099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3701272014451277504983445 173497125677403633046099)
                  ·
                    rfl

theorem cell22_1520480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_1520480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520480 prefixEnd_1520480 := by exact prefixLift 1520480
  have htrace : WordTrace (prefixWord ++ tailWord_1520480) baseStart_1520480 baseEnd_1520480 := by
    simpa [prefixWord, tailWord_1520480, baseEnd_1520480] using wordTrace_append hprefix tailTrace_1520480
  have hstable : (prefixWord ++ tailWord_1520480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520480).length < 2 ^ (prefixWord ++ tailWord_1520480).sum := by decide
  have hdescent : baseEnd_1520480 < baseStart_1520480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520570 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_1520570 : Nat := 118140960795 + 1520570 * 2 ^ 59
def prefixEnd_1520570 : Nat := 4983230072969 + 3 ^ 40 * 1520570 * 2
def baseEnd_1520570 : Nat := 173507395290493554796007

theorem tailTrace_1520570 : CollatzResearch.WordTrace tailWord_1520570 prefixEnd_1520570 173507395290493554796007 := by
  unfold tailWord_1520570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864936025310514381479791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36973162734161371683946109 13864936025310514381479791)
  ·
    refine ⟨20797404037965771572219687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13864936025310514381479791 20797404037965771572219687)
    ·
      refine ⟨31196106056948657358329531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20797404037965771572219687 31196106056948657358329531)
      ·
        refine ⟨46794159085422986037494297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31196106056948657358329531 46794159085422986037494297)
        ·
          refine ⟨35095619314067239528120723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46794159085422986037494297 35095619314067239528120723)
          ·
            refine ⟨52643428971100859292181085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35095619314067239528120723 52643428971100859292181085)
            ·
              refine ⟨19741285864162822234567907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52643428971100859292181085 19741285864162822234567907)
              ·
                refine ⟨29611928796244233351851861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19741285864162822234567907 29611928796244233351851861)
                ·
                  refine ⟨173507395290493554796007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29611928796244233351851861 173507395290493554796007)
                  ·
                    rfl

theorem cell22_1520570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_1520570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520570 prefixEnd_1520570 := by exact prefixLift 1520570
  have htrace : WordTrace (prefixWord ++ tailWord_1520570) baseStart_1520570 baseEnd_1520570 := by
    simpa [prefixWord, tailWord_1520570, baseEnd_1520570] using wordTrace_append hprefix tailTrace_1520570
  have hstable : (prefixWord ++ tailWord_1520570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520570).length < 2 ^ (prefixWord ++ tailWord_1520570).sum := by decide
  have hdescent : baseEnd_1520570 < baseStart_1520570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520582 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1520582 : Nat := 118140960795 + 1520582 * 2 ^ 59
def prefixEnd_1520582 : Nat := 4983230072969 + 3 ^ 40 * 1520582 * 2
def baseEnd_1520582 : Nat := 173508764572238877695995

theorem tailTrace_1520582 : CollatzResearch.WordTrace tailWord_1520582 prefixEnd_1520582 173508764572238877695995 := by
  unfold tailWord_1520582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733130680537455736729875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36973454518132389050237333 1733130680537455736729875)
  ·
    refine ⟨2599696020806183605094813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733130680537455736729875 2599696020806183605094813)
    ·
      refine ⟨974886007802318851910555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2599696020806183605094813 974886007802318851910555)
      ·
        refine ⟨1462329011703478277865833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974886007802318851910555 1462329011703478277865833)
        ·
          refine ⟨1096746758777608708399375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462329011703478277865833 1096746758777608708399375)
          ·
            refine ⟨1645120138166413062599063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096746758777608708399375 1645120138166413062599063)
            ·
              refine ⟨2467680207249619593898595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645120138166413062599063 2467680207249619593898595)
              ·
                refine ⟨3701520310874429390847893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467680207249619593898595 3701520310874429390847893)
                ·
                  refine ⟨173508764572238877695995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3701520310874429390847893 173508764572238877695995)
                  ·
                    rfl

theorem cell22_1520582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1520582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520582 prefixEnd_1520582 := by exact prefixLift 1520582
  have htrace : WordTrace (prefixWord ++ tailWord_1520582) baseStart_1520582 baseEnd_1520582 := by
    simpa [prefixWord, tailWord_1520582, baseEnd_1520582] using wordTrace_append hprefix tailTrace_1520582
  have hstable : (prefixWord ++ tailWord_1520582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520582).length < 2 ^ (prefixWord ++ tailWord_1520582).sum := by decide
  have hdescent : baseEnd_1520582 < baseStart_1520582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520647 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1520647 : Nat := 118140960795 + 1520647 * 2 ^ 59
def prefixEnd_1520647 : Nat := 4983230072969 + 3 ^ 40 * 1520647 * 2
def baseEnd_1520647 : Nat := 520548544545078130212785

theorem tailTrace_1520647 : CollatzResearch.WordTrace tailWord_1520647 prefixEnd_1520647 520548544545078130212785 := by
  unfold tailWord_1520647
  simp only [CollatzResearch.WordTrace]
  refine ⟨55462552521963099676472195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36975035014642066450981463 55462552521963099676472195)
  ·
    refine ⟨83193828782944649514708293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55462552521963099676472195 83193828782944649514708293)
    ·
      refine ⟨15598842896802121784007805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83193828782944649514708293 15598842896802121784007805)
      ·
        refine ⟨5849566086300795669002927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15598842896802121784007805 5849566086300795669002927)
        ·
          refine ⟨8774349129451193503504391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849566086300795669002927 8774349129451193503504391)
          ·
            refine ⟨13161523694176790255256587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8774349129451193503504391 13161523694176790255256587)
            ·
              refine ⟨19742285541265185382884881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13161523694176790255256587 19742285541265185382884881)
              ·
                refine ⟨14806714155948889037163661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19742285541265185382884881 14806714155948889037163661)
                ·
                  refine ⟨5552517808480833388936373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14806714155948889037163661 5552517808480833388936373)
                  ·
                    refine ⟨520548544545078130212785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5552517808480833388936373 520548544545078130212785)
                    ·
                      rfl

theorem cell22_1520647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1520647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520647 prefixEnd_1520647 := by exact prefixLift 1520647
  have htrace : WordTrace (prefixWord ++ tailWord_1520647) baseStart_1520647 baseEnd_1520647 := by
    simpa [prefixWord, tailWord_1520647, baseEnd_1520647] using wordTrace_append hprefix tailTrace_1520647
  have hstable : (prefixWord ++ tailWord_1520647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520647).length < 2 ^ (prefixWord ++ tailWord_1520647).sum := by decide
  have hdescent : baseEnd_1520647 < baseStart_1520647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520664 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_1520664 : Nat := 118140960795 + 1520664 * 2 ^ 59
def prefixEnd_1520664 : Nat := 4983230072969 + 3 ^ 40 * 1520664 * 2
def baseEnd_1520664 : Nat := 520554363992495752537733

theorem tailTrace_1520664 : CollatzResearch.WordTrace tailWord_1520664 prefixEnd_1520664 520554363992495752537733 := by
  unfold tailWord_1520664
  simp only [CollatzResearch.WordTrace]
  refine ⟨27731586281450755789920523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36975448375267674386560697 27731586281450755789920523)
  ·
    refine ⟨41597379422176133684880785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27731586281450755789920523 41597379422176133684880785)
    ·
      refine ⟨31198034566632100263660589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41597379422176133684880785 31198034566632100263660589)
      ·
        refine ⟨11699262962487037598872721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31198034566632100263660589 11699262962487037598872721)
        ·
          refine ⟨8774447221865278199154541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11699262962487037598872721 8774447221865278199154541)
          ·
            refine ⟨3290417708199479324682953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8774447221865278199154541 3290417708199479324682953)
            ·
              refine ⟨2467813281149609493512215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290417708199479324682953 2467813281149609493512215)
              ·
                refine ⟨3701719921724414240268323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467813281149609493512215 3701719921724414240268323)
                ·
                  refine ⟨5552579882586621360402485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701719921724414240268323 5552579882586621360402485)
                  ·
                    refine ⟨520554363992495752537733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5552579882586621360402485 520554363992495752537733)
                    ·
                      rfl

theorem cell22_1520664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_1520664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520664 prefixEnd_1520664 := by exact prefixLift 1520664
  have htrace : WordTrace (prefixWord ++ tailWord_1520664) baseStart_1520664 baseEnd_1520664 := by
    simpa [prefixWord, tailWord_1520664, baseEnd_1520664] using wordTrace_append hprefix tailTrace_1520664
  have hstable : (prefixWord ++ tailWord_1520664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520664).length < 2 ^ (prefixWord ++ tailWord_1520664).sum := by decide
  have hdescent : baseEnd_1520664 < baseStart_1520664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520694 : List Nat := [5, 1, 2, 1, 1, 3, 9]
def baseStart_1520694 : Nat := 118140960795 + 1520694 * 2 ^ 59
def prefixEnd_1520694 : Nat := 4983230072969 + 3 ^ 40 * 1520694 * 2
def baseEnd_1520694 : Nat := 19280171615021691640283

theorem tailTrace_1520694 : CollatzResearch.WordTrace tailWord_1520694 prefixEnd_1520694 19280171615021691640283 := by
  unfold tailWord_1520694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466516672049551668964571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36976177835195217802288757 3466516672049551668964571)
  ·
    refine ⟨5199775008074327503446857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3466516672049551668964571 5199775008074327503446857)
    ·
      refine ⟨3899831256055745627585143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5199775008074327503446857 3899831256055745627585143)
      ·
        refine ⟨5849746884083618441377715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899831256055745627585143 5849746884083618441377715)
        ·
          refine ⟨8774620326125427662066573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849746884083618441377715 8774620326125427662066573)
          ·
            refine ⟨3290482622297035373274965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8774620326125427662066573 3290482622297035373274965)
            ·
              refine ⟨19280171615021691640283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3290482622297035373274965 19280171615021691640283)
              ·
                rfl

theorem cell22_1520694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 9].length) (baseStart_1520694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520694 prefixEnd_1520694 := by exact prefixLift 1520694
  have htrace : WordTrace (prefixWord ++ tailWord_1520694) baseStart_1520694 baseEnd_1520694 := by
    simpa [prefixWord, tailWord_1520694, baseEnd_1520694] using wordTrace_append hprefix tailTrace_1520694
  have hstable : (prefixWord ++ tailWord_1520694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520694).length < 2 ^ (prefixWord ++ tailWord_1520694).sum := by decide
  have hdescent : baseEnd_1520694 < baseStart_1520694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520709 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_1520709 : Nat := 118140960795 + 1520709 * 2 ^ 59
def prefixEnd_1520709 : Nat := 4983230072969 + 3 ^ 40 * 1520709 * 2
def baseEnd_1520709 : Nat := 520569768412130635162595

theorem tailTrace_1520709 : CollatzResearch.WordTrace tailWord_1520709 prefixEnd_1520709 520569768412130635162595 := by
  unfold tailWord_1520709
  simp only [CollatzResearch.WordTrace]
  refine ⟨55464813847738484265229181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36976542565158989510152787 55464813847738484265229181)
  ·
    refine ⟨20799305192901931599460943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55464813847738484265229181 20799305192901931599460943)
    ·
      refine ⟨31198957789352897399191415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20799305192901931599460943 31198957789352897399191415)
      ·
        refine ⟨46798436684029346098787123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31198957789352897399191415 46798436684029346098787123)
        ·
          refine ⟨70197655026044019148180685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46798436684029346098787123 70197655026044019148180685)
          ·
            refine ⟨26324120634766507180567757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70197655026044019148180685 26324120634766507180567757)
            ·
              refine ⟨9871545238037440192712909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26324120634766507180567757 9871545238037440192712909)
              ·
                refine ⟨3701829464264040072267341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9871545238037440192712909 3701829464264040072267341)
                ·
                  refine ⟨1388186049099015027100253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3701829464264040072267341 1388186049099015027100253)
                  ·
                    refine ⟨520569768412130635162595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388186049099015027100253 520569768412130635162595)
                    ·
                      rfl

theorem cell22_1520709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_1520709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520709 prefixEnd_1520709 := by exact prefixLift 1520709
  have htrace : WordTrace (prefixWord ++ tailWord_1520709) baseStart_1520709 baseEnd_1520709 := by
    simpa [prefixWord, tailWord_1520709, baseEnd_1520709] using wordTrace_append hprefix tailTrace_1520709
  have hstable : (prefixWord ++ tailWord_1520709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520709).length < 2 ^ (prefixWord ++ tailWord_1520709).sum := by decide
  have hdescent : baseEnd_1520709 < baseStart_1520709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520737 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1520737 : Nat := 118140960795 + 1520737 * 2 ^ 59
def prefixEnd_1520737 : Nat := 4983230072969 + 3 ^ 40 * 1520737 * 2
def baseEnd_1520737 : Nat := 520579353384347895462509

theorem tailTrace_1520737 : CollatzResearch.WordTrace tailWord_1520737 prefixEnd_1520737 520579353384347895462509 := by
  unfold tailWord_1520737
  simp only [CollatzResearch.WordTrace]
  refine ⟨55465835091637045047248465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36977223394424696698165643 55465835091637045047248465)
  ·
    refine ⟨41599376318727783785436349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55465835091637045047248465 41599376318727783785436349)
    ·
      refine ⟨15599766119522918919538631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41599376318727783785436349 15599766119522918919538631)
      ·
        refine ⟨23399649179284378379307947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15599766119522918919538631 23399649179284378379307947)
        ·
          refine ⟨35099473768926567568961921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23399649179284378379307947 35099473768926567568961921)
          ·
            refine ⟨26324605326694925676721441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35099473768926567568961921 26324605326694925676721441)
            ·
              refine ⟨19743453995021194257541081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26324605326694925676721441 19743453995021194257541081)
              ·
                refine ⟨14807590496265895693155811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19743453995021194257541081 14807590496265895693155811)
                ·
                  refine ⟨22211385744398843539733717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14807590496265895693155811 22211385744398843539733717)
                  ·
                    refine ⟨520579353384347895462509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22211385744398843539733717 520579353384347895462509)
                    ·
                      rfl

theorem cell22_1520737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1520737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520737 prefixEnd_1520737 := by exact prefixLift 1520737
  have htrace : WordTrace (prefixWord ++ tailWord_1520737) baseStart_1520737 baseEnd_1520737 := by
    simpa [prefixWord, tailWord_1520737, baseEnd_1520737] using wordTrace_append hprefix tailTrace_1520737
  have hstable : (prefixWord ++ tailWord_1520737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520737).length < 2 ^ (prefixWord ++ tailWord_1520737).sum := by decide
  have hdescent : baseEnd_1520737 < baseStart_1520737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520743 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1520743 : Nat := 118140960795 + 1520743 * 2 ^ 59
def prefixEnd_1520743 : Nat := 4983230072969 + 3 ^ 40 * 1520743 * 2
def baseEnd_1520743 : Nat := 520581407306965879812491

theorem tailTrace_1520743 : CollatzResearch.WordTrace tailWord_1520743 prefixEnd_1520743 520581407306965879812491 := by
  unfold tailWord_1520743
  simp only [CollatzResearch.WordTrace]
  refine ⟨55466053929615308071966883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36977369286410205381311255 55466053929615308071966883)
  ·
    refine ⟨83199080894422962107950325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55466053929615308071966883 83199080894422962107950325)
    ·
      refine ⟨7799913833852152697620343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83199080894422962107950325 7799913833852152697620343)
      ·
        refine ⟨11699870750778229046430515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7799913833852152697620343 11699870750778229046430515)
        ·
          refine ⟨17549806126167343569645773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11699870750778229046430515 17549806126167343569645773)
          ·
            refine ⟨6581177297312753838617165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17549806126167343569645773 6581177297312753838617165)
            ·
              refine ⟨2467941486492282689481437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6581177297312753838617165 2467941486492282689481437)
              ·
                refine ⟨925478057434606008555539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2467941486492282689481437 925478057434606008555539)
                ·
                  refine ⟨1388217086151909012833309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925478057434606008555539 1388217086151909012833309)
                  ·
                    refine ⟨520581407306965879812491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388217086151909012833309 520581407306965879812491)
                    ·
                      rfl

theorem cell22_1520743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1520743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520743 prefixEnd_1520743 := by exact prefixLift 1520743
  have htrace : WordTrace (prefixWord ++ tailWord_1520743) baseStart_1520743 baseEnd_1520743 := by
    simpa [prefixWord, tailWord_1520743, baseEnd_1520743] using wordTrace_append hprefix tailTrace_1520743
  have hstable : (prefixWord ++ tailWord_1520743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520743).length < 2 ^ (prefixWord ++ tailWord_1520743).sum := by decide
  have hdescent : baseEnd_1520743 < baseStart_1520743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520766 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1520766 : Nat := 118140960795 + 1520766 * 2 ^ 59
def prefixEnd_1520766 : Nat := 4983230072969 + 3 ^ 40 * 1520766 * 2
def baseEnd_1520766 : Nat := 520589280677001486487421

theorem tailTrace_1520766 : CollatzResearch.WordTrace tailWord_1520766 prefixEnd_1520766 520589280677001486487421 := by
  unfold tailWord_1520766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933361601066497875006769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36977928539021322000036101 6933361601066497875006769)
  ·
    refine ⟨5200021200799873406255077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6933361601066497875006769 5200021200799873406255077)
    ·
      refine ⟨975003975149976263672827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5200021200799873406255077 975003975149976263672827)
      ·
        refine ⟨1462505962724964395509241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975003975149976263672827 1462505962724964395509241)
        ·
          refine ⟨1096879472043723296631931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462505962724964395509241 1096879472043723296631931)
          ·
            refine ⟨1645319208065584944947897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096879472043723296631931 1645319208065584944947897)
            ·
              refine ⟨1233989406049188708710923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645319208065584944947897 1233989406049188708710923)
              ·
                refine ⟨1850984109073783063066385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233989406049188708710923 1850984109073783063066385)
                ·
                  refine ⟨1388238081805337297299789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1850984109073783063066385 1388238081805337297299789)
                  ·
                    refine ⟨520589280677001486487421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388238081805337297299789 520589280677001486487421)
                    ·
                      rfl

theorem cell22_1520766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1520766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520766 prefixEnd_1520766 := by exact prefixLift 1520766
  have htrace : WordTrace (prefixWord ++ tailWord_1520766) baseStart_1520766 baseEnd_1520766 := by
    simpa [prefixWord, tailWord_1520766, baseEnd_1520766] using wordTrace_append hprefix tailTrace_1520766
  have hstable : (prefixWord ++ tailWord_1520766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520766).length < 2 ^ (prefixWord ++ tailWord_1520766).sum := by decide
  have hdescent : baseEnd_1520766 < baseStart_1520766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520773 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 5]
def baseStart_1520773 : Nat := 118140960795 + 1520773 * 2 ^ 59
def prefixEnd_1520773 : Nat := 4983230072969 + 3 ^ 40 * 1520773 * 2
def baseEnd_1520773 : Nat := 173530558973351933854133

theorem tailTrace_1520773 : CollatzResearch.WordTrace tailWord_1520773 prefixEnd_1520773 173530558973351933854133 := by
  unfold tailWord_1520773
  simp only [CollatzResearch.WordTrace]
  refine ⟨55467148119506623195558973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36978098746337748797039315 55467148119506623195558973)
  ·
    refine ⟨20800180544814983698334615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55467148119506623195558973 20800180544814983698334615)
    ·
      refine ⟨31200270817222475547501923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20800180544814983698334615 31200270817222475547501923)
      ·
        refine ⟨46800406225833713321252885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31200270817222475547501923 46800406225833713321252885)
        ·
          refine ⟨2193769041835955311933729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46800406225833713321252885 2193769041835955311933729)
          ·
            refine ⟨1645326781376966483950297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2193769041835955311933729 1645326781376966483950297)
            ·
              refine ⟨1233995086032724862962723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645326781376966483950297 1233995086032724862962723)
              ·
                refine ⟨1850992629049087294444085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233995086032724862962723 1850992629049087294444085)
                ·
                  refine ⟨173530558973351933854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1850992629049087294444085 173530558973351933854133)
                  ·
                    rfl

theorem cell22_1520773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_1520773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520773 prefixEnd_1520773 := by exact prefixLift 1520773
  have htrace : WordTrace (prefixWord ++ tailWord_1520773) baseStart_1520773 baseEnd_1520773 := by
    simpa [prefixWord, tailWord_1520773, baseEnd_1520773] using wordTrace_append hprefix tailTrace_1520773
  have hstable : (prefixWord ++ tailWord_1520773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520773).length < 2 ^ (prefixWord ++ tailWord_1520773).sum := by decide
  have hdescent : baseEnd_1520773 < baseStart_1520773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520786 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1520786 : Nat := 118140960795 + 1520786 * 2 ^ 59
def prefixEnd_1520786 : Nat := 4983230072969 + 3 ^ 40 * 1520786 * 2
def baseEnd_1520786 : Nat := 520596127085728100987359

theorem tailTrace_1520786 : CollatzResearch.WordTrace tailWord_1520786 prefixEnd_1520786 520596127085728100987359 := by
  unfold tailWord_1520786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866905567114881603945553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36978414845639684277188141 13866905567114881603945553)
  ·
    refine ⟨10400179175336161202959165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13866905567114881603945553 10400179175336161202959165)
    ·
      refine ⟨3900067190751060451109687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10400179175336161202959165 3900067190751060451109687)
      ·
        refine ⟨5850100786126590676664531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900067190751060451109687 5850100786126590676664531)
        ·
          refine ⟨8775151179189886014996797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850100786126590676664531 8775151179189886014996797)
          ·
            refine ⟨3290681692196207255623799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8775151179189886014996797 3290681692196207255623799)
            ·
              refine ⟨4936022538294310883435699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290681692196207255623799 4936022538294310883435699)
              ·
                refine ⟨7404033807441466325153549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936022538294310883435699 7404033807441466325153549)
                ·
                  refine ⟨2776512677790549871932581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7404033807441466325153549 2776512677790549871932581)
                  ·
                    refine ⟨520596127085728100987359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2776512677790549871932581 520596127085728100987359)
                    ·
                      rfl

theorem cell22_1520786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1520786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520786 prefixEnd_1520786 := by exact prefixLift 1520786
  have htrace : WordTrace (prefixWord ++ tailWord_1520786) baseStart_1520786 baseEnd_1520786 := by
    simpa [prefixWord, tailWord_1520786, baseEnd_1520786] using wordTrace_append hprefix tailTrace_1520786
  have hstable : (prefixWord ++ tailWord_1520786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520786).length < 2 ^ (prefixWord ++ tailWord_1520786).sum := by decide
  have hdescent : baseEnd_1520786 < baseStart_1520786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520801 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 4]
def baseStart_1520801 : Nat := 118140960795 + 1520801 * 2 ^ 59
def prefixEnd_1520801 : Nat := 4983230072969 + 3 ^ 40 * 1520801 * 2
def baseEnd_1520801 : Nat := 173533753964091020620771

theorem tailTrace_1520801 : CollatzResearch.WordTrace tailWord_1520801 prefixEnd_1520801 173533753964091020620771 := by
  unfold tailWord_1520801
  simp only [CollatzResearch.WordTrace]
  refine ⟨55468169363405183977578257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36978779575603455985052171 55468169363405183977578257)
  ·
    refine ⟨41601127022553887983183693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55468169363405183977578257 41601127022553887983183693)
    ·
      refine ⟨15600422633457707993693885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41601127022553887983183693 15600422633457707993693885)
      ·
        refine ⟨5850158487546640497635207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15600422633457707993693885 5850158487546640497635207)
        ·
          refine ⟨8775237731319960746452811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850158487546640497635207 8775237731319960746452811)
          ·
            refine ⟨13162856596979941119679217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775237731319960746452811 13162856596979941119679217)
            ·
              refine ⟨9872142447734955839759413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13162856596979941119679217 9872142447734955839759413)
              ·
                refine ⟨925513354475152109977445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9872142447734955839759413 925513354475152109977445)
                ·
                  refine ⟨173533753964091020620771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925513354475152109977445 173533753964091020620771)
                  ·
                    rfl

theorem cell22_1520801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_1520801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520801 prefixEnd_1520801 := by exact prefixLift 1520801
  have htrace : WordTrace (prefixWord ++ tailWord_1520801) baseStart_1520801 baseEnd_1520801 := by
    simpa [prefixWord, tailWord_1520801, baseEnd_1520801] using wordTrace_append hprefix tailTrace_1520801
  have hstable : (prefixWord ++ tailWord_1520801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520801).length < 2 ^ (prefixWord ++ tailWord_1520801).sum := by decide
  have hdescent : baseEnd_1520801 < baseStart_1520801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520818 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1520818 : Nat := 118140960795 + 1520818 * 2 ^ 59
def prefixEnd_1520818 : Nat := 4983230072969 + 3 ^ 40 * 1520818 * 2
def baseEnd_1520818 : Nat := 173535693779896894729087

theorem tailTrace_1520818 : CollatzResearch.WordTrace tailWord_1520818 prefixEnd_1520818 173535693779896894729087 := by
  unfold tailWord_1520818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867197351085898970236777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36979192936229063920631405 13867197351085898970236777)
  ·
    refine ⟨10400398013314424227677583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13867197351085898970236777 10400398013314424227677583)
    ·
      refine ⟨15600597019971636341516375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400398013314424227677583 15600597019971636341516375)
      ·
        refine ⟨23400895529957454512274563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600597019971636341516375 23400895529957454512274563)
        ·
          refine ⟨35101343294936181768411845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23400895529957454512274563 35101343294936181768411845)
          ·
            refine ⟨6581501867800534081577221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35101343294936181768411845 6581501867800534081577221)
            ·
              refine ⟨1234031600212600140295729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6581501867800534081577221 1234031600212600140295729)
              ·
                refine ⟨925523700159450105221797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234031600212600140295729 925523700159450105221797)
                ·
                  refine ⟨173535693779896894729087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925523700159450105221797 173535693779896894729087)
                  ·
                    rfl

theorem cell22_1520818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1520818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520818 prefixEnd_1520818 := by exact prefixLift 1520818
  have htrace : WordTrace (prefixWord ++ tailWord_1520818) baseStart_1520818 baseEnd_1520818 := by
    simpa [prefixWord, tailWord_1520818, baseEnd_1520818] using wordTrace_append hprefix tailTrace_1520818
  have hstable : (prefixWord ++ tailWord_1520818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520818).length < 2 ^ (prefixWord ++ tailWord_1520818).sum := by decide
  have hdescent : baseEnd_1520818 < baseStart_1520818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520829 : List Nat := [1, 4, 1, 2, 1, 1, 5, 7]
def baseStart_1520829 : Nat := 118140960795 + 1520829 * 2 ^ 59
def prefixEnd_1520829 : Nat := 4983230072969 + 3 ^ 40 * 1520829 * 2
def baseEnd_1520829 : Nat := 57845649651610035795803

theorem tailTrace_1520829 : CollatzResearch.WordTrace tailWord_1520829 prefixEnd_1520829 57845649651610035795803 := by
  unfold tailWord_1520829
  simp only [CollatzResearch.WordTrace]
  refine ⟨55469190607303744759597541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36979460404869163173065027 55469190607303744759597541)
  ·
    refine ⟨10400473238869452142424539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55469190607303744759597541 10400473238869452142424539)
    ·
      refine ⟨15600709858304178213636809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400473238869452142424539 15600709858304178213636809)
      ·
        refine ⟨11700532393728133660227607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15600709858304178213636809 11700532393728133660227607)
        ·
          refine ⟨17550798590592200490341411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11700532393728133660227607 17550798590592200490341411)
          ·
            refine ⟨26326197885888300735512117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17550798590592200490341411 26326197885888300735512117)
            ·
              refine ⟨2468081051802028193954261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26326197885888300735512117 2468081051802028193954261)
              ·
                refine ⟨57845649651610035795803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2468081051802028193954261 57845649651610035795803)
                ·
                  rfl

theorem cell22_1520829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 7].length) (baseStart_1520829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520829 prefixEnd_1520829 := by exact prefixLift 1520829
  have htrace : WordTrace (prefixWord ++ tailWord_1520829) baseStart_1520829 baseEnd_1520829 := by
    simpa [prefixWord, tailWord_1520829, baseEnd_1520829] using wordTrace_append hprefix tailTrace_1520829
  have hstable : (prefixWord ++ tailWord_1520829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520829).length < 2 ^ (prefixWord ++ tailWord_1520829).sum := by decide
  have hdescent : baseEnd_1520829 < baseStart_1520829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520833 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1520833 : Nat := 118140960795 + 1520833 * 2 ^ 59
def prefixEnd_1520833 : Nat := 4983230072969 + 3 ^ 40 * 1520833 * 2
def baseEnd_1520833 : Nat := 520612216146235645062215

theorem tailTrace_1520833 : CollatzResearch.WordTrace tailWord_1520833 prefixEnd_1520833 520612216146235645062215 := by
  unfold tailWord_1520833
  simp only [CollatzResearch.WordTrace]
  refine ⟨55469336499289253442743153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36979557666192835628495435 55469336499289253442743153)
  ·
    refine ⟨41602002374466940082057365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55469336499289253442743153 41602002374466940082057365)
    ·
      refine ⟨1950093861303137816346439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41602002374466940082057365 1950093861303137816346439)
      ·
        refine ⟨2925140791954706724519659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950093861303137816346439 2925140791954706724519659)
        ·
          refine ⟨4387711187932060086779489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925140791954706724519659 4387711187932060086779489)
          ·
            refine ⟨3290783390949045065084617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4387711187932060086779489 3290783390949045065084617)
            ·
              refine ⟨2468087543211783798813463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290783390949045065084617 2468087543211783798813463)
              ·
                refine ⟨3702131314817675698220195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468087543211783798813463 3702131314817675698220195)
                ·
                  refine ⟨5553196972226513547330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702131314817675698220195 5553196972226513547330293)
                  ·
                    refine ⟨520612216146235645062215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553196972226513547330293 520612216146235645062215)
                    ·
                      rfl

theorem cell22_1520833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1520833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520833 prefixEnd_1520833 := by exact prefixLift 1520833
  have htrace : WordTrace (prefixWord ++ tailWord_1520833) baseStart_1520833 baseEnd_1520833 := by
    simpa [prefixWord, tailWord_1520833, baseEnd_1520833] using wordTrace_append hprefix tailTrace_1520833
  have hstable : (prefixWord ++ tailWord_1520833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520833).length < 2 ^ (prefixWord ++ tailWord_1520833).sum := by decide
  have hdescent : baseEnd_1520833 < baseStart_1520833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520854 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1520854 : Nat := 118140960795 + 1520854 * 2 ^ 59
def prefixEnd_1520854 : Nat := 4983230072969 + 3 ^ 40 * 1520854 * 2
def baseEnd_1520854 : Nat := 520619404875398590287151

theorem tailTrace_1520854 : CollatzResearch.WordTrace tailWord_1520854 prefixEnd_1520854 520619404875398590287151 := by
  unfold tailWord_1520854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466881402013323376828601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36980068288142116019505077 3466881402013323376828601)
  ·
    refine ⟨2600161051509992532621451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3466881402013323376828601 2600161051509992532621451)
    ·
      refine ⟨3900241577264988798932177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600161051509992532621451 3900241577264988798932177)
      ·
        refine ⟨2925181182948741599199133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3900241577264988798932177 2925181182948741599199133)
        ·
          refine ⟨1096942943605778099699675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2925181182948741599199133 1096942943605778099699675)
          ·
            refine ⟨1645414415408667149549513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096942943605778099699675 1645414415408667149549513)
            ·
              refine ⟨1234060811556500362162135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645414415408667149549513 1234060811556500362162135)
              ·
                refine ⟨1851091217334750543243203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234060811556500362162135 1851091217334750543243203)
                ·
                  refine ⟨2776636826002125814864805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851091217334750543243203 2776636826002125814864805)
                  ·
                    refine ⟨520619404875398590287151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2776636826002125814864805 520619404875398590287151)
                    ·
                      rfl

theorem cell22_1520854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1520854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520854 prefixEnd_1520854 := by exact prefixLift 1520854
  have htrace : WordTrace (prefixWord ++ tailWord_1520854) baseStart_1520854 baseEnd_1520854 := by
    simpa [prefixWord, tailWord_1520854, baseEnd_1520854] using wordTrace_append hprefix tailTrace_1520854
  have hstable : (prefixWord ++ tailWord_1520854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520854).length < 2 ^ (prefixWord ++ tailWord_1520854).sum := by decide
  have hdescent : baseEnd_1520854 < baseStart_1520854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520884 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1520884 : Nat := 118140960795 + 1520884 * 2 ^ 59
def prefixEnd_1520884 : Nat := 4983230072969 + 3 ^ 40 * 1520884 * 2
def baseEnd_1520884 : Nat := 520629674488488512037059

theorem tailTrace_1520884 : CollatzResearch.WordTrace tailWord_1520884 prefixEnd_1520884 520629674488488512037059 := by
  unfold tailWord_1520884
  simp only [CollatzResearch.WordTrace]
  refine ⟨27735598311052244576424853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36980797748069659435233137 27735598311052244576424853)
  ·
    refine ⟨1300106170830573964519915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27735598311052244576424853 1300106170830573964519915)
    ·
      refine ⟨1950159256245860946779873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300106170830573964519915 1950159256245860946779873)
      ·
        refine ⟨1462619442184395710084905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950159256245860946779873 1462619442184395710084905)
        ·
          refine ⟨1096964581638296782563679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462619442184395710084905 1096964581638296782563679)
          ·
            refine ⟨1645446872457445173845519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096964581638296782563679 1645446872457445173845519)
            ·
              refine ⟨2468170308686167760768279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645446872457445173845519 2468170308686167760768279)
              ·
                refine ⟨3702255463029251641152419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468170308686167760768279 3702255463029251641152419)
                ·
                  refine ⟨5553383194543877461728629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702255463029251641152419 5553383194543877461728629)
                  ·
                    refine ⟨520629674488488512037059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553383194543877461728629 520629674488488512037059)
                    ·
                      rfl

theorem cell22_1520884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1520884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520884 prefixEnd_1520884 := by exact prefixLift 1520884
  have htrace : WordTrace (prefixWord ++ tailWord_1520884) baseStart_1520884 baseEnd_1520884 := by
    simpa [prefixWord, tailWord_1520884, baseEnd_1520884] using wordTrace_append hprefix tailTrace_1520884
  have hstable : (prefixWord ++ tailWord_1520884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520884).length < 2 ^ (prefixWord ++ tailWord_1520884).sum := by decide
  have hdescent : baseEnd_1520884 < baseStart_1520884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520889 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_1520889 : Nat := 118140960795 + 1520889 * 2 ^ 59
def prefixEnd_1520889 : Nat := 4983230072969 + 3 ^ 40 * 1520889 * 2
def baseEnd_1520889 : Nat := 520631386090670165662043

theorem tailTrace_1520889 : CollatzResearch.WordTrace tailWord_1520889 prefixEnd_1520889 520631386090670165662043 := by
  unfold tailWord_1520889
  simp only [CollatzResearch.WordTrace]
  refine ⟨55471378987086375006781721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36980919324724250004521147 55471378987086375006781721)
  ·
    refine ⟨41603534240314781255086291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55471378987086375006781721 41603534240314781255086291)
    ·
      refine ⟨62405301360472171882629437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41603534240314781255086291 62405301360472171882629437)
      ·
        refine ⟨23401988010177064455986039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62405301360472171882629437 23401988010177064455986039)
        ·
          refine ⟨35102982015265596683979059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23401988010177064455986039 35102982015265596683979059)
          ·
            refine ⟨52654473022898395025968589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35102982015265596683979059 52654473022898395025968589)
            ·
              refine ⟨19745427383586898134738221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52654473022898395025968589 19745427383586898134738221)
              ·
                refine ⟨7404535268845086800526833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19745427383586898134738221 7404535268845086800526833)
                ·
                  refine ⟨5553401451633815100395125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7404535268845086800526833 5553401451633815100395125)
                  ·
                    refine ⟨520631386090670165662043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553401451633815100395125 520631386090670165662043)
                    ·
                      rfl

theorem cell22_1520889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_1520889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1520889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1520889 prefixEnd_1520889 := by exact prefixLift 1520889
  have htrace : WordTrace (prefixWord ++ tailWord_1520889) baseStart_1520889 baseEnd_1520889 := by
    simpa [prefixWord, tailWord_1520889, baseEnd_1520889] using wordTrace_append hprefix tailTrace_1520889
  have hstable : (prefixWord ++ tailWord_1520889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520889).length < 2 ^ (prefixWord ++ tailWord_1520889).sum := by decide
  have hdescent : baseEnd_1520889 < baseStart_1520889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521058 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1521058 : Nat := 118140960795 + 1521058 * 2 ^ 59
def prefixEnd_1521058 : Nat := 4983230072969 + 3 ^ 40 * 1521058 * 2
def baseEnd_1521058 : Nat := 520689238244410058186525

theorem tailTrace_1521058 : CollatzResearch.WordTrace tailWord_1521058 prefixEnd_1521058 520689238244410058186525 := by
  unfold tailWord_1521058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13869385730868529217420957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36985028615649411246455885 13869385730868529217420957)
  ·
    refine ⟨5201019649075698456532859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13869385730868529217420957 5201019649075698456532859)
    ·
      refine ⟨7801529473613547684799289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5201019649075698456532859 7801529473613547684799289)
      ·
        refine ⟨5851147105210160763599467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7801529473613547684799289 5851147105210160763599467)
        ·
          refine ⟨8776720657815241145399201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851147105210160763599467 8776720657815241145399201)
          ·
            refine ⟨6582540493361430859049401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8776720657815241145399201 6582540493361430859049401)
            ·
              refine ⟨4936905370021073144287051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6582540493361430859049401 4936905370021073144287051)
              ·
                refine ⟨7405358055031609716430577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936905370021073144287051 7405358055031609716430577)
                ·
                  refine ⟨5554018541273707287322933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7405358055031609716430577 5554018541273707287322933)
                  ·
                    refine ⟨520689238244410058186525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5554018541273707287322933 520689238244410058186525)
                    ·
                      rfl

theorem cell22_1521058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1521058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521058 prefixEnd_1521058 := by exact prefixLift 1521058
  have htrace : WordTrace (prefixWord ++ tailWord_1521058) baseStart_1521058 baseEnd_1521058 := by
    simpa [prefixWord, tailWord_1521058, baseEnd_1521058] using wordTrace_append hprefix tailTrace_1521058
  have hstable : (prefixWord ++ tailWord_1521058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521058).length < 2 ^ (prefixWord ++ tailWord_1521058).sum := by decide
  have hdescent : baseEnd_1521058 < baseStart_1521058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521103 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 4, 3]
def baseStart_1521103 : Nat := 118140960795 + 1521103 * 2 ^ 59
def prefixEnd_1521103 : Nat := 4983230072969 + 3 ^ 40 * 1521103 * 2
def baseEnd_1521103 : Nat := 520704642664044940811387

theorem tailTrace_1521103 : CollatzResearch.WordTrace tailWord_1521103 prefixEnd_1521103 520704642664044940811387 := by
  unfold tailWord_1521103
  simp only [CollatzResearch.WordTrace]
  refine ⟨55479184208311089555071963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36986122805540726370047975 55479184208311089555071963)
  ·
    refine ⟨83218776312466634332607945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55479184208311089555071963 83218776312466634332607945)
    ·
      refine ⟨62414082234349975749455959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83218776312466634332607945 62414082234349975749455959)
      ·
        refine ⟨93621123351524963624183939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62414082234349975749455959 93621123351524963624183939)
        ·
          refine ⟨140431685027287445436275909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93621123351524963624183939 140431685027287445436275909)
          ·
            refine ⟨26330940942616396019301733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140431685027287445436275909 26330940942616396019301733)
            ·
              refine ⟨4937051426740574253619075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26330940942616396019301733 4937051426740574253619075)
              ·
                refine ⟨7405577140110861380428613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937051426740574253619075 7405577140110861380428613)
                ·
                  refine ⟨1388545713770786508830365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7405577140110861380428613 1388545713770786508830365)
                  ·
                    refine ⟨520704642664044940811387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388545713770786508830365 520704642664044940811387)
                    ·
                      rfl

theorem cell22_1521103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_1521103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521103 prefixEnd_1521103 := by exact prefixLift 1521103
  have htrace : WordTrace (prefixWord ++ tailWord_1521103) baseStart_1521103 baseEnd_1521103 := by
    simpa [prefixWord, tailWord_1521103, baseEnd_1521103] using wordTrace_append hprefix tailTrace_1521103
  have hstable : (prefixWord ++ tailWord_1521103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521103).length < 2 ^ (prefixWord ++ tailWord_1521103).sum := by decide
  have hdescent : baseEnd_1521103 < baseStart_1521103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521150 : List Nat := [4, 2, 2, 3, 1, 10]
def baseStart_1521150 : Nat := 118140960795 + 1521150 * 2 ^ 59
def prefixEnd_1521150 : Nat := 4983230072969 + 3 ^ 40 * 1521150 * 2
def baseEnd_1521150 : Nat := 6428651008945092406003

theorem tailTrace_1521150 : CollatzResearch.WordTrace tailWord_1521150 prefixEnd_1521150 6428651008945092406003 := by
  unfold tailWord_1521150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935112304892602072754113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36987265626093877721355269 6935112304892602072754113)
  ·
    refine ⟨5201334228669451554565585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6935112304892602072754113 5201334228669451554565585)
    ·
      refine ⟨3901000671502088665924189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5201334228669451554565585 3901000671502088665924189)
      ·
        refine ⟨1462875251813283249721571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3901000671502088665924189 1462875251813283249721571)
        ·
          refine ⟨2194312877719924874582357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462875251813283249721571 2194312877719924874582357)
          ·
            refine ⟨6428651008945092406003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2194312877719924874582357 6428651008945092406003)
            ·
              rfl

theorem cell22_1521150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 10].length) (baseStart_1521150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521150 prefixEnd_1521150 := by exact prefixLift 1521150
  have htrace : WordTrace (prefixWord ++ tailWord_1521150) baseStart_1521150 baseEnd_1521150 := by
    simpa [prefixWord, tailWord_1521150, baseEnd_1521150] using wordTrace_append hprefix tailTrace_1521150
  have hstable : (prefixWord ++ tailWord_1521150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521150).length < 2 ^ (prefixWord ++ tailWord_1521150).sum := by decide
  have hdescent : baseEnd_1521150 < baseStart_1521150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521154 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1521154 : Nat := 118140960795 + 1521154 * 2 ^ 59
def prefixEnd_1521154 : Nat := 4983230072969 + 3 ^ 40 * 1521154 * 2
def baseEnd_1521154 : Nat := 520722101006297807786231

theorem tailTrace_1521154 : CollatzResearch.WordTrace tailWord_1521154 prefixEnd_1521154 520722101006297807786231 := by
  unfold tailWord_1521154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13870261082781581316294629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36987362887417550176785677 13870261082781581316294629)
  ·
    refine ⟨2600673953021546496805243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13870261082781581316294629 2600673953021546496805243)
    ·
      refine ⟨3901010929532319745207865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600673953021546496805243 3901010929532319745207865)
      ·
        refine ⟨2925758197149239808905899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3901010929532319745207865 2925758197149239808905899)
        ·
          refine ⟨4388637295723859713358849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925758197149239808905899 4388637295723859713358849)
          ·
            refine ⟨3291477971792894785019137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4388637295723859713358849 3291477971792894785019137)
            ·
              refine ⟨2468608478844671088764353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291477971792894785019137 2468608478844671088764353)
              ·
                refine ⟨1851456359133503316573265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2468608478844671088764353 1851456359133503316573265)
                ·
                  refine ⟨1388592269350127487429949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1851456359133503316573265 1388592269350127487429949)
                  ·
                    refine ⟨520722101006297807786231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388592269350127487429949 520722101006297807786231)
                    ·
                      rfl

theorem cell22_1521154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1521154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521154 prefixEnd_1521154 := by exact prefixLift 1521154
  have htrace : WordTrace (prefixWord ++ tailWord_1521154) baseStart_1521154 baseEnd_1521154 := by
    simpa [prefixWord, tailWord_1521154, baseEnd_1521154] using wordTrace_append hprefix tailTrace_1521154
  have hstable : (prefixWord ++ tailWord_1521154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521154).length < 2 ^ (prefixWord ++ tailWord_1521154).sum := by decide
  have hdescent : baseEnd_1521154 < baseStart_1521154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521156 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 4]
def baseStart_1521156 : Nat := 118140960795 + 1521156 * 2 ^ 59
def prefixEnd_1521156 : Nat := 4983230072969 + 3 ^ 40 * 1521156 * 2
def baseEnd_1521156 : Nat := 173574261882390156412075

theorem tailTrace_1521156 : CollatzResearch.WordTrace tailWord_1521156 prefixEnd_1521156 173574261882390156412075 := by
  unfold tailWord_1521156
  simp only [CollatzResearch.WordTrace]
  refine ⟨27740558638559539803375661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36987411518079386404500881 27740558638559539803375661)
  ·
    refine ⟨10402709489459827426265873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27740558638559539803375661 10402709489459827426265873)
    ·
      refine ⟨7802032117094870569699405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10402709489459827426265873 7802032117094870569699405)
      ·
        refine ⟨2925762043910576463637277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7802032117094870569699405 2925762043910576463637277)
        ·
          refine ⟨1097160766466466173863979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2925762043910576463637277 1097160766466466173863979)
          ·
            refine ⟨1645741149699699260795969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097160766466466173863979 1645741149699699260795969)
            ·
              refine ⟨1234305862274774445596977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645741149699699260795969 1234305862274774445596977)
              ·
                refine ⟨925729396706080834197733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234305862274774445596977 925729396706080834197733)
                ·
                  refine ⟨173574261882390156412075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925729396706080834197733 173574261882390156412075)
                  ·
                    rfl

theorem cell22_1521156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_1521156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521156 prefixEnd_1521156 := by exact prefixLift 1521156
  have htrace : WordTrace (prefixWord ++ tailWord_1521156) baseStart_1521156 baseEnd_1521156 := by
    simpa [prefixWord, tailWord_1521156, baseEnd_1521156] using wordTrace_append hprefix tailTrace_1521156
  have hstable : (prefixWord ++ tailWord_1521156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521156).length < 2 ^ (prefixWord ++ tailWord_1521156).sum := by decide
  have hdescent : baseEnd_1521156 < baseStart_1521156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521212 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 5]
def baseStart_1521212 : Nat := 118140960795 + 1521212 * 2 ^ 59
def prefixEnd_1521212 : Nat := 4983230072969 + 3 ^ 40 * 1521212 * 2
def baseEnd_1521212 : Nat := 173580651863868329945351

theorem tailTrace_1521212 : CollatzResearch.WordTrace tailWord_1521212 prefixEnd_1521212 173580651863868329945351 := by
  unfold tailWord_1521212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27741579882458100585394945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36988773176610800780526593 27741579882458100585394945)
  ·
    refine ⟨20806184911843575439046209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27741579882458100585394945 20806184911843575439046209)
    ·
      refine ⟨15604638683882681579284657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20806184911843575439046209 15604638683882681579284657)
      ·
        refine ⟨11703479012912011184463493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15604638683882681579284657 11703479012912011184463493)
        ·
          refine ⟨2194402314921002097086905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11703479012912011184463493 2194402314921002097086905)
          ·
            refine ⟨1645801736190751572815179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2194402314921002097086905 1645801736190751572815179)
            ·
              refine ⟨2468702604286127359222769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645801736190751572815179 2468702604286127359222769)
              ·
                refine ⟨1851526953214595519417077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2468702604286127359222769 1851526953214595519417077)
                ·
                  refine ⟨173580651863868329945351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851526953214595519417077 173580651863868329945351)
                  ·
                    rfl

theorem cell22_1521212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_1521212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521212 prefixEnd_1521212 := by exact prefixLift 1521212
  have htrace : WordTrace (prefixWord ++ tailWord_1521212) baseStart_1521212 baseEnd_1521212 := by
    simpa [prefixWord, tailWord_1521212, baseEnd_1521212] using wordTrace_append hprefix tailTrace_1521212
  have hstable : (prefixWord ++ tailWord_1521212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521212).length < 2 ^ (prefixWord ++ tailWord_1521212).sum := by decide
  have hdescent : baseEnd_1521212 < baseStart_1521212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521229 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1521229 : Nat := 118140960795 + 1521229 * 2 ^ 59
def prefixEnd_1521229 : Nat := 4983230072969 + 3 ^ 40 * 1521229 * 2
def baseEnd_1521229 : Nat := 173582591679674204053667

theorem tailTrace_1521229 : CollatzResearch.WordTrace tailWord_1521229 prefixEnd_1521229 173582591679674204053667 := by
  unfold tailWord_1521229
  simp only [CollatzResearch.WordTrace]
  refine ⟨55483779805854613074158741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36989186537236408716105827 55483779805854613074158741)
  ·
    refine ⟨2600802178399434987851191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55483779805854613074158741 2600802178399434987851191)
    ·
      refine ⟨3901203267599152481776787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600802178399434987851191 3901203267599152481776787)
      ·
        refine ⟨5851804901398728722665181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901203267599152481776787 5851804901398728722665181)
        ·
          refine ⟨2194426838024523270999443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5851804901398728722665181 2194426838024523270999443)
          ·
            refine ⟨3291640257036784906499165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194426838024523270999443 3291640257036784906499165)
            ·
              refine ⟨1234365096388794339937187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3291640257036784906499165 1234365096388794339937187)
              ·
                refine ⟨1851547644583191509905781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234365096388794339937187 1851547644583191509905781)
                ·
                  refine ⟨173582591679674204053667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851547644583191509905781 173582591679674204053667)
                  ·
                    rfl

theorem cell22_1521229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1521229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521229 prefixEnd_1521229 := by exact prefixLift 1521229
  have htrace : WordTrace (prefixWord ++ tailWord_1521229) baseStart_1521229 baseEnd_1521229 := by
    simpa [prefixWord, tailWord_1521229, baseEnd_1521229] using wordTrace_append hprefix tailTrace_1521229
  have hstable : (prefixWord ++ tailWord_1521229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521229).length < 2 ^ (prefixWord ++ tailWord_1521229).sum := by decide
  have hdescent : baseEnd_1521229 < baseStart_1521229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521255 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1521255 : Nat := 118140960795 + 1521255 * 2 ^ 59
def prefixEnd_1521255 : Nat := 4983230072969 + 3 ^ 40 * 1521255 * 2
def baseEnd_1521255 : Nat := 520756675370367211010921

theorem tailTrace_1521255 : CollatzResearch.WordTrace tailWord_1521255 prefixEnd_1521255 520756675370367211010921 := by
  unfold tailWord_1521255
  simp only [CollatzResearch.WordTrace]
  refine ⟨55484728103760419514605219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36989818735840279676403479 55484728103760419514605219)
  ·
    refine ⟨83227092155640629271907829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55484728103760419514605219 83227092155640629271907829)
    ·
      refine ⟨7802539889591308994241359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83227092155640629271907829 7802539889591308994241359)
      ·
        refine ⟨11703809834386963491362039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7802539889591308994241359 11703809834386963491362039)
        ·
          refine ⟨17555714751580445237043059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11703809834386963491362039 17555714751580445237043059)
          ·
            refine ⟨26333572127370667855564589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17555714751580445237043059 26333572127370667855564589)
            ·
              refine ⟨9875089547764000445836721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26333572127370667855564589 9875089547764000445836721)
              ·
                refine ⟨7406317160823000334377541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9875089547764000445836721 7406317160823000334377541)
                ·
                  refine ⟨1388684467654312562695789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7406317160823000334377541 1388684467654312562695789)
                  ·
                    refine ⟨520756675370367211010921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388684467654312562695789 520756675370367211010921)
                    ·
                      rfl

theorem cell22_1521255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1521255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521255 prefixEnd_1521255 := by exact prefixLift 1521255
  have htrace : WordTrace (prefixWord ++ tailWord_1521255) baseStart_1521255 baseEnd_1521255 := by
    simpa [prefixWord, tailWord_1521255, baseEnd_1521255] using wordTrace_append hprefix tailTrace_1521255
  have hstable : (prefixWord ++ tailWord_1521255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521255).length < 2 ^ (prefixWord ++ tailWord_1521255).sum := by decide
  have hdescent : baseEnd_1521255 < baseStart_1521255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521330 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_1521330 : Nat := 118140960795 + 1521330 * 2 ^ 59
def prefixEnd_1521330 : Nat := 4983230072969 + 3 ^ 40 * 1521330 * 2
def baseEnd_1521330 : Nat := 173594116467697338461897

theorem tailTrace_1521330 : CollatzResearch.WordTrace tailWord_1521330 prefixEnd_1521330 173594116467697338461897 := by
  unfold tailWord_1521330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871865894622176830896361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36991642385659138215723629 13871865894622176830896361)
  ·
    refine ⟨10403899420966632623172271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13871865894622176830896361 10403899420966632623172271)
    ·
      refine ⟨15605849131449948934758407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10403899420966632623172271 15605849131449948934758407)
      ·
        refine ⟨23408773697174923402137611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15605849131449948934758407 23408773697174923402137611)
        ·
          refine ⟨35113160545762385103206417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23408773697174923402137611 35113160545762385103206417)
          ·
            refine ⟨26334870409321788827404813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35113160545762385103206417 26334870409321788827404813)
            ·
              refine ⟨9875576403495670810276805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26334870409321788827404813 9875576403495670810276805)
              ·
                refine ⟨1851670575655438276926901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9875576403495670810276805 1851670575655438276926901)
                ·
                  refine ⟨173594116467697338461897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1851670575655438276926901 173594116467697338461897)
                  ·
                    rfl

theorem cell22_1521330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_1521330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521330 prefixEnd_1521330 := by exact prefixLift 1521330
  have htrace : WordTrace (prefixWord ++ tailWord_1521330) baseStart_1521330 baseEnd_1521330 := by
    simpa [prefixWord, tailWord_1521330, baseEnd_1521330] using wordTrace_append hprefix tailTrace_1521330
  have hstable : (prefixWord ++ tailWord_1521330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521330).length < 2 ^ (prefixWord ++ tailWord_1521330).sum := by decide
  have hdescent : baseEnd_1521330 < baseStart_1521330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521405 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1521405 : Nat := 118140960795 + 1521405 * 2 ^ 59
def prefixEnd_1521405 : Nat := 4983230072969 + 3 ^ 40 * 1521405 * 2
def baseEnd_1521405 : Nat := 520808023435816819760461

theorem tailTrace_1521405 : CollatzResearch.WordTrace tailWord_1521405 prefixEnd_1521405 520808023435816819760461 := by
  unfold tailWord_1521405
  simp only [CollatzResearch.WordTrace]
  refine ⟨55490199053216995132565669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36993466035477996755043779 55490199053216995132565669)
  ·
    refine ⟨10404412322478186587356063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55490199053216995132565669 10404412322478186587356063)
    ·
      refine ⟨15606618483717279881034095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10404412322478186587356063 15606618483717279881034095)
      ·
        refine ⟨23409927725575919821551143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15606618483717279881034095 23409927725575919821551143)
        ·
          refine ⟨35114891588363879732326715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23409927725575919821551143 35114891588363879732326715)
          ·
            refine ⟨52672337382545819598490073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35114891588363879732326715 52672337382545819598490073)
            ·
              refine ⟨39504253036909364698867555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52672337382545819598490073 39504253036909364698867555)
              ·
                refine ⟨59256379555364047048301333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39504253036909364698867555 59256379555364047048301333)
                ·
                  refine ⟨2777642791657689705389125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59256379555364047048301333 2777642791657689705389125)
                  ·
                    refine ⟨520808023435816819760461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2777642791657689705389125 520808023435816819760461)
                    ·
                      rfl

theorem cell22_1521405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1521405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521405 prefixEnd_1521405 := by exact prefixLift 1521405
  have htrace : WordTrace (prefixWord ++ tailWord_1521405) baseStart_1521405 baseEnd_1521405 := by
    simpa [prefixWord, tailWord_1521405, baseEnd_1521405] using wordTrace_append hprefix tailTrace_1521405
  have hstable : (prefixWord ++ tailWord_1521405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521405).length < 2 ^ (prefixWord ++ tailWord_1521405).sum := by decide
  have hdescent : baseEnd_1521405 < baseStart_1521405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521407 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 2, 3]
def baseStart_1521407 : Nat := 118140960795 + 1521407 * 2 ^ 59
def prefixEnd_1521407 : Nat := 4983230072969 + 3 ^ 40 * 1521407 * 2
def baseEnd_1521407 : Nat := 520808708076689481210455

theorem tailTrace_1521407 : CollatzResearch.WordTrace tailWord_1521407 prefixEnd_1521407 520808708076689481210455 := by
  unfold tailWord_1521407
  simp only [CollatzResearch.WordTrace]
  refine ⟨55490271999209749474138475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36993514666139832982758983 55490271999209749474138475)
  ·
    refine ⟨83235407998814624211207713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55490271999209749474138475 83235407998814624211207713)
    ·
      refine ⟨62426555999110968158405785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83235407998814624211207713 62426555999110968158405785)
      ·
        refine ⟨46819916999333226118804339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62426555999110968158405785 46819916999333226118804339)
        ·
          refine ⟨70229875498999839178206509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46819916999333226118804339 70229875498999839178206509)
          ·
            refine ⟨26336203312124939691827441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70229875498999839178206509 26336203312124939691827441)
            ·
              refine ⟨19752152484093704768870581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26336203312124939691827441 19752152484093704768870581)
              ·
                refine ⟨1851764295383784822081617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19752152484093704768870581 1851764295383784822081617)
                ·
                  refine ⟨1388823221537838616561213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1851764295383784822081617 1388823221537838616561213)
                  ·
                    refine ⟨520808708076689481210455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388823221537838616561213 520808708076689481210455)
                    ·
                      rfl

theorem cell22_1521407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_1521407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521407 prefixEnd_1521407 := by exact prefixLift 1521407
  have htrace : WordTrace (prefixWord ++ tailWord_1521407) baseStart_1521407 baseEnd_1521407 := by
    simpa [prefixWord, tailWord_1521407, baseEnd_1521407] using wordTrace_append hprefix tailTrace_1521407
  have hstable : (prefixWord ++ tailWord_1521407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521407).length < 2 ^ (prefixWord ++ tailWord_1521407).sum := by decide
  have hdescent : baseEnd_1521407 < baseStart_1521407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521426 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_1521426 : Nat := 118140960795 + 1521426 * 2 ^ 59
def prefixEnd_1521426 : Nat := 4983230072969 + 3 ^ 40 * 1521426 * 2
def baseEnd_1521426 : Nat := 173605070721659921661799

theorem tailTrace_1521426 : CollatzResearch.WordTrace tailWord_1521426 prefixEnd_1521426 173605070721659921661799 := by
  unfold tailWord_1521426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872741246535228929770033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36993976657427277146053421 13872741246535228929770033)
  ·
    refine ⟨10404555934901421697327525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13872741246535228929770033 10404555934901421697327525)
    ·
      refine ⟨1950854237794016568248911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10404555934901421697327525 1950854237794016568248911)
      ·
        refine ⟨2926281356691024852373367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950854237794016568248911 2926281356691024852373367)
        ·
          refine ⟨4389422035036537278560051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926281356691024852373367 4389422035036537278560051)
          ·
            refine ⟨6584133052554805917840077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389422035036537278560051 6584133052554805917840077)
            ·
              refine ⟨2469049894708052219190029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6584133052554805917840077 2469049894708052219190029)
              ·
                refine ⟨925893710515519582196261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2469049894708052219190029 925893710515519582196261)
                ·
                  refine ⟨173605070721659921661799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925893710515519582196261 173605070721659921661799)
                  ·
                    rfl

theorem cell22_1521426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_1521426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521426 prefixEnd_1521426 := by exact prefixLift 1521426
  have htrace : WordTrace (prefixWord ++ tailWord_1521426) baseStart_1521426 baseEnd_1521426 := by
    simpa [prefixWord, tailWord_1521426, baseEnd_1521426] using wordTrace_append hprefix tailTrace_1521426
  have hstable : (prefixWord ++ tailWord_1521426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521426).length < 2 ^ (prefixWord ++ tailWord_1521426).sum := by decide
  have hdescent : baseEnd_1521426 < baseStart_1521426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521454 : List Nat := [4, 1, 3, 2, 2, 1, 2, 7]
def baseStart_1521454 : Nat := 118140960795 + 1521454 * 2 ^ 59
def prefixEnd_1521454 : Nat := 4983230072969 + 3 ^ 40 * 1521454 * 2
def baseEnd_1521454 : Nat := 57869421904133002809479

theorem tailTrace_1521454 : CollatzResearch.WordTrace tailWord_1521454 prefixEnd_1521454 57869421904133002809479 := by
  unfold tailWord_1521454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6936498278754934562637427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36994657486692984334066277 6936498278754934562637427)
  ·
    refine ⟨10404747418132401843956141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6936498278754934562637427 10404747418132401843956141)
    ·
      refine ⟨3901780281799650691483553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10404747418132401843956141 3901780281799650691483553)
      ·
        refine ⟨2926335211349738018612665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3901780281799650691483553 2926335211349738018612665)
        ·
          refine ⟨2194751408512303513959499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2926335211349738018612665 2194751408512303513959499)
          ·
            refine ⟨3292127112768455270939249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194751408512303513959499 3292127112768455270939249)
            ·
              refine ⟨2469095334576341453204437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292127112768455270939249 2469095334576341453204437)
              ·
                refine ⟨57869421904133002809479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2469095334576341453204437 57869421904133002809479)
                ·
                  rfl

theorem cell22_1521454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_1521454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521454 prefixEnd_1521454 := by exact prefixLift 1521454
  have htrace : WordTrace (prefixWord ++ tailWord_1521454) baseStart_1521454 baseEnd_1521454 := by
    simpa [prefixWord, tailWord_1521454, baseEnd_1521454] using wordTrace_append hprefix tailTrace_1521454
  have hstable : (prefixWord ++ tailWord_1521454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521454).length < 2 ^ (prefixWord ++ tailWord_1521454).sum := by decide
  have hdescent : baseEnd_1521454 < baseStart_1521454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521503 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 1, 3]
def baseStart_1521503 : Nat := 118140960795 + 1521503 * 2 ^ 59
def prefixEnd_1521503 : Nat := 4983230072969 + 3 ^ 40 * 1521503 * 2
def baseEnd_1521503 : Nat := 520841570838577230810161

theorem tailTrace_1521503 : CollatzResearch.WordTrace tailWord_1521503 prefixEnd_1521503 520841570838577230810161 := by
  unfold tailWord_1521503
  simp only [CollatzResearch.WordTrace]
  refine ⟨55493773406861957869633163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36995848937907971913088775 55493773406861957869633163)
  ·
    refine ⟨83240660110292936804449745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55493773406861957869633163 83240660110292936804449745)
    ·
      refine ⟨62430495082719702603337309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83240660110292936804449745 62430495082719702603337309)
      ·
        refine ⟨23411435656019888476251491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62430495082719702603337309 23411435656019888476251491)
        ·
          refine ⟨35117153484029832714377237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23411435656019888476251491 35117153484029832714377237)
          ·
            refine ⟨1646116569563898408486433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35117153484029832714377237 1646116569563898408486433)
            ·
              refine ⟨1234587427172923806364825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646116569563898408486433 1234587427172923806364825)
              ·
                refine ⟨925940570379692854773619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234587427172923806364825 925940570379692854773619)
                ·
                  refine ⟨1388910855569539282160429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925940570379692854773619 1388910855569539282160429)
                  ·
                    refine ⟨520841570838577230810161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388910855569539282160429 520841570838577230810161)
                    ·
                      rfl

theorem cell22_1521503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_1521503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521503 prefixEnd_1521503 := by exact prefixLift 1521503
  have htrace : WordTrace (prefixWord ++ tailWord_1521503) baseStart_1521503 baseEnd_1521503 := by
    simpa [prefixWord, tailWord_1521503, baseEnd_1521503] using wordTrace_append hprefix tailTrace_1521503
  have hstable : (prefixWord ++ tailWord_1521503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521503).length < 2 ^ (prefixWord ++ tailWord_1521503).sum := by decide
  have hdescent : baseEnd_1521503 < baseStart_1521503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521512 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1521512 : Nat := 118140960795 + 1521512 * 2 ^ 59
def prefixEnd_1521512 : Nat := 4983230072969 + 3 ^ 40 * 1521512 * 2
def baseEnd_1521512 : Nat := 520844651722504207335133

theorem tailTrace_1521512 : CollatzResearch.WordTrace tailWord_1521512 prefixEnd_1521512 520844651722504207335133 := by
  unfold tailWord_1521512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27747050831914676203355395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36996067775886234937807193 27747050831914676203355395)
  ·
    refine ⟨41620576247872014305033093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27747050831914676203355395 41620576247872014305033093)
    ·
      refine ⟨7803858046476002682193705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41620576247872014305033093 7803858046476002682193705)
      ·
        refine ⟨5852893534857002011645279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7803858046476002682193705 5852893534857002011645279)
        ·
          refine ⟨8779340302285503017467919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852893534857002011645279 8779340302285503017467919)
          ·
            refine ⟨13169010453428254526201879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779340302285503017467919 13169010453428254526201879)
            ·
              refine ⟨19753515680142381789302819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13169010453428254526201879 19753515680142381789302819)
              ·
                refine ⟨29630273520213572683954229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19753515680142381789302819 29630273520213572683954229)
                ·
                  refine ⟨2777838142520022439120709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29630273520213572683954229 2777838142520022439120709)
                  ·
                    refine ⟨520844651722504207335133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2777838142520022439120709 520844651722504207335133)
                    ·
                      rfl

theorem cell22_1521512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1521512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521512 prefixEnd_1521512 := by exact prefixLift 1521512
  have htrace : WordTrace (prefixWord ++ tailWord_1521512) baseStart_1521512 baseEnd_1521512 := by
    simpa [prefixWord, tailWord_1521512, baseEnd_1521512] using wordTrace_append hprefix tailTrace_1521512
  have hstable : (prefixWord ++ tailWord_1521512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521512).length < 2 ^ (prefixWord ++ tailWord_1521512).sum := by decide
  have hdescent : baseEnd_1521512 < baseStart_1521512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521546 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1521546 : Nat := 118140960795 + 1521546 * 2 ^ 59
def prefixEnd_1521546 : Nat := 4983230072969 + 3 ^ 40 * 1521546 * 2
def baseEnd_1521546 : Nat := 520856290617339451985029

theorem tailTrace_1521546 : CollatzResearch.WordTrace tailWord_1521546 prefixEnd_1521546 520856290617339451985029 := by
  unfold tailWord_1521546
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873835436426544053362123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36996894497137450808965661 13873835436426544053362123)
  ·
    refine ⟨20810753154639816080043185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13873835436426544053362123 20810753154639816080043185)
    ·
      refine ⟨15608064865979862060032389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20810753154639816080043185 15608064865979862060032389)
      ·
        refine ⟨2926512162371224136256073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15608064865979862060032389 2926512162371224136256073)
        ·
          refine ⟨2194884121778418102192055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2926512162371224136256073 2194884121778418102192055)
          ·
            refine ⟨3292326182667627153288083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194884121778418102192055 3292326182667627153288083)
            ·
              refine ⟨4938489274001440729932125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292326182667627153288083 4938489274001440729932125)
              ·
                refine ⟨1851933477750540273724547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4938489274001440729932125 1851933477750540273724547)
                ·
                  refine ⟨2777900216625810410586821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851933477750540273724547 2777900216625810410586821)
                  ·
                    refine ⟨520856290617339451985029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2777900216625810410586821 520856290617339451985029)
                    ·
                      rfl

theorem cell22_1521546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1521546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521546 prefixEnd_1521546 := by exact prefixLift 1521546
  have htrace : WordTrace (prefixWord ++ tailWord_1521546) baseStart_1521546 baseEnd_1521546 := by
    simpa [prefixWord, tailWord_1521546, baseEnd_1521546] using wordTrace_append hprefix tailTrace_1521546
  have hstable : (prefixWord ++ tailWord_1521546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521546).length < 2 ^ (prefixWord ++ tailWord_1521546).sum := by decide
  have hdescent : baseEnd_1521546 < baseStart_1521546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521557 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1521557 : Nat := 118140960795 + 1521557 * 2 ^ 59
def prefixEnd_1521557 : Nat := 4983230072969 + 3 ^ 40 * 1521557 * 2
def baseEnd_1521557 : Nat := 520860056142139089959995

theorem tailTrace_1521557 : CollatzResearch.WordTrace tailWord_1521557 prefixEnd_1521557 520860056142139089959995 := by
  unfold tailWord_1521557
  simp only [CollatzResearch.WordTrace]
  refine ⟨55495742948666325092098925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36997161965777550061399283 55495742948666325092098925)
  ·
    refine ⟨20810903605749871909537097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55495742948666325092098925 20810903605749871909537097)
    ·
      refine ⟨15608177704312403932152823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20810903605749871909537097 15608177704312403932152823)
      ·
        refine ⟨23412266556468605898229235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15608177704312403932152823 23412266556468605898229235)
        ·
          refine ⟨35118399834702908847343853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23412266556468605898229235 35118399834702908847343853)
          ·
            refine ⟨13169399938013590817753945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35118399834702908847343853 13169399938013590817753945)
            ·
              refine ⟨9877049953510193113315459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13169399938013590817753945 9877049953510193113315459)
              ·
                refine ⟨14815574930265289669973189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9877049953510193113315459 14815574930265289669973189)
                ·
                  refine ⟨2777920299424741813119973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14815574930265289669973189 2777920299424741813119973)
                  ·
                    refine ⟨520860056142139089959995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2777920299424741813119973 520860056142139089959995)
                    ·
                      rfl

theorem cell22_1521557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1521557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521557 prefixEnd_1521557 := by exact prefixLift 1521557
  have htrace : WordTrace (prefixWord ++ tailWord_1521557) baseStart_1521557 baseEnd_1521557 := by
    simpa [prefixWord, tailWord_1521557, baseEnd_1521557] using wordTrace_append hprefix tailTrace_1521557
  have hstable : (prefixWord ++ tailWord_1521557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521557).length < 2 ^ (prefixWord ++ tailWord_1521557).sum := by decide
  have hdescent : baseEnd_1521557 < baseStart_1521557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521559 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 4, 3]
def baseStart_1521559 : Nat := 118140960795 + 1521559 * 2 ^ 59
def prefixEnd_1521559 : Nat := 4983230072969 + 3 ^ 40 * 1521559 * 2
def baseEnd_1521559 : Nat := 520860740783011751409989

theorem tailTrace_1521559 : CollatzResearch.WordTrace tailWord_1521559 prefixEnd_1521559 520860740783011751409989 := by
  unfold tailWord_1521559
  simp only [CollatzResearch.WordTrace]
  refine ⟨55495815894659079433671731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36997210596439386289114487 55495815894659079433671731)
  ·
    refine ⟨83243723841988619150507597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55495815894659079433671731 83243723841988619150507597)
    ·
      refine ⟨31216396440745732181440349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83243723841988619150507597 31216396440745732181440349)
      ·
        refine ⟨11706148665279649568040131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31216396440745732181440349 11706148665279649568040131)
        ·
          refine ⟨17559222997919474352060197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11706148665279649568040131 17559222997919474352060197)
          ·
            refine ⟨3292354312109901441011287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17559222997919474352060197 3292354312109901441011287)
            ·
              refine ⟨4938531468164852161516931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292354312109901441011287 4938531468164852161516931)
              ·
                refine ⟨7407797202247278242275397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938531468164852161516931 7407797202247278242275397)
                ·
                  refine ⟨1388961975421364670426637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7407797202247278242275397 1388961975421364670426637)
                  ·
                    refine ⟨520860740783011751409989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1388961975421364670426637 520860740783011751409989)
                    ·
                      rfl

theorem cell22_1521559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_1521559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521559 prefixEnd_1521559 := by exact prefixLift 1521559
  have htrace : WordTrace (prefixWord ++ tailWord_1521559) baseStart_1521559 baseEnd_1521559 := by
    simpa [prefixWord, tailWord_1521559, baseEnd_1521559] using wordTrace_append hprefix tailTrace_1521559
  have hstable : (prefixWord ++ tailWord_1521559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521559).length < 2 ^ (prefixWord ++ tailWord_1521559).sum := by decide
  have hdescent : baseEnd_1521559 < baseStart_1521559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521589 : List Nat := [1, 3, 3, 2, 1, 2, 4, 6]
def baseStart_1521589 : Nat := 118140960795 + 1521589 * 2 ^ 59
def prefixEnd_1521589 : Nat := 4983230072969 + 3 ^ 40 * 1521589 * 2
def baseEnd_1521589 : Nat := 57874556710677963684433

theorem tailTrace_1521589 : CollatzResearch.WordTrace tailWord_1521589 prefixEnd_1521589 57874556710677963684433 := by
  unfold tailWord_1521589
  simp only [CollatzResearch.WordTrace]
  refine ⟨55496910084550394557263821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36997940056366929704842547 55496910084550394557263821)
  ·
    refine ⟨20811341281706397958973933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55496910084550394557263821 20811341281706397958973933)
    ·
      refine ⟨7804252980639899234615225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20811341281706397958973933 7804252980639899234615225)
      ·
        refine ⟨5853189735479924425961419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7804252980639899234615225 5853189735479924425961419)
        ·
          refine ⟨8779784603219886638942129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853189735479924425961419 8779784603219886638942129)
          ·
            refine ⟨6584838452414914979206597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8779784603219886638942129 6584838452414914979206597)
            ·
              refine ⟨1234657209827796558601237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6584838452414914979206597 1234657209827796558601237)
              ·
                refine ⟨57874556710677963684433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1234657209827796558601237 57874556710677963684433)
                ·
                  rfl

theorem cell22_1521589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 6].length) (baseStart_1521589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521589 prefixEnd_1521589 := by exact prefixLift 1521589
  have htrace : WordTrace (prefixWord ++ tailWord_1521589) baseStart_1521589 baseEnd_1521589 := by
    simpa [prefixWord, tailWord_1521589, baseEnd_1521589] using wordTrace_append hprefix tailTrace_1521589
  have hstable : (prefixWord ++ tailWord_1521589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521589).length < 2 ^ (prefixWord ++ tailWord_1521589).sum := by decide
  have hdescent : baseEnd_1521589 < baseStart_1521589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521621 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_1521621 : Nat := 118140960795 + 1521621 * 2 ^ 59
def prefixEnd_1521621 : Nat := 4983230072969 + 3 ^ 40 * 1521621 * 2
def baseEnd_1521621 : Nat := 520881964650064256359799

theorem tailTrace_1521621 : CollatzResearch.WordTrace tailWord_1521621 prefixEnd_1521621 520881964650064256359799 := by
  unfold tailWord_1521621
  simp only [CollatzResearch.WordTrace]
  refine ⟨55498077220434464022428717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36998718146956309348285811 55498077220434464022428717)
  ·
    refine ⟨20811778957662924008410769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55498077220434464022428717 20811778957662924008410769)
    ·
      refine ⟨15608834218247193006308077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20811778957662924008410769 15608834218247193006308077)
      ·
        refine ⟨5853312831842697377365529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15608834218247193006308077 5853312831842697377365529)
        ·
          refine ⟨4389984623882023033024147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5853312831842697377365529 4389984623882023033024147)
          ·
            refine ⟨6584976935823034549536221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389984623882023033024147 6584976935823034549536221)
            ·
              refine ⟨2469366350933637956076083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6584976935823034549536221 2469366350933637956076083)
              ·
                refine ⟨3704049526400456934114125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469366350933637956076083 3704049526400456934114125)
                ·
                  refine ⟨1389018572400171350292797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3704049526400456934114125 1389018572400171350292797)
                  ·
                    refine ⟨520881964650064256359799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389018572400171350292797 520881964650064256359799)
                    ·
                      rfl

theorem cell22_1521621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_1521621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521621 prefixEnd_1521621 := by exact prefixLift 1521621
  have htrace : WordTrace (prefixWord ++ tailWord_1521621) baseStart_1521621 baseEnd_1521621 := by
    simpa [prefixWord, tailWord_1521621, baseEnd_1521621] using wordTrace_append hprefix tailTrace_1521621
  have hstable : (prefixWord ++ tailWord_1521621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521621).length < 2 ^ (prefixWord ++ tailWord_1521621).sum := by decide
  have hdescent : baseEnd_1521621 < baseStart_1521621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521632 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_1521632 : Nat := 118140960795 + 1521632 * 2 ^ 59
def prefixEnd_1521632 : Nat := 4983230072969 + 3 ^ 40 * 1521632 * 2
def baseEnd_1521632 : Nat := 520885730174863894334765

theorem tailTrace_1521632 : CollatzResearch.WordTrace tailWord_1521632 prefixEnd_1521632 520885730174863894334765 := by
  unfold tailWord_1521632
  simp only [CollatzResearch.WordTrace]
  refine ⟨27749239211697306450539575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36998985615596408600719433 27749239211697306450539575)
  ·
    refine ⟨41623858817545959675809363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27749239211697306450539575 41623858817545959675809363)
    ·
      refine ⟨62435788226318939513714045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41623858817545959675809363 62435788226318939513714045)
      ·
        refine ⟨23413420584869602317642767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62435788226318939513714045 23413420584869602317642767)
        ·
          refine ⟨35120130877304403476464151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23413420584869602317642767 35120130877304403476464151)
          ·
            refine ⟨52680196315956605214696227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35120130877304403476464151 52680196315956605214696227)
            ·
              refine ⟨79020294473934907822044341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52680196315956605214696227 79020294473934907822044341)
              ·
                refine ⟨7408152606931397608316657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79020294473934907822044341 7408152606931397608316657)
                ·
                  refine ⟨5556114455198548206237493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7408152606931397608316657 5556114455198548206237493)
                  ·
                    refine ⟨520885730174863894334765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5556114455198548206237493 520885730174863894334765)
                    ·
                      rfl

theorem cell22_1521632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_1521632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521632 prefixEnd_1521632 := by exact prefixLift 1521632
  have htrace : WordTrace (prefixWord ++ tailWord_1521632) baseStart_1521632 baseEnd_1521632 := by
    simpa [prefixWord, tailWord_1521632, baseEnd_1521632] using wordTrace_append hprefix tailTrace_1521632
  have hstable : (prefixWord ++ tailWord_1521632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521632).length < 2 ^ (prefixWord ++ tailWord_1521632).sum := by decide
  have hdescent : baseEnd_1521632 < baseStart_1521632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521668 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1521668 : Nat := 118140960795 + 1521668 * 2 ^ 59
def prefixEnd_1521668 : Nat := 4983230072969 + 3 ^ 40 * 1521668 * 2
def baseEnd_1521668 : Nat := 173632684570190600144885

theorem tailTrace_1521668 : CollatzResearch.WordTrace tailWord_1521668 prefixEnd_1521668 173632684570190600144885 := by
  unfold tailWord_1521668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27749895725632095524694829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36999860967509460699593105 27749895725632095524694829)
  ·
    refine ⟨10406210897112035821760561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27749895725632095524694829 10406210897112035821760561)
    ·
      refine ⟨7804658172834026866320421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10406210897112035821760561 7804658172834026866320421)
      ·
        refine ⟨1463373407406380037435079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7804658172834026866320421 1463373407406380037435079)
        ·
          refine ⟨2195060111109570056152619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463373407406380037435079 2195060111109570056152619)
          ·
            refine ⟨3292590166664355084228929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195060111109570056152619 3292590166664355084228929)
            ·
              refine ⟨2469442624998266313171697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292590166664355084228929 2469442624998266313171697)
              ·
                refine ⟨1852081968748699734878773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469442624998266313171697 1852081968748699734878773)
                ·
                  refine ⟨173632684570190600144885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852081968748699734878773 173632684570190600144885)
                  ·
                    rfl

theorem cell22_1521668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1521668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521668 prefixEnd_1521668 := by exact prefixLift 1521668
  have htrace : WordTrace (prefixWord ++ tailWord_1521668) baseStart_1521668 baseEnd_1521668 := by
    simpa [prefixWord, tailWord_1521668, baseEnd_1521668] using wordTrace_append hprefix tailTrace_1521668
  have hstable : (prefixWord ++ tailWord_1521668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521668).length < 2 ^ (prefixWord ++ tailWord_1521668).sum := by decide
  have hdescent : baseEnd_1521668 < baseStart_1521668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521728 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_1521728 : Nat := 118140960795 + 1521728 * 2 ^ 59
def prefixEnd_1521728 : Nat := 4983230072969 + 3 ^ 40 * 1521728 * 2
def baseEnd_1521728 : Nat := 520918592936751643934471

theorem tailTrace_1521728 : CollatzResearch.WordTrace tailWord_1521728 prefixEnd_1521728 520918592936751643934471 := by
  unfold tailWord_1521728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27750989915523410648286919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37001319887364547531049225 27750989915523410648286919)
  ·
    refine ⟨41626484873285115972430379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27750989915523410648286919 41626484873285115972430379)
    ·
      refine ⟨62439727309927673958645569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41626484873285115972430379 62439727309927673958645569)
      ·
        refine ⟨46829795482445755468984177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62439727309927673958645569 46829795482445755468984177)
        ·
          refine ⟨35122346611834316601738133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46829795482445755468984177 35122346611834316601738133)
          ·
            refine ⟨1646359997429733590706475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35122346611834316601738133 1646359997429733590706475)
            ·
              refine ⟨2469539996144600386059713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646359997429733590706475 2469539996144600386059713)
              ·
                refine ⟨1852154997108450289544785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469539996144600386059713 1852154997108450289544785)
                ·
                  refine ⟨1389116247831337717158589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852154997108450289544785 1389116247831337717158589)
                  ·
                    refine ⟨520918592936751643934471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389116247831337717158589 520918592936751643934471)
                    ·
                      rfl

theorem cell22_1521728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_1521728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521728 prefixEnd_1521728 := by exact prefixLift 1521728
  have htrace : WordTrace (prefixWord ++ tailWord_1521728) baseStart_1521728 baseEnd_1521728 := by
    simpa [prefixWord, tailWord_1521728, baseEnd_1521728] using wordTrace_append hprefix tailTrace_1521728
  have hstable : (prefixWord ++ tailWord_1521728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521728).length < 2 ^ (prefixWord ++ tailWord_1521728).sum := by decide
  have hdescent : baseEnd_1521728 < baseStart_1521728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521739 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 7, 3]
def baseStart_1521739 : Nat := 118140960795 + 1521739 * 2 ^ 59
def prefixEnd_1521739 : Nat := 4983230072969 + 3 ^ 40 * 1521739 * 2
def baseEnd_1521739 : Nat := 520922358461551281909437

theorem tailTrace_1521739 : CollatzResearch.WordTrace tailWord_1521739 prefixEnd_1521739 520922358461551281909437 := by
  unfold tailWord_1521739
  simp only [CollatzResearch.WordTrace]
  refine ⟨55502381034006970175224271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37001587356004646783482847 55502381034006970175224271)
  ·
    refine ⟨83253571551010455262836407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55502381034006970175224271 83253571551010455262836407)
    ·
      refine ⟨124880357326515682894254611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83253571551010455262836407 124880357326515682894254611)
      ·
        refine ⟨187320535989773524341381917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124880357326515682894254611 187320535989773524341381917)
        ·
          refine ⟨70245200996165071628018219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187320535989773524341381917 70245200996165071628018219)
          ·
            refine ⟨105367801494247607442027329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70245200996165071628018219 105367801494247607442027329)
            ·
              refine ⟨79025851120685705581520497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105367801494247607442027329 79025851120685705581520497)
              ·
                refine ⟨59269388340514279186140373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79025851120685705581520497 59269388340514279186140373)
                ·
                  refine ⟨1389126289230803418425165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 59269388340514279186140373 1389126289230803418425165)
                  ·
                    refine ⟨520922358461551281909437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389126289230803418425165 520922358461551281909437)
                    ·
                      rfl

theorem cell22_1521739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 3].length) (baseStart_1521739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521739 prefixEnd_1521739 := by exact prefixLift 1521739
  have htrace : WordTrace (prefixWord ++ tailWord_1521739) baseStart_1521739 baseEnd_1521739 := by
    simpa [prefixWord, tailWord_1521739, baseEnd_1521739] using wordTrace_append hprefix tailTrace_1521739
  have hstable : (prefixWord ++ tailWord_1521739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521739).length < 2 ^ (prefixWord ++ tailWord_1521739).sum := by decide
  have hdescent : baseEnd_1521739 < baseStart_1521739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521884 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1521884 : Nat := 118140960795 + 1521884 * 2 ^ 59
def prefixEnd_1521884 : Nat := 4983230072969 + 3 ^ 40 * 1521884 * 2
def baseEnd_1521884 : Nat := 520971994924819237033993

theorem tailTrace_1521884 : CollatzResearch.WordTrace tailWord_1521884 prefixEnd_1521884 520971994924819237033993 := by
  unfold tailWord_1521884
  simp only [CollatzResearch.WordTrace]
  refine ⟨27753834809240829969626353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37005113078987773292835137 27753834809240829969626353)
  ·
    refine ⟨20815376106930622477219765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27753834809240829969626353 20815376106930622477219765)
    ·
      refine ⟨1951441510024745857239353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20815376106930622477219765 1951441510024745857239353)
      ·
        refine ⟨1463581132518559392929515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1951441510024745857239353 1463581132518559392929515)
        ·
          refine ⟨2195371698777839089394273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463581132518559392929515 2195371698777839089394273)
          ·
            refine ⟨1646528774083379317045705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195371698777839089394273 1646528774083379317045705)
            ·
              refine ⟨1234896580562534487784279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646528774083379317045705 1234896580562534487784279)
              ·
                refine ⟨1852344870843801731676419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234896580562534487784279 1852344870843801731676419)
                ·
                  refine ⟨2778517306265702597514629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852344870843801731676419 2778517306265702597514629)
                  ·
                    refine ⟨520971994924819237033993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2778517306265702597514629 520971994924819237033993)
                    ·
                      rfl

theorem cell22_1521884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1521884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521884 prefixEnd_1521884 := by exact prefixLift 1521884
  have htrace : WordTrace (prefixWord ++ tailWord_1521884) baseStart_1521884 baseEnd_1521884 := by
    simpa [prefixWord, tailWord_1521884, baseEnd_1521884] using wordTrace_append hprefix tailTrace_1521884
  have hstable : (prefixWord ++ tailWord_1521884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521884).length < 2 ^ (prefixWord ++ tailWord_1521884).sum := by decide
  have hdescent : baseEnd_1521884 < baseStart_1521884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521927 : List Nat := [1, 1, 4, 5, 2, 1, 2, 6]
def baseStart_1521927 : Nat := 118140960795 + 1521927 * 2 ^ 59
def prefixEnd_1521927 : Nat := 4983230072969 + 3 ^ 40 * 1521927 * 2
def baseEnd_1521927 : Nat := 57887412744842384245429

theorem tailTrace_1521927 : CollatzResearch.WordTrace tailWord_1521927 prefixEnd_1521927 57887412744842384245429 := by
  unfold tailWord_1521927
  simp only [CollatzResearch.WordTrace]
  refine ⟨55509237957325878283068035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37006158638217252188712023 55509237957325878283068035)
  ·
    refine ⟨83263856935988817424602053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55509237957325878283068035 83263856935988817424602053)
    ·
      refine ⟨15611973175497903267112885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83263856935988817424602053 15611973175497903267112885)
      ·
        refine ⟨1463622485202928431291833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15611973175497903267112885 1463622485202928431291833)
        ·
          refine ⟨1097716863902196323468875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463622485202928431291833 1097716863902196323468875)
          ·
            refine ⟨1646575295853294485203313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097716863902196323468875 1646575295853294485203313)
            ·
              refine ⟨1234931471889970863902485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646575295853294485203313 1234931471889970863902485)
              ·
                refine ⟨57887412744842384245429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1234931471889970863902485 57887412744842384245429)
                ·
                  rfl

theorem cell22_1521927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 6].length) (baseStart_1521927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521927 prefixEnd_1521927 := by exact prefixLift 1521927
  have htrace : WordTrace (prefixWord ++ tailWord_1521927) baseStart_1521927 baseEnd_1521927 := by
    simpa [prefixWord, tailWord_1521927, baseEnd_1521927] using wordTrace_append hprefix tailTrace_1521927
  have hstable : (prefixWord ++ tailWord_1521927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521927).length < 2 ^ (prefixWord ++ tailWord_1521927).sum := by decide
  have hdescent : baseEnd_1521927 < baseStart_1521927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521972 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1521972 : Nat := 118140960795 + 1521972 * 2 ^ 59
def prefixEnd_1521972 : Nat := 4983230072969 + 3 ^ 40 * 1521972 * 2
def baseEnd_1521972 : Nat := 173667373041072113611241

theorem tailTrace_1521972 : CollatzResearch.WordTrace tailWord_1521972 prefixEnd_1521972 173667373041072113611241 := by
  unfold tailWord_1521972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27755439621081425484228085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37007252828108567312304113 27755439621081425484228085)
  ·
    refine ⟨2602072464476383639146383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27755439621081425484228085 2602072464476383639146383)
    ·
      refine ⟨3903108696714575458719575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602072464476383639146383 3903108696714575458719575)
      ·
        refine ⟨5854663045071863188079363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903108696714575458719575 5854663045071863188079363)
        ·
          refine ⟨8781994567607794782119045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5854663045071863188079363 8781994567607794782119045)
          ·
            refine ⟨1646623981426461521647321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8781994567607794782119045 1646623981426461521647321)
            ·
              refine ⟨1234967986069846141235491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646623981426461521647321 1234967986069846141235491)
              ·
                refine ⟨1852451979104769211853237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234967986069846141235491 1852451979104769211853237)
                ·
                  refine ⟨173667373041072113611241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852451979104769211853237 173667373041072113611241)
                  ·
                    rfl

theorem cell22_1521972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1521972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521972 prefixEnd_1521972 := by exact prefixLift 1521972
  have htrace : WordTrace (prefixWord ++ tailWord_1521972) baseStart_1521972 baseEnd_1521972 := by
    simpa [prefixWord, tailWord_1521972, baseEnd_1521972] using wordTrace_append hprefix tailTrace_1521972
  have hstable : (prefixWord ++ tailWord_1521972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521972).length < 2 ^ (prefixWord ++ tailWord_1521972).sum := by decide
  have hdescent : baseEnd_1521972 < baseStart_1521972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521985 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1521985 : Nat := 118140960795 + 1521985 * 2 ^ 59
def prefixEnd_1521985 : Nat := 4983230072969 + 3 ^ 40 * 1521985 * 2
def baseEnd_1521985 : Nat := 521006569288888640258683

theorem tailTrace_1521985 : CollatzResearch.WordTrace tailWord_1521985 prefixEnd_1521985 521006569288888640258683 := by
  unfold tailWord_1521985
  simp only [CollatzResearch.WordTrace]
  refine ⟨55511353391115754188679409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37007568927410502792452939 55511353391115754188679409)
  ·
    refine ⟨41633515043336815641509557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55511353391115754188679409 41633515043336815641509557)
    ·
      refine ⟨3903142035312826466391521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41633515043336815641509557 3903142035312826466391521)
      ·
        refine ⟨2927356526484619849793641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3903142035312826466391521 2927356526484619849793641)
        ·
          refine ⟨2195517394863464887345231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927356526484619849793641 2195517394863464887345231)
          ·
            refine ⟨3293276092295197331017847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195517394863464887345231 3293276092295197331017847)
            ·
              refine ⟨4939914138442795996526771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293276092295197331017847 4939914138442795996526771)
              ·
                refine ⟨7409871207664193994790157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939914138442795996526771 7409871207664193994790157)
                ·
                  refine ⟨2778701702874072748046309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7409871207664193994790157 2778701702874072748046309)
                  ·
                    refine ⟨521006569288888640258683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2778701702874072748046309 521006569288888640258683)
                    ·
                      rfl

theorem cell22_1521985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1521985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521985 prefixEnd_1521985 := by exact prefixLift 1521985
  have htrace : WordTrace (prefixWord ++ tailWord_1521985) baseStart_1521985 baseEnd_1521985 := by
    simpa [prefixWord, tailWord_1521985, baseEnd_1521985] using wordTrace_append hprefix tailTrace_1521985
  have hstable : (prefixWord ++ tailWord_1521985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521985).length < 2 ^ (prefixWord ++ tailWord_1521985).sum := by decide
  have hdescent : baseEnd_1521985 < baseStart_1521985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521998 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_1521998 : Nat := 118140960795 + 1521998 * 2 ^ 59
def prefixEnd_1521998 : Nat := 4983230072969 + 3 ^ 40 * 1521998 * 2
def baseEnd_1521998 : Nat := 521011019454560939683643

theorem tailTrace_1521998 : CollatzResearch.WordTrace tailWord_1521998 prefixEnd_1521998 521011019454560939683643 := by
  unfold tailWord_1521998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938978442508582176112831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37007885026712438272601765 6938978442508582176112831)
  ·
    refine ⟨10408467663762873264169247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6938978442508582176112831 10408467663762873264169247)
    ·
      refine ⟨15612701495644309896253871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10408467663762873264169247 15612701495644309896253871)
      ·
        refine ⟨23419052243466464844380807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15612701495644309896253871 23419052243466464844380807)
        ·
          refine ⟨35128578365199697266571211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23419052243466464844380807 35128578365199697266571211)
          ·
            refine ⟨52692867547799545899856817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35128578365199697266571211 52692867547799545899856817)
            ·
              refine ⟨39519650660849659424892613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52692867547799545899856817 39519650660849659424892613)
              ·
                refine ⟨7409934498909311142167365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39519650660849659424892613 7409934498909311142167365)
                ·
                  refine ⟨1389362718545495839156381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7409934498909311142167365 1389362718545495839156381)
                  ·
                    refine ⟨521011019454560939683643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389362718545495839156381 521011019454560939683643)
                    ·
                      rfl

theorem cell22_1521998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_1521998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1521998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1521998 prefixEnd_1521998 := by exact prefixLift 1521998
  have htrace : WordTrace (prefixWord ++ tailWord_1521998) baseStart_1521998 baseEnd_1521998 := by
    simpa [prefixWord, tailWord_1521998, baseEnd_1521998] using wordTrace_append hprefix tailTrace_1521998
  have hstable : (prefixWord ++ tailWord_1521998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521998).length < 2 ^ (prefixWord ++ tailWord_1521998).sum := by decide
  have hdescent : baseEnd_1521998 < baseStart_1521998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522041 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_1522041 : Nat := 118140960795 + 1522041 * 2 ^ 59
def prefixEnd_1522041 : Nat := 4983230072969 + 3 ^ 40 * 1522041 * 2
def baseEnd_1522041 : Nat := 521025739233323160858511

theorem tailTrace_1522041 : CollatzResearch.WordTrace tailWord_1522041 prefixEnd_1522041 521025739233323160858511 := by
  unfold tailWord_1522041
  simp only [CollatzResearch.WordTrace]
  refine ⟨55513395878912875752717977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37008930585941917168478651 55513395878912875752717977)
  ·
    refine ⟨41635046909184656814538483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55513395878912875752717977 41635046909184656814538483)
    ·
      refine ⟨62452570363776985221807725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41635046909184656814538483 62452570363776985221807725)
      ·
        refine ⟨23419713886416369458177897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62452570363776985221807725 23419713886416369458177897)
        ·
          refine ⟨17564785414812277093633423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23419713886416369458177897 17564785414812277093633423)
          ·
            refine ⟨26347178122218415640450135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17564785414812277093633423 26347178122218415640450135)
            ·
              refine ⟨39520767183327623460675203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26347178122218415640450135 39520767183327623460675203)
              ·
                refine ⟨59281150774991435191012805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39520767183327623460675203 59281150774991435191012805)
                ·
                  refine ⟨11115215770310894098314901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59281150774991435191012805 11115215770310894098314901)
                  ·
                    refine ⟨521025739233323160858511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11115215770310894098314901 521025739233323160858511)
                    ·
                      rfl

theorem cell22_1522041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_1522041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522041 prefixEnd_1522041 := by exact prefixLift 1522041
  have htrace : WordTrace (prefixWord ++ tailWord_1522041) baseStart_1522041 baseEnd_1522041 := by
    simpa [prefixWord, tailWord_1522041, baseEnd_1522041] using wordTrace_append hprefix tailTrace_1522041
  have hstable : (prefixWord ++ tailWord_1522041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522041).length < 2 ^ (prefixWord ++ tailWord_1522041).sum := by decide
  have hdescent : baseEnd_1522041 < baseStart_1522041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522043 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 5, 3]
def baseStart_1522043 : Nat := 118140960795 + 1522043 * 2 ^ 59
def prefixEnd_1522043 : Nat := 4983230072969 + 3 ^ 40 * 1522043 * 2
def baseEnd_1522043 : Nat := 521026423874195822308505

theorem tailTrace_1522043 : CollatzResearch.WordTrace tailWord_1522043 prefixEnd_1522043 521026423874195822308505 := by
  unfold tailWord_1522043
  simp only [CollatzResearch.WordTrace]
  refine ⟨55513468824905630094290783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37008979216603753396193855 55513468824905630094290783)
  ·
    refine ⟨83270203237358445141436175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55513468824905630094290783 83270203237358445141436175)
    ·
      refine ⟨124905304856037667712154263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83270203237358445141436175 124905304856037667712154263)
      ·
        refine ⟨187357957284056501568231395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124905304856037667712154263 187357957284056501568231395)
        ·
          refine ⟨281036935926084752352347093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187357957284056501568231395 281036935926084752352347093)
          ·
            refine ⟨6586803185767611383258135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 281036935926084752352347093 6586803185767611383258135)
            ·
              refine ⟨9880204778651417074887203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586803185767611383258135 9880204778651417074887203)
              ·
                refine ⟨14820307167977125612330805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9880204778651417074887203 14820307167977125612330805)
                ·
                  refine ⟨1389403796997855526156013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14820307167977125612330805 1389403796997855526156013)
                  ·
                    refine ⟨521026423874195822308505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389403796997855526156013 521026423874195822308505)
                    ·
                      rfl

theorem cell22_1522043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 3].length) (baseStart_1522043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522043 prefixEnd_1522043 := by exact prefixLift 1522043
  have htrace : WordTrace (prefixWord ++ tailWord_1522043) baseStart_1522043 baseEnd_1522043 := by
    simpa [prefixWord, tailWord_1522043, baseEnd_1522043] using wordTrace_append hprefix tailTrace_1522043
  have hstable : (prefixWord ++ tailWord_1522043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522043).length < 2 ^ (prefixWord ++ tailWord_1522043).sum := by decide
  have hdescent : baseEnd_1522043 < baseStart_1522043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522077 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1522077 : Nat := 118140960795 + 1522077 * 2 ^ 59
def prefixEnd_1522077 : Nat := 4983230072969 + 3 ^ 40 * 1522077 * 2
def baseEnd_1522077 : Nat := 521038062769031066958401

theorem tailTrace_1522077 : CollatzResearch.WordTrace tailWord_1522077 prefixEnd_1522077 521038062769031066958401 := by
  unfold tailWord_1522077
  simp only [CollatzResearch.WordTrace]
  refine ⟨55514708906782453901028485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37009805937854969267352323 55514708906782453901028485)
  ·
    refine ⟨10409007920021710106442841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55514708906782453901028485 10409007920021710106442841)
    ·
      refine ⟨7806755940016282579832131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10409007920021710106442841 7806755940016282579832131)
      ·
        refine ⟨11710133910024423869748197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7806755940016282579832131 11710133910024423869748197)
        ·
          refine ⟨2195650108129579475577787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11710133910024423869748197 2195650108129579475577787)
          ·
            refine ⟨3293475162194369213366681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195650108129579475577787 3293475162194369213366681)
            ·
              refine ⟨2470106371645776910025011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3293475162194369213366681 2470106371645776910025011)
              ·
                refine ⟨3705159557468665365037517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470106371645776910025011 3705159557468665365037517)
                ·
                  refine ⟨1389434834050749511889069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3705159557468665365037517 1389434834050749511889069)
                  ·
                    refine ⟨521038062769031066958401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389434834050749511889069 521038062769031066958401)
                    ·
                      rfl

theorem cell22_1522077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1522077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522077 prefixEnd_1522077 := by exact prefixLift 1522077
  have htrace : WordTrace (prefixWord ++ tailWord_1522077) baseStart_1522077 baseEnd_1522077 := by
    simpa [prefixWord, tailWord_1522077, baseEnd_1522077] using wordTrace_append hprefix tailTrace_1522077
  have hstable : (prefixWord ++ tailWord_1522077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522077).length < 2 ^ (prefixWord ++ tailWord_1522077).sum := by decide
  have hdescent : baseEnd_1522077 < baseStart_1522077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522120 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_1522120 : Nat := 118140960795 + 1522120 * 2 ^ 59
def prefixEnd_1522120 : Nat := 4983230072969 + 3 ^ 40 * 1522120 * 2
def baseEnd_1522120 : Nat := 521052782547793288133269

theorem tailTrace_1522120 : CollatzResearch.WordTrace tailWord_1522120 prefixEnd_1522120 521052782547793288133269 := by
  unfold tailWord_1522120
  simp only [CollatzResearch.WordTrace]
  refine ⟨27758138622813336122421907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37010851497084448163229209 27758138622813336122421907)
  ·
    refine ⟨41637207934220004183632861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27758138622813336122421907 41637207934220004183632861)
    ·
      refine ⟨15613952975332501568862323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41637207934220004183632861 15613952975332501568862323)
      ·
        refine ⟨23420929462998752353293485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15613952975332501568862323 23420929462998752353293485)
        ·
          refine ⟨8782848548624532132485057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23420929462998752353293485 8782848548624532132485057)
          ·
            refine ⟨6587136411468399099363793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8782848548624532132485057 6587136411468399099363793)
            ·
              refine ⟨4940352308601299324522845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6587136411468399099363793 4940352308601299324522845)
              ·
                refine ⟨1852632115725487246696067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4940352308601299324522845 1852632115725487246696067)
                ·
                  refine ⟨2778948173588230870044101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852632115725487246696067 2778948173588230870044101)
                  ·
                    refine ⟨521052782547793288133269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2778948173588230870044101 521052782547793288133269)
                    ·
                      rfl

theorem cell22_1522120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_1522120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522120 prefixEnd_1522120 := by exact prefixLift 1522120
  have htrace : WordTrace (prefixWord ++ tailWord_1522120) baseStart_1522120 baseEnd_1522120 := by
    simpa [prefixWord, tailWord_1522120, baseEnd_1522120] using wordTrace_append hprefix tailTrace_1522120
  have hstable : (prefixWord ++ tailWord_1522120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522120).length < 2 ^ (prefixWord ++ tailWord_1522120).sum := by decide
  have hdescent : baseEnd_1522120 < baseStart_1522120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522195 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 3, 3]
def baseStart_1522195 : Nat := 118140960795 + 1522195 * 2 ^ 59
def prefixEnd_1522195 : Nat := 4983230072969 + 3 ^ 40 * 1522195 * 2
def baseEnd_1522195 : Nat := 521078456580518092508039

theorem tailTrace_1522195 : CollatzResearch.WordTrace tailWord_1522195 prefixEnd_1522195 521078456580518092508039 := by
  unfold tailWord_1522195
  simp only [CollatzResearch.WordTrace]
  refine ⟨55519012720354960053824039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37012675146903306702549359 55519012720354960053824039)
  ·
    refine ⟨83278519080532440080736059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55519012720354960053824039 83278519080532440080736059)
    ·
      refine ⟨124917778620798660121104089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83278519080532440080736059 124917778620798660121104089)
      ·
        refine ⟨93688333965598995090828067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124917778620798660121104089 93688333965598995090828067)
        ·
          refine ⟨140532500948398492636242101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93688333965598995090828067 140532500948398492636242101)
          ·
            refine ⟨13174921963912358684647697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140532500948398492636242101 13174921963912358684647697)
            ·
              refine ⟨9881191472934269013485773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13174921963912358684647697 9881191472934269013485773)
              ·
                refine ⟨3705446802350350880057165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9881191472934269013485773 3705446802350350880057165)
                ·
                  refine ⟨1389542550881381580021437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3705446802350350880057165 1389542550881381580021437)
                  ·
                    refine ⟨521078456580518092508039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389542550881381580021437 521078456580518092508039)
                    ·
                      rfl

theorem cell22_1522195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 3].length) (baseStart_1522195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522195 prefixEnd_1522195 := by exact prefixLift 1522195
  have htrace : WordTrace (prefixWord ++ tailWord_1522195) baseStart_1522195 baseEnd_1522195 := by
    simpa [prefixWord, tailWord_1522195, baseEnd_1522195] using wordTrace_append hprefix tailTrace_1522195
  have hstable : (prefixWord ++ tailWord_1522195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522195).length < 2 ^ (prefixWord ++ tailWord_1522195).sum := by decide
  have hdescent : baseEnd_1522195 < baseStart_1522195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522229 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1522229 : Nat := 118140960795 + 1522229 * 2 ^ 59
def prefixEnd_1522229 : Nat := 4983230072969 + 3 ^ 40 * 1522229 * 2
def baseEnd_1522229 : Nat := 521090095475353337157935

theorem tailTrace_1522229 : CollatzResearch.WordTrace tailWord_1522229 prefixEnd_1522229 521090095475353337157935 := by
  unfold tailWord_1522229
  simp only [CollatzResearch.WordTrace]
  refine ⟨55520252802231783860561741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37013501868154522573707827 55520252802231783860561741)
  ·
    refine ⟨20820094800836918947710653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55520252802231783860561741 20820094800836918947710653)
    ·
      refine ⟨7807535550313844605391495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20820094800836918947710653 7807535550313844605391495)
      ·
        refine ⟨11711303325470766908087243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7807535550313844605391495 11711303325470766908087243)
        ·
          refine ⟨17566954988206150362130865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11711303325470766908087243 17566954988206150362130865)
          ·
            refine ⟨13175216241154612771598149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17566954988206150362130865 13175216241154612771598149)
            ·
              refine ⟨2470353045216489894674653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13175216241154612771598149 2470353045216489894674653)
              ·
                refine ⟨926382391956183710502995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2470353045216489894674653 926382391956183710502995)
                ·
                  refine ⟨1389573587934275565754493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926382391956183710502995 1389573587934275565754493)
                  ·
                    refine ⟨521090095475353337157935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389573587934275565754493 521090095475353337157935)
                    ·
                      rfl

theorem cell22_1522229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1522229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522229 prefixEnd_1522229 := by exact prefixLift 1522229
  have htrace : WordTrace (prefixWord ++ tailWord_1522229) baseStart_1522229 baseEnd_1522229 := by
    simpa [prefixWord, tailWord_1522229, baseEnd_1522229] using wordTrace_append hprefix tailTrace_1522229
  have hstable : (prefixWord ++ tailWord_1522229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522229).length < 2 ^ (prefixWord ++ tailWord_1522229).sum := by decide
  have hdescent : baseEnd_1522229 < baseStart_1522229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522246 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1522246 : Nat := 118140960795 + 1522246 * 2 ^ 59
def prefixEnd_1522246 : Nat := 4983230072969 + 3 ^ 40 * 1522246 * 2
def baseEnd_1522246 : Nat := 521095914922770959482883

theorem tailTrace_1522246 : CollatzResearch.WordTrace tailWord_1522246 prefixEnd_1522246 521095914922770959482883 := by
  unfold tailWord_1522246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735027276349068617622831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37013915228780130509287061 1735027276349068617622831)
  ·
    refine ⟨2602540914523602926434247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735027276349068617622831 2602540914523602926434247)
    ·
      refine ⟨3903811371785404389651371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602540914523602926434247 3903811371785404389651371)
      ·
        refine ⟨5855717057678106584477057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903811371785404389651371 5855717057678106584477057)
        ·
          refine ⟨4391787793258579938357793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5855717057678106584477057 4391787793258579938357793)
          ·
            refine ⟨3293840844943934953768345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4391787793258579938357793 3293840844943934953768345)
            ·
              refine ⟨2470380633707951215326259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3293840844943934953768345 2470380633707951215326259)
              ·
                refine ⟨3705570950561926822989389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470380633707951215326259 3705570950561926822989389)
                ·
                  refine ⟨1389589106460722558621021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3705570950561926822989389 1389589106460722558621021)
                  ·
                    refine ⟨521095914922770959482883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389589106460722558621021 521095914922770959482883)
                    ·
                      rfl

theorem cell22_1522246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1522246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522246 prefixEnd_1522246 := by exact prefixLift 1522246
  have htrace : WordTrace (prefixWord ++ tailWord_1522246) baseStart_1522246 baseEnd_1522246 := by
    simpa [prefixWord, tailWord_1522246, baseEnd_1522246] using wordTrace_append hprefix tailTrace_1522246
  have hstable : (prefixWord ++ tailWord_1522246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522246).length < 2 ^ (prefixWord ++ tailWord_1522246).sum := by decide
  have hdescent : baseEnd_1522246 < baseStart_1522246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522287 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 4]
def baseStart_1522287 : Nat := 118140960795 + 1522287 * 2 ^ 59
def prefixEnd_1522287 : Nat := 4983230072969 + 3 ^ 40 * 1522287 * 2
def baseEnd_1522287 : Nat := 173703316686886839735919

theorem tailTrace_1522287 : CollatzResearch.WordTrace tailWord_1522287 prefixEnd_1522287 173703316686886839735919 := by
  unfold tailWord_1522287
  simp only [CollatzResearch.WordTrace]
  refine ⟨55522368236021659766173115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37014912157347773177448743 55522368236021659766173115)
  ·
    refine ⟨83283552354032489649259673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55522368236021659766173115 83283552354032489649259673)
    ·
      refine ⟨62462664265524367236944755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83283552354032489649259673 62462664265524367236944755)
      ·
        refine ⟨93693996398286550855417133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62462664265524367236944755 93693996398286550855417133)
        ·
          refine ⟨35135248649357456570781425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93693996398286550855417133 35135248649357456570781425)
          ·
            refine ⟨26351436487018092428086069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35135248649357456570781425 26351436487018092428086069)
            ·
              refine ⟨2470447170657946165133069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26351436487018092428086069 2470447170657946165133069)
              ·
                refine ⟨926417688996729811924901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2470447170657946165133069 926417688996729811924901)
                ·
                  refine ⟨173703316686886839735919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 926417688996729811924901 173703316686886839735919)
                  ·
                    rfl

theorem cell22_1522287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 4].length) (baseStart_1522287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522287 prefixEnd_1522287 := by exact prefixLift 1522287
  have htrace : WordTrace (prefixWord ++ tailWord_1522287) baseStart_1522287 baseEnd_1522287 := by
    simpa [prefixWord, tailWord_1522287, baseEnd_1522287] using wordTrace_append hprefix tailTrace_1522287
  have hstable : (prefixWord ++ tailWord_1522287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522287).length < 2 ^ (prefixWord ++ tailWord_1522287).sum := by decide
  have hdescent : baseEnd_1522287 < baseStart_1522287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522300 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1522300 : Nat := 118140960795 + 1522300 * 2 ^ 59
def prefixEnd_1522300 : Nat := 4983230072969 + 3 ^ 40 * 1522300 * 2
def baseEnd_1522300 : Nat := 521114400226332818632717

theorem tailTrace_1522300 : CollatzResearch.WordTrace tailWord_1522300 prefixEnd_1522300 521114400226332818632717 := by
  unfold tailWord_1522300
  simp only [CollatzResearch.WordTrace]
  refine ⟨27761421192487281493198177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37015228256649708657597569 27761421192487281493198177)
  ·
    refine ⟨20821065894365461119898633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27761421192487281493198177 20821065894365461119898633)
    ·
      refine ⟨15615799420774095839923975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20821065894365461119898633 15615799420774095839923975)
      ·
        refine ⟨23423699131161143759885963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15615799420774095839923975 23423699131161143759885963)
        ·
          refine ⟨35135548696741715639828945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23423699131161143759885963 35135548696741715639828945)
          ·
            refine ⟨26351661522556286729871709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35135548696741715639828945 26351661522556286729871709)
            ·
              refine ⟨9881873070958607523701891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26351661522556286729871709 9881873070958607523701891)
              ·
                refine ⟨14822809606437911285552837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881873070958607523701891 14822809606437911285552837)
                ·
                  refine ⟨2779276801207108366041157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14822809606437911285552837 2779276801207108366041157)
                  ·
                    refine ⟨521114400226332818632717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2779276801207108366041157 521114400226332818632717)
                    ·
                      rfl

theorem cell22_1522300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1522300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522300 prefixEnd_1522300 := by exact prefixLift 1522300
  have htrace : WordTrace (prefixWord ++ tailWord_1522300) baseStart_1522300 baseEnd_1522300 := by
    simpa [prefixWord, tailWord_1522300, baseEnd_1522300] using wordTrace_append hprefix tailTrace_1522300
  have hstable : (prefixWord ++ tailWord_1522300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522300).length < 2 ^ (prefixWord ++ tailWord_1522300).sum := by decide
  have hdescent : baseEnd_1522300 < baseStart_1522300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522304 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 4]
def baseStart_1522304 : Nat := 118140960795 + 1522304 * 2 ^ 59
def prefixEnd_1522304 : Nat := 4983230072969 + 3 ^ 40 * 1522304 * 2
def baseEnd_1522304 : Nat := 173705256502692713844235

theorem tailTrace_1522304 : CollatzResearch.WordTrace tailWord_1522304 prefixEnd_1522304 173705256502692713844235 := by
  unfold tailWord_1522304
  simp only [CollatzResearch.WordTrace]
  refine ⟨27761494138480035834770983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37015325517973381113027977 27761494138480035834770983)
  ·
    refine ⟨41642241207720053752156475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27761494138480035834770983 41642241207720053752156475)
    ·
      refine ⟨62463361811580080628234713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41642241207720053752156475 62463361811580080628234713)
      ·
        refine ⟨46847521358685060471176035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62463361811580080628234713 46847521358685060471176035)
        ·
          refine ⟨70271282038027590706764053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46847521358685060471176035 70271282038027590706764053)
          ·
            refine ⟨3293966345532543314379565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70271282038027590706764053 3293966345532543314379565)
            ·
              refine ⟨1235237379574703742892337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3293966345532543314379565 1235237379574703742892337)
              ·
                refine ⟨926428034681027807169253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235237379574703742892337 926428034681027807169253)
                ·
                  refine ⟨173705256502692713844235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 926428034681027807169253 173705256502692713844235)
                  ·
                    rfl

theorem cell22_1522304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_1522304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522304 prefixEnd_1522304 := by exact prefixLift 1522304
  have htrace : WordTrace (prefixWord ++ tailWord_1522304) baseStart_1522304 baseEnd_1522304 := by
    simpa [prefixWord, tailWord_1522304, baseEnd_1522304] using wordTrace_append hprefix tailTrace_1522304
  have hstable : (prefixWord ++ tailWord_1522304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522304).length < 2 ^ (prefixWord ++ tailWord_1522304).sum := by decide
  have hdescent : baseEnd_1522304 < baseStart_1522304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522334 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1522334 : Nat := 118140960795 + 1522334 * 2 ^ 59
def prefixEnd_1522334 : Nat := 4983230072969 + 3 ^ 40 * 1522334 * 2
def baseEnd_1522334 : Nat := 521126039121168063282613

theorem tailTrace_1522334 : CollatzResearch.WordTrace tailWord_1522334 prefixEnd_1522334 521126039121168063282613 := by
  unfold tailWord_1522334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940510308356423349141757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37016054977900924528756037 6940510308356423349141757)
  ·
    refine ⟨2602691365633658755928159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6940510308356423349141757 2602691365633658755928159)
    ·
      refine ⟨3904037048450488133892239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602691365633658755928159 3904037048450488133892239)
      ·
        refine ⟨5856055572675732200838359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904037048450488133892239 5856055572675732200838359)
        ·
          refine ⟨8784083359013598301257539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856055572675732200838359 8784083359013598301257539)
          ·
            refine ⟨13176125038520397451886309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8784083359013598301257539 13176125038520397451886309)
            ·
              refine ⟨2470523444722574522228683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13176125038520397451886309 2470523444722574522228683)
              ·
                refine ⟨3705785167083861783343025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470523444722574522228683 3705785167083861783343025)
                ·
                  refine ⟨2779338875312896337507269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705785167083861783343025 2779338875312896337507269)
                  ·
                    refine ⟨521126039121168063282613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2779338875312896337507269 521126039121168063282613)
                    ·
                      rfl

theorem cell22_1522334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1522334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522334 prefixEnd_1522334 := by exact prefixLift 1522334
  have htrace : WordTrace (prefixWord ++ tailWord_1522334) baseStart_1522334 baseEnd_1522334 := by
    simpa [prefixWord, tailWord_1522334, baseEnd_1522334] using wordTrace_append hprefix tailTrace_1522334
  have hstable : (prefixWord ++ tailWord_1522334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522334).length < 2 ^ (prefixWord ++ tailWord_1522334).sum := by decide
  have hdescent : baseEnd_1522334 < baseStart_1522334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522527 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_1522527 : Nat := 118140960795 + 1522527 * 2 ^ 59
def prefixEnd_1522527 : Nat := 4983230072969 + 3 ^ 40 * 1522527 * 2
def baseEnd_1522527 : Nat := 521192106965379893207021

theorem tailTrace_1522527 : CollatzResearch.WordTrace tailWord_1522527 prefixEnd_1522527 521192106965379893207021 := by
  unfold tailWord_1522527
  simp only [CollatzResearch.WordTrace]
  refine ⟨55531121755152180754909835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37020747836768120503273223 55531121755152180754909835)
  ·
    refine ⟨83296682632728271132364753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55531121755152180754909835 83296682632728271132364753)
    ·
      refine ⟨62472511974546203349273565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83296682632728271132364753 62472511974546203349273565)
      ·
        refine ⟨23427191990454826255977587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62472511974546203349273565 23427191990454826255977587)
        ·
          refine ⟨35140787985682239383966381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23427191990454826255977587 35140787985682239383966381)
          ·
            refine ⟨13177795494630839768987393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35140787985682239383966381 13177795494630839768987393)
            ·
              refine ⟨9883346620973129826740545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13177795494630839768987393 9883346620973129826740545)
              ·
                refine ⟨7412509965729847370055409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9883346620973129826740545 7412509965729847370055409)
                ·
                  refine ⟨5559382474297385527541557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412509965729847370055409 5559382474297385527541557)
                  ·
                    refine ⟨521192106965379893207021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5559382474297385527541557 521192106965379893207021)
                    ·
                      rfl

theorem cell22_1522527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_1522527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522527 prefixEnd_1522527 := by exact prefixLift 1522527
  have htrace : WordTrace (prefixWord ++ tailWord_1522527) baseStart_1522527 baseEnd_1522527 := by
    simpa [prefixWord, tailWord_1522527, baseEnd_1522527] using wordTrace_append hprefix tailTrace_1522527
  have hstable : (prefixWord ++ tailWord_1522527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522527).length < 2 ^ (prefixWord ++ tailWord_1522527).sum := by decide
  have hdescent : baseEnd_1522527 < baseStart_1522527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522533 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_1522533 : Nat := 118140960795 + 1522533 * 2 ^ 59
def prefixEnd_1522533 : Nat := 4983230072969 + 3 ^ 40 * 1522533 * 2
def baseEnd_1522533 : Nat := 521194160887997877557003

theorem tailTrace_1522533 : CollatzResearch.WordTrace tailWord_1522533 prefixEnd_1522533 521194160887997877557003 := by
  unfold tailWord_1522533
  simp only [CollatzResearch.WordTrace]
  refine ⟨55531340593130443779628253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37020893728753629186418835 55531340593130443779628253)
  ·
    refine ⟨20824252722423916417360595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55531340593130443779628253 20824252722423916417360595)
    ·
      refine ⟨31236379083635874626040893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20824252722423916417360595 31236379083635874626040893)
      ·
        refine ⟨11713642156363452984765335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31236379083635874626040893 11713642156363452984765335)
        ·
          refine ⟨17570463234545179477148003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11713642156363452984765335 17570463234545179477148003)
          ·
            refine ⟨26355694851817769215722005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17570463234545179477148003 26355694851817769215722005)
            ·
              refine ⟨1235423196178957931986969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26355694851817769215722005 1235423196178957931986969)
              ·
                refine ⟨926567397134218448990227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235423196178957931986969 926567397134218448990227)
                ·
                  refine ⟨1389851095701327673485341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926567397134218448990227 1389851095701327673485341)
                  ·
                    refine ⟨521194160887997877557003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389851095701327673485341 521194160887997877557003)
                    ·
                      rfl

theorem cell22_1522533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_1522533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522533 prefixEnd_1522533 := by exact prefixLift 1522533
  have htrace : WordTrace (prefixWord ++ tailWord_1522533) baseStart_1522533 baseEnd_1522533 := by
    simpa [prefixWord, tailWord_1522533, baseEnd_1522533] using wordTrace_append hprefix tailTrace_1522533
  have hstable : (prefixWord ++ tailWord_1522533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522533).length < 2 ^ (prefixWord ++ tailWord_1522533).sum := by decide
  have hdescent : baseEnd_1522533 < baseStart_1522533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522557 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 8]
def baseStart_1522557 : Nat := 118140960795 + 1522557 * 2 ^ 59
def prefixEnd_1522557 : Nat := 4983230072969 + 3 ^ 40 * 1522557 * 2
def baseEnd_1522557 : Nat := 173734125526156604985643

theorem tailTrace_1522557 : CollatzResearch.WordTrace tailWord_1522557 prefixEnd_1522557 173734125526156604985643 := by
  unfold tailWord_1522557
  simp only [CollatzResearch.WordTrace]
  refine ⟨55532215945043495878501925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37021477296695663919001283 55532215945043495878501925)
  ·
    refine ⟨10412290489695655477219111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55532215945043495878501925 10412290489695655477219111)
    ·
      refine ⟨15618435734543483215828667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10412290489695655477219111 15618435734543483215828667)
      ·
        refine ⟨23427653601815224823743001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618435734543483215828667 23427653601815224823743001)
        ·
          refine ⟨17570740201361418617807251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23427653601815224823743001 17570740201361418617807251)
          ·
            refine ⟨26356110302042127926710877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17570740201361418617807251 26356110302042127926710877)
            ·
              refine ⟨9883541363265797972516579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26356110302042127926710877 9883541363265797972516579)
              ·
                refine ⟨14825312044898696958774869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9883541363265797972516579 14825312044898696958774869)
                ·
                  refine ⟨173734125526156604985643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14825312044898696958774869 173734125526156604985643)
                  ·
                    rfl

theorem cell22_1522557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_1522557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522557 prefixEnd_1522557 := by exact prefixLift 1522557
  have htrace : WordTrace (prefixWord ++ tailWord_1522557) baseStart_1522557 baseEnd_1522557 := by
    simpa [prefixWord, tailWord_1522557, baseEnd_1522557] using wordTrace_append hprefix tailTrace_1522557
  have hstable : (prefixWord ++ tailWord_1522557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522557).length < 2 ^ (prefixWord ++ tailWord_1522557).sum := by decide
  have hdescent : baseEnd_1522557 < baseStart_1522557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522591 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 4]
def baseStart_1522591 : Nat := 118140960795 + 1522591 * 2 ^ 59
def prefixEnd_1522591 : Nat := 4983230072969 + 3 ^ 40 * 1522591 * 2
def baseEnd_1522591 : Nat := 173738005157768353202275

theorem tailTrace_1522591 : CollatzResearch.WordTrace tailWord_1522591 prefixEnd_1522591 173738005157768353202275 := by
  unfold tailWord_1522591
  simp only [CollatzResearch.WordTrace]
  refine ⟨55533456026920319685239627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37022304017946879790159751 55533456026920319685239627)
  ·
    refine ⟨83300184040380479527859441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55533456026920319685239627 83300184040380479527859441)
    ·
      refine ⟨62475138030285359645894581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83300184040380479527859441 62475138030285359645894581)
      ·
        refine ⟨5857044190339252466802617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62475138030285359645894581 5857044190339252466802617)
        ·
          refine ⟨4392783142754439350101963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857044190339252466802617 4392783142754439350101963)
          ·
            refine ⟨6589174714131659025152945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392783142754439350101963 6589174714131659025152945)
            ·
              refine ⟨4941881035598744268864709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6589174714131659025152945 4941881035598744268864709)
              ·
                refine ⟨926602694174764550412133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4941881035598744268864709 926602694174764550412133)
                ·
                  refine ⟨173738005157768353202275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 926602694174764550412133 173738005157768353202275)
                  ·
                    rfl

theorem cell22_1522591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 4].length) (baseStart_1522591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522591 prefixEnd_1522591 := by exact prefixLift 1522591
  have htrace : WordTrace (prefixWord ++ tailWord_1522591) baseStart_1522591 baseEnd_1522591 := by
    simpa [prefixWord, tailWord_1522591, baseEnd_1522591] using wordTrace_append hprefix tailTrace_1522591
  have hstable : (prefixWord ++ tailWord_1522591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522591).length < 2 ^ (prefixWord ++ tailWord_1522591).sum := by decide
  have hdescent : baseEnd_1522591 < baseStart_1522591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522702 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_1522702 : Nat := 118140960795 + 1522702 * 2 ^ 59
def prefixEnd_1522702 : Nat := 4983230072969 + 3 ^ 40 * 1522702 * 2
def baseEnd_1522702 : Nat := 521252013041737770081485

theorem tailTrace_1522702 : CollatzResearch.WordTrace tailWord_1522702 prefixEnd_1522702 521252013041737770081485 := by
  unfold tailWord_1522702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942188066189773205316295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37025003019678790428353573 6942188066189773205316295)
  ·
    refine ⟨10413282099284659807974443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942188066189773205316295 10413282099284659807974443)
    ·
      refine ⟨15619923148926989711961665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10413282099284659807974443 15619923148926989711961665)
      ·
        refine ⟨11714942361695242283971249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15619923148926989711961665 11714942361695242283971249)
        ·
          refine ⟨8786206771271431712978437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11714942361695242283971249 8786206771271431712978437)
          ·
            refine ⟨1647413769613393446183457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8786206771271431712978437 1647413769613393446183457)
            ·
              refine ⟨1235560327210045084637593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647413769613393446183457 1235560327210045084637593)
              ·
                refine ⟨926670245407533813478195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235560327210045084637593 926670245407533813478195)
                ·
                  refine ⟨1390005368111300720217293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926670245407533813478195 1390005368111300720217293)
                  ·
                    refine ⟨521252013041737770081485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390005368111300720217293 521252013041737770081485)
                    ·
                      rfl

theorem cell22_1522702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_1522702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522702 prefixEnd_1522702 := by exact prefixLift 1522702
  have htrace : WordTrace (prefixWord ++ tailWord_1522702) baseStart_1522702 baseEnd_1522702 := by
    simpa [prefixWord, tailWord_1522702, baseEnd_1522702] using wordTrace_append hprefix tailTrace_1522702
  have hstable : (prefixWord ++ tailWord_1522702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522702).length < 2 ^ (prefixWord ++ tailWord_1522702).sum := by decide
  have hdescent : baseEnd_1522702 < baseStart_1522702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522711 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1522711 : Nat := 118140960795 + 1522711 * 2 ^ 59
def prefixEnd_1522711 : Nat := 4983230072969 + 3 ^ 40 * 1522711 * 2
def baseEnd_1522711 : Nat := 521255093925664746606457

theorem tailTrace_1522711 : CollatzResearch.WordTrace tailWord_1522711 prefixEnd_1522711 521255093925664746606457 := by
  unfold tailWord_1522711
  simp only [CollatzResearch.WordTrace]
  refine ⟨55537832786485580179607987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37025221857657053453071991 55537832786485580179607987)
  ·
    refine ⟨83306749179728370269411981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55537832786485580179607987 83306749179728370269411981)
    ·
      refine ⟨31240030942398138851029493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83306749179728370269411981 31240030942398138851029493)
      ·
        refine ⟨2928752900849825517284015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31240030942398138851029493 2928752900849825517284015)
        ·
          refine ⟨4393129351274738275926023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928752900849825517284015 4393129351274738275926023)
          ·
            refine ⟨6589694026912107413889035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393129351274738275926023 6589694026912107413889035)
            ·
              refine ⟨9884541040368161120833553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589694026912107413889035 9884541040368161120833553)
              ·
                refine ⟨7413405780276120840625165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9884541040368161120833553 7413405780276120840625165)
                ·
                  refine ⟨2780027167603545315234437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7413405780276120840625165 2780027167603545315234437)
                  ·
                    refine ⟨521255093925664746606457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780027167603545315234437 521255093925664746606457)
                    ·
                      rfl

theorem cell22_1522711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1522711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522711 prefixEnd_1522711 := by exact prefixLift 1522711
  have htrace : WordTrace (prefixWord ++ tailWord_1522711) baseStart_1522711 baseEnd_1522711 := by
    simpa [prefixWord, tailWord_1522711, baseEnd_1522711] using wordTrace_append hprefix tailTrace_1522711
  have hstable : (prefixWord ++ tailWord_1522711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522711).length < 2 ^ (prefixWord ++ tailWord_1522711).sum := by decide
  have hdescent : baseEnd_1522711 < baseStart_1522711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522741 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1522741 : Nat := 118140960795 + 1522741 * 2 ^ 59
def prefixEnd_1522741 : Nat := 4983230072969 + 3 ^ 40 * 1522741 * 2
def baseEnd_1522741 : Nat := 521265363538754668356365

theorem tailTrace_1522741 : CollatzResearch.WordTrace tailWord_1522741 prefixEnd_1522741 521265363538754668356365 := by
  unfold tailWord_1522741
  simp only [CollatzResearch.WordTrace]
  refine ⟨55538926976376895303200077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37025951317584596868800051 55538926976376895303200077)
  ·
    refine ⟨20827097616141335738700029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55538926976376895303200077 20827097616141335738700029)
    ·
      refine ⟨7810161606053000902012511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20827097616141335738700029 7810161606053000902012511)
      ·
        refine ⟨11715242409079501353018767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810161606053000902012511 11715242409079501353018767)
        ·
          refine ⟨17572863613619252029528151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11715242409079501353018767 17572863613619252029528151)
          ·
            refine ⟨26359295420428878044292227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17572863613619252029528151 26359295420428878044292227)
            ·
              refine ⟨39538943130643317066438341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26359295420428878044292227 39538943130643317066438341)
              ·
                refine ⟨7413551836995621949957189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39538943130643317066438341 7413551836995621949957189)
                ·
                  refine ⟨1390040969436679115616973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7413551836995621949957189 1390040969436679115616973)
                  ·
                    refine ⟨521265363538754668356365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390040969436679115616973 521265363538754668356365)
                    ·
                      rfl

theorem cell22_1522741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1522741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522741 prefixEnd_1522741 := by exact prefixLift 1522741
  have htrace : WordTrace (prefixWord ++ tailWord_1522741) baseStart_1522741 baseEnd_1522741 := by
    simpa [prefixWord, tailWord_1522741, baseEnd_1522741] using wordTrace_append hprefix tailTrace_1522741
  have hstable : (prefixWord ++ tailWord_1522741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522741).length < 2 ^ (prefixWord ++ tailWord_1522741).sum := by decide
  have hdescent : baseEnd_1522741 < baseStart_1522741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522745 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 1, 4]
def baseStart_1522745 : Nat := 118140960795 + 1522745 * 2 ^ 59
def prefixEnd_1522745 : Nat := 4983230072969 + 3 ^ 40 * 1522745 * 2
def baseEnd_1522745 : Nat := 521266732820499991256353

theorem tailTrace_1522745 : CollatzResearch.WordTrace tailWord_1522745 prefixEnd_1522745 521266732820499991256353 := by
  unfold tailWord_1522745
  simp only [CollatzResearch.WordTrace]
  refine ⟨55539072868362403986345689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37026048578908269324230459 55539072868362403986345689)
  ·
    refine ⟨41654304651271802989759267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55539072868362403986345689 41654304651271802989759267)
    ·
      refine ⟨62481456976907704484638901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41654304651271802989759267 62481456976907704484638901)
      ·
        refine ⟨5857636591585097295434897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62481456976907704484638901 5857636591585097295434897)
        ·
          refine ⟨4393227443688822971576173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857636591585097295434897 4393227443688822971576173)
          ·
            refine ⟨1647460291383308614341065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4393227443688822971576173 1647460291383308614341065)
            ·
              refine ⟨1235595218537481460755799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647460291383308614341065 1235595218537481460755799)
              ·
                refine ⟨1853392827806222191133699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235595218537481460755799 1853392827806222191133699)
                ·
                  refine ⟨2780089241709333286700549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853392827806222191133699 2780089241709333286700549)
                  ·
                    refine ⟨521266732820499991256353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780089241709333286700549 521266732820499991256353)
                    ·
                      rfl

theorem cell22_1522745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_1522745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522745 prefixEnd_1522745 := by exact prefixLift 1522745
  have htrace : WordTrace (prefixWord ++ tailWord_1522745) baseStart_1522745 baseEnd_1522745 := by
    simpa [prefixWord, tailWord_1522745, baseEnd_1522745] using wordTrace_append hprefix tailTrace_1522745
  have hstable : (prefixWord ++ tailWord_1522745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522745).length < 2 ^ (prefixWord ++ tailWord_1522745).sum := by decide
  have hdescent : baseEnd_1522745 < baseStart_1522745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522799 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 9]
def baseStart_1522799 : Nat := 118140960795 + 1522799 * 2 ^ 59
def prefixEnd_1522799 : Nat := 4983230072969 + 3 ^ 40 * 1522799 * 2
def baseEnd_1522799 : Nat := 173761739374687283468729

theorem tailTrace_1522799 : CollatzResearch.WordTrace tailWord_1522799 prefixEnd_1522799 173761739374687283468729 := by
  unfold tailWord_1522799
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541042410166771208811451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37027361606777847472540967 55541042410166771208811451)
  ·
    refine ⟨83311563615250156813217177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55541042410166771208811451 83311563615250156813217177)
    ·
      refine ⟨62483672711437617609912883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83311563615250156813217177 62483672711437617609912883)
      ·
        refine ⟨93725509067156426414869325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62483672711437617609912883 93725509067156426414869325)
        ·
          refine ⟨35147065900183659905575997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93725509067156426414869325 35147065900183659905575997)
          ·
            refine ⟨13180149712568872464590999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35147065900183659905575997 13180149712568872464590999)
            ·
              refine ⟨19770224568853308696886499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13180149712568872464590999 19770224568853308696886499)
              ·
                refine ⟨29655336853279963045329749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19770224568853308696886499 29655336853279963045329749)
                ·
                  refine ⟨173761739374687283468729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29655336853279963045329749 173761739374687283468729)
                  ·
                    rfl

theorem cell22_1522799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_1522799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522799 prefixEnd_1522799 := by exact prefixLift 1522799
  have htrace : WordTrace (prefixWord ++ tailWord_1522799) baseStart_1522799 baseEnd_1522799 := by
    simpa [prefixWord, tailWord_1522799, baseEnd_1522799] using wordTrace_append hprefix tailTrace_1522799
  have hstable : (prefixWord ++ tailWord_1522799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522799).length < 2 ^ (prefixWord ++ tailWord_1522799).sum := by decide
  have hdescent : baseEnd_1522799 < baseStart_1522799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522805 : List Nat := [1, 3, 4, 3, 2, 1, 8]
def baseStart_1522805 : Nat := 118140960795 + 1522805 * 2 ^ 59
def prefixEnd_1522805 : Nat := 4983230072969 + 3 ^ 40 * 1522805 * 2
def baseEnd_1522805 : Nat := 19306936001728882768747

theorem tailTrace_1522805 : CollatzResearch.WordTrace tailWord_1522805 prefixEnd_1522805 19306936001728882768747 := by
  unfold tailWord_1522805
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541261248145034233529869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37027507498763356155686579 55541261248145034233529869)
  ·
    refine ⟨20827972968054387837573701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55541261248145034233529869 20827972968054387837573701)
    ·
      refine ⟨3905244931510197719545069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20827972968054387837573701 3905244931510197719545069)
      ·
        refine ⟨1464466849316324144829401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3905244931510197719545069 1464466849316324144829401)
        ·
          refine ⟨1098350136987243108622051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1464466849316324144829401 1098350136987243108622051)
          ·
            refine ⟨1647525205480864662933077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098350136987243108622051 1647525205480864662933077)
            ·
              refine ⟨19306936001728882768747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1647525205480864662933077 19306936001728882768747)
              ·
                rfl

theorem cell22_1522805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 8].length) (baseStart_1522805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522805 prefixEnd_1522805 := by exact prefixLift 1522805
  have htrace : WordTrace (prefixWord ++ tailWord_1522805) baseStart_1522805 baseEnd_1522805 := by
    simpa [prefixWord, tailWord_1522805, baseEnd_1522805] using wordTrace_append hprefix tailTrace_1522805
  have hstable : (prefixWord ++ tailWord_1522805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522805).length < 2 ^ (prefixWord ++ tailWord_1522805).sum := by decide
  have hdescent : baseEnd_1522805 < baseStart_1522805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522820 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1522820 : Nat := 118140960795 + 1522820 * 2 ^ 59
def prefixEnd_1522820 : Nat := 4983230072969 + 3 ^ 40 * 1522820 * 2
def baseEnd_1522820 : Nat := 521292406853224795631123

theorem tailTrace_1522820 : CollatzResearch.WordTrace tailWord_1522820 prefixEnd_1522820 521292406853224795631123 := by
  unfold tailWord_1522820
  simp only [CollatzResearch.WordTrace]
  refine ⟨27770904171545345897662957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37027872228727127863550609 27770904171545345897662957)
  ·
    refine ⟨10414089064329504711623609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27770904171545345897662957 10414089064329504711623609)
    ·
      refine ⟨7810566798247128533717707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10414089064329504711623609 7810566798247128533717707)
      ·
        refine ⟨11715850197370692800576561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810566798247128533717707 11715850197370692800576561)
        ·
          refine ⟨8786887648028019600432421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11715850197370692800576561 8786887648028019600432421)
          ·
            refine ⟨1647541434005253675081079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8786887648028019600432421 1647541434005253675081079)
            ·
              refine ⟨2471312151007880512621619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647541434005253675081079 2471312151007880512621619)
              ·
                refine ⟨3706968226511820768932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471312151007880512621619 3706968226511820768932429)
                ·
                  refine ⟨1390113084941932788349661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3706968226511820768932429 1390113084941932788349661)
                  ·
                    refine ⟨521292406853224795631123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390113084941932788349661 521292406853224795631123)
                    ·
                      rfl

theorem cell22_1522820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1522820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522820 prefixEnd_1522820 := by exact prefixLift 1522820
  have htrace : WordTrace (prefixWord ++ tailWord_1522820) baseStart_1522820 baseEnd_1522820 := by
    simpa [prefixWord, tailWord_1522820, baseEnd_1522820] using wordTrace_append hprefix tailTrace_1522820
  have hstable : (prefixWord ++ tailWord_1522820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522820).length < 2 ^ (prefixWord ++ tailWord_1522820).sum := by decide
  have hdescent : baseEnd_1522820 < baseStart_1522820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522882 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1522882 : Nat := 118140960795 + 1522882 * 2 ^ 59
def prefixEnd_1522882 : Nat := 4983230072969 + 3 ^ 40 * 1522882 * 2
def baseEnd_1522882 : Nat := 521313630720277300580933

theorem tailTrace_1522882 : CollatzResearch.WordTrace tailWord_1522882 prefixEnd_1522882 521313630720277300580933 := by
  unfold tailWord_1522882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886017417216519096020725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37029379779244050922721933 13886017417216519096020725)
  ·
    refine ⟨1301814132864048665251943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13886017417216519096020725 1301814132864048665251943)
    ·
      refine ⟨1952721199296072997877915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301814132864048665251943 1952721199296072997877915)
      ·
        refine ⟨2929081798944109496816873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952721199296072997877915 2929081798944109496816873)
        ·
          refine ⟨2196811349208082122612655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2929081798944109496816873 2196811349208082122612655)
          ·
            refine ⟨3295217023812123183918983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196811349208082122612655 3295217023812123183918983)
            ·
              refine ⟨4942825535718184775878475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295217023812123183918983 4942825535718184775878475)
              ·
                refine ⟨7414238303577277163817713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942825535718184775878475 7414238303577277163817713)
                ·
                  refine ⟨5560678727682957872863285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7414238303577277163817713 5560678727682957872863285)
                  ·
                    refine ⟨521313630720277300580933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5560678727682957872863285 521313630720277300580933)
                    ·
                      rfl

theorem cell22_1522882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1522882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522882 prefixEnd_1522882 := by exact prefixLift 1522882
  have htrace : WordTrace (prefixWord ++ tailWord_1522882) baseStart_1522882 baseEnd_1522882 := by
    simpa [prefixWord, tailWord_1522882, baseEnd_1522882] using wordTrace_append hprefix tailTrace_1522882
  have hstable : (prefixWord ++ tailWord_1522882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522882).length < 2 ^ (prefixWord ++ tailWord_1522882).sum := by decide
  have hdescent : baseEnd_1522882 < baseStart_1522882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522927 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 2, 3]
def baseStart_1522927 : Nat := 118140960795 + 1522927 * 2 ^ 59
def prefixEnd_1522927 : Nat := 4983230072969 + 3 ^ 40 * 1522927 * 2
def baseEnd_1522927 : Nat := 521329035139912183205795

theorem tailTrace_1522927 : CollatzResearch.WordTrace tailWord_1522927 prefixEnd_1522927 521329035139912183205795 := by
  unfold tailWord_1522927
  simp only [CollatzResearch.WordTrace]
  refine ⟨55545710953703049069471035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37030473969135366046314023 55545710953703049069471035)
  ·
    refine ⟨83318566430554573604206553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55545710953703049069471035 83318566430554573604206553)
    ·
      refine ⟨62488924822915930203154915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83318566430554573604206553 62488924822915930203154915)
      ·
        refine ⟨93733387234373895304732373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62488924822915930203154915 93733387234373895304732373)
        ·
          refine ⟨2196876263305638171204665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93733387234373895304732373 2196876263305638171204665)
          ·
            refine ⟨1647657197479228628403499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196876263305638171204665 1647657197479228628403499)
            ·
              refine ⟨2471485796218842942605249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647657197479228628403499 2471485796218842942605249)
              ·
                refine ⟨1853614347164132206953937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471485796218842942605249 1853614347164132206953937)
                ·
                  refine ⟨1390210760373099155215453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853614347164132206953937 1390210760373099155215453)
                  ·
                    refine ⟨521329035139912183205795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390210760373099155215453 521329035139912183205795)
                    ·
                      rfl

theorem cell22_1522927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_1522927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522927 prefixEnd_1522927 := by exact prefixLift 1522927
  have htrace : WordTrace (prefixWord ++ tailWord_1522927) baseStart_1522927 baseEnd_1522927 := by
    simpa [prefixWord, tailWord_1522927, baseEnd_1522927] using wordTrace_append hprefix tailTrace_1522927
  have hstable : (prefixWord ++ tailWord_1522927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522927).length < 2 ^ (prefixWord ++ tailWord_1522927).sum := by decide
  have hdescent : baseEnd_1522927 < baseStart_1522927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522972 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_1522972 : Nat := 118140960795 + 1522972 * 2 ^ 59
def prefixEnd_1522972 : Nat := 4983230072969 + 3 ^ 40 * 1522972 * 2
def baseEnd_1522972 : Nat := 521344439559547065830657

theorem tailTrace_1522972 : CollatzResearch.WordTrace tailWord_1522972 prefixEnd_1522972 521344439559547065830657 := by
  unfold tailWord_1522972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27773676119270010877429585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37031568159026681169906113 27773676119270010877429585)
  ·
    refine ⟨20830257089452508158072189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27773676119270010877429585 20830257089452508158072189)
    ·
      refine ⟨7811346408544690559277071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20830257089452508158072189 7811346408544690559277071)
      ·
        refine ⟨11717019612817035838915607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811346408544690559277071 11717019612817035838915607)
        ·
          refine ⟨17575529419225553758373411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11717019612817035838915607 17575529419225553758373411)
          ·
            refine ⟨26363294128838330637560117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17575529419225553758373411 26363294128838330637560117)
            ·
              refine ⟨2471558824578593497271261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26363294128838330637560117 2471558824578593497271261)
              ·
                refine ⟨926834559216972561476723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2471558824578593497271261 926834559216972561476723)
                ·
                  refine ⟨1390251838825458842215085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926834559216972561476723 1390251838825458842215085)
                  ·
                    refine ⟨521344439559547065830657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390251838825458842215085 521344439559547065830657)
                    ·
                      rfl

theorem cell22_1522972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_1522972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522972 prefixEnd_1522972 := by exact prefixLift 1522972
  have htrace : WordTrace (prefixWord ++ tailWord_1522972) baseStart_1522972 baseEnd_1522972 := by
    simpa [prefixWord, tailWord_1522972, baseEnd_1522972] using wordTrace_append hprefix tailTrace_1522972
  have hstable : (prefixWord ++ tailWord_1522972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522972).length < 2 ^ (prefixWord ++ tailWord_1522972).sum := by decide
  have hdescent : baseEnd_1522972 < baseStart_1522972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522989 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1522989 : Nat := 118140960795 + 1522989 * 2 ^ 59
def prefixEnd_1522989 : Nat := 4983230072969 + 3 ^ 40 * 1522989 * 2
def baseEnd_1522989 : Nat := 521350259006964688155605

theorem tailTrace_1522989 : CollatzResearch.WordTrace tailWord_1522989 prefixEnd_1522989 521350259006964688155605 := by
  unfold tailWord_1522989
  simp only [CollatzResearch.WordTrace]
  refine ⟨55547972279478433658228021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37031981519652289105485347 55547972279478433658228021)
  ·
    refine ⟨5207622401201103155458877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55547972279478433658228021 5207622401201103155458877)
    ·
      refine ⟨1952858400450413683297079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5207622401201103155458877 1952858400450413683297079)
      ·
        refine ⟨2929287600675620524945619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952858400450413683297079 2929287600675620524945619)
        ·
          refine ⟨4393931401013430787418429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929287600675620524945619 4393931401013430787418429)
          ·
            refine ⟨1647724275380036545281911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4393931401013430787418429 1647724275380036545281911)
            ·
              refine ⟨2471586413070054817922867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647724275380036545281911 2471586413070054817922867)
              ·
                refine ⟨3707379619605082226884301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471586413070054817922867 3707379619605082226884301)
                ·
                  refine ⟨1390267357351905835081613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3707379619605082226884301 1390267357351905835081613)
                  ·
                    refine ⟨521350259006964688155605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390267357351905835081613 521350259006964688155605)
                    ·
                      rfl

theorem cell22_1522989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1522989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1522989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1522989 prefixEnd_1522989 := by exact prefixLift 1522989
  have htrace : WordTrace (prefixWord ++ tailWord_1522989) baseStart_1522989 baseEnd_1522989 := by
    simpa [prefixWord, tailWord_1522989, baseEnd_1522989] using wordTrace_append hprefix tailTrace_1522989
  have hstable : (prefixWord ++ tailWord_1522989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522989).length < 2 ^ (prefixWord ++ tailWord_1522989).sum := by decide
  have hdescent : baseEnd_1522989 < baseStart_1522989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523015 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1523015 : Nat := 118140960795 + 1523015 * 2 ^ 59
def prefixEnd_1523015 : Nat := 4983230072969 + 3 ^ 40 * 1523015 * 2
def baseEnd_1523015 : Nat := 521359159338309287005525

theorem tailTrace_1523015 : CollatzResearch.WordTrace tailWord_1523015 prefixEnd_1523015 521359159338309287005525 := by
  unfold tailWord_1523015
  simp only [CollatzResearch.WordTrace]
  refine ⟨55548920577384240098674499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37032613718256160065782999 55548920577384240098674499)
  ·
    refine ⟨83323380866076360148011749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55548920577384240098674499 83323380866076360148011749)
    ·
      refine ⟨15623133912389317527752203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83323380866076360148011749 15623133912389317527752203)
      ·
        refine ⟨23434700868583976291628305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15623133912389317527752203 23434700868583976291628305)
        ·
          refine ⟨17576025651437982218721229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23434700868583976291628305 17576025651437982218721229)
          ·
            refine ⟨6591009619289243332020461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17576025651437982218721229 6591009619289243332020461)
            ·
              refine ⟨2471628607233466249507673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6591009619289243332020461 2471628607233466249507673)
              ·
                refine ⟨1853721455425099687130755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471628607233466249507673 1853721455425099687130755)
                ·
                  refine ⟨2780582183137649530696133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853721455425099687130755 2780582183137649530696133)
                  ·
                    refine ⟨521359159338309287005525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2780582183137649530696133 521359159338309287005525)
                    ·
                      rfl

theorem cell22_1523015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1523015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523015 prefixEnd_1523015 := by exact prefixLift 1523015
  have htrace : WordTrace (prefixWord ++ tailWord_1523015) baseStart_1523015 baseEnd_1523015 := by
    simpa [prefixWord, tailWord_1523015, baseEnd_1523015] using wordTrace_append hprefix tailTrace_1523015
  have hstable : (prefixWord ++ tailWord_1523015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523015).length < 2 ^ (prefixWord ++ tailWord_1523015).sum := by decide
  have hdescent : baseEnd_1523015 < baseStart_1523015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523047 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 4]
def baseStart_1523047 : Nat := 118140960795 + 1523047 * 2 ^ 59
def prefixEnd_1523047 : Nat := 4983230072969 + 3 ^ 40 * 1523047 * 2
def baseEnd_1523047 : Nat := 173790037864090623401809

theorem tailTrace_1523047 : CollatzResearch.WordTrace tailWord_1523047 prefixEnd_1523047 173790037864090623401809 := by
  unfold tailWord_1523047
  simp only [CollatzResearch.WordTrace]
  refine ⟨55550087713268309563839395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37033391808845539709226263 55550087713268309563839395)
  ·
    refine ⟨83325131569902464345759093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55550087713268309563839395 83325131569902464345759093)
    ·
      refine ⟨7811731084678356032414915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83325131569902464345759093 7811731084678356032414915)
      ·
        refine ⟨11717596627017534048622373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811731084678356032414915 11717596627017534048622373)
        ·
          refine ⟨2197049367565787634116695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11717596627017534048622373 2197049367565787634116695)
          ·
            refine ⟨3295574051348681451175043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197049367565787634116695 3295574051348681451175043)
            ·
              refine ⟨4943361077023022176762565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295574051348681451175043 4943361077023022176762565)
              ·
                refine ⟨926880201941816658142981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4943361077023022176762565 926880201941816658142981)
                ·
                  refine ⟨173790037864090623401809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 926880201941816658142981 173790037864090623401809)
                  ·
                    rfl

theorem cell22_1523047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 4].length) (baseStart_1523047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523047 prefixEnd_1523047 := by exact prefixLift 1523047
  have htrace : WordTrace (prefixWord ++ tailWord_1523047) baseStart_1523047 baseEnd_1523047 := by
    simpa [prefixWord, tailWord_1523047, baseEnd_1523047] using wordTrace_append hprefix tailTrace_1523047
  have hstable : (prefixWord ++ tailWord_1523047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523047).length < 2 ^ (prefixWord ++ tailWord_1523047).sum := by decide
  have hdescent : baseEnd_1523047 < baseStart_1523047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523075 : List Nat := [1, 1, 1, 3, 5, 2, 3, 6]
def baseStart_1523075 : Nat := 118140960795 + 1523075 * 2 ^ 59
def prefixEnd_1523075 : Nat := 4983230072969 + 3 ^ 40 * 1523075 * 2
def baseEnd_1523075 : Nat := 57931077618276570056149

theorem tailTrace_1523075 : CollatzResearch.WordTrace tailWord_1523075 prefixEnd_1523075 57931077618276570056149 := by
  unfold tailWord_1523075
  simp only [CollatzResearch.WordTrace]
  refine ⟨55551108957166870345858679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37034072638111246897239119 55551108957166870345858679)
  ·
    refine ⟨83326663435750305518788019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55551108957166870345858679 83326663435750305518788019)
    ·
      refine ⟨124989995153625458278182029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83326663435750305518788019 124989995153625458278182029)
      ·
        refine ⟨46871248182609546854318261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124989995153625458278182029 46871248182609546854318261)
        ·
          refine ⟨4394179517119645017592337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46871248182609546854318261 4394179517119645017592337)
          ·
            refine ⟨3295634637839733763194253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4394179517119645017592337 3295634637839733763194253)
            ·
              refine ⟨1235862989189900161197845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3295634637839733763194253 1235862989189900161197845)
              ·
                refine ⟨57931077618276570056149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1235862989189900161197845 57931077618276570056149)
                ·
                  rfl

theorem cell22_1523075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 6].length) (baseStart_1523075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523075 prefixEnd_1523075 := by exact prefixLift 1523075
  have htrace : WordTrace (prefixWord ++ tailWord_1523075) baseStart_1523075 baseEnd_1523075 := by
    simpa [prefixWord, tailWord_1523075, baseEnd_1523075] using wordTrace_append hprefix tailTrace_1523075
  have hstable : (prefixWord ++ tailWord_1523075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523075).length < 2 ^ (prefixWord ++ tailWord_1523075).sum := by decide
  have hdescent : baseEnd_1523075 < baseStart_1523075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523096 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 2, 3]
def baseStart_1523096 : Nat := 118140960795 + 1523096 * 2 ^ 59
def prefixEnd_1523096 : Nat := 4983230072969 + 3 ^ 40 * 1523096 * 2
def baseEnd_1523096 : Nat := 521386887293652075730277

theorem tailTrace_1523096 : CollatzResearch.WordTrace tailWord_1523096 prefixEnd_1523096 521386887293652075730277 := by
  unfold tailWord_1523096
  simp only [CollatzResearch.WordTrace]
  refine ⟨27775937445045395466186571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37034583260060527288248761 27775937445045395466186571)
  ·
    refine ⟨41663906167568093199279857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27775937445045395466186571 41663906167568093199279857)
    ·
      refine ⟨31247929625676069899459893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41663906167568093199279857 31247929625676069899459893)
      ·
        refine ⟨2929493402407131553074365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31247929625676069899459893 2929493402407131553074365)
        ·
          refine ⟨1098560025902674332402887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2929493402407131553074365 1098560025902674332402887)
          ·
            refine ⟨1647840038854011498604331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098560025902674332402887 1647840038854011498604331)
            ·
              refine ⟨2471760058281017247906497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647840038854011498604331 2471760058281017247906497)
              ·
                refine ⟨1853820043710762935929873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471760058281017247906497 1853820043710762935929873)
                ·
                  refine ⟨1390365032783072201947405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853820043710762935929873 1390365032783072201947405)
                  ·
                    refine ⟨521386887293652075730277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390365032783072201947405 521386887293652075730277)
                    ·
                      rfl

theorem cell22_1523096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_1523096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523096 prefixEnd_1523096 := by exact prefixLift 1523096
  have htrace : WordTrace (prefixWord ++ tailWord_1523096) baseStart_1523096 baseEnd_1523096 := by
    simpa [prefixWord, tailWord_1523096, baseEnd_1523096] using wordTrace_append hprefix tailTrace_1523096
  have hstable : (prefixWord ++ tailWord_1523096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523096).length < 2 ^ (prefixWord ++ tailWord_1523096).sum := by decide
  have hdescent : baseEnd_1523096 < baseStart_1523096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523107 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 1, 3]
def baseStart_1523107 : Nat := 118140960795 + 1523107 * 2 ^ 59
def prefixEnd_1523107 : Nat := 4983230072969 + 3 ^ 40 * 1523107 * 2
def baseEnd_1523107 : Nat := 521390652818451713705243

theorem tailTrace_1523107 : CollatzResearch.WordTrace tailWord_1523107 prefixEnd_1523107 521390652818451713705243 := by
  unfold tailWord_1523107
  simp only [CollatzResearch.WordTrace]
  refine ⟨55552276093050939811023575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37034850728700626540682383 55552276093050939811023575)
  ·
    refine ⟨83328414139576409716535363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55552276093050939811023575 83328414139576409716535363)
    ·
      refine ⟨124992621209364614574803045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83328414139576409716535363 124992621209364614574803045)
      ·
        refine ⟨23436116476755865232775571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124992621209364614574803045 23436116476755865232775571)
        ·
          refine ⟨35154174715133797849163357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23436116476755865232775571 35154174715133797849163357)
          ·
            refine ⟨13182815518175174193436259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35154174715133797849163357 13182815518175174193436259)
            ·
              refine ⟨19774223277262761290154389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13182815518175174193436259 19774223277262761290154389)
              ·
                refine ⟨926916716121691935475987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19774223277262761290154389 926916716121691935475987)
                ·
                  refine ⟨1390375074182537903213981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926916716121691935475987 1390375074182537903213981)
                  ·
                    refine ⟨521390652818451713705243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390375074182537903213981 521390652818451713705243)
                    ·
                      rfl

theorem cell22_1523107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 3].length) (baseStart_1523107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523107 prefixEnd_1523107 := by exact prefixLift 1523107
  have htrace : WordTrace (prefixWord ++ tailWord_1523107) baseStart_1523107 baseEnd_1523107 := by
    simpa [prefixWord, tailWord_1523107, baseEnd_1523107] using wordTrace_append hprefix tailTrace_1523107
  have hstable : (prefixWord ++ tailWord_1523107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523107).length < 2 ^ (prefixWord ++ tailWord_1523107).sum := by decide
  have hdescent : baseEnd_1523107 < baseStart_1523107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523158 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1523158 : Nat := 118140960795 + 1523158 * 2 ^ 59
def prefixEnd_1523158 : Nat := 4983230072969 + 3 ^ 40 * 1523158 * 2
def baseEnd_1523158 : Nat := 521408111160704580680087

theorem tailTrace_1523158 : CollatzResearch.WordTrace tailWord_1523158 prefixEnd_1523158 521408111160704580680087 := by
  unfold tailWord_1523158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472133513491635970070633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37036090810577450347420085 3472133513491635970070633)
  ·
    refine ⟨2604100135118726977552975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3472133513491635970070633 2604100135118726977552975)
    ·
      refine ⟨3906150202678090466329463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604100135118726977552975 3906150202678090466329463)
      ·
        refine ⟨5859225304017135699494195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3906150202678090466329463 5859225304017135699494195)
        ·
          refine ⟨8788837956025703549241293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859225304017135699494195 8788837956025703549241293)
          ·
            refine ⟨3295814233509638830965485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8788837956025703549241293 3295814233509638830965485)
            ·
              refine ⟨1235930337566114561612057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3295814233509638830965485 1235930337566114561612057)
              ·
                refine ⟨926947753174585921209043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235930337566114561612057 926947753174585921209043)
                ·
                  refine ⟨1390421629761878881813565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926947753174585921209043 1390421629761878881813565)
                  ·
                    refine ⟨521408111160704580680087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390421629761878881813565 521408111160704580680087)
                    ·
                      rfl

theorem cell22_1523158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1523158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523158 prefixEnd_1523158 := by exact prefixLift 1523158
  have htrace : WordTrace (prefixWord ++ tailWord_1523158) baseStart_1523158 baseEnd_1523158 := by
    simpa [prefixWord, tailWord_1523158, baseEnd_1523158] using wordTrace_append hprefix tailTrace_1523158
  have hstable : (prefixWord ++ tailWord_1523158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523158).length < 2 ^ (prefixWord ++ tailWord_1523158).sum := by decide
  have hdescent : baseEnd_1523158 < baseStart_1523158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523180 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_1523180 : Nat := 118140960795 + 1523180 * 2 ^ 59
def prefixEnd_1523180 : Nat := 4983230072969 + 3 ^ 40 * 1523180 * 2
def baseEnd_1523180 : Nat := 521415642210303856630019

theorem tailTrace_1523180 : CollatzResearch.WordTrace tailWord_1523180 prefixEnd_1523180 521415642210303856630019 := by
  unfold tailWord_1523180
  simp only [CollatzResearch.WordTrace]
  refine ⟨27777469310893236639215497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37036625747857648852287329 27777469310893236639215497)
  ·
    refine ⟨20833101983169927479411623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27777469310893236639215497 20833101983169927479411623)
    ·
      refine ⟨31249652974754891219117435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20833101983169927479411623 31249652974754891219117435)
      ·
        refine ⟨46874479462132336828676153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31249652974754891219117435 46874479462132336828676153)
        ·
          refine ⟨35155859596599252621507115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46874479462132336828676153 35155859596599252621507115)
          ·
            refine ⟨52733789394898878932260673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35155859596599252621507115 52733789394898878932260673)
            ·
              refine ⟨39550342046174159199195505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52733789394898878932260673 39550342046174159199195505)
              ·
                refine ⟨29662756534630619399396629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39550342046174159199195505 29662756534630619399396629)
                ·
                  refine ⟨1390441712560810284346717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29662756534630619399396629 1390441712560810284346717)
                  ·
                    refine ⟨521415642210303856630019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390441712560810284346717 521415642210303856630019)
                    ·
                      rfl

theorem cell22_1523180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_1523180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523180 prefixEnd_1523180 := by exact prefixLift 1523180
  have htrace : WordTrace (prefixWord ++ tailWord_1523180) baseStart_1523180 baseEnd_1523180 := by
    simpa [prefixWord, tailWord_1523180, baseEnd_1523180] using wordTrace_append hprefix tailTrace_1523180
  have hstable : (prefixWord ++ tailWord_1523180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523180).length < 2 ^ (prefixWord ++ tailWord_1523180).sum := by decide
  have hdescent : baseEnd_1523180 < baseStart_1523180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523310 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1523310 : Nat := 118140960795 + 1523310 * 2 ^ 59
def prefixEnd_1523310 : Nat := 4983230072969 + 3 ^ 40 * 1523310 * 2
def baseEnd_1523310 : Nat := 521460143867026850879621

theorem tailTrace_1523310 : CollatzResearch.WordTrace tailWord_1523310 prefixEnd_1523310 521460143867026850879621 := by
  unfold tailWord_1523310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944960013914438185082923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37039786740877003653775589 6944960013914438185082923)
  ·
    refine ⟨10417440020871657277624385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944960013914438185082923 10417440020871657277624385)
    ·
      refine ⟨7813080015653742958218289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10417440020871657277624385 7813080015653742958218289)
      ·
        refine ⟨5859810011740307218663717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7813080015653742958218289 5859810011740307218663717)
        ·
          refine ⟨1098714377201307603499447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5859810011740307218663717 1098714377201307603499447)
          ·
            refine ⟨1648071565801961405249171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098714377201307603499447 1648071565801961405249171)
            ·
              refine ⟨2472107348702942107873757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648071565801961405249171 2472107348702942107873757)
              ·
                refine ⟨927040255763603290452659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472107348702942107873757 927040255763603290452659)
                ·
                  refine ⟨1390560383645404935678989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927040255763603290452659 1390560383645404935678989)
                  ·
                    refine ⟨521460143867026850879621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390560383645404935678989 521460143867026850879621)
                    ·
                      rfl

theorem cell22_1523310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1523310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523310 prefixEnd_1523310 := by exact prefixLift 1523310
  have htrace : WordTrace (prefixWord ++ tailWord_1523310) baseStart_1523310 baseEnd_1523310 := by
    simpa [prefixWord, tailWord_1523310, baseEnd_1523310] using wordTrace_append hprefix tailTrace_1523310
  have hstable : (prefixWord ++ tailWord_1523310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523310).length < 2 ^ (prefixWord ++ tailWord_1523310).sum := by decide
  have hdescent : baseEnd_1523310 < baseStart_1523310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523364 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1523364 : Nat := 118140960795 + 1523364 * 2 ^ 59
def prefixEnd_1523364 : Nat := 4983230072969 + 3 ^ 40 * 1523364 * 2
def baseEnd_1523364 : Nat := 521478629170588710029455

theorem tailTrace_1523364 : CollatzResearch.WordTrace tailWord_1523364 prefixEnd_1523364 521478629170588710029455 := by
  unfold tailWord_1523364
  simp only [CollatzResearch.WordTrace]
  refine ⟨27780824826559936351564573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37041099768746581802086097 27780824826559936351564573)
  ·
    refine ⟨10417809309959976131836715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27780824826559936351564573 10417809309959976131836715)
    ·
      refine ⟨15626713964939964197755073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417809309959976131836715 15626713964939964197755073)
      ·
        refine ⟨11720035473704973148316305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15626713964939964197755073 11720035473704973148316305)
        ·
          refine ⟨8790026605278729861237229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11720035473704973148316305 8790026605278729861237229)
          ·
            refine ⟨3296259976979523697963961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8790026605278729861237229 3296259976979523697963961)
            ·
              refine ⟨2472194982734642773472971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296259976979523697963961 2472194982734642773472971)
              ·
                refine ⟨3708292474101964160209457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472194982734642773472971 3708292474101964160209457)
                ·
                  refine ⟨2781219355576473120157093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708292474101964160209457 2781219355576473120157093)
                  ·
                    refine ⟨521478629170588710029455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781219355576473120157093 521478629170588710029455)
                    ·
                      rfl

theorem cell22_1523364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1523364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523364 prefixEnd_1523364 := by exact prefixLift 1523364
  have htrace : WordTrace (prefixWord ++ tailWord_1523364) baseStart_1523364 baseEnd_1523364 := by
    simpa [prefixWord, tailWord_1523364, baseEnd_1523364] using wordTrace_append hprefix tailTrace_1523364
  have hstable : (prefixWord ++ tailWord_1523364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523364).length < 2 ^ (prefixWord ++ tailWord_1523364).sum := by decide
  have hdescent : baseEnd_1523364 < baseStart_1523364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523484 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1523484 : Nat := 118140960795 + 1523484 * 2 ^ 59
def prefixEnd_1523484 : Nat := 4983230072969 + 3 ^ 40 * 1523484 * 2
def baseEnd_1523484 : Nat := 521519707622948397029087

theorem tailTrace_1523484 : CollatzResearch.WordTrace tailWord_1523484 prefixEnd_1523484 521519707622948397029087 := by
  unfold tailWord_1523484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27783013206342566598748753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37044017608456755464998337 27783013206342566598748753)
  ·
    refine ⟨20837259904756924949061565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27783013206342566598748753 20837259904756924949061565)
    ·
      refine ⟨7813972464283846855898087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20837259904756924949061565 7813972464283846855898087)
      ·
        refine ⟨11720958696425770283847131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813972464283846855898087 11720958696425770283847131)
        ·
          refine ⟨17581438044638655425770697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11720958696425770283847131 17581438044638655425770697)
          ·
            refine ⟨13186078533478991569328023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17581438044638655425770697 13186078533478991569328023)
            ·
              refine ⟨19779117800218487353992035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13186078533478991569328023 19779117800218487353992035)
              ·
                refine ⟨29668676700327731030988053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19779117800218487353992035 29668676700327731030988053)
                ·
                  refine ⟨1390719220327862392077565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29668676700327731030988053 1390719220327862392077565)
                  ·
                    refine ⟨521519707622948397029087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390719220327862392077565 521519707622948397029087)
                    ·
                      rfl

theorem cell22_1523484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1523484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523484 prefixEnd_1523484 := by exact prefixLift 1523484
  have htrace : WordTrace (prefixWord ++ tailWord_1523484) baseStart_1523484 baseEnd_1523484 := by
    simpa [prefixWord, tailWord_1523484, baseEnd_1523484] using wordTrace_append hprefix tailTrace_1523484
  have hstable : (prefixWord ++ tailWord_1523484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523484).length < 2 ^ (prefixWord ++ tailWord_1523484).sum := by decide
  have hdescent : baseEnd_1523484 < baseStart_1523484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523514 : List Nat := [3, 1, 1, 1, 5, 2, 2, 7]
def baseStart_1523514 : Nat := 118140960795 + 1523514 * 2 ^ 59
def prefixEnd_1523514 : Nat := 4983230072969 + 3 ^ 40 * 1523514 * 2
def baseEnd_1523514 : Nat := 57947775248448702086555

theorem tailTrace_1523514 : CollatzResearch.WordTrace tailWord_1523514 prefixEnd_1523514 57947775248448702086555 := by
  unfold tailWord_1523514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891780150644112080272399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37044747068384298880726397 13891780150644112080272399)
  ·
    refine ⟨20837670225966168120408599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13891780150644112080272399 20837670225966168120408599)
    ·
      refine ⟨31256505338949252180612899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20837670225966168120408599 31256505338949252180612899)
      ·
        refine ⟨46884758008423878270919349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31256505338949252180612899 46884758008423878270919349)
        ·
          refine ⟨4395446063289738587898689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46884758008423878270919349 4395446063289738587898689)
          ·
            refine ⟨3296584547467303940924017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4395446063289738587898689 3296584547467303940924017)
            ·
              refine ⟨2472438410600477955693013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296584547467303940924017 2472438410600477955693013)
              ·
                refine ⟨57947775248448702086555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2472438410600477955693013 57947775248448702086555)
                ·
                  rfl

theorem cell22_1523514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_1523514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523514 prefixEnd_1523514 := by exact prefixLift 1523514
  have htrace : WordTrace (prefixWord ++ tailWord_1523514) baseStart_1523514 baseEnd_1523514 := by
    simpa [prefixWord, tailWord_1523514, baseEnd_1523514] using wordTrace_append hprefix tailTrace_1523514
  have hstable : (prefixWord ++ tailWord_1523514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523514).length < 2 ^ (prefixWord ++ tailWord_1523514).sum := by decide
  have hdescent : baseEnd_1523514 < baseStart_1523514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523518 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1523518 : Nat := 118140960795 + 1523518 * 2 ^ 59
def prefixEnd_1523518 : Nat := 4983230072969 + 3 ^ 40 * 1523518 * 2
def baseEnd_1523518 : Nat := 521531346517783641678983

theorem tailTrace_1523518 : CollatzResearch.WordTrace tailWord_1523518 prefixEnd_1523518 521531346517783641678983 := by
  unfold tailWord_1523518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945908311820244625529401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37044844329707971336156805 6945908311820244625529401)
  ·
    refine ⟨5209431233865183469147051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6945908311820244625529401 5209431233865183469147051)
    ·
      refine ⟨7814146850797775203720577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5209431233865183469147051 7814146850797775203720577)
      ·
        refine ⟨5860610138098331402790433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7814146850797775203720577 5860610138098331402790433)
        ·
          refine ⟨4395457603573748552092825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5860610138098331402790433 4395457603573748552092825)
          ·
            refine ⟨3296593202680311414069619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4395457603573748552092825 3296593202680311414069619)
            ·
              refine ⟨4944889804020467121104429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296593202680311414069619 4944889804020467121104429)
              ·
                refine ⟨1854333676507675170414161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4944889804020467121104429 1854333676507675170414161)
                ·
                  refine ⟨1390750257380756377810621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854333676507675170414161 1390750257380756377810621)
                  ·
                    refine ⟨521531346517783641678983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390750257380756377810621 521531346517783641678983)
                    ·
                      rfl

theorem cell22_1523518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1523518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523518 prefixEnd_1523518 := by exact prefixLift 1523518
  have htrace : WordTrace (prefixWord ++ tailWord_1523518) baseStart_1523518 baseEnd_1523518 := by
    simpa [prefixWord, tailWord_1523518, baseEnd_1523518] using wordTrace_append hprefix tailTrace_1523518
  have hstable : (prefixWord ++ tailWord_1523518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523518).length < 2 ^ (prefixWord ++ tailWord_1523518).sum := by decide
  have hdescent : baseEnd_1523518 < baseStart_1523518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523529 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_1523529 : Nat := 118140960795 + 1523529 * 2 ^ 59
def prefixEnd_1523529 : Nat := 4983230072969 + 3 ^ 40 * 1523529 * 2
def baseEnd_1523529 : Nat := 521535112042583279653949

theorem tailTrace_1523529 : CollatzResearch.WordTrace tailWord_1523529 prefixEnd_1523529 521535112042583279653949 := by
  unfold tailWord_1523529
  simp only [CollatzResearch.WordTrace]
  refine ⟨55567667697522105882885641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37045111798348070588590427 55567667697522105882885641)
  ·
    refine ⟨41675750773141579412164231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55567667697522105882885641 41675750773141579412164231)
    ·
      refine ⟨62513626159712369118246347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41675750773141579412164231 62513626159712369118246347)
      ·
        refine ⟨93770439239568553677369521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62513626159712369118246347 93770439239568553677369521)
        ·
          refine ⟨70327829429676415258027141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93770439239568553677369521 70327829429676415258027141)
          ·
            refine ⟨13186468018064327860880089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70327829429676415258027141 13186468018064327860880089)
            ·
              refine ⟨9889851013548245895660067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13186468018064327860880089 9889851013548245895660067)
              ·
                refine ⟨14834776520322368843490101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9889851013548245895660067 14834776520322368843490101)
                ·
                  refine ⟨1390760298780222079077197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14834776520322368843490101 1390760298780222079077197)
                  ·
                    refine ⟨521535112042583279653949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390760298780222079077197 521535112042583279653949)
                    ·
                      rfl

theorem cell22_1523529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_1523529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523529 prefixEnd_1523529 := by exact prefixLift 1523529
  have htrace : WordTrace (prefixWord ++ tailWord_1523529) baseStart_1523529 baseEnd_1523529 := by
    simpa [prefixWord, tailWord_1523529, baseEnd_1523529] using wordTrace_append hprefix tailTrace_1523529
  have hstable : (prefixWord ++ tailWord_1523529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523529).length < 2 ^ (prefixWord ++ tailWord_1523529).sum := by decide
  have hdescent : baseEnd_1523529 < baseStart_1523529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523533 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1523533 : Nat := 118140960795 + 1523533 * 2 ^ 59
def prefixEnd_1523533 : Nat := 4983230072969 + 3 ^ 40 * 1523533 * 2
def baseEnd_1523533 : Nat := 521536481324328602553937

theorem tailTrace_1523533 : CollatzResearch.WordTrace tailWord_1523533 prefixEnd_1523533 521536481324328602553937 := by
  unfold tailWord_1523533
  simp only [CollatzResearch.WordTrace]
  refine ⟨55567813589507614566031253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37045209059671743044020835 55567813589507614566031253)
  ·
    refine ⟨2604741262008169432782715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55567813589507614566031253 2604741262008169432782715)
    ·
      refine ⟨3907111893012254149174073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604741262008169432782715 3907111893012254149174073)
      ·
        refine ⟨2930333919759190611880555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3907111893012254149174073 2930333919759190611880555)
        ·
          refine ⟨4395500879638785917820833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930333919759190611880555 4395500879638785917820833)
          ·
            refine ⟨3296625659729089438365625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4395500879638785917820833 3296625659729089438365625)
            ·
              refine ⟨2472469244796817078774219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296625659729089438365625 2472469244796817078774219)
              ·
                refine ⟨3708703867195225618161329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472469244796817078774219 3708703867195225618161329)
                ·
                  refine ⟨2781527900396419213620997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708703867195225618161329 2781527900396419213620997)
                  ·
                    refine ⟨521536481324328602553937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781527900396419213620997 521536481324328602553937)
                    ·
                      rfl

theorem cell22_1523533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1523533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523533 prefixEnd_1523533 := by exact prefixLift 1523533
  have htrace : WordTrace (prefixWord ++ tailWord_1523533) baseStart_1523533 baseEnd_1523533 := by
    simpa [prefixWord, tailWord_1523533, baseEnd_1523533] using wordTrace_append hprefix tailTrace_1523533
  have hstable : (prefixWord ++ tailWord_1523533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523533).length < 2 ^ (prefixWord ++ tailWord_1523533).sum := by decide
  have hdescent : baseEnd_1523533 < baseStart_1523533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523589 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_1523589 : Nat := 118140960795 + 1523589 * 2 ^ 59
def prefixEnd_1523589 : Nat := 4983230072969 + 3 ^ 40 * 1523589 * 2
def baseEnd_1523589 : Nat := 521555651268763123153765

theorem tailTrace_1523589 : CollatzResearch.WordTrace tailWord_1523589 prefixEnd_1523589 521555651268763123153765 := by
  unfold tailWord_1523589
  simp only [CollatzResearch.WordTrace]
  refine ⟨55569856077304736130069821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37046570718203157420046547 55569856077304736130069821)
  ·
    refine ⟨20838696028989276048776183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55569856077304736130069821 20838696028989276048776183)
    ·
      refine ⟨31258044043483914073164275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20838696028989276048776183 31258044043483914073164275)
      ·
        refine ⟨46887066065225871109746413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31258044043483914073164275 46887066065225871109746413)
        ·
          refine ⟨17582649774459701666154905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46887066065225871109746413 17582649774459701666154905)
          ·
            refine ⟨13186987330844776249616179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17582649774459701666154905 13186987330844776249616179)
            ·
              refine ⟨19780480996267164374424269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13186987330844776249616179 19780480996267164374424269)
              ·
                refine ⟨7417680373600186640409101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19780480996267164374424269 7417680373600186640409101)
                ·
                  refine ⟨2781630140100069990153413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7417680373600186640409101 2781630140100069990153413)
                  ·
                    refine ⟨521555651268763123153765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781630140100069990153413 521555651268763123153765)
                    ·
                      rfl

theorem cell22_1523589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_1523589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523589 prefixEnd_1523589 := by exact prefixLift 1523589
  have htrace : WordTrace (prefixWord ++ tailWord_1523589) baseStart_1523589 baseEnd_1523589 := by
    simpa [prefixWord, tailWord_1523589, baseEnd_1523589] using wordTrace_append hprefix tailTrace_1523589
  have hstable : (prefixWord ++ tailWord_1523589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523589).length < 2 ^ (prefixWord ++ tailWord_1523589).sum := by decide
  have hdescent : baseEnd_1523589 < baseStart_1523589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523687 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1523687 : Nat := 118140960795 + 1523687 * 2 ^ 59
def prefixEnd_1523687 : Nat := 4983230072969 + 3 ^ 40 * 1523687 * 2
def baseEnd_1523687 : Nat := 521589198671523534203465

theorem tailTrace_1523687 : CollatzResearch.WordTrace tailWord_1523687 prefixEnd_1523687 521589198671523534203465 := by
  unfold tailWord_1523687
  simp only [CollatzResearch.WordTrace]
  refine ⟨55573430430949698867137315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37048953620633132578091543 55573430430949698867137315)
  ·
    refine ⟨83360145646424548300705973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55573430430949698867137315 83360145646424548300705973)
    ·
      refine ⟨7815013654352301403191185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83360145646424548300705973 7815013654352301403191185)
      ·
        refine ⟨5861260240764226052393389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7815013654352301403191185 5861260240764226052393389)
        ·
          refine ⟨2197972590286584769647521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5861260240764226052393389 2197972590286584769647521)
          ·
            refine ⟨1648479442714938577235641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2197972590286584769647521 1648479442714938577235641)
            ·
              refine ⟨1236359582036203932926731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648479442714938577235641 1236359582036203932926731)
              ·
                refine ⟨1854539373054305899390097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236359582036203932926731 1854539373054305899390097)
                ·
                  refine ⟨1390904529790729424542573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854539373054305899390097 1390904529790729424542573)
                  ·
                    refine ⟨521589198671523534203465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390904529790729424542573 521589198671523534203465)
                    ·
                      rfl

theorem cell22_1523687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1523687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523687 prefixEnd_1523687 := by exact prefixLift 1523687
  have htrace : WordTrace (prefixWord ++ tailWord_1523687) baseStart_1523687 baseEnd_1523687 := by
    simpa [prefixWord, tailWord_1523687, baseEnd_1523687] using wordTrace_append hprefix tailTrace_1523687
  have hstable : (prefixWord ++ tailWord_1523687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523687).length < 2 ^ (prefixWord ++ tailWord_1523687).sum := by decide
  have hdescent : baseEnd_1523687 < baseStart_1523687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523726 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1523726 : Nat := 118140960795 + 1523726 * 2 ^ 59
def prefixEnd_1523726 : Nat := 4983230072969 + 3 ^ 40 * 1523726 * 2
def baseEnd_1523726 : Nat := 521602549168540432478345

theorem tailTrace_1523726 : CollatzResearch.WordTrace tailWord_1523726 prefixEnd_1523726 521602549168540432478345 := by
  unfold tailWord_1523726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946856609726051065975879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37049901918538939018538021 6946856609726051065975879)
  ·
    refine ⟨10420284914589076598963819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6946856609726051065975879 10420284914589076598963819)
    ·
      refine ⟨15630427371883614898445729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10420284914589076598963819 15630427371883614898445729)
      ·
        refine ⟨11722820528912711173834297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15630427371883614898445729 11722820528912711173834297)
        ·
          refine ⟨8792115396684533380375723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11722820528912711173834297 8792115396684533380375723)
          ·
            refine ⟨13188173095026800070563585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8792115396684533380375723 13188173095026800070563585)
            ·
              refine ⟨9891129821270100052922689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13188173095026800070563585 9891129821270100052922689)
              ·
                refine ⟨7418347365952575039692017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9891129821270100052922689 7418347365952575039692017)
                ·
                  refine ⟨5563760524464431279769013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7418347365952575039692017 5563760524464431279769013)
                  ·
                    refine ⟨521602549168540432478345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5563760524464431279769013 521602549168540432478345)
                    ·
                      rfl

theorem cell22_1523726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1523726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523726 prefixEnd_1523726 := by exact prefixLift 1523726
  have htrace : WordTrace (prefixWord ++ tailWord_1523726) baseStart_1523726 baseEnd_1523726 := by
    simpa [prefixWord, tailWord_1523726, baseEnd_1523726] using wordTrace_append hprefix tailTrace_1523726
  have hstable : (prefixWord ++ tailWord_1523726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523726).length < 2 ^ (prefixWord ++ tailWord_1523726).sum := by decide
  have hdescent : baseEnd_1523726 < baseStart_1523726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523758 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1523758 : Nat := 118140960795 + 1523758 * 2 ^ 59
def prefixEnd_1523758 : Nat := 4983230072969 + 3 ^ 40 * 1523758 * 2
def baseEnd_1523758 : Nat := 521613503422503015678247

theorem tailTrace_1523758 : CollatzResearch.WordTrace tailWord_1523758 prefixEnd_1523758 521613503422503015678247 := by
  unfold tailWord_1523758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947002501711559749121491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37050680009128318661981285 6947002501711559749121491)
  ·
    refine ⟨10420503752567339623682237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947002501711559749121491 10420503752567339623682237)
    ·
      refine ⟨3907688907212752358880839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10420503752567339623682237 3907688907212752358880839)
      ·
        refine ⟨5861533360819128538321259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907688907212752358880839 5861533360819128538321259)
        ·
          refine ⟨8792300041228692807481889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861533360819128538321259 8792300041228692807481889)
          ·
            refine ⟨6594225030921519605611417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8792300041228692807481889 6594225030921519605611417)
            ·
              refine ⟨4945668773191139704208563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594225030921519605611417 4945668773191139704208563)
              ·
                refine ⟨7418503159786709556312845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945668773191139704208563 7418503159786709556312845)
                ·
                  refine ⟨2781938684920016083617317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7418503159786709556312845 2781938684920016083617317)
                  ·
                    refine ⟨521613503422503015678247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781938684920016083617317 521613503422503015678247)
                    ·
                      rfl

theorem cell22_1523758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1523758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523758 prefixEnd_1523758 := by exact prefixLift 1523758
  have htrace : WordTrace (prefixWord ++ tailWord_1523758) baseStart_1523758 baseEnd_1523758 := by
    simpa [prefixWord, tailWord_1523758, baseEnd_1523758] using wordTrace_append hprefix tailTrace_1523758
  have hstable : (prefixWord ++ tailWord_1523758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523758).length < 2 ^ (prefixWord ++ tailWord_1523758).sum := by decide
  have hdescent : baseEnd_1523758 < baseStart_1523758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523771 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 6, 3]
def baseStart_1523771 : Nat := 118140960795 + 1523771 * 2 ^ 59
def prefixEnd_1523771 : Nat := 4983230072969 + 3 ^ 40 * 1523771 * 2
def baseEnd_1523771 : Nat := 521617953588175315103207

theorem tailTrace_1523771 : CollatzResearch.WordTrace tailWord_1523771 prefixEnd_1523771 521617953588175315103207 := by
  unfold tailWord_1523771
  simp only [CollatzResearch.WordTrace]
  refine ⟨55576494162645381213195167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37050996108430254142130111 55576494162645381213195167)
  ·
    refine ⟨83364741243968071819792751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55576494162645381213195167 83364741243968071819792751)
    ·
      refine ⟨125047111865952107729689127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83364741243968071819792751 125047111865952107729689127)
      ·
        refine ⟨187570667798928161594533691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125047111865952107729689127 187570667798928161594533691)
        ·
          refine ⟨281356001698392242391800537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187570667798928161594533691 281356001698392242391800537)
          ·
            refine ⟨211017001273794181793850403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281356001698392242391800537 211017001273794181793850403)
            ·
              refine ⟨316525501910691272690775605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211017001273794181793850403 316525501910691272690775605)
              ·
                refine ⟨29674265804127306814760213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 316525501910691272690775605 29674265804127306814760213)
                ·
                  refine ⟨1390981209568467506941885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29674265804127306814760213 1390981209568467506941885)
                  ·
                    refine ⟨521617953588175315103207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1390981209568467506941885 521617953588175315103207)
                    ·
                      rfl

theorem cell22_1523771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 3].length) (baseStart_1523771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523771 prefixEnd_1523771 := by exact prefixLift 1523771
  have htrace : WordTrace (prefixWord ++ tailWord_1523771) baseStart_1523771 baseEnd_1523771 := by
    simpa [prefixWord, tailWord_1523771, baseEnd_1523771] using wordTrace_append hprefix tailTrace_1523771
  have hstable : (prefixWord ++ tailWord_1523771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523771).length < 2 ^ (prefixWord ++ tailWord_1523771).sum := by decide
  have hdescent : baseEnd_1523771 < baseStart_1523771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523786 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1523786 : Nat := 118140960795 + 1523786 * 2 ^ 59
def prefixEnd_1523786 : Nat := 4983230072969 + 3 ^ 40 * 1523786 * 2
def baseEnd_1523786 : Nat := 521623088394720275978161

theorem tailTrace_1523786 : CollatzResearch.WordTrace tailWord_1523786 prefixEnd_1523786 521623088394720275978161 := by
  unfold tailWord_1523786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894260314397759693747803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37051360838394025849994141 13894260314397759693747803)
  ·
    refine ⟨20841390471596639540621705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894260314397759693747803 20841390471596639540621705)
    ·
      refine ⟨15631042853697479655466279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20841390471596639540621705 15631042853697479655466279)
      ·
        refine ⟨23446564280546219483199419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15631042853697479655466279 23446564280546219483199419)
        ·
          refine ⟨35169846420819329224799129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23446564280546219483199419 35169846420819329224799129)
          ·
            refine ⟨26377384815614496918599347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35169846420819329224799129 26377384815614496918599347)
            ·
              refine ⟨39566077223421745377899021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26377384815614496918599347 39566077223421745377899021)
              ·
                refine ⟨14837278958783154516712133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39566077223421745377899021 14837278958783154516712133)
                ·
                  refine ⟨2781989804771841471883525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14837278958783154516712133 2781989804771841471883525)
                  ·
                    refine ⟨521623088394720275978161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2781989804771841471883525 521623088394720275978161)
                    ·
                      rfl

theorem cell22_1523786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1523786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523786 prefixEnd_1523786 := by exact prefixLift 1523786
  have htrace : WordTrace (prefixWord ++ tailWord_1523786) baseStart_1523786 baseEnd_1523786 := by
    simpa [prefixWord, tailWord_1523786, baseEnd_1523786] using wordTrace_append hprefix tailTrace_1523786
  have hstable : (prefixWord ++ tailWord_1523786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523786).length < 2 ^ (prefixWord ++ tailWord_1523786).sum := by decide
  have hdescent : baseEnd_1523786 < baseStart_1523786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523805 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1523805 : Nat := 118140960795 + 1523805 * 2 ^ 59
def prefixEnd_1523805 : Nat := 4983230072969 + 3 ^ 40 * 1523805 * 2
def baseEnd_1523805 : Nat := 521629592483010559753103

theorem tailTrace_1523805 : CollatzResearch.WordTrace tailWord_1523805 prefixEnd_1523805 521629592483010559753103 := by
  unfold tailWord_1523805
  simp only [CollatzResearch.WordTrace]
  refine ⟨55577734244522205019932869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37051822829681470013288579 55577734244522205019932869)
  ·
    refine ⟨10420825170847913441237413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55577734244522205019932869 10420825170847913441237413)
    ·
      refine ⟨1953904719533983770232015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10420825170847913441237413 1953904719533983770232015)
      ·
        refine ⟨2930857079300975655348023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953904719533983770232015 2930857079300975655348023)
        ·
          refine ⟨4396285618951463483022035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930857079300975655348023 4396285618951463483022035)
          ·
            refine ⟨6594428428427195224533053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396285618951463483022035 6594428428427195224533053)
            ·
              refine ⟨2472910660660198209199895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6594428428427195224533053 2472910660660198209199895)
              ·
                refine ⟨3709365990990297313799843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472910660660198209199895 3709365990990297313799843)
                ·
                  refine ⟨5564048986485445970699765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709365990990297313799843 5564048986485445970699765)
                  ·
                    refine ⟨521629592483010559753103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5564048986485445970699765 521629592483010559753103)
                    ·
                      rfl

theorem cell22_1523805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1523805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523805 prefixEnd_1523805 := by exact prefixLift 1523805
  have htrace : WordTrace (prefixWord ++ tailWord_1523805) baseStart_1523805 baseEnd_1523805 := by
    simpa [prefixWord, tailWord_1523805, baseEnd_1523805] using wordTrace_append hprefix tailTrace_1523805
  have hstable : (prefixWord ++ tailWord_1523805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523805).length < 2 ^ (prefixWord ++ tailWord_1523805).sum := by decide
  have hdescent : baseEnd_1523805 < baseStart_1523805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523818 : List Nat := [3, 1, 3, 2, 3, 1, 1, 8]
def baseStart_1523818 : Nat := 118140960795 + 1523818 * 2 ^ 59
def prefixEnd_1523818 : Nat := 4983230072969 + 3 ^ 40 * 1523818 * 2
def baseEnd_1523818 : Nat := 57959338072075873242007

theorem tailTrace_1523818 : CollatzResearch.WordTrace tailWord_1523818 prefixEnd_1523818 57959338072075873242007 := by
  unfold tailWord_1523818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894552098368777060039027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37052138928983405493437405 13894552098368777060039027)
  ·
    refine ⟨20841828147553165590058541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894552098368777060039027 20841828147553165590058541)
    ·
      refine ⟨7815685555332437096271953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20841828147553165590058541 7815685555332437096271953)
      ·
        refine ⟨5861764166499327822203965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7815685555332437096271953 5861764166499327822203965)
        ·
          refine ⟨2198161562437247933326487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5861764166499327822203965 2198161562437247933326487)
          ·
            refine ⟨3297242343655871899989731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198161562437247933326487 3297242343655871899989731)
            ·
              refine ⟨4945863515483807849984597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297242343655871899989731 4945863515483807849984597)
              ·
                refine ⟨57959338072075873242007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4945863515483807849984597 57959338072075873242007)
                ·
                  rfl

theorem cell22_1523818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_1523818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523818 prefixEnd_1523818 := by exact prefixLift 1523818
  have htrace : WordTrace (prefixWord ++ tailWord_1523818) baseStart_1523818 baseEnd_1523818 := by
    simpa [prefixWord, tailWord_1523818, baseEnd_1523818] using wordTrace_append hprefix tailTrace_1523818
  have hstable : (prefixWord ++ tailWord_1523818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523818).length < 2 ^ (prefixWord ++ tailWord_1523818).sum := by decide
  have hdescent : baseEnd_1523818 < baseStart_1523818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523850 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1523850 : Nat := 118140960795 + 1523850 * 2 ^ 59
def prefixEnd_1523850 : Nat := 4983230072969 + 3 ^ 40 * 1523850 * 2
def baseEnd_1523850 : Nat := 521644996902645442377965

theorem tailTrace_1523850 : CollatzResearch.WordTrace tailWord_1523850 prefixEnd_1523850 521644996902645442377965 := by
  unfold tailWord_1523850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894843882339794426330251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37052917019572785136880669 13894843882339794426330251)
  ·
    refine ⟨20842265823509691639495377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894843882339794426330251 20842265823509691639495377)
    ·
      refine ⟨15631699367632268729621533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20842265823509691639495377 15631699367632268729621533)
      ·
        refine ⟨5861887262862100773608075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15631699367632268729621533 5861887262862100773608075)
        ·
          refine ⟨8792830894293151160412113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861887262862100773608075 8792830894293151160412113)
          ·
            refine ⟨6594623170719863370309085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8792830894293151160412113 6594623170719863370309085)
            ·
              refine ⟨2472983689019948763865907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6594623170719863370309085 2472983689019948763865907)
              ·
                refine ⟨3709475533529923145798861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472983689019948763865907 3709475533529923145798861)
                ·
                  refine ⟨1391053325073721179674573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3709475533529923145798861 1391053325073721179674573)
                  ·
                    refine ⟨521644996902645442377965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391053325073721179674573 521644996902645442377965)
                    ·
                      rfl

theorem cell22_1523850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1523850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523850 prefixEnd_1523850 := by exact prefixLift 1523850
  have htrace : WordTrace (prefixWord ++ tailWord_1523850) baseStart_1523850 baseEnd_1523850 := by
    simpa [prefixWord, tailWord_1523850, baseEnd_1523850] using wordTrace_append hprefix tailTrace_1523850
  have hstable : (prefixWord ++ tailWord_1523850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523850).length < 2 ^ (prefixWord ++ tailWord_1523850).sum := by decide
  have hdescent : baseEnd_1523850 < baseStart_1523850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523861 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1523861 : Nat := 118140960795 + 1523861 * 2 ^ 59
def prefixEnd_1523861 : Nat := 4983230072969 + 3 ^ 40 * 1523861 * 2
def baseEnd_1523861 : Nat := 521648762427445080352931

theorem tailTrace_1523861 : CollatzResearch.WordTrace tailWord_1523861 prefixEnd_1523861 521648762427445080352931 := by
  unfold tailWord_1523861
  simp only [CollatzResearch.WordTrace]
  refine ⟨55579776732319326583971437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37053184488212884389314291 55579776732319326583971437)
  ·
    refine ⟨20842416274619747468989289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55579776732319326583971437 20842416274619747468989289)
    ·
      refine ⟨15631812205964810601741967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20842416274619747468989289 15631812205964810601741967)
      ·
        refine ⟨23447718308947215902612951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15631812205964810601741967 23447718308947215902612951)
        ·
          refine ⟨35171577463420823853919427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23447718308947215902612951 35171577463420823853919427)
          ·
            refine ⟨52757366195131235780879141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35171577463420823853919427 52757366195131235780879141)
            ·
              refine ⟨9892006161587106708914839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52757366195131235780879141 9892006161587106708914839)
              ·
                refine ⟨14838009242380660063372259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9892006161587106708914839 14838009242380660063372259)
                ·
                  refine ⟨22257013863570990095058389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14838009242380660063372259 22257013863570990095058389)
                  ·
                    refine ⟨521648762427445080352931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22257013863570990095058389 521648762427445080352931)
                    ·
                      rfl

theorem cell22_1523861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1523861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523861 prefixEnd_1523861 := by exact prefixLift 1523861
  have htrace : WordTrace (prefixWord ++ tailWord_1523861) baseStart_1523861 baseEnd_1523861 := by
    simpa [prefixWord, tailWord_1523861, baseEnd_1523861] using wordTrace_append hprefix tailTrace_1523861
  have hstable : (prefixWord ++ tailWord_1523861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523861).length < 2 ^ (prefixWord ++ tailWord_1523861).sum := by decide
  have hdescent : baseEnd_1523861 < baseStart_1523861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523925 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 6]
def baseStart_1523925 : Nat := 118140960795 + 1523925 * 2 ^ 59
def prefixEnd_1523925 : Nat := 4983230072969 + 3 ^ 40 * 1523925 * 2
def baseEnd_1523925 : Nat := 173890223645123415584245

theorem tailTrace_1523925 : CollatzResearch.WordTrace tailWord_1523925 prefixEnd_1523925 173890223645123415584245 := by
  unfold tailWord_1523925
  simp only [CollatzResearch.WordTrace]
  refine ⟨55582111004087465514301229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37054740669391643676200819 55582111004087465514301229)
  ·
    refine ⟨20843291626532799567862961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55582111004087465514301229 20843291626532799567862961)
    ·
      refine ⟨15632468719899599675897221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20843291626532799567862961 15632468719899599675897221)
      ·
        refine ⟨2931087884981174939230729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15632468719899599675897221 2931087884981174939230729)
        ·
          refine ⟨2198315913735881204423047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931087884981174939230729 2198315913735881204423047)
          ·
            refine ⟨3297473870603821806634571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198315913735881204423047 3297473870603821806634571)
            ·
              refine ⟨4946210805905732709951857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297473870603821806634571 4946210805905732709951857)
              ·
                refine ⟨3709658104429299532463893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4946210805905732709951857 3709658104429299532463893)
                ·
                  refine ⟨173890223645123415584245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3709658104429299532463893 173890223645123415584245)
                  ·
                    rfl

theorem cell22_1523925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_1523925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523925 prefixEnd_1523925 := by exact prefixLift 1523925
  have htrace : WordTrace (prefixWord ++ tailWord_1523925) baseStart_1523925 baseEnd_1523925 := by
    simpa [prefixWord, tailWord_1523925, baseEnd_1523925] using wordTrace_append hprefix tailTrace_1523925
  have hstable : (prefixWord ++ tailWord_1523925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523925).length < 2 ^ (prefixWord ++ tailWord_1523925).sum := by decide
  have hdescent : baseEnd_1523925 < baseStart_1523925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1523985 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_1523985 : Nat := 118140960795 + 1523985 * 2 ^ 59
def prefixEnd_1523985 : Nat := 4983230072969 + 3 ^ 40 * 1523985 * 2
def baseEnd_1523985 : Nat := 521691210161550090252551

theorem tailTrace_1523985 : CollatzResearch.WordTrace tailWord_1523985 prefixEnd_1523985 521691210161550090252551 := by
  unfold tailWord_1523985
  simp only [CollatzResearch.WordTrace]
  refine ⟨55584299383870095761485409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37056199589246730507656939 55584299383870095761485409)
  ·
    refine ⟨41688224537902571821114057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55584299383870095761485409 41688224537902571821114057)
    ·
      refine ⟨31266168403426928865835543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41688224537902571821114057 31266168403426928865835543)
      ·
        refine ⟨46899252605140393298753315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31266168403426928865835543 46899252605140393298753315)
        ·
          refine ⟨70348878907710589948129973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46899252605140393298753315 70348878907710589948129973)
          ·
            refine ⟨6595207397597867807637185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70348878907710589948129973 6595207397597867807637185)
            ·
              refine ⟨4946405548198400855727889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6595207397597867807637185 4946405548198400855727889)
              ·
                refine ⟨3709804161148800641795917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4946405548198400855727889 3709804161148800641795917)
                ·
                  refine ⟨1391176560430800240673469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3709804161148800641795917 1391176560430800240673469)
                  ·
                    refine ⟨521691210161550090252551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391176560430800240673469 521691210161550090252551)
                    ·
                      rfl

theorem cell22_1523985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_1523985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1523985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1523985 prefixEnd_1523985 := by exact prefixLift 1523985
  have htrace : WordTrace (prefixWord ++ tailWord_1523985) baseStart_1523985 baseEnd_1523985 := by
    simpa [prefixWord, tailWord_1523985, baseEnd_1523985] using wordTrace_append hprefix tailTrace_1523985
  have hstable : (prefixWord ++ tailWord_1523985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1523985).length < 2 ^ (prefixWord ++ tailWord_1523985).sum := by decide
  have hdescent : baseEnd_1523985 < baseStart_1523985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1523985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524019 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 1, 3]
def baseStart_1524019 : Nat := 118140960795 + 1524019 * 2 ^ 59
def prefixEnd_1524019 : Nat := 4983230072969 + 3 ^ 40 * 1524019 * 2
def baseEnd_1524019 : Nat := 521702849056385334902447

theorem tailTrace_1524019 : CollatzResearch.WordTrace tailWord_1524019 prefixEnd_1524019 521702849056385334902447 := by
  unfold tailWord_1524019
  simp only [CollatzResearch.WordTrace]
  refine ⟨55585539465746919568223111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37057026310497946378815407 55585539465746919568223111)
  ·
    refine ⟨83378309198620379352334667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55585539465746919568223111 83378309198620379352334667)
    ·
      refine ⟨125067463797930569028502001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83378309198620379352334667 125067463797930569028502001)
      ·
        refine ⟨93800597848447926771376501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125067463797930569028502001 93800597848447926771376501)
        ·
          refine ⟨8793806048291993134816547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93800597848447926771376501 8793806048291993134816547)
          ·
            refine ⟨13190709072437989702224821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793806048291993134816547 13190709072437989702224821)
            ·
              refine ⟨1236628975541061534583577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13190709072437989702224821 1236628975541061534583577)
              ·
                refine ⟨927471731655796150937683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236628975541061534583577 927471731655796150937683)
                ·
                  refine ⟨1391207597483694226406525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927471731655796150937683 1391207597483694226406525)
                  ·
                    refine ⟨521702849056385334902447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391207597483694226406525 521702849056385334902447)
                    ·
                      rfl

theorem cell22_1524019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 3].length) (baseStart_1524019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524019 prefixEnd_1524019 := by exact prefixLift 1524019
  have htrace : WordTrace (prefixWord ++ tailWord_1524019) baseStart_1524019 baseEnd_1524019 := by
    simpa [prefixWord, tailWord_1524019, baseEnd_1524019] using wordTrace_append hprefix tailTrace_1524019
  have hstable : (prefixWord ++ tailWord_1524019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524019).length < 2 ^ (prefixWord ++ tailWord_1524019).sum := by decide
  have hdescent : baseEnd_1524019 < baseStart_1524019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524077 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 4]
def baseStart_1524077 : Nat := 118140960795 + 1524077 * 2 ^ 59
def prefixEnd_1524077 : Nat := 4983230072969 + 3 ^ 40 * 1524077 * 2
def baseEnd_1524077 : Nat := 173907567880564172317423

theorem tailTrace_1524077 : CollatzResearch.WordTrace tailWord_1524077 prefixEnd_1524077 173907567880564172317423 := by
  unfold tailWord_1524077
  simp only [CollatzResearch.WordTrace]
  refine ⟨55587654899536795473834485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37058436599691196982556323 55587654899536795473834485)
  ·
    refine ⟨5211342646831574575671983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55587654899536795473834485 5211342646831574575671983)
    ·
      refine ⟨7817013970247361863507975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211342646831574575671983 7817013970247361863507975)
      ·
        refine ⟨11725520955371042795261963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817013970247361863507975 11725520955371042795261963)
        ·
          refine ⟨17588281433056564192892945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11725520955371042795261963 17588281433056564192892945)
          ·
            refine ⟨13191211074792423144669709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17588281433056564192892945 13191211074792423144669709)
            ·
              refine ⟨4946704153047158679251141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13191211074792423144669709 4946704153047158679251141)
              ·
                refine ⟨927507028696342252359589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4946704153047158679251141 927507028696342252359589)
                ·
                  refine ⟨173907567880564172317423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927507028696342252359589 173907567880564172317423)
                  ·
                    rfl

theorem cell22_1524077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_1524077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524077 prefixEnd_1524077 := by exact prefixLift 1524077
  have htrace : WordTrace (prefixWord ++ tailWord_1524077) baseStart_1524077 baseEnd_1524077 := by
    simpa [prefixWord, tailWord_1524077, baseEnd_1524077] using wordTrace_append hprefix tailTrace_1524077
  have hstable : (prefixWord ++ tailWord_1524077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524077).length < 2 ^ (prefixWord ++ tailWord_1524077).sum := by decide
  have hdescent : baseEnd_1524077 < baseStart_1524077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524107 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 2, 4]
def baseStart_1524107 : Nat := 118140960795 + 1524107 * 2 ^ 59
def prefixEnd_1524107 : Nat := 4983230072969 + 3 ^ 40 * 1524107 * 2
def baseEnd_1524107 : Nat := 521732973254782438702177

theorem tailTrace_1524107 : CollatzResearch.WordTrace tailWord_1524107 prefixEnd_1524107 521732973254782438702177 := by
  unfold tailWord_1524107
  simp only [CollatzResearch.WordTrace]
  refine ⟨55588749089428110597426575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37059166059618740398284383 55588749089428110597426575)
  ·
    refine ⟨83383123634142165896139863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55588749089428110597426575 83383123634142165896139863)
    ·
      refine ⟨125074685451213248844209795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83383123634142165896139863 125074685451213248844209795)
      ·
        refine ⟨187612028176819873266314693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125074685451213248844209795 187612028176819873266314693)
        ·
          refine ⟨35177255283153726237434005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187612028176819873266314693 35177255283153726237434005)
          ·
            refine ⟨1648933841397830917379719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35177255283153726237434005 1648933841397830917379719)
            ·
              refine ⟨2473400762096746376069579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648933841397830917379719 2473400762096746376069579)
              ·
                refine ⟨3710101143145119564104369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473400762096746376069579 3710101143145119564104369)
                ·
                  refine ⟨2782575857358839673078277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3710101143145119564104369 2782575857358839673078277)
                  ·
                    refine ⟨521732973254782438702177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2782575857358839673078277 521732973254782438702177)
                    ·
                      rfl

theorem cell22_1524107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 4].length) (baseStart_1524107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524107 prefixEnd_1524107 := by exact prefixLift 1524107
  have htrace : WordTrace (prefixWord ++ tailWord_1524107) baseStart_1524107 baseEnd_1524107 := by
    simpa [prefixWord, tailWord_1524107, baseEnd_1524107] using wordTrace_append hprefix tailTrace_1524107
  have hstable : (prefixWord ++ tailWord_1524107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524107).length < 2 ^ (prefixWord ++ tailWord_1524107).sum := by decide
  have hdescent : baseEnd_1524107 < baseStart_1524107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524126 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1524126 : Nat := 118140960795 + 1524126 * 2 ^ 59
def prefixEnd_1524126 : Nat := 4983230072969 + 3 ^ 40 * 1524126 * 2
def baseEnd_1524126 : Nat := 521739477343072722477119

theorem tailTrace_1524126 : CollatzResearch.WordTrace tailWord_1524126 prefixEnd_1524126 521739477343072722477119 := by
  unfold tailWord_1524126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948680259544909605296029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37059628050906184561578821 6948680259544909605296029)
  ·
    refine ⟨2605755097329341101986011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6948680259544909605296029 2605755097329341101986011)
    ·
      refine ⟨3908632645994011652979017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2605755097329341101986011 3908632645994011652979017)
      ·
        refine ⟨2931474484495508739734263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3908632645994011652979017 2931474484495508739734263)
        ·
          refine ⟨4397211726743263109601395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931474484495508739734263 4397211726743263109601395)
          ·
            refine ⟨6595817590114894664402093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397211726743263109601395 6595817590114894664402093)
            ·
              refine ⟨2473431596293085499150785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6595817590114894664402093 2473431596293085499150785)
              ·
                refine ⟨1855073697219814124363089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473431596293085499150785 1855073697219814124363089)
                ·
                  refine ⟨1391305272914860593272317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1855073697219814124363089 1391305272914860593272317)
                  ·
                    refine ⟨521739477343072722477119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391305272914860593272317 521739477343072722477119)
                    ·
                      rfl

theorem cell22_1524126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1524126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524126 prefixEnd_1524126 := by exact prefixLift 1524126
  have htrace : WordTrace (prefixWord ++ tailWord_1524126) baseStart_1524126 baseEnd_1524126 := by
    simpa [prefixWord, tailWord_1524126, baseEnd_1524126] using wordTrace_append hprefix tailTrace_1524126
  have hstable : (prefixWord ++ tailWord_1524126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524126).length < 2 ^ (prefixWord ++ tailWord_1524126).sum := by decide
  have hdescent : baseEnd_1524126 < baseStart_1524126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524231 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 1, 4]
def baseStart_1524231 : Nat := 118140960795 + 1524231 * 2 ^ 59
def prefixEnd_1524231 : Nat := 4983230072969 + 3 ^ 40 * 1524231 * 2
def baseEnd_1524231 : Nat := 521775420988887448601797

theorem tailTrace_1524231 : CollatzResearch.WordTrace tailWord_1524231 prefixEnd_1524231 521775420988887448601797 := by
  unfold tailWord_1524231
  simp only [CollatzResearch.WordTrace]
  refine ⟨55593271740978879774940547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37062181160652586516627031 55593271740978879774940547)
  ·
    refine ⟨83389907611468319662410821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55593271740978879774940547 83389907611468319662410821)
    ·
      refine ⟨15635607677150309936702029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83389907611468319662410821 15635607677150309936702029)
      ·
        refine ⟨5863352878931366226263261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15635607677150309936702029 5863352878931366226263261)
        ·
          refine ⟨2198757329599262334848723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5863352878931366226263261 2198757329599262334848723)
          ·
            refine ⟨3298135994398893502273085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198757329599262334848723 3298135994398893502273085)
            ·
              refine ⟨1236800997899585063352407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3298135994398893502273085 1236800997899585063352407)
              ·
                refine ⟨1855201496849377595028611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236800997899585063352407 1855201496849377595028611)
                ·
                  refine ⟨2782802245274066392542917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855201496849377595028611 2782802245274066392542917)
                  ·
                    refine ⟨521775420988887448601797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2782802245274066392542917 521775420988887448601797)
                    ·
                      rfl

theorem cell22_1524231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_1524231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524231 prefixEnd_1524231 := by exact prefixLift 1524231
  have htrace : WordTrace (prefixWord ++ tailWord_1524231) baseStart_1524231 baseEnd_1524231 := by
    simpa [prefixWord, tailWord_1524231, baseEnd_1524231] using wordTrace_append hprefix tailTrace_1524231
  have hstable : (prefixWord ++ tailWord_1524231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524231).length < 2 ^ (prefixWord ++ tailWord_1524231).sum := by decide
  have hdescent : baseEnd_1524231 < baseStart_1524231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524255 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_1524255 : Nat := 118140960795 + 1524255 * 2 ^ 59
def prefixEnd_1524255 : Nat := 4983230072969 + 3 ^ 40 * 1524255 * 2
def baseEnd_1524255 : Nat := 521783636679359386001723

theorem tailTrace_1524255 : CollatzResearch.WordTrace tailWord_1524255 prefixEnd_1524255 521783636679359386001723 := by
  unfold tailWord_1524255
  simp only [CollatzResearch.WordTrace]
  refine ⟨55594147092891931873814219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37062764728594621249209479 55594147092891931873814219)
  ·
    refine ⟨83391220639337897810721329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55594147092891931873814219 83391220639337897810721329)
    ·
      refine ⟨62543415479503423358040997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83391220639337897810721329 62543415479503423358040997)
      ·
        refine ⟨11726890402406891879632687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62543415479503423358040997 11726890402406891879632687)
        ·
          refine ⟨17590335603610337819449031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11726890402406891879632687 17590335603610337819449031)
          ·
            refine ⟨26385503405415506729173547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17590335603610337819449031 26385503405415506729173547)
            ·
              refine ⟨39578255108123260093760321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26385503405415506729173547 39578255108123260093760321)
              ·
                refine ⟨29683691331092445070320241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39578255108123260093760321 29683691331092445070320241)
                ·
                  refine ⟨22262768498319333802740181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29683691331092445070320241 22262768498319333802740181)
                  ·
                    refine ⟨521783636679359386001723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22262768498319333802740181 521783636679359386001723)
                    ·
                      rfl

theorem cell22_1524255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_1524255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524255 prefixEnd_1524255 := by exact prefixLift 1524255
  have htrace : WordTrace (prefixWord ++ tailWord_1524255) baseStart_1524255 baseEnd_1524255 := by
    simpa [prefixWord, tailWord_1524255, baseEnd_1524255] using wordTrace_append hprefix tailTrace_1524255
  have hstable : (prefixWord ++ tailWord_1524255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524255).length < 2 ^ (prefixWord ++ tailWord_1524255).sum := by decide
  have hdescent : baseEnd_1524255 < baseStart_1524255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524272 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_1524272 : Nat := 118140960795 + 1524272 * 2 ^ 59
def prefixEnd_1524272 : Nat := 4983230072969 + 3 ^ 40 * 1524272 * 2
def baseEnd_1524272 : Nat := 521789456126777008326671

theorem tailTrace_1524272 : CollatzResearch.WordTrace tailWord_1524272 prefixEnd_1524272 521789456126777008326671 := by
  unfold tailWord_1524272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27797383566915171888591535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37063178089220229184788713 27797383566915171888591535)
  ·
    refine ⟨41696075350372757832887303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27797383566915171888591535 41696075350372757832887303)
    ·
      refine ⟨62544113025559136749330955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41696075350372757832887303 62544113025559136749330955)
      ·
        refine ⟨93816169538338705123996433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62544113025559136749330955 93816169538338705123996433)
        ·
          refine ⟨70362127153754028842997325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93816169538338705123996433 70362127153754028842997325)
          ·
            refine ⟨26385797682657760816123997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70362127153754028842997325 26385797682657760816123997)
            ·
              refine ⟨9894674130996660306046499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26385797682657760816123997 9894674130996660306046499)
              ·
                refine ⟨14842011196494990459069749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894674130996660306046499 14842011196494990459069749)
                ·
                  refine ⟨1391438549671405355537789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14842011196494990459069749 1391438549671405355537789)
                  ·
                    refine ⟨521789456126777008326671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391438549671405355537789 521789456126777008326671)
                    ·
                      rfl

theorem cell22_1524272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_1524272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524272 prefixEnd_1524272 := by exact prefixLift 1524272
  have htrace : WordTrace (prefixWord ++ tailWord_1524272) baseStart_1524272 baseEnd_1524272 := by
    simpa [prefixWord, tailWord_1524272, baseEnd_1524272] using wordTrace_append hprefix tailTrace_1524272
  have hstable : (prefixWord ++ tailWord_1524272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524272).length < 2 ^ (prefixWord ++ tailWord_1524272).sum := by decide
  have hdescent : baseEnd_1524272 < baseStart_1524272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524276 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1524276 : Nat := 118140960795 + 1524276 * 2 ^ 59
def prefixEnd_1524276 : Nat := 4983230072969 + 3 ^ 40 * 1524276 * 2
def baseEnd_1524276 : Nat := 521790825408522331226659

theorem tailTrace_1524276 : CollatzResearch.WordTrace tailWord_1524276 prefixEnd_1524276 521790825408522331226659 := by
  unfold tailWord_1524276
  simp only [CollatzResearch.WordTrace]
  refine ⟨27797456512907926230164341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37063275350543901640219121 27797456512907926230164341)
  ·
    refine ⟨2606011548085118084077907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27797456512907926230164341 2606011548085118084077907)
    ·
      refine ⟨3909017322127677126116861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606011548085118084077907 3909017322127677126116861)
      ·
        refine ⟨1465881495797878922293823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3909017322127677126116861 1465881495797878922293823)
        ·
          refine ⟨2198822243696818383440735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465881495797878922293823 2198822243696818383440735)
          ·
            refine ⟨3298233365545227575161103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198822243696818383440735 3298233365545227575161103)
            ·
              refine ⟨4947350048317841362741655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298233365545227575161103 4947350048317841362741655)
              ·
                refine ⟨7421025072476762044112483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947350048317841362741655 7421025072476762044112483)
                ·
                  refine ⟨11131537608715143066168725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421025072476762044112483 11131537608715143066168725)
                  ·
                    refine ⟨521790825408522331226659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11131537608715143066168725 521790825408522331226659)
                    ·
                      rfl

theorem cell22_1524276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1524276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524276 prefixEnd_1524276 := by exact prefixLift 1524276
  have htrace : WordTrace (prefixWord ++ tailWord_1524276) baseStart_1524276 baseEnd_1524276 := by
    simpa [prefixWord, tailWord_1524276, baseEnd_1524276] using wordTrace_append hprefix tailTrace_1524276
  have hstable : (prefixWord ++ tailWord_1524276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524276).length < 2 ^ (prefixWord ++ tailWord_1524276).sum := by decide
  have hdescent : baseEnd_1524276 < baseStart_1524276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524306 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_1524306 : Nat := 118140960795 + 1524306 * 2 ^ 59
def prefixEnd_1524306 : Nat := 4983230072969 + 3 ^ 40 * 1524306 * 2
def baseEnd_1524306 : Nat := 521801095021612252976567

theorem tailTrace_1524306 : CollatzResearch.WordTrace tailWord_1524306 prefixEnd_1524306 521801095021612252976567 := by
  unfold tailWord_1524306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13899001803926791895980193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37064004810471445055947181 13899001803926791895980193)
  ·
    refine ⟨10424251352945093921985145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13899001803926791895980193 10424251352945093921985145)
    ·
      refine ⟨7818188514708820441488859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10424251352945093921985145 7818188514708820441488859)
      ·
        refine ⟨11727282772063230662233289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7818188514708820441488859 11727282772063230662233289)
        ·
          refine ⟨8795462079047422996674967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11727282772063230662233289 8795462079047422996674967)
          ·
            refine ⟨13193193118571134495012451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8795462079047422996674967 13193193118571134495012451)
            ·
              refine ⟨19789789677856701742518677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13193193118571134495012451 19789789677856701742518677)
              ·
                refine ⟨927646391149532894180563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19789789677856701742518677 927646391149532894180563)
                ·
                  refine ⟨1391469586724299341270845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927646391149532894180563 1391469586724299341270845)
                  ·
                    refine ⟨521801095021612252976567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391469586724299341270845 521801095021612252976567)
                    ·
                      rfl

theorem cell22_1524306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_1524306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524306 prefixEnd_1524306 := by exact prefixLift 1524306
  have htrace : WordTrace (prefixWord ++ tailWord_1524306) baseStart_1524306 baseEnd_1524306 := by
    simpa [prefixWord, tailWord_1524306, baseEnd_1524306] using wordTrace_append hprefix tailTrace_1524306
  have hstable : (prefixWord ++ tailWord_1524306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524306).length < 2 ^ (prefixWord ++ tailWord_1524306).sum := by decide
  have hdescent : baseEnd_1524306 < baseStart_1524306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524332 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_1524332 : Nat := 118140960795 + 1524332 * 2 ^ 59
def prefixEnd_1524332 : Nat := 4983230072969 + 3 ^ 40 * 1524332 * 2
def baseEnd_1524332 : Nat := 521809995352956851826487

theorem tailTrace_1524332 : CollatzResearch.WordTrace tailWord_1524332 prefixEnd_1524332 521809995352956851826487 := by
  unfold tailWord_1524332
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798477756806487012183625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37064637009075316016244833 27798477756806487012183625)
  ·
    refine ⟨20848858317604865259137719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27798477756806487012183625 20848858317604865259137719)
    ·
      refine ⟨31273287476407297888706579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20848858317604865259137719 31273287476407297888706579)
      ·
        refine ⟨46909931214610946833059869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31273287476407297888706579 46909931214610946833059869)
        ·
          refine ⟨17591224205479105062397451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46909931214610946833059869 17591224205479105062397451)
          ·
            refine ⟨26386836308218657593596177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17591224205479105062397451 26386836308218657593596177)
            ·
              refine ⟨19790127231163993195197133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26386836308218657593596177 19790127231163993195197133)
              ·
                refine ⟨7421297711686497448198925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19790127231163993195197133 7421297711686497448198925)
                ·
                  refine ⟨2782986641882436543074597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7421297711686497448198925 2782986641882436543074597)
                  ·
                    refine ⟨521809995352956851826487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2782986641882436543074597 521809995352956851826487)
                    ·
                      rfl

theorem cell22_1524332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_1524332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524332 prefixEnd_1524332 := by exact prefixLift 1524332
  have htrace : WordTrace (prefixWord ++ tailWord_1524332) baseStart_1524332 baseEnd_1524332 := by
    simpa [prefixWord, tailWord_1524332, baseEnd_1524332] using wordTrace_append hprefix tailTrace_1524332
  have hstable : (prefixWord ++ tailWord_1524332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524332).length < 2 ^ (prefixWord ++ tailWord_1524332).sum := by decide
  have hdescent : baseEnd_1524332 < baseStart_1524332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524377 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_1524377 : Nat := 118140960795 + 1524377 * 2 ^ 59
def prefixEnd_1524377 : Nat := 4983230072969 + 3 ^ 40 * 1524377 * 2
def baseEnd_1524377 : Nat := 521825399772591734451349

theorem tailTrace_1524377 : CollatzResearch.WordTrace tailWord_1524377 prefixEnd_1524377 521825399772591734451349 := by
  unfold tailWord_1524377
  simp only [CollatzResearch.WordTrace]
  refine ⟨55598596798449946709755385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37065731198966631139836923 55598596798449946709755385)
  ·
    refine ⟨41698947598837460032316539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55598596798449946709755385 41698947598837460032316539)
    ·
      refine ⟨62548421398256190048474809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41698947598837460032316539 62548421398256190048474809)
      ·
        refine ⟨46911316048692142536356107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62548421398256190048474809 46911316048692142536356107)
        ·
          refine ⟨70366974073038213804534161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46911316048692142536356107 70366974073038213804534161)
          ·
            refine ⟨52775230554778660353400621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70366974073038213804534161 52775230554778660353400621)
            ·
              refine ⟨19790711458041997632525233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52775230554778660353400621 19790711458041997632525233)
              ·
                refine ⟨14843033593531498224393925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19790711458041997632525233 14843033593531498224393925)
                ·
                  refine ⟨2783068798787155917073861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14843033593531498224393925 2783068798787155917073861)
                  ·
                    refine ⟨521825399772591734451349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2783068798787155917073861 521825399772591734451349)
                    ·
                      rfl

theorem cell22_1524377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_1524377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524377 prefixEnd_1524377 := by exact prefixLift 1524377
  have htrace : WordTrace (prefixWord ++ tailWord_1524377) baseStart_1524377 baseEnd_1524377 := by
    simpa [prefixWord, tailWord_1524377, baseEnd_1524377] using wordTrace_append hprefix tailTrace_1524377
  have hstable : (prefixWord ++ tailWord_1524377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524377).length < 2 ^ (prefixWord ++ tailWord_1524377).sum := by decide
  have hdescent : baseEnd_1524377 < baseStart_1524377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524501 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1524501 : Nat := 118140960795 + 1524501 * 2 ^ 59
def prefixEnd_1524501 : Nat := 4983230072969 + 3 ^ 40 * 1524501 * 2
def baseEnd_1524501 : Nat := 521867847506696744350969

theorem tailTrace_1524501 : CollatzResearch.WordTrace tailWord_1524501 prefixEnd_1524501 521867847506696744350969 := by
  unfold tailWord_1524501
  simp only [CollatzResearch.WordTrace]
  refine ⟨55603119450000715887269357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37068746300000477258179571 55603119450000715887269357)
  ·
    refine ⟨20851169793750268457726009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55603119450000715887269357 20851169793750268457726009)
    ·
      refine ⟨15638377345312701343294507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20851169793750268457726009 15638377345312701343294507)
      ·
        refine ⟨23457566017969052014941761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15638377345312701343294507 23457566017969052014941761)
        ·
          refine ⟨17593174513476789011206321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23457566017969052014941761 17593174513476789011206321)
          ·
            refine ⟨13194880885107591758404741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17593174513476789011206321 13194880885107591758404741)
            ·
              refine ⟨2474040165957673454700889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13194880885107591758404741 2474040165957673454700889)
              ·
                refine ⟨1855530124468255091025667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474040165957673454700889 1855530124468255091025667)
                ·
                  refine ⟨2783295186702382636538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855530124468255091025667 2783295186702382636538501)
                  ·
                    refine ⟨521867847506696744350969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2783295186702382636538501 521867847506696744350969)
                    ·
                      rfl

theorem cell22_1524501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1524501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524501 prefixEnd_1524501 := by exact prefixLift 1524501
  have htrace : WordTrace (prefixWord ++ tailWord_1524501) baseStart_1524501 baseEnd_1524501 := by
    simpa [prefixWord, tailWord_1524501, baseEnd_1524501] using wordTrace_append hprefix tailTrace_1524501
  have hstable : (prefixWord ++ tailWord_1524501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524501).length < 2 ^ (prefixWord ++ tailWord_1524501).sum := by decide
  have hdescent : baseEnd_1524501 < baseStart_1524501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524509 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_1524509 : Nat := 118140960795 + 1524509 * 2 ^ 59
def prefixEnd_1524509 : Nat := 4983230072969 + 3 ^ 40 * 1524509 * 2
def baseEnd_1524509 : Nat := 521870586070187390150945

theorem tailTrace_1524509 : CollatzResearch.WordTrace tailWord_1524509 prefixEnd_1524509 521870586070187390150945 := by
  unfold tailWord_1524509
  simp only [CollatzResearch.WordTrace]
  refine ⟨55603411233971733253560581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37068940822647822169040387 55603411233971733253560581)
  ·
    refine ⟨10425639606369699985042609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55603411233971733253560581 10425639606369699985042609)
    ·
      refine ⟨7819229704777274988781957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10425639606369699985042609 7819229704777274988781957)
      ·
        refine ⟨1466105569645739060396617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7819229704777274988781957 1466105569645739060396617)
        ·
          refine ⟨1099579177234304295297463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466105569645739060396617 1099579177234304295297463)
          ·
            refine ⟨1649368765851456442946195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099579177234304295297463 1649368765851456442946195)
            ·
              refine ⟨2474053148777184664419293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649368765851456442946195 2474053148777184664419293)
              ·
                refine ⟨927769930791444249157235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2474053148777184664419293 927769930791444249157235)
                ·
                  refine ⟨1391654896187166373735853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927769930791444249157235 1391654896187166373735853)
                  ·
                    refine ⟨521870586070187390150945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391654896187166373735853 521870586070187390150945)
                    ·
                      rfl

theorem cell22_1524509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_1524509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524509 prefixEnd_1524509 := by exact prefixLift 1524509
  have htrace : WordTrace (prefixWord ++ tailWord_1524509) baseStart_1524509 baseEnd_1524509 := by
    simpa [prefixWord, tailWord_1524509, baseEnd_1524509] using wordTrace_append hprefix tailTrace_1524509
  have hstable : (prefixWord ++ tailWord_1524509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524509).length < 2 ^ (prefixWord ++ tailWord_1524509).sum := by decide
  have hdescent : baseEnd_1524509 < baseStart_1524509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524531 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 4, 3]
def baseStart_1524531 : Nat := 118140960795 + 1524531 * 2 ^ 59
def prefixEnd_1524531 : Nat := 4983230072969 + 3 ^ 40 * 1524531 * 2
def baseEnd_1524531 : Nat := 521878117119786666100877

theorem tailTrace_1524531 : CollatzResearch.WordTrace tailWord_1524531 prefixEnd_1524531 521878117119786666100877 := by
  unfold tailWord_1524531
  simp only [CollatzResearch.WordTrace]
  refine ⟨55604213639892031010861447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37069475759928020673907631 55604213639892031010861447)
  ·
    refine ⟨83406320459838046516292171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55604213639892031010861447 83406320459838046516292171)
    ·
      refine ⟨125109480689757069774438257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83406320459838046516292171 125109480689757069774438257)
      ·
        refine ⟨93832110517317802330828693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125109480689757069774438257 93832110517317802330828693)
        ·
          refine ⟨4398380180499271984257595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93832110517317802330828693 4398380180499271984257595)
          ·
            refine ⟨6597570270748907976386393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398380180499271984257595 6597570270748907976386393)
            ·
              refine ⟨4948177703061680982289795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6597570270748907976386393 4948177703061680982289795)
              ·
                refine ⟨7422266554592521473434693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948177703061680982289795 7422266554592521473434693)
                ·
                  refine ⟨1391674978986097776269005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7422266554592521473434693 1391674978986097776269005)
                  ·
                    refine ⟨521878117119786666100877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391674978986097776269005 521878117119786666100877)
                    ·
                      rfl

theorem cell22_1524531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 3].length) (baseStart_1524531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524531 prefixEnd_1524531 := by exact prefixLift 1524531
  have htrace : WordTrace (prefixWord ++ tailWord_1524531) baseStart_1524531 baseEnd_1524531 := by
    simpa [prefixWord, tailWord_1524531, baseEnd_1524531] using wordTrace_append hprefix tailTrace_1524531
  have hstable : (prefixWord ++ tailWord_1524531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524531).length < 2 ^ (prefixWord ++ tailWord_1524531).sum := by decide
  have hdescent : baseEnd_1524531 < baseStart_1524531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524696 : List Nat := [2, 1, 2, 2, 2, 5, 8]
def baseStart_1524696 : Nat := 118140960795 + 1524696 * 2 ^ 59
def prefixEnd_1524696 : Nat := 4983230072969 + 3 ^ 40 * 1524696 * 2
def baseEnd_1524696 : Nat := 19330911110806712434273

theorem tailTrace_1524696 : CollatzResearch.WordTrace tailWord_1524696 prefixEnd_1524696 19330911110806712434273 := by
  unfold tailWord_1524696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27805115842147132095308971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37073487789529509460411961 27805115842147132095308971)
  ·
    refine ⟨41707673763220698142963457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27805115842147132095308971 41707673763220698142963457)
    ·
      refine ⟨31280755322415523607222593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41707673763220698142963457 31280755322415523607222593)
      ·
        refine ⟨23460566491811642705416945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31280755322415523607222593 23460566491811642705416945)
        ·
          refine ⟨17595424868858732029062709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23460566491811642705416945 17595424868858732029062709)
          ·
            refine ⟨1649571081455506127724629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17595424868858732029062709 1649571081455506127724629)
            ·
              refine ⟨19330911110806712434273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1649571081455506127724629 19330911110806712434273)
              ·
                rfl

theorem cell22_1524696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 8].length) (baseStart_1524696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524696 prefixEnd_1524696 := by exact prefixLift 1524696
  have htrace : WordTrace (prefixWord ++ tailWord_1524696) baseStart_1524696 baseEnd_1524696 := by
    simpa [prefixWord, tailWord_1524696, baseEnd_1524696] using wordTrace_append hprefix tailTrace_1524696
  have hstable : (prefixWord ++ tailWord_1524696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524696).length < 2 ^ (prefixWord ++ tailWord_1524696).sum := by decide
  have hdescent : baseEnd_1524696 < baseStart_1524696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524698 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_1524698 : Nat := 118140960795 + 1524698 * 2 ^ 59
def prefixEnd_1524698 : Nat := 4983230072969 + 3 ^ 40 * 1524698 * 2
def baseEnd_1524698 : Nat := 521935284632653897175365

theorem tailTrace_1524698 : CollatzResearch.WordTrace tailWord_1524698 prefixEnd_1524698 521935284632653897175365 := by
  unfold tailWord_1524698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902576157571754633047687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37073536420191345688127165 13902576157571754633047687)
  ·
    refine ⟨20853864236357631949571531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13902576157571754633047687 20853864236357631949571531)
    ·
      refine ⟨31280796354536447924357297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20853864236357631949571531 31280796354536447924357297)
      ·
        refine ⟨23460597265902335943267973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31280796354536447924357297 23460597265902335943267973)
        ·
          refine ⟨4398861987356687989362745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23460597265902335943267973 4398861987356687989362745)
          ·
            refine ⟨3299146490517515992022059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398861987356687989362745 3299146490517515992022059)
            ·
              refine ⟨4948719735776273988033089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299146490517515992022059 4948719735776273988033089)
              ·
                refine ⟨3711539801832205491024817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4948719735776273988033089 3711539801832205491024817)
                ·
                  refine ⟨2783654851374154118268613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3711539801832205491024817 2783654851374154118268613)
                  ·
                    refine ⟨521935284632653897175365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2783654851374154118268613 521935284632653897175365)
                    ·
                      rfl

theorem cell22_1524698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_1524698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524698 prefixEnd_1524698 := by exact prefixLift 1524698
  have htrace : WordTrace (prefixWord ++ tailWord_1524698) baseStart_1524698 baseEnd_1524698 := by
    simpa [prefixWord, tailWord_1524698, baseEnd_1524698] using wordTrace_append hprefix tailTrace_1524698
  have hstable : (prefixWord ++ tailWord_1524698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524698).length < 2 ^ (prefixWord ++ tailWord_1524698).sum := by decide
  have hdescent : baseEnd_1524698 < baseStart_1524698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524775 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 5]
def baseStart_1524775 : Nat := 118140960795 + 1524775 * 2 ^ 59
def prefixEnd_1524775 : Nat := 4983230072969 + 3 ^ 40 * 1524775 * 2
def baseEnd_1524775 : Nat := 173987214435417121000043

theorem tailTrace_1524775 : CollatzResearch.WordTrace tailWord_1524775 prefixEnd_1524775 173987214435417121000043 := by
  unfold tailWord_1524775
  simp only [CollatzResearch.WordTrace]
  refine ⟨55613113051008060682743779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37075408700672040455162519 55613113051008060682743779)
  ·
    refine ⟨83419669576512091024115669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55613113051008060682743779 83419669576512091024115669)
    ·
      refine ⟨1955148505699502133377711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 83419669576512091024115669 1955148505699502133377711)
      ·
        refine ⟨2932722758549253200066567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955148505699502133377711 2932722758549253200066567)
        ·
          refine ⟨4399084137823879800099851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932722758549253200066567 4399084137823879800099851)
          ·
            refine ⟨6598626206735819700149777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399084137823879800099851 6598626206735819700149777)
            ·
              refine ⟨4948969655051864775112333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6598626206735819700149777 4948969655051864775112333)
              ·
                refine ⟨1855863620644449290667125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4948969655051864775112333 1855863620644449290667125)
                ·
                  refine ⟨173987214435417121000043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1855863620644449290667125 173987214435417121000043)
                  ·
                    rfl

theorem cell22_1524775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 5].length) (baseStart_1524775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524775 prefixEnd_1524775 := by exact prefixLift 1524775
  have htrace : WordTrace (prefixWord ++ tailWord_1524775) baseStart_1524775 baseEnd_1524775 := by
    simpa [prefixWord, tailWord_1524775, baseEnd_1524775] using wordTrace_append hprefix tailTrace_1524775
  have hstable : (prefixWord ++ tailWord_1524775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524775).length < 2 ^ (prefixWord ++ tailWord_1524775).sum := by decide
  have hdescent : baseEnd_1524775 < baseStart_1524775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524805 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_1524805 : Nat := 118140960795 + 1524805 * 2 ^ 59
def prefixEnd_1524805 : Nat := 4983230072969 + 3 ^ 40 * 1524805 * 2
def baseEnd_1524805 : Nat := 521971912919341284750037

theorem tailTrace_1524805 : CollatzResearch.WordTrace tailWord_1524805 prefixEnd_1524805 521971912919341284750037 := by
  unfold tailWord_1524805
  simp only [CollatzResearch.WordTrace]
  refine ⟨55614207240899375806335869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37076138160599583870890579 55614207240899375806335869)
  ·
    refine ⟨20855327715337265927375951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55614207240899375806335869 20855327715337265927375951)
    ·
      refine ⟨31282991573005898891063927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20855327715337265927375951 31282991573005898891063927)
      ·
        refine ⟨46924487359508848336595891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31282991573005898891063927 46924487359508848336595891)
        ·
          refine ⟨70386731039263272504893837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46924487359508848336595891 70386731039263272504893837)
          ·
            refine ⟨26395024139723727189335189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70386731039263272504893837 26395024139723727189335189)
            ·
              refine ⟨1237266756549549712000087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26395024139723727189335189 1237266756549549712000087)
              ·
                refine ⟨1855900134824324568000131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237266756549549712000087 1855900134824324568000131)
                ·
                  refine ⟨2783850202236486852000197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855900134824324568000131 2783850202236486852000197)
                  ·
                    refine ⟨521971912919341284750037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2783850202236486852000197 521971912919341284750037)
                    ·
                      rfl

theorem cell22_1524805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_1524805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524805 prefixEnd_1524805 := by exact prefixLift 1524805
  have htrace : WordTrace (prefixWord ++ tailWord_1524805) baseStart_1524805 baseEnd_1524805 := by
    simpa [prefixWord, tailWord_1524805, baseEnd_1524805] using wordTrace_append hprefix tailTrace_1524805
  have hstable : (prefixWord ++ tailWord_1524805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524805).length < 2 ^ (prefixWord ++ tailWord_1524805).sum := by decide
  have hdescent : baseEnd_1524805 < baseStart_1524805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524820 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1524820 : Nat := 118140960795 + 1524820 * 2 ^ 59
def prefixEnd_1524820 : Nat := 4983230072969 + 3 ^ 40 * 1524820 * 2
def baseEnd_1524820 : Nat := 173992349241962081874997

theorem tailTrace_1524820 : CollatzResearch.WordTrace tailWord_1524820 prefixEnd_1524820 173992349241962081874997 := by
  unfold tailWord_1524820
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807377167922516684065957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37076502890563355578754609 27807377167922516684065957)
  ·
    refine ⟨5213883218985471878262367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27807377167922516684065957 5213883218985471878262367)
    ·
      refine ⟨7820824828478207817393551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213883218985471878262367 7820824828478207817393551)
      ·
        refine ⟨11731237242717311726090327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7820824828478207817393551 11731237242717311726090327)
        ·
          refine ⟨17596855864075967589135491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11731237242717311726090327 17596855864075967589135491)
          ·
            refine ⟨26395283796113951383703237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17596855864075967589135491 26395283796113951383703237)
            ·
              refine ⟨4949115711771365884444357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26395283796113951383703237 4949115711771365884444357)
              ·
                refine ⟨927959195957131103333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4949115711771365884444357 927959195957131103333317)
                ·
                  refine ⟨173992349241962081874997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927959195957131103333317 173992349241962081874997)
                  ·
                    rfl

theorem cell22_1524820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1524820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524820 prefixEnd_1524820 := by exact prefixLift 1524820
  have htrace : WordTrace (prefixWord ++ tailWord_1524820) baseStart_1524820 baseEnd_1524820 := by
    simpa [prefixWord, tailWord_1524820, baseEnd_1524820] using wordTrace_append hprefix tailTrace_1524820
  have hstable : (prefixWord ++ tailWord_1524820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524820).length < 2 ^ (prefixWord ++ tailWord_1524820).sum := by decide
  have hdescent : baseEnd_1524820 < baseStart_1524820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524831 : List Nat := [1, 1, 2, 3, 1, 1, 4, 9]
def baseStart_1524831 : Nat := 118140960795 + 1524831 * 2 ^ 59
def prefixEnd_1524831 : Nat := 4983230072969 + 3 ^ 40 * 1524831 * 2
def baseEnd_1524831 : Nat := 57997868138965098177773

theorem tailTrace_1524831 : CollatzResearch.WordTrace tailWord_1524831 prefixEnd_1524831 57997868138965098177773 := by
  unfold tailWord_1524831
  simp only [CollatzResearch.WordTrace]
  refine ⟨55615155538805182246782347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37076770359203454831188231 55615155538805182246782347)
  ·
    refine ⟨83422733308207773370173521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55615155538805182246782347 83422733308207773370173521)
    ·
      refine ⟨62567049981155830027630141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83422733308207773370173521 62567049981155830027630141)
      ·
        refine ⟨23462643742933436260361303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62567049981155830027630141 23462643742933436260361303)
        ·
          refine ⟨35193965614400154390541955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23462643742933436260361303 35193965614400154390541955)
          ·
            refine ⟨52790948421600231585812933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35193965614400154390541955 52790948421600231585812933)
            ·
              refine ⟨9898302829050043422339925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52790948421600231585812933 9898302829050043422339925)
              ·
                refine ⟨57997868138965098177773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9898302829050043422339925 57997868138965098177773)
                ·
                  rfl

theorem cell22_1524831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 9].length) (baseStart_1524831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524831 prefixEnd_1524831 := by exact prefixLift 1524831
  have htrace : WordTrace (prefixWord ++ tailWord_1524831) baseStart_1524831 baseEnd_1524831 := by
    simpa [prefixWord, tailWord_1524831, baseEnd_1524831] using wordTrace_append hprefix tailTrace_1524831
  have hstable : (prefixWord ++ tailWord_1524831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524831).length < 2 ^ (prefixWord ++ tailWord_1524831).sum := by decide
  have hdescent : baseEnd_1524831 < baseStart_1524831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524970 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1524970 : Nat := 118140960795 + 1524970 * 2 ^ 59
def prefixEnd_1524970 : Nat := 4983230072969 + 3 ^ 40 * 1524970 * 2
def baseEnd_1524970 : Nat := 522028395791335854374531

theorem tailTrace_1524970 : CollatzResearch.WordTrace tailWord_1524970 prefixEnd_1524970 522028395791335854374531 := by
  unfold tailWord_1524970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905056321325402246523091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37080150190201072657394909 13905056321325402246523091)
  ·
    refine ⟨20857584481988103369784637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13905056321325402246523091 20857584481988103369784637)
    ·
      refine ⟨7821594180745538763669239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20857584481988103369784637 7821594180745538763669239)
      ·
        refine ⟨11732391271118308145503859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821594180745538763669239 11732391271118308145503859)
        ·
          refine ⟨17598586906677462218255789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11732391271118308145503859 17598586906677462218255789)
          ·
            refine ⟨6599470090004048331845921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17598586906677462218255789 6599470090004048331845921)
            ·
              refine ⟨4949602567503036248884441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6599470090004048331845921 4949602567503036248884441)
              ·
                refine ⟨3712201925627277186663331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949602567503036248884441 3712201925627277186663331)
                ·
                  refine ⟨5568302888440915779994997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712201925627277186663331 5568302888440915779994997)
                  ·
                    refine ⟨522028395791335854374531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5568302888440915779994997 522028395791335854374531)
                    ·
                      rfl

theorem cell22_1524970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1524970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524970 prefixEnd_1524970 := by exact prefixLift 1524970
  have htrace : WordTrace (prefixWord ++ tailWord_1524970) baseStart_1524970 baseEnd_1524970 := by
    simpa [prefixWord, tailWord_1524970, baseEnd_1524970] using wordTrace_append hprefix tailTrace_1524970
  have hstable : (prefixWord ++ tailWord_1524970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524970).length < 2 ^ (prefixWord ++ tailWord_1524970).sum := by decide
  have hdescent : baseEnd_1524970 < baseStart_1524970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524972 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 4]
def baseStart_1524972 : Nat := 118140960795 + 1524972 * 2 ^ 59
def prefixEnd_1524972 : Nat := 4983230072969 + 3 ^ 40 * 1524972 * 2
def baseEnd_1524972 : Nat := 174009693477402838608175

theorem tailTrace_1524972 : CollatzResearch.WordTrace tailWord_1524972 prefixEnd_1524972 174009693477402838608175 := by
  unfold tailWord_1524972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810149115647181663832585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37080198820862908885110113 27810149115647181663832585)
  ·
    refine ⟨20857611836735386247874439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27810149115647181663832585 20857611836735386247874439)
    ·
      refine ⟨31286417755103079371811659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20857611836735386247874439 31286417755103079371811659)
      ·
        refine ⟨46929626632654619057717489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31286417755103079371811659 46929626632654619057717489)
        ·
          refine ⟨35197219974490964293288117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46929626632654619057717489 35197219974490964293288117)
          ·
            refine ⟨3299739372608527902495761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35197219974490964293288117 3299739372608527902495761)
            ·
              refine ⟨2474804529456395926871821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3299739372608527902495761 2474804529456395926871821)
              ·
                refine ⟨928051698546148472576933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2474804529456395926871821 928051698546148472576933)
                ·
                  refine ⟨174009693477402838608175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928051698546148472576933 174009693477402838608175)
                  ·
                    rfl

theorem cell22_1524972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_1524972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1524972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1524972 prefixEnd_1524972 := by exact prefixLift 1524972
  have htrace : WordTrace (prefixWord ++ tailWord_1524972) baseStart_1524972 baseEnd_1524972 := by
    simpa [prefixWord, tailWord_1524972, baseEnd_1524972] using wordTrace_append hprefix tailTrace_1524972
  have hstable : (prefixWord ++ tailWord_1524972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524972).length < 2 ^ (prefixWord ++ tailWord_1524972).sum := by decide
  have hdescent : baseEnd_1524972 < baseStart_1524972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525004 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_1525004 : Nat := 118140960795 + 1525004 * 2 ^ 59
def prefixEnd_1525004 : Nat := 4983230072969 + 3 ^ 40 * 1525004 * 2
def baseEnd_1525004 : Nat := 522040034686171099024427

theorem tailTrace_1525004 : CollatzResearch.WordTrace tailWord_1525004 prefixEnd_1525004 522040034686171099024427 := by
  unfold tailWord_1525004
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810732683589216396415033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37080976911452288528553377 27810732683589216396415033)
  ·
    refine ⟨20858049512691912297311275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27810732683589216396415033 20858049512691912297311275)
    ·
      refine ⟨31287074269037868445966913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858049512691912297311275 31287074269037868445966913)
      ·
        refine ⟨23465305701778401334475185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31287074269037868445966913 23465305701778401334475185)
        ·
          refine ⟨17598979276333801000856389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23465305701778401334475185 17598979276333801000856389)
          ·
            refine ⟨3299808614312587687660573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17598979276333801000856389 3299808614312587687660573)
            ·
              refine ⟨1237428230367220382872715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3299808614312587687660573 1237428230367220382872715)
              ·
                refine ⟨1856142345550830574309073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237428230367220382872715 1856142345550830574309073)
                ·
                  refine ⟨1392106759163122930731805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856142345550830574309073 1392106759163122930731805)
                  ·
                    refine ⟨522040034686171099024427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1392106759163122930731805 522040034686171099024427)
                    ·
                      rfl

theorem cell22_1525004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_1525004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525004 prefixEnd_1525004 := by exact prefixLift 1525004
  have htrace : WordTrace (prefixWord ++ tailWord_1525004) baseStart_1525004 baseEnd_1525004 := by
    simpa [prefixWord, tailWord_1525004, baseEnd_1525004] using wordTrace_append hprefix tailTrace_1525004
  have hstable : (prefixWord ++ tailWord_1525004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525004).length < 2 ^ (prefixWord ++ tailWord_1525004).sum := by decide
  have hdescent : baseEnd_1525004 < baseStart_1525004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525045 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 7]
def baseStart_1525045 : Nat := 118140960795 + 1525045 * 2 ^ 59
def prefixEnd_1525045 : Nat := 4983230072969 + 3 ^ 40 * 1525045 * 2
def baseEnd_1525045 : Nat := 174018023274686886249767

theorem tailTrace_1525045 : CollatzResearch.WordTrace tailWord_1525045 prefixEnd_1525045 174018023274686886249767 := by
  unfold tailWord_1525045
  simp only [CollatzResearch.WordTrace]
  refine ⟨55622960760029896795072589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37081973840019931196715059 55622960760029896795072589)
  ·
    refine ⟨20858610285011211298152221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55622960760029896795072589 20858610285011211298152221)
    ·
      refine ⟨7821978856879204236807083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20858610285011211298152221 7821978856879204236807083)
      ·
        refine ⟨11732968285318806355210625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821978856879204236807083 11732968285318806355210625)
        ·
          refine ⟨8799726213989104766407969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11732968285318806355210625 8799726213989104766407969)
          ·
            refine ⟨6599794660491828574805977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8799726213989104766407969 6599794660491828574805977)
            ·
              refine ⟨4949845995368871431104483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6599794660491828574805977 4949845995368871431104483)
              ·
                refine ⟨7424768993053307146656725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949845995368871431104483 7424768993053307146656725)
                ·
                  refine ⟨174018023274686886249767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7424768993053307146656725 174018023274686886249767)
                  ·
                    rfl

theorem cell22_1525045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_1525045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525045 prefixEnd_1525045 := by exact prefixLift 1525045
  have htrace : WordTrace (prefixWord ++ tailWord_1525045) baseStart_1525045 baseEnd_1525045 := by
    simpa [prefixWord, tailWord_1525045, baseEnd_1525045] using wordTrace_append hprefix tailTrace_1525045
  have hstable : (prefixWord ++ tailWord_1525045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525045).length < 2 ^ (prefixWord ++ tailWord_1525045).sum := by decide
  have hdescent : baseEnd_1525045 < baseStart_1525045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525075 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 3, 4]
def baseStart_1525075 : Nat := 118140960795 + 1525075 * 2 ^ 59
def prefixEnd_1525075 : Nat := 4983230072969 + 3 ^ 40 * 1525075 * 2
def baseEnd_1525075 : Nat := 522064339437150580499209

theorem tailTrace_1525075 : CollatzResearch.WordTrace tailWord_1525075 prefixEnd_1525075 522064339437150580499209 := by
  unfold tailWord_1525075
  simp only [CollatzResearch.WordTrace]
  refine ⟨55624054949921211918664679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37082703299947474612443119 55624054949921211918664679)
  ·
    refine ⟨83436082424881817877997019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55624054949921211918664679 83436082424881817877997019)
    ·
      refine ⟨125154123637322726816995529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83436082424881817877997019 125154123637322726816995529)
      ·
        refine ⟨93865592727992045112746647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125154123637322726816995529 93865592727992045112746647)
        ·
          refine ⟨140798389091988067669119971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93865592727992045112746647 140798389091988067669119971)
          ·
            refine ⟨211197583637982101503679957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140798389091988067669119971 211197583637982101503679957)
            ·
              refine ⟨4949943366515205503992499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 211197583637982101503679957 4949943366515205503992499)
              ·
                refine ⟨7424915049772808255988749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949943366515205503992499 7424915049772808255988749)
                ·
                  refine ⟨2784343143664803095995781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7424915049772808255988749 2784343143664803095995781)
                  ·
                    refine ⟨522064339437150580499209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784343143664803095995781 522064339437150580499209)
                    ·
                      rfl

theorem cell22_1525075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_1525075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525075 prefixEnd_1525075 := by exact prefixLift 1525075
  have htrace : WordTrace (prefixWord ++ tailWord_1525075) baseStart_1525075 baseEnd_1525075 := by
    simpa [prefixWord, tailWord_1525075, baseEnd_1525075] using wordTrace_append hprefix tailTrace_1525075
  have hstable : (prefixWord ++ tailWord_1525075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525075).length < 2 ^ (prefixWord ++ tailWord_1525075).sum := by decide
  have hdescent : baseEnd_1525075 < baseStart_1525075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525120 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_1525120 : Nat := 118140960795 + 1525120 * 2 ^ 59
def prefixEnd_1525120 : Nat := 4983230072969 + 3 ^ 40 * 1525120 * 2
def baseEnd_1525120 : Nat := 522079743856785463124071

theorem tailTrace_1525120 : CollatzResearch.WordTrace tailWord_1525120 prefixEnd_1525120 522079743856785463124071 := by
  unfold tailWord_1525120
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812848117379092302026407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37083797489838789736035209 27812848117379092302026407)
  ·
    refine ⟨41719272176068638453039611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27812848117379092302026407 41719272176068638453039611)
    ·
      refine ⟨62578908264102957679559417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41719272176068638453039611 62578908264102957679559417)
      ·
        refine ⟨46934181198077218259669563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62578908264102957679559417 46934181198077218259669563)
        ·
          refine ⟨70401271797115827389504345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46934181198077218259669563 70401271797115827389504345)
          ·
            refine ⟨52800953847836870542128259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70401271797115827389504345 52800953847836870542128259)
            ·
              refine ⟨79201430771755305813192389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52800953847836870542128259 79201430771755305813192389)
              ·
                refine ⟨14850268269704119839973573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79201430771755305813192389 14850268269704119839973573)
                ·
                  refine ⟨2784425300569522469995045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14850268269704119839973573 2784425300569522469995045)
                  ·
                    refine ⟨522079743856785463124071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784425300569522469995045 522079743856785463124071)
                    ·
                      rfl

theorem cell22_1525120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_1525120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525120 prefixEnd_1525120 := by exact prefixLift 1525120
  have htrace : WordTrace (prefixWord ++ tailWord_1525120) baseStart_1525120 baseEnd_1525120 := by
    simpa [prefixWord, tailWord_1525120, baseEnd_1525120] using wordTrace_append hprefix tailTrace_1525120
  have hstable : (prefixWord ++ tailWord_1525120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525120).length < 2 ^ (prefixWord ++ tailWord_1525120).sum := by decide
  have hdescent : baseEnd_1525120 < baseStart_1525120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525195 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_1525195 : Nat := 118140960795 + 1525195 * 2 ^ 59
def prefixEnd_1525195 : Nat := 4983230072969 + 3 ^ 40 * 1525195 * 2
def baseEnd_1525195 : Nat := 522105417889510267498841

theorem tailTrace_1525195 : CollatzResearch.WordTrace tailWord_1525195 prefixEnd_1525195 522105417889510267498841 := by
  unfold tailWord_1525195
  simp only [CollatzResearch.WordTrace]
  refine ⟨55628431709486472413033039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37085621139657648275355359 55628431709486472413033039)
  ·
    refine ⟨83442647564229708619549559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55628431709486472413033039 83442647564229708619549559)
    ·
      refine ⟨125163971346344562929324339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83442647564229708619549559 125163971346344562929324339)
      ·
        refine ⟨187745957019516844393986509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125163971346344562929324339 187745957019516844393986509)
        ·
          refine ⟨70404733882318816647744941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187745957019516844393986509 70404733882318816647744941)
          ·
            refine ⟨26401775205869556242904353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70404733882318816647744941 26401775205869556242904353)
            ·
              refine ⟨19801331404402167182178265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26401775205869556242904353 19801331404402167182178265)
              ·
                refine ⟨14850998553301625386633699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19801331404402167182178265 14850998553301625386633699)
                ·
                  refine ⟨22276497829952438079950549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14850998553301625386633699 22276497829952438079950549)
                  ·
                    refine ⟨522105417889510267498841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22276497829952438079950549 522105417889510267498841)
                    ·
                      rfl

theorem cell22_1525195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_1525195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525195 prefixEnd_1525195 := by exact prefixLift 1525195
  have htrace : WordTrace (prefixWord ++ tailWord_1525195) baseStart_1525195 baseEnd_1525195 := by
    simpa [prefixWord, tailWord_1525195, baseEnd_1525195] using wordTrace_append hprefix tailTrace_1525195
  have hstable : (prefixWord ++ tailWord_1525195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525195).length < 2 ^ (prefixWord ++ tailWord_1525195).sum := by decide
  have hdescent : baseEnd_1525195 < baseStart_1525195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525244 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_1525244 : Nat := 118140960795 + 1525244 * 2 ^ 59
def prefixEnd_1525244 : Nat := 4983230072969 + 3 ^ 40 * 1525244 * 2
def baseEnd_1525244 : Nat := 522122191590890473023691

theorem tailTrace_1525244 : CollatzResearch.WordTrace tailWord_1525244 prefixEnd_1525244 522122191590890473023691 := by
  unfold tailWord_1525244
  simp only [CollatzResearch.WordTrace]
  refine ⟨27815109443154476890783393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37086812590872635854377857 27815109443154476890783393)
  ·
    refine ⟨20861332082365857668087545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27815109443154476890783393 20861332082365857668087545)
    ·
      refine ⟨15645999061774393251065659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20861332082365857668087545 15645999061774393251065659)
      ·
        refine ⟨23468998592661589876598489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15645999061774393251065659 23468998592661589876598489)
        ·
          refine ⟨17601748944496192407448867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23468998592661589876598489 17601748944496192407448867)
          ·
            refine ⟨26402623416744288611173301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17601748944496192407448867 26402623416744288611173301)
            ·
              refine ⟨2475245945319777057297497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26402623416744288611173301 2475245945319777057297497)
              ·
                refine ⟨1856434458989832792973123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475245945319777057297497 1856434458989832792973123)
                ·
                  refine ⟨2784651688484749189459685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856434458989832792973123 2784651688484749189459685)
                  ·
                    refine ⟨522122191590890473023691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784651688484749189459685 522122191590890473023691)
                    ·
                      rfl

theorem cell22_1525244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_1525244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525244 prefixEnd_1525244 := by exact prefixLift 1525244
  have htrace : WordTrace (prefixWord ++ tailWord_1525244) baseStart_1525244 baseEnd_1525244 := by
    simpa [prefixWord, tailWord_1525244, baseEnd_1525244] using wordTrace_append hprefix tailTrace_1525244
  have hstable : (prefixWord ++ tailWord_1525244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525244).length < 2 ^ (prefixWord ++ tailWord_1525244).sum := by decide
  have hdescent : baseEnd_1525244 < baseStart_1525244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525257 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_1525257 : Nat := 118140960795 + 1525257 * 2 ^ 59
def prefixEnd_1525257 : Nat := 4983230072969 + 3 ^ 40 * 1525257 * 2
def baseEnd_1525257 : Nat := 522126641756562772448651

theorem tailTrace_1525257 : CollatzResearch.WordTrace tailWord_1525257 prefixEnd_1525257 522126641756562772448651 := by
  unfold tailWord_1525257
  simp only [CollatzResearch.WordTrace]
  refine ⟨55630693035261857001790025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37087128690174571334526683 55630693035261857001790025)
  ·
    refine ⟨41723019776446392751342519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55630693035261857001790025 41723019776446392751342519)
    ·
      refine ⟨62584529664669589127013779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41723019776446392751342519 62584529664669589127013779)
      ·
        refine ⟨93876794497004383690520669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62584529664669589127013779 93876794497004383690520669)
        ·
          refine ⟨35203797936376643883945251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93876794497004383690520669 35203797936376643883945251)
          ·
            refine ⟨52805696904564965825917877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35203797936376643883945251 52805696904564965825917877)
            ·
              refine ⟨4950534084802965546179801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52805696904564965825917877 4950534084802965546179801)
              ·
                refine ⟨3712900563602224159634851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4950534084802965546179801 3712900563602224159634851)
                ·
                  refine ⟨5569350845403336239452277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712900563602224159634851 5569350845403336239452277)
                  ·
                    refine ⟨522126641756562772448651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5569350845403336239452277 522126641756562772448651)
                    ·
                      rfl

theorem cell22_1525257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_1525257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525257 prefixEnd_1525257 := by exact prefixLift 1525257
  have htrace : WordTrace (prefixWord ++ tailWord_1525257) baseStart_1525257 baseEnd_1525257 := by
    simpa [prefixWord, tailWord_1525257, baseEnd_1525257] using wordTrace_append hprefix tailTrace_1525257
  have hstable : (prefixWord ++ tailWord_1525257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525257).length < 2 ^ (prefixWord ++ tailWord_1525257).sum := by decide
  have hdescent : baseEnd_1525257 < baseStart_1525257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525304 : List Nat := [2, 1, 2, 1, 4, 3, 3, 6]
def baseStart_1525304 : Nat := 118140960795 + 1525304 * 2 ^ 59
def prefixEnd_1525304 : Nat := 4983230072969 + 3 ^ 40 * 1525304 * 2
def baseEnd_1525304 : Nat := 58015858979674479613723

theorem tailTrace_1525304 : CollatzResearch.WordTrace tailWord_1525304 prefixEnd_1525304 58015858979674479613723 := by
  unfold tailWord_1525304
  simp only [CollatzResearch.WordTrace]
  refine ⟨27816203633045792014375483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37088271510727722685833977 27816203633045792014375483)
  ·
    refine ⟨41724305449568688021563225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27816203633045792014375483 41724305449568688021563225)
    ·
      refine ⟨31293229087176516016172419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41724305449568688021563225 31293229087176516016172419)
      ·
        refine ⟨46939843630764774024258629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31293229087176516016172419 46939843630764774024258629)
        ·
          refine ⟨8801220680768395129548493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46939843630764774024258629 8801220680768395129548493)
          ·
            refine ⟨3300457755288148173580685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8801220680768395129548493 3300457755288148173580685)
            ·
              refine ⟨1237671658233055565092757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3300457755288148173580685 1237671658233055565092757)
              ·
                refine ⟨58015858979674479613723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1237671658233055565092757 58015858979674479613723)
                ·
                  rfl

theorem cell22_1525304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_1525304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525304 prefixEnd_1525304 := by exact prefixLift 1525304
  have htrace : WordTrace (prefixWord ++ tailWord_1525304) baseStart_1525304 baseEnd_1525304 := by
    simpa [prefixWord, tailWord_1525304, baseEnd_1525304] using wordTrace_append hprefix tailTrace_1525304
  have hstable : (prefixWord ++ tailWord_1525304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525304).length < 2 ^ (prefixWord ++ tailWord_1525304).sum := by decide
  have hdescent : baseEnd_1525304 < baseStart_1525304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525325 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1525325 : Nat := 118140960795 + 1525325 * 2 ^ 59
def prefixEnd_1525325 : Nat := 4983230072969 + 3 ^ 40 * 1525325 * 2
def baseEnd_1525325 : Nat := 522149919546233261748443

theorem tailTrace_1525325 : CollatzResearch.WordTrace tailWord_1525325 prefixEnd_1525325 522149919546233261748443 := by
  unfold tailWord_1525325
  simp only [CollatzResearch.WordTrace]
  refine ⟨55633173199015504615265429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37088782132677003076843619 55633173199015504615265429)
  ·
    refine ⟨2607804993703851778840567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55633173199015504615265429 2607804993703851778840567)
    ·
      refine ⟨3911707490555777668260851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607804993703851778840567 3911707490555777668260851)
      ·
        refine ⟨5867561235833666502391277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911707490555777668260851 5867561235833666502391277)
        ·
          refine ⟨2200335463437624938396729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5867561235833666502391277 2200335463437624938396729)
          ·
            refine ⟨1650251597578218703797547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200335463437624938396729 1650251597578218703797547)
            ·
              refine ⟨2475377396367328055696321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650251597578218703797547 2475377396367328055696321)
              ·
                refine ⟨1856533047275496041772241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475377396367328055696321 1856533047275496041772241)
                ·
                  refine ⟨1392399785456622031329181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856533047275496041772241 1392399785456622031329181)
                  ·
                    refine ⟨522149919546233261748443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1392399785456622031329181 522149919546233261748443)
                    ·
                      rfl

theorem cell22_1525325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1525325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525325 prefixEnd_1525325 := by exact prefixLift 1525325
  have htrace : WordTrace (prefixWord ++ tailWord_1525325) baseStart_1525325 baseEnd_1525325 := by
    simpa [prefixWord, tailWord_1525325, baseEnd_1525325] using wordTrace_append hprefix tailTrace_1525325
  have hstable : (prefixWord ++ tailWord_1525325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525325).length < 2 ^ (prefixWord ++ tailWord_1525325).sum := by decide
  have hdescent : baseEnd_1525325 < baseStart_1525325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525424 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_1525424 : Nat := 118140960795 + 1525424 * 2 ^ 59
def prefixEnd_1525424 : Nat := 4983230072969 + 3 ^ 40 * 1525424 * 2
def baseEnd_1525424 : Nat := 522183809269430003523139

theorem tailTrace_1525424 : CollatzResearch.WordTrace tailWord_1525424 prefixEnd_1525424 522183809269430003523139 := by
  unfold tailWord_1525424
  simp only [CollatzResearch.WordTrace]
  refine ⟨27818392012828422261559663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37091189350437896348746217 27818392012828422261559663)
  ·
    refine ⟨41727588019242633392339495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27818392012828422261559663 41727588019242633392339495)
    ·
      refine ⟨62591382028863950088509243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41727588019242633392339495 62591382028863950088509243)
      ·
        refine ⟨93887073043295925132763865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62591382028863950088509243 93887073043295925132763865)
        ·
          refine ⟨70415304782471943849572899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93887073043295925132763865 70415304782471943849572899)
          ·
            refine ⟨105622957173707915774359349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70415304782471943849572899 105622957173707915774359349)
            ·
              refine ⟨9902152235035117103846189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105622957173707915774359349 9902152235035117103846189)
              ·
                refine ⟨3713307088138168913942321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9902152235035117103846189 3713307088138168913942321)
                ·
                  refine ⟨2784980316103626685456741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713307088138168913942321 2784980316103626685456741)
                  ·
                    refine ⟨522183809269430003523139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2784980316103626685456741 522183809269430003523139)
                    ·
                      rfl

theorem cell22_1525424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_1525424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525424 prefixEnd_1525424 := by exact prefixLift 1525424
  have htrace : WordTrace (prefixWord ++ tailWord_1525424) baseStart_1525424 baseEnd_1525424 := by
    simpa [prefixWord, tailWord_1525424, baseEnd_1525424] using wordTrace_append hprefix tailTrace_1525424
  have hstable : (prefixWord ++ tailWord_1525424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525424).length < 2 ^ (prefixWord ++ tailWord_1525424).sum := by decide
  have hdescent : baseEnd_1525424 < baseStart_1525424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525471 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 3, 3]
def baseStart_1525471 : Nat := 118140960795 + 1525471 * 2 ^ 59
def prefixEnd_1525471 : Nat := 4983230072969 + 3 ^ 40 * 1525471 * 2
def baseEnd_1525471 : Nat := 522199898329937547597995

theorem tailTrace_1525471 : CollatzResearch.WordTrace tailWord_1525471 prefixEnd_1525471 522199898329937547597995 := by
  unfold tailWord_1525471
  simp only [CollatzResearch.WordTrace]
  refine ⟨55638498256486571550080267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37092332170991047700053511 55638498256486571550080267)
  ·
    refine ⟨83457747384729857325120401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55638498256486571550080267 83457747384729857325120401)
    ·
      refine ⟨62593310538547392993840301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83457747384729857325120401 62593310538547392993840301)
      ·
        refine ⟨23472491451955272372690113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62593310538547392993840301 23472491451955272372690113)
        ·
          refine ⟨17604368588966454279517585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23472491451955272372690113 17604368588966454279517585)
          ·
            refine ⟨13203276441724840709638189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17604368588966454279517585 13203276441724840709638189)
            ·
              refine ⟨4951228665646815266114321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13203276441724840709638189 4951228665646815266114321)
              ·
                refine ⟨3713421499235111449585741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951228665646815266114321 3713421499235111449585741)
                ·
                  refine ⟨1392533062213166793594653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3713421499235111449585741 1392533062213166793594653)
                  ·
                    refine ⟨522199898329937547597995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1392533062213166793594653 522199898329937547597995)
                    ·
                      rfl

theorem cell22_1525471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_1525471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525471 prefixEnd_1525471 := by exact prefixLift 1525471
  have htrace : WordTrace (prefixWord ++ tailWord_1525471) baseStart_1525471 baseEnd_1525471 := by
    simpa [prefixWord, tailWord_1525471, baseEnd_1525471] using wordTrace_append hprefix tailTrace_1525471
  have hstable : (prefixWord ++ tailWord_1525471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525471).length < 2 ^ (prefixWord ++ tailWord_1525471).sum := by decide
  have hdescent : baseEnd_1525471 < baseStart_1525471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525475 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 2, 4]
def baseStart_1525475 : Nat := 118140960795 + 1525475 * 2 ^ 59
def prefixEnd_1525475 : Nat := 4983230072969 + 3 ^ 40 * 1525475 * 2
def baseEnd_1525475 : Nat := 522201267611682870497983

theorem tailTrace_1525475 : CollatzResearch.WordTrace tailWord_1525475 prefixEnd_1525475 522201267611682870497983 := by
  unfold tailWord_1525475
  simp only [CollatzResearch.WordTrace]
  refine ⟨55638644148472080233225879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37092429432314720155483919 55638644148472080233225879)
  ·
    refine ⟨83457966222708120349838819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55638644148472080233225879 83457966222708120349838819)
    ·
      refine ⟨125186949334062180524758229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83457966222708120349838819 125186949334062180524758229)
      ·
        refine ⟨2934069125017082356049021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 125186949334062180524758229 2934069125017082356049021)
        ·
          refine ⟨1100275921881405883518383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2934069125017082356049021 1100275921881405883518383)
          ·
            refine ⟨1650413882822108825277575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100275921881405883518383 1650413882822108825277575)
            ·
              refine ⟨2475620824233163237916363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650413882822108825277575 2475620824233163237916363)
              ·
                refine ⟨3713431236349744856874545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475620824233163237916363 3713431236349744856874545)
                ·
                  refine ⟨2785073427262308642655909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713431236349744856874545 2785073427262308642655909)
                  ·
                    refine ⟨522201267611682870497983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2785073427262308642655909 522201267611682870497983)
                    ·
                      rfl

theorem cell22_1525475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 4].length) (baseStart_1525475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525475 prefixEnd_1525475 := by exact prefixLift 1525475
  have htrace : WordTrace (prefixWord ++ tailWord_1525475) baseStart_1525475 baseEnd_1525475 := by
    simpa [prefixWord, tailWord_1525475, baseEnd_1525475] using wordTrace_append hprefix tailTrace_1525475
  have hstable : (prefixWord ++ tailWord_1525475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525475).length < 2 ^ (prefixWord ++ tailWord_1525475).sum := by decide
  have hdescent : baseEnd_1525475 < baseStart_1525475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525524 : List Nat := [2, 4, 4, 1, 2, 1, 2, 6]
def baseStart_1525524 : Nat := 118140960795 + 1525524 * 2 ^ 59
def prefixEnd_1525524 : Nat := 4983230072969 + 3 ^ 40 * 1525524 * 2
def baseEnd_1525524 : Nat := 58024226812562564002537

theorem tailTrace_1525524 : CollatzResearch.WordTrace tailWord_1525524 prefixEnd_1525524 58024226812562564002537 := by
  unfold tailWord_1525524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27820215662647280800879813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37093620883529707734506417 27820215662647280800879813)
  ·
    refine ⟨5216290436746365150164965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27820215662647280800879813 5216290436746365150164965)
    ·
      refine ⟨978054456889943465655931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5216290436746365150164965 978054456889943465655931)
      ·
        refine ⟨1467081685334915198483897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978054456889943465655931 1467081685334915198483897)
        ·
          refine ⟨1100311264001186398862923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467081685334915198483897 1100311264001186398862923)
          ·
            refine ⟨1650466896001779598294385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100311264001186398862923 1650466896001779598294385)
            ·
              refine ⟨1237850172001334698720789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650466896001779598294385 1237850172001334698720789)
              ·
                refine ⟨58024226812562564002537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1237850172001334698720789 58024226812562564002537)
                ·
                  rfl

theorem cell22_1525524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 6].length) (baseStart_1525524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525524 prefixEnd_1525524 := by exact prefixLift 1525524
  have htrace : WordTrace (prefixWord ++ tailWord_1525524) baseStart_1525524 baseEnd_1525524 := by
    simpa [prefixWord, tailWord_1525524, baseEnd_1525524] using wordTrace_append hprefix tailTrace_1525524
  have hstable : (prefixWord ++ tailWord_1525524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525524).length < 2 ^ (prefixWord ++ tailWord_1525524).sum := by decide
  have hdescent : baseEnd_1525524 < baseStart_1525524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525559 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1525559 : Nat := 118140960795 + 1525559 * 2 ^ 59
def prefixEnd_1525559 : Nat := 4983230072969 + 3 ^ 40 * 1525559 * 2
def baseEnd_1525559 : Nat := 522230022528334651397725

theorem tailTrace_1525559 : CollatzResearch.WordTrace tailWord_1525559 prefixEnd_1525559 522230022528334651397725 := by
  unfold tailWord_1525559
  simp only [CollatzResearch.WordTrace]
  refine ⟨55641707880167762579283731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37094471920111841719522487 55641707880167762579283731)
  ·
    refine ⟨83462561820251643868925597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55641707880167762579283731 83462561820251643868925597)
    ·
      refine ⟨31298460682594366450847099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83462561820251643868925597 31298460682594366450847099)
      ·
        refine ⟨46947691023891549676270649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31298460682594366450847099 46947691023891549676270649)
        ·
          refine ⟨35210768267918662257202987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46947691023891549676270649 35210768267918662257202987)
          ·
            refine ⟨52816152401877993385804481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35210768267918662257202987 52816152401877993385804481)
            ·
              refine ⟨39612114301408495039353361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52816152401877993385804481 39612114301408495039353361)
              ·
                refine ⟨29709085726056371279515021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39612114301408495039353361 29709085726056371279515021)
                ·
                  refine ⟨11140907147271139229818133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29709085726056371279515021 11140907147271139229818133)
                  ·
                    refine ⟨522230022528334651397725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11140907147271139229818133 522230022528334651397725)
                    ·
                      rfl

theorem cell22_1525559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1525559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525559 prefixEnd_1525559 := by exact prefixLift 1525559
  have htrace : WordTrace (prefixWord ++ tailWord_1525559) baseStart_1525559 baseEnd_1525559 := by
    simpa [prefixWord, tailWord_1525559, baseEnd_1525559] using wordTrace_append hprefix tailTrace_1525559
  have hstable : (prefixWord ++ tailWord_1525559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525559).length < 2 ^ (prefixWord ++ tailWord_1525559).sum := by decide
  have hdescent : baseEnd_1525559 < baseStart_1525559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525578 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1525578 : Nat := 118140960795 + 1525578 * 2 ^ 59
def prefixEnd_1525578 : Nat := 4983230072969 + 3 ^ 40 * 1525578 * 2
def baseEnd_1525578 : Nat := 522236526616624935172667

theorem tailTrace_1525578 : CollatzResearch.WordTrace tailWord_1525578 prefixEnd_1525578 522236526616624935172667 := by
  unfold tailWord_1525578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13910600216774732206056347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37094933911399285882816925 13910600216774732206056347)
  ·
    refine ⟨20865900325162098309084521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13910600216774732206056347 20865900325162098309084521)
    ·
      refine ⟨15649425243871573731813391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20865900325162098309084521 15649425243871573731813391)
      ·
        refine ⟨23474137865807360597720087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15649425243871573731813391 23474137865807360597720087)
        ·
          refine ⟨35211206798711040896580131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23474137865807360597720087 35211206798711040896580131)
          ·
            refine ⟨52816810198066561344870197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35211206798711040896580131 52816810198066561344870197)
            ·
              refine ⟨4951575956068740126081581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52816810198066561344870197 4951575956068740126081581)
              ·
                refine ⟨1856840983525777547280593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4951575956068740126081581 1856840983525777547280593)
                ·
                  refine ⟨1392630737644333160460445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856840983525777547280593 1392630737644333160460445)
                  ·
                    refine ⟨522236526616624935172667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1392630737644333160460445 522236526616624935172667)
                    ·
                      rfl

theorem cell22_1525578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1525578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525578 prefixEnd_1525578 := by exact prefixLift 1525578
  have htrace : WordTrace (prefixWord ++ tailWord_1525578) baseStart_1525578 baseEnd_1525578 := by
    simpa [prefixWord, tailWord_1525578, baseEnd_1525578] using wordTrace_append hprefix tailTrace_1525578
  have hstable : (prefixWord ++ tailWord_1525578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525578).length < 2 ^ (prefixWord ++ tailWord_1525578).sum := by decide
  have hdescent : baseEnd_1525578 < baseStart_1525578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525621 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1525621 : Nat := 118140960795 + 1525621 * 2 ^ 59
def prefixEnd_1525621 : Nat := 4983230072969 + 3 ^ 40 * 1525621 * 2
def baseEnd_1525621 : Nat := 522251246395387156347535

theorem tailTrace_1525621 : CollatzResearch.WordTrace tailWord_1525621 prefixEnd_1525621 522251246395387156347535 := by
  unfold tailWord_1525621
  simp only [CollatzResearch.WordTrace]
  refine ⟨55643969205943147168040717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37095979470628764778693811 55643969205943147168040717)
  ·
    refine ⟨20866488452228680188015269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55643969205943147168040717 20866488452228680188015269)
    ·
      refine ⟨3912466584792877535252863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20866488452228680188015269 3912466584792877535252863)
      ·
        refine ⟨5868699877189316302879295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3912466584792877535252863 5868699877189316302879295)
        ·
          refine ⟨8803049815783974454318943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5868699877189316302879295 8803049815783974454318943)
          ·
            refine ⟨13204574723675961681478415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8803049815783974454318943 13204574723675961681478415)
            ·
              refine ⟨19806862085513942522217623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13204574723675961681478415 19806862085513942522217623)
              ·
                refine ⟨29710293128270913783326435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19806862085513942522217623 29710293128270913783326435)
                ·
                  refine ⟨44565439692406370674989653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29710293128270913783326435 44565439692406370674989653)
                  ·
                    refine ⟨522251246395387156347535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44565439692406370674989653 522251246395387156347535)
                    ·
                      rfl

theorem cell22_1525621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1525621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525621 prefixEnd_1525621 := by exact prefixLift 1525621
  have htrace : WordTrace (prefixWord ++ tailWord_1525621) baseStart_1525621 baseEnd_1525621 := by
    simpa [prefixWord, tailWord_1525621, baseEnd_1525621] using wordTrace_append hprefix tailTrace_1525621
  have hstable : (prefixWord ++ tailWord_1525621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525621).length < 2 ^ (prefixWord ++ tailWord_1525621).sum := by decide
  have hdescent : baseEnd_1525621 < baseStart_1525621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525640 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1525640 : Nat := 118140960795 + 1525640 * 2 ^ 59
def prefixEnd_1525640 : Nat := 4983230072969 + 3 ^ 40 * 1525640 * 2
def baseEnd_1525640 : Nat := 522257750483677440122477

theorem tailTrace_1525640 : CollatzResearch.WordTrace tailWord_1525640 prefixEnd_1525640 522257750483677440122477 := by
  unfold tailWord_1525640
  simp only [CollatzResearch.WordTrace]
  refine ⟨27822331096437156706491187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37096441461916208941988249 27822331096437156706491187)
  ·
    refine ⟨41733496644655735059736781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27822331096437156706491187 41733496644655735059736781)
    ·
      refine ⟨15650061241745900647401293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41733496644655735059736781 15650061241745900647401293)
      ·
        refine ⟨5868772965654712742775485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15650061241745900647401293 5868772965654712742775485)
        ·
          refine ⟨2200789862120517278540807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5868772965654712742775485 2200789862120517278540807)
          ·
            refine ⟨3301184793180775917811211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200789862120517278540807 3301184793180775917811211)
            ·
              refine ⟨4951777189771163876716817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3301184793180775917811211 4951777189771163876716817)
              ·
                refine ⟨3713832892328372907537613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951777189771163876716817 3713832892328372907537613)
                ·
                  refine ⟨1392687334623139840326605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3713832892328372907537613 1392687334623139840326605)
                  ·
                    refine ⟨522257750483677440122477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1392687334623139840326605 522257750483677440122477)
                    ·
                      rfl

theorem cell22_1525640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1525640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525640 prefixEnd_1525640 := by exact prefixLift 1525640
  have htrace : WordTrace (prefixWord ++ tailWord_1525640) baseStart_1525640 baseEnd_1525640 := by
    simpa [prefixWord, tailWord_1525640, baseEnd_1525640] using wordTrace_append hprefix tailTrace_1525640
  have hstable : (prefixWord ++ tailWord_1525640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525640).length < 2 ^ (prefixWord ++ tailWord_1525640).sum := by decide
  have hdescent : baseEnd_1525640 < baseStart_1525640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525711 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_1525711 : Nat := 118140960795 + 1525711 * 2 ^ 59
def prefixEnd_1525711 : Nat := 4983230072969 + 3 ^ 40 * 1525711 * 2
def baseEnd_1525711 : Nat := 522282055234656921597259

theorem tailTrace_1525711 : CollatzResearch.WordTrace tailWord_1525711 prefixEnd_1525711 522282055234656921597259 := by
  unfold tailWord_1525711
  simp only [CollatzResearch.WordTrace]
  refine ⟨55647251775617092538816987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37098167850411395025877991 55647251775617092538816987)
  ·
    refine ⟨83470877663425638808225481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55647251775617092538816987 83470877663425638808225481)
    ·
      refine ⟨62603158247569229106169111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83470877663425638808225481 62603158247569229106169111)
      ·
        refine ⟨93904737371353843659253667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62603158247569229106169111 93904737371353843659253667)
        ·
          refine ⟨140857106057030765488880501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93904737371353843659253667 140857106057030765488880501)
          ·
            refine ⟨13205353692846634264582547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140857106057030765488880501 13205353692846634264582547)
            ·
              refine ⟨19808030539269951396873821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13205353692846634264582547 19808030539269951396873821)
              ·
                refine ⟨7428011452226231773827683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19808030539269951396873821 7428011452226231773827683)
                ·
                  refine ⟨11142017178339347660741525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7428011452226231773827683 11142017178339347660741525)
                  ·
                    refine ⟨522282055234656921597259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11142017178339347660741525 522282055234656921597259)
                    ·
                      rfl

theorem cell22_1525711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_1525711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525711 prefixEnd_1525711 := by exact prefixLift 1525711
  have htrace : WordTrace (prefixWord ++ tailWord_1525711) baseStart_1525711 baseEnd_1525711 := by
    simpa [prefixWord, tailWord_1525711, baseEnd_1525711] using wordTrace_append hprefix tailTrace_1525711
  have hstable : (prefixWord ++ tailWord_1525711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525711).length < 2 ^ (prefixWord ++ tailWord_1525711).sum := by decide
  have hdescent : baseEnd_1525711 < baseStart_1525711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525850 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_1525850 : Nat := 118140960795 + 1525850 * 2 ^ 59
def prefixEnd_1525850 : Nat := 4983230072969 + 3 ^ 40 * 1525850 * 2
def baseEnd_1525850 : Nat := 174109879258435630790611

theorem tailTrace_1525850 : CollatzResearch.WordTrace tailWord_1525850 prefixEnd_1525850 174109879258435630790611 := by
  unfold tailWord_1525850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913080380528379819531751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37101547681409012852084669 13913080380528379819531751)
  ·
    refine ⟨20869620570792569729297627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13913080380528379819531751 20869620570792569729297627)
    ·
      refine ⟨31304430856188854593946441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20869620570792569729297627 31304430856188854593946441)
      ·
        refine ⟨23478323142141640945459831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31304430856188854593946441 23478323142141640945459831)
        ·
          refine ⟨35217484713212461418189747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23478323142141640945459831 35217484713212461418189747)
          ·
            refine ⟨52826227069818692127284621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35217484713212461418189747 52826227069818692127284621)
            ·
              refine ⟨19809835151182009547731733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52826227069818692127284621 19809835151182009547731733)
              ·
                refine ⟨928586022711656697549925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19809835151182009547731733 928586022711656697549925)
                ·
                  refine ⟨174109879258435630790611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928586022711656697549925 174109879258435630790611)
                  ·
                    rfl

theorem cell22_1525850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_1525850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525850 prefixEnd_1525850 := by exact prefixLift 1525850
  have htrace : WordTrace (prefixWord ++ tailWord_1525850) baseStart_1525850 baseEnd_1525850 := by
    simpa [prefixWord, tailWord_1525850, baseEnd_1525850] using wordTrace_append hprefix tailTrace_1525850
  have hstable : (prefixWord ++ tailWord_1525850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525850).length < 2 ^ (prefixWord ++ tailWord_1525850).sum := by decide
  have hdescent : baseEnd_1525850 < baseStart_1525850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525863 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1525863 : Nat := 118140960795 + 1525863 * 2 ^ 59
def prefixEnd_1525863 : Nat := 4983230072969 + 3 ^ 40 * 1525863 * 2
def baseEnd_1525863 : Nat := 522334087940979191796793

theorem tailTrace_1525863 : CollatzResearch.WordTrace tailWord_1525863 prefixEnd_1525863 522334087940979191796793 := by
  unfold tailWord_1525863
  simp only [CollatzResearch.WordTrace]
  refine ⟨55652795671066422498350243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37101863780710948332233495 55652795671066422498350243)
  ·
    refine ⟨83479193506599633747525365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55652795671066422498350243 83479193506599633747525365)
    ·
      refine ⟨7826174391243715663830503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83479193506599633747525365 7826174391243715663830503)
      ·
        refine ⟨11739261586865573495745755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7826174391243715663830503 11739261586865573495745755)
        ·
          refine ⟨17608892380298360243618633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11739261586865573495745755 17608892380298360243618633)
          ·
            refine ⟨13206669285223770182713975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17608892380298360243618633 13206669285223770182713975)
            ·
              refine ⟨19810003927835655274070963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13206669285223770182713975 19810003927835655274070963)
              ·
                refine ⟨29715005891753482911106445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19810003927835655274070963 29715005891753482911106445)
                ·
                  refine ⟨11143127209407556091664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29715005891753482911106445 11143127209407556091664917)
                  ·
                    refine ⟨522334087940979191796793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11143127209407556091664917 522334087940979191796793)
                    ·
                      rfl

theorem cell22_1525863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1525863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525863 prefixEnd_1525863 := by exact prefixLift 1525863
  have htrace : WordTrace (prefixWord ++ tailWord_1525863) baseStart_1525863 baseEnd_1525863 := by
    simpa [prefixWord, tailWord_1525863, baseEnd_1525863] using wordTrace_append hprefix tailTrace_1525863
  have hstable : (prefixWord ++ tailWord_1525863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525863).length < 2 ^ (prefixWord ++ tailWord_1525863).sum := by decide
  have hdescent : baseEnd_1525863 < baseStart_1525863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525968 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_1525968 : Nat := 118140960795 + 1525968 * 2 ^ 59
def prefixEnd_1525968 : Nat := 4983230072969 + 3 ^ 40 * 1525968 * 2
def baseEnd_1525968 : Nat := 174123343862264639307157

theorem tailTrace_1525968 : CollatzResearch.WordTrace tailWord_1525968 prefixEnd_1525968 174123343862264639307157 := by
  unfold tailWord_1525968
  simp only [CollatzResearch.WordTrace]
  refine ⟨27828312667843012715461279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37104416890457350287281705 27828312667843012715461279)
  ·
    refine ⟨41742469001764519073191919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27828312667843012715461279 41742469001764519073191919)
    ·
      refine ⟨62613703502646778609787879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41742469001764519073191919 62613703502646778609787879)
      ·
        refine ⟨93920555253970167914681819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62613703502646778609787879 93920555253970167914681819)
        ·
          refine ⟨140880832880955251872022729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93920555253970167914681819 140880832880955251872022729)
          ·
            refine ⟨105660624660716438904017047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140880832880955251872022729 105660624660716438904017047)
            ·
              refine ⟨158490936991074658356025571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105660624660716438904017047 158490936991074658356025571)
              ·
                refine ⟨237736405486611987534038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158490936991074658356025571 237736405486611987534038357)
                ·
                  refine ⟨174123343862264639307157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 237736405486611987534038357 174123343862264639307157)
                  ·
                    rfl

theorem cell22_1525968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_1525968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525968 prefixEnd_1525968 := by exact prefixLift 1525968
  have htrace : WordTrace (prefixWord ++ tailWord_1525968) baseStart_1525968 baseEnd_1525968 := by
    simpa [prefixWord, tailWord_1525968, baseEnd_1525968] using wordTrace_append hprefix tailTrace_1525968
  have hstable : (prefixWord ++ tailWord_1525968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525968).length < 2 ^ (prefixWord ++ tailWord_1525968).sum := by decide
  have hdescent : baseEnd_1525968 < baseStart_1525968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525974 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1525974 : Nat := 118140960795 + 1525974 * 2 ^ 59
def prefixEnd_1525974 : Nat := 4983230072969 + 3 ^ 40 * 1525974 * 2
def baseEnd_1525974 : Nat := 174124028503137300757151

theorem tailTrace_1525974 : CollatzResearch.WordTrace tailWord_1525974 prefixEnd_1525974 174124028503137300757151 := by
  unfold tailWord_1525974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478552760854018028477561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37104562782442858970427317 3478552760854018028477561)
  ·
    refine ⟨2608914570640513521358171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3478552760854018028477561 2608914570640513521358171)
    ·
      refine ⟨3913371855960770282037257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2608914570640513521358171 3913371855960770282037257)
      ·
        refine ⟨2935028891970577711527943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3913371855960770282037257 2935028891970577711527943)
        ·
          refine ⟨4402543337955866567291915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935028891970577711527943 4402543337955866567291915)
          ·
            refine ⟨6603815006933799850937873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402543337955866567291915 6603815006933799850937873)
            ·
              refine ⟨4952861255200349888203405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603815006933799850937873 4952861255200349888203405)
              ·
                refine ⟨1857322970700131208076277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4952861255200349888203405 1857322970700131208076277)
                ·
                  refine ⟨174124028503137300757151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1857322970700131208076277 174124028503137300757151)
                  ·
                    rfl

theorem cell22_1525974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1525974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525974 prefixEnd_1525974 := by exact prefixLift 1525974
  have htrace : WordTrace (prefixWord ++ tailWord_1525974) baseStart_1525974 baseEnd_1525974 := by
    simpa [prefixWord, tailWord_1525974, baseEnd_1525974] using wordTrace_append hprefix tailTrace_1525974
  have hstable : (prefixWord ++ tailWord_1525974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525974).length < 2 ^ (prefixWord ++ tailWord_1525974).sum := by decide
  have hdescent : baseEnd_1525974 < baseStart_1525974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1525985 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 6]
def baseStart_1525985 : Nat := 118140960795 + 1525985 * 2 ^ 59
def prefixEnd_1525985 : Nat := 4983230072969 + 3 ^ 40 * 1525985 * 2
def baseEnd_1525985 : Nat := 174125283678070513415473

theorem tailTrace_1525985 : CollatzResearch.WordTrace tailWord_1525985 prefixEnd_1525985 174125283678070513415473 := by
  unfold tailWord_1525985
  simp only [CollatzResearch.WordTrace]
  refine ⟨55657245376624437334291409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37104830251082958222860939 55657245376624437334291409)
  ·
    refine ⟨41742934032468328000718557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55657245376624437334291409 41742934032468328000718557)
    ·
      refine ⟨15653600262175623000269459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41742934032468328000718557 15653600262175623000269459)
      ·
        refine ⟨23480400393263434500404189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15653600262175623000269459 23480400393263434500404189)
        ·
          refine ⟨8805150147473787937651571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23480400393263434500404189 8805150147473787937651571)
          ·
            refine ⟨13207725221210681906477357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805150147473787937651571 13207725221210681906477357)
            ·
              refine ⟨4952896957954005714929009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13207725221210681906477357 4952896957954005714929009)
              ·
                refine ⟨3714672718465504286196757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952896957954005714929009 3714672718465504286196757)
                ·
                  refine ⟨174125283678070513415473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3714672718465504286196757 174125283678070513415473)
                  ·
                    rfl

theorem cell22_1525985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_1525985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1525985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1525985 prefixEnd_1525985 := by exact prefixLift 1525985
  have htrace : WordTrace (prefixWord ++ tailWord_1525985) baseStart_1525985 baseEnd_1525985 := by
    simpa [prefixWord, tailWord_1525985, baseEnd_1525985] using wordTrace_append hprefix tailTrace_1525985
  have hstable : (prefixWord ++ tailWord_1525985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1525985).length < 2 ^ (prefixWord ++ tailWord_1525985).sum := by decide
  have hdescent : baseEnd_1525985 < baseStart_1525985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1525985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526015 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 4, 4]
def baseStart_1526015 : Nat := 118140960795 + 1526015 * 2 ^ 59
def prefixEnd_1526015 : Nat := 4983230072969 + 3 ^ 40 * 1526015 * 2
def baseEnd_1526015 : Nat := 522386120647301461996327

theorem tailTrace_1526015 : CollatzResearch.WordTrace tailWord_1526015 prefixEnd_1526015 522386120647301461996327 := by
  unfold tailWord_1526015
  simp only [CollatzResearch.WordTrace]
  refine ⟨55658339566515752457883499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37105559711010501638588999 55658339566515752457883499)
  ·
    refine ⟨83487509349773628686825249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55658339566515752457883499 83487509349773628686825249)
    ·
      refine ⟨62615632012330221515118937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83487509349773628686825249 62615632012330221515118937)
      ·
        refine ⟨46961724009247666136339203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62615632012330221515118937 46961724009247666136339203)
        ·
          refine ⟨70442586013871499204508805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46961724009247666136339203 70442586013871499204508805)
          ·
            refine ⟨13207984877600906100845401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70442586013871499204508805 13207984877600906100845401)
            ·
              refine ⟨9905988658200679575634051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13207984877600906100845401 9905988658200679575634051)
              ·
                refine ⟨14858982987301019363451077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9905988658200679575634051 14858982987301019363451077)
                ·
                  refine ⟨2786059310118941130647077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14858982987301019363451077 2786059310118941130647077)
                  ·
                    refine ⟨522386120647301461996327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786059310118941130647077 522386120647301461996327)
                    ·
                      rfl

theorem cell22_1526015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_1526015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526015 prefixEnd_1526015 := by exact prefixLift 1526015
  have htrace : WordTrace (prefixWord ++ tailWord_1526015) baseStart_1526015 baseEnd_1526015 := by
    simpa [prefixWord, tailWord_1526015, baseEnd_1526015] using wordTrace_append hprefix tailTrace_1526015
  have hstable : (prefixWord ++ tailWord_1526015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526015).length < 2 ^ (prefixWord ++ tailWord_1526015).sum := by decide
  have hdescent : baseEnd_1526015 < baseStart_1526015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526017 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1526017 : Nat := 118140960795 + 1526017 * 2 ^ 59
def prefixEnd_1526017 : Nat := 4983230072969 + 3 ^ 40 * 1526017 * 2
def baseEnd_1526017 : Nat := 522386805288174123446321

theorem tailTrace_1526017 : CollatzResearch.WordTrace tailWord_1526017 prefixEnd_1526017 522386805288174123446321 := by
  unfold tailWord_1526017
  simp only [CollatzResearch.WordTrace]
  refine ⟨55658412512508506799456305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37105608341672337866304203 55658412512508506799456305)
  ·
    refine ⟨41743809384381380099592229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55658412512508506799456305 41743809384381380099592229)
    ·
      refine ⟨7826964259571508768673543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41743809384381380099592229 7826964259571508768673543)
      ·
        refine ⟨11740446389357263153010315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7826964259571508768673543 11740446389357263153010315)
        ·
          refine ⟨17610669584035894729515473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11740446389357263153010315 17610669584035894729515473)
          ·
            refine ⟨13208002188026921047136605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17610669584035894729515473 13208002188026921047136605)
            ·
              refine ⟨4953000820510095392676227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13208002188026921047136605 4953000820510095392676227)
              ·
                refine ⟨7429501230765143089014341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953000820510095392676227 7429501230765143089014341)
                ·
                  refine ⟨1393031480768464329190189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7429501230765143089014341 1393031480768464329190189)
                  ·
                    refine ⟨522386805288174123446321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393031480768464329190189 522386805288174123446321)
                    ·
                      rfl

theorem cell22_1526017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1526017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526017 prefixEnd_1526017 := by exact prefixLift 1526017
  have htrace : WordTrace (prefixWord ++ tailWord_1526017) baseStart_1526017 baseEnd_1526017 := by
    simpa [prefixWord, tailWord_1526017, baseEnd_1526017] using wordTrace_append hprefix tailTrace_1526017
  have hstable : (prefixWord ++ tailWord_1526017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526017).length < 2 ^ (prefixWord ++ tailWord_1526017).sum := by decide
  have hdescent : baseEnd_1526017 < baseStart_1526017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526030 : List Nat := [4, 1, 1, 2, 1, 2, 2, 9]
def baseStart_1526030 : Nat := 118140960795 + 1526030 * 2 ^ 59
def prefixEnd_1526030 : Nat := 4983230072969 + 3 ^ 40 * 1526030 * 2
def baseEnd_1526030 : Nat := 58043472828205158096809

theorem tailTrace_1526030 : CollatzResearch.WordTrace tailWord_1526030 prefixEnd_1526030 58043472828205158096809 := by
  unfold tailWord_1526030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957360832682676252459943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37105924440974273346453029 6957360832682676252459943)
  ·
    refine ⟨10436041249024014378689915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6957360832682676252459943 10436041249024014378689915)
    ·
      refine ⟨15654061873536021568034873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10436041249024014378689915 15654061873536021568034873)
      ·
        refine ⟨11740546405152016176026155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15654061873536021568034873 11740546405152016176026155)
        ·
          refine ⟨17610819607728024264039233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11740546405152016176026155 17610819607728024264039233)
          ·
            refine ⟨13208114705796018198029425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17610819607728024264039233 13208114705796018198029425)
            ·
              refine ⟨9906086029347013648522069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13208114705796018198029425 9906086029347013648522069)
              ·
                refine ⟨58043472828205158096809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9906086029347013648522069 58043472828205158096809)
                ·
                  rfl

theorem cell22_1526030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_1526030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526030 prefixEnd_1526030 := by exact prefixLift 1526030
  have htrace : WordTrace (prefixWord ++ tailWord_1526030) baseStart_1526030 baseEnd_1526030 := by
    simpa [prefixWord, tailWord_1526030, baseEnd_1526030] using wordTrace_append hprefix tailTrace_1526030
  have hstable : (prefixWord ++ tailWord_1526030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526030).length < 2 ^ (prefixWord ++ tailWord_1526030).sum := by decide
  have hdescent : baseEnd_1526030 < baseStart_1526030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526047 : List Nat := [1, 1, 2, 4, 3, 1, 4, 6]
def baseStart_1526047 : Nat := 118140960795 + 1526047 * 2 ^ 59
def prefixEnd_1526047 : Nat := 4983230072969 + 3 ^ 40 * 1526047 * 2
def baseEnd_1526047 : Nat := 58044119433473782799581

theorem tailTrace_1526047 : CollatzResearch.WordTrace tailWord_1526047 prefixEnd_1526047 58044119433473782799581 := by
  unfold tailWord_1526047
  simp only [CollatzResearch.WordTrace]
  refine ⟨55659506702399821923048395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37106337801599881282032263 55659506702399821923048395)
  ·
    refine ⟨83489260053599732884572593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55659506702399821923048395 83489260053599732884572593)
    ·
      refine ⟨62616945040199799663429445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83489260053599732884572593 62616945040199799663429445)
      ·
        refine ⟨11740677195037462436893021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62616945040199799663429445 11740677195037462436893021)
        ·
          refine ⟨4402753948139048413834883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11740677195037462436893021 4402753948139048413834883)
          ·
            refine ⟨6604130922208572620752325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402753948139048413834883 6604130922208572620752325)
            ·
              refine ⟨1238274547914107366391061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6604130922208572620752325 1238274547914107366391061)
              ·
                refine ⟨58044119433473782799581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1238274547914107366391061 58044119433473782799581)
                ·
                  rfl

theorem cell22_1526047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 6].length) (baseStart_1526047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526047 prefixEnd_1526047 := by exact prefixLift 1526047
  have htrace : WordTrace (prefixWord ++ tailWord_1526047) baseStart_1526047 baseEnd_1526047 := by
    simpa [prefixWord, tailWord_1526047, baseEnd_1526047] using wordTrace_append hprefix tailTrace_1526047
  have hstable : (prefixWord ++ tailWord_1526047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526047).length < 2 ^ (prefixWord ++ tailWord_1526047).sum := by decide
  have hdescent : baseEnd_1526047 < baseStart_1526047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526092 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_1526092 : Nat := 118140960795 + 1526092 * 2 ^ 59
def prefixEnd_1526092 : Nat := 4983230072969 + 3 ^ 40 * 1526092 * 2
def baseEnd_1526092 : Nat := 174137493106966309273697

theorem tailTrace_1526092 : CollatzResearch.WordTrace tailWord_1526092 prefixEnd_1526092 174137493106966309273697 := by
  unfold tailWord_1526092
  simp only [CollatzResearch.WordTrace]
  refine ⟨27830573993618397304218265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37107431991491196405624353 27830573993618397304218265)
  ·
    refine ⟨20872930495213797978163699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27830573993618397304218265 20872930495213797978163699)
    ·
      refine ⟨31309395742820696967245549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20872930495213797978163699 31309395742820696967245549)
      ·
        refine ⟨11741023403557761362717081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31309395742820696967245549 11741023403557761362717081)
        ·
          refine ⟨8805767552668321022037811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11741023403557761362717081 8805767552668321022037811)
          ·
            refine ⟨13208651329002481533056717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805767552668321022037811 13208651329002481533056717)
            ·
              refine ⟨4953244248375930574896269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13208651329002481533056717 4953244248375930574896269)
              ·
                refine ⟨1857466593140973965586101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4953244248375930574896269 1857466593140973965586101)
                ·
                  refine ⟨174137493106966309273697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1857466593140973965586101 174137493106966309273697)
                  ·
                    rfl

theorem cell22_1526092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_1526092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526092 prefixEnd_1526092 := by exact prefixLift 1526092
  have htrace : WordTrace (prefixWord ++ tailWord_1526092) baseStart_1526092 baseEnd_1526092 := by
    simpa [prefixWord, tailWord_1526092, baseEnd_1526092] using wordTrace_append hprefix tailTrace_1526092
  have hstable : (prefixWord ++ tailWord_1526092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526092).length < 2 ^ (prefixWord ++ tailWord_1526092).sum := by decide
  have hdescent : baseEnd_1526092 < baseStart_1526092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526173 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_1526173 : Nat := 118140960795 + 1526173 * 2 ^ 59
def prefixEnd_1526173 : Nat := 4983230072969 + 3 ^ 40 * 1526173 * 2
def baseEnd_1526173 : Nat := 522440207276241716545843

theorem tailTrace_1526173 : CollatzResearch.WordTrace tailWord_1526173 prefixEnd_1526173 522440207276241716545843 := by
  unfold tailWord_1526173
  simp only [CollatzResearch.WordTrace]
  refine ⟨55664102299943345442135173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37109401533295563628090115 55664102299943345442135173)
  ·
    refine ⟨10437019181239377270400345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55664102299943345442135173 10437019181239377270400345)
    ·
      refine ⟨7827764385929532952800259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10437019181239377270400345 7827764385929532952800259)
      ·
        refine ⟨11741646578894299429200389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827764385929532952800259 11741646578894299429200389)
        ·
          refine ⟨2201558733542681142975073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11741646578894299429200389 2201558733542681142975073)
          ·
            refine ⟨1651169050157010857231305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201558733542681142975073 1651169050157010857231305)
            ·
              refine ⟨1238376787617758142923479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651169050157010857231305 1238376787617758142923479)
              ·
                refine ⟨1857565181426637214385219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238376787617758142923479 1857565181426637214385219)
                ·
                  refine ⟨2786347772139955821577829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857565181426637214385219 2786347772139955821577829)
                  ·
                    refine ⟨522440207276241716545843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786347772139955821577829 522440207276241716545843)
                    ·
                      rfl

theorem cell22_1526173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_1526173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526173 prefixEnd_1526173 := by exact prefixLift 1526173
  have htrace : WordTrace (prefixWord ++ tailWord_1526173) baseStart_1526173 baseEnd_1526173 := by
    simpa [prefixWord, tailWord_1526173, baseEnd_1526173] using wordTrace_append hprefix tailTrace_1526173
  have hstable : (prefixWord ++ tailWord_1526173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526173).length < 2 ^ (prefixWord ++ tailWord_1526173).sum := by decide
  have hdescent : baseEnd_1526173 < baseStart_1526173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526287 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_1526287 : Nat := 118140960795 + 1526287 * 2 ^ 59
def prefixEnd_1526287 : Nat := 4983230072969 + 3 ^ 40 * 1526287 * 2
def baseEnd_1526287 : Nat := 522479231805983419195493

theorem tailTrace_1526287 : CollatzResearch.WordTrace tailWord_1526287 prefixEnd_1526287 522479231805983419195493 := by
  unfold tailWord_1526287
  simp only [CollatzResearch.WordTrace]
  refine ⟨55668260221530342911785115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37112173481020228607856743 55668260221530342911785115)
  ·
    refine ⟨83502390332295514367677673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55668260221530342911785115 83502390332295514367677673)
    ·
      refine ⟨62626792749221635775758255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83502390332295514367677673 62626792749221635775758255)
      ·
        refine ⟨93940189123832453663637383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62626792749221635775758255 93940189123832453663637383)
        ·
          refine ⟨140910283685748680495456075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93940189123832453663637383 140910283685748680495456075)
          ·
            refine ⟨211365425528623020743184113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140910283685748680495456075 211365425528623020743184113)
            ·
              refine ⟨158524069146467265557388085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211365425528623020743184113 158524069146467265557388085)
              ·
                refine ⟨14861631482481306146005133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158524069146467265557388085 14861631482481306146005133)
                ·
                  refine ⟨5573111805930489804751925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14861631482481306146005133 5573111805930489804751925)
                  ·
                    refine ⟨522479231805983419195493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5573111805930489804751925 522479231805983419195493)
                    ·
                      rfl

theorem cell22_1526287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_1526287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526287 prefixEnd_1526287 := by exact prefixLift 1526287
  have htrace : WordTrace (prefixWord ++ tailWord_1526287) baseStart_1526287 baseEnd_1526287 := by
    simpa [prefixWord, tailWord_1526287, baseEnd_1526287] using wordTrace_append hprefix tailTrace_1526287
  have hstable : (prefixWord ++ tailWord_1526287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526287).length < 2 ^ (prefixWord ++ tailWord_1526287).sum := by decide
  have hdescent : baseEnd_1526287 < baseStart_1526287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526291 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 1, 4]
def baseStart_1526291 : Nat := 118140960795 + 1526291 * 2 ^ 59
def prefixEnd_1526291 : Nat := 4983230072969 + 3 ^ 40 * 1526291 * 2
def baseEnd_1526291 : Nat := 522480601087728742095481

theorem tailTrace_1526291 : CollatzResearch.WordTrace tailWord_1526291 prefixEnd_1526291 522480601087728742095481 := by
  unfold tailWord_1526291
  simp only [CollatzResearch.WordTrace]
  refine ⟨55668406113515851594930727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37112270742343901063287151 55668406113515851594930727)
  ·
    refine ⟨83502609170273777392396091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55668406113515851594930727 83502609170273777392396091)
    ·
      refine ⟨125253913755410666088594137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83502609170273777392396091 125253913755410666088594137)
      ·
        refine ⟨93940435316557999566445603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125253913755410666088594137 93940435316557999566445603)
        ·
          refine ⟨140910652974836999349668405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93940435316557999566445603 140910652974836999349668405)
          ·
            refine ⟨13210373716390968689031413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140910652974836999349668405 13210373716390968689031413)
            ·
              refine ⟨1238472535911653314596695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13210373716390968689031413 1238472535911653314596695)
              ·
                refine ⟨1857708803867479971895043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238472535911653314596695 1857708803867479971895043)
                ·
                  refine ⟨2786563205801219957842565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857708803867479971895043 2786563205801219957842565)
                  ·
                    refine ⟨522480601087728742095481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786563205801219957842565 522480601087728742095481)
                    ·
                      rfl

theorem cell22_1526291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 4].length) (baseStart_1526291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526291 prefixEnd_1526291 := by exact prefixLift 1526291
  have htrace : WordTrace (prefixWord ++ tailWord_1526291) baseStart_1526291 baseEnd_1526291 := by
    simpa [prefixWord, tailWord_1526291, baseEnd_1526291] using wordTrace_append hprefix tailTrace_1526291
  have hstable : (prefixWord ++ tailWord_1526291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526291).length < 2 ^ (prefixWord ++ tailWord_1526291).sum := by decide
  have hdescent : baseEnd_1526291 < baseStart_1526291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
