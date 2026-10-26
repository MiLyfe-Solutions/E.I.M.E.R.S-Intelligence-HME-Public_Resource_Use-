import V185TrunkScan23Chunk1328

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7871990 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_7871990 : Nat := 118140960795 + 7871990 * 2 ^ 59
def prefixEnd_7871990 : Nat := 4983230072969 + 3 ^ 40 * 7871990 * 2
def baseEnd_7871990 : Nat := 449123841931862337402487

theorem tailTrace_7871990 : CollatzResearch.WordTrace tailWord_7871990 prefixEnd_7871990 449123841931862337402487 := by
  unfold tailWord_7871990
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944691421945758356353839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191410041834088089134440949 17944691421945758356353839)
  ·
    refine ⟨26917037132918637534530759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17944691421945758356353839 26917037132918637534530759)
    ·
      refine ⟨40375555699377956301796139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26917037132918637534530759 40375555699377956301796139)
      ·
        refine ⟨60563333549066934452694209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40375555699377956301796139 60563333549066934452694209)
        ·
          refine ⟨45422500161800200839520657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60563333549066934452694209 45422500161800200839520657)
          ·
            refine ⟨34066875121350150629640493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45422500161800200839520657 34066875121350150629640493)
            ·
              refine ⟨12775078170506306486115185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34066875121350150629640493 12775078170506306486115185)
              ·
                refine ⟨9581308627879729864586389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12775078170506306486115185 9581308627879729864586389)
                ·
                  refine ⟨449123841931862337402487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9581308627879729864586389 449123841931862337402487)
                  ·
                    rfl

theorem cell23_7871990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_7871990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871990 prefixEnd_7871990 := by exact prefixLift 7871990
  have htrace : WordTrace (prefixWord ++ tailWord_7871990) baseStart_7871990 baseEnd_7871990 := by
    simpa [prefixWord, tailWord_7871990, baseEnd_7871990] using wordTrace_append hprefix tailTrace_7871990
  have hstable : (prefixWord ++ tailWord_7871990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871990).length < 2 ^ (prefixWord ++ tailWord_7871990).sum := by decide
  have hdescent : baseEnd_7871990 < baseStart_7871990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872010 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_7872010 : Nat := 118140960795 + 7872010 * 2 ^ 59
def prefixEnd_7872010 : Nat := 4983230072969 + 3 ^ 40 * 7872010 * 2
def baseEnd_7872010 : Nat := 4042124846999850958372291

theorem tailTrace_7872010 : CollatzResearch.WordTrace tailWord_7872010 prefixEnd_7872010 4042124846999850958372291 := by
  unfold tailWord_7872010
  simp only [CollatzResearch.WordTrace]
  refine ⟨71778948052764919279347371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191410528140706451411592989 71778948052764919279347371)
  ·
    refine ⟨107668422079147378919021057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71778948052764919279347371 107668422079147378919021057)
    ·
      refine ⟨80751316559360534189265793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107668422079147378919021057 80751316559360534189265793)
      ·
        refine ⟨60563487419520400641949345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80751316559360534189265793 60563487419520400641949345)
        ·
          refine ⟨45422615564640300481462009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60563487419520400641949345 45422615564640300481462009)
          ·
            refine ⟨34066961673480225361096507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45422615564640300481462009 34066961673480225361096507)
            ·
              refine ⟨51100442510220338041644761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34066961673480225361096507 51100442510220338041644761)
              ·
                refine ⟨38325331882665253531233571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51100442510220338041644761 38325331882665253531233571)
                ·
                  refine ⟨57487997823997880296850357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38325331882665253531233571 57487997823997880296850357)
                  ·
                    refine ⟨5389499795999801277829721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57487997823997880296850357 5389499795999801277829721)
                    ·
                      refine ⟨4042124846999850958372291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389499795999801277829721 4042124846999850958372291)
                      ·
                        rfl

theorem cell23_7872010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_7872010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872010 prefixEnd_7872010 := by exact prefixLift 7872010
  have htrace : WordTrace (prefixWord ++ tailWord_7872010) baseStart_7872010 baseEnd_7872010 := by
    simpa [prefixWord, tailWord_7872010, baseEnd_7872010] using wordTrace_append hprefix tailTrace_7872010
  have hstable : (prefixWord ++ tailWord_7872010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872010).length < 2 ^ (prefixWord ++ tailWord_7872010).sum := by decide
  have hdescent : baseEnd_7872010 < baseStart_7872010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872034 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_7872034 : Nat := 118140960795 + 7872034 * 2 ^ 59
def prefixEnd_7872034 : Nat := 4983230072969 + 3 ^ 40 * 7872034 * 2
def baseEnd_7872034 : Nat := 4042137170535558864472181

theorem tailTrace_7872034 : CollatzResearch.WordTrace tailWord_7872034 prefixEnd_7872034 4042137170535558864472181 := by
  unfold tailWord_7872034
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779166890743182304065789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191411111708648486144175437 71779166890743182304065789)
  ·
    refine ⟨26917187584028693364024671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71779166890743182304065789 26917187584028693364024671)
    ·
      refine ⟨40375781376043040046037007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26917187584028693364024671 40375781376043040046037007)
      ·
        refine ⟨60563672064064560069055511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40375781376043040046037007 60563672064064560069055511)
        ·
          refine ⟨90845508096096840103583267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60563672064064560069055511 90845508096096840103583267)
          ·
            refine ⟨136268262144145260155374901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90845508096096840103583267 136268262144145260155374901)
            ·
              refine ⟨12775149576013618139566397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136268262144145260155374901 12775149576013618139566397)
              ·
                refine ⟨4790681091005106802337399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12775149576013618139566397 4790681091005106802337399)
                ·
                  refine ⟨7186021636507660203506099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790681091005106802337399 7186021636507660203506099)
                  ·
                    refine ⟨10779032454761490305259149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7186021636507660203506099 10779032454761490305259149)
                    ·
                      refine ⟨4042137170535558864472181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779032454761490305259149 4042137170535558864472181)
                      ·
                        rfl

theorem cell23_7872034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_7872034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872034 prefixEnd_7872034 := by exact prefixLift 7872034
  have htrace : WordTrace (prefixWord ++ tailWord_7872034) baseStart_7872034 baseEnd_7872034 := by
    simpa [prefixWord, tailWord_7872034, baseEnd_7872034] using wordTrace_append hprefix tailTrace_7872034
  have hstable : (prefixWord ++ tailWord_7872034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872034).length < 2 ^ (prefixWord ++ tailWord_7872034).sum := by decide
  have hdescent : baseEnd_7872034 < baseStart_7872034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872043 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 3]
def baseStart_7872043 : Nat := 118140960795 + 7872043 * 2 ^ 59
def prefixEnd_7872043 : Nat := 4983230072969 + 3 ^ 40 * 7872043 * 2
def baseEnd_7872043 : Nat := 4042141791861449329259639

theorem tailTrace_7872043 : CollatzResearch.WordTrace tailWord_7872043 prefixEnd_7872043 4042141791861449329259639 := by
  unfold tailWord_7872043
  simp only [CollatzResearch.WordTrace]
  refine ⟨287116995819940123753340783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191411330546626749168893855 287116995819940123753340783)
  ·
    refine ⟨430675493729910185630011175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287116995819940123753340783 430675493729910185630011175)
    ·
      refine ⟨646013240594865278445016763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430675493729910185630011175 646013240594865278445016763)
      ·
        refine ⟨969019860892297917667525145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646013240594865278445016763 969019860892297917667525145)
        ·
          refine ⟨726764895669223438250643859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969019860892297917667525145 726764895669223438250643859)
          ·
            refine ⟨1090147343503835157375965789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726764895669223438250643859 1090147343503835157375965789)
            ·
              refine ⟨408805253813938184015987171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090147343503835157375965789 408805253813938184015987171)
              ·
                refine ⟨613207880720907276023980757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408805253813938184015987171 613207880720907276023980757)
                ·
                  refine ⟨14372059704396264281812049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 613207880720907276023980757 14372059704396264281812049)
                  ·
                    refine ⟨10779044778297198211359037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14372059704396264281812049 10779044778297198211359037)
                    ·
                      refine ⟨4042141791861449329259639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779044778297198211359037 4042141791861449329259639)
                      ·
                        rfl

theorem cell23_7872043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 3].length) (baseStart_7872043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872043 prefixEnd_7872043 := by exact prefixLift 7872043
  have htrace : WordTrace (prefixWord ++ tailWord_7872043) baseStart_7872043 baseEnd_7872043 := by
    simpa [prefixWord, tailWord_7872043, baseEnd_7872043] using wordTrace_append hprefix tailTrace_7872043
  have hstable : (prefixWord ++ tailWord_7872043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872043).length < 2 ^ (prefixWord ++ tailWord_7872043).sum := by decide
  have hdescent : baseEnd_7872043 < baseStart_7872043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872050 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_7872050 : Nat := 118140960795 + 7872050 * 2 ^ 59
def prefixEnd_7872050 : Nat := 4983230072969 + 3 ^ 40 * 7872050 * 2
def baseEnd_7872050 : Nat := 1347381795408676933957369

theorem tailTrace_7872050 : CollatzResearch.WordTrace tailWord_7872050 prefixEnd_7872050 1347381795408676933957369 := by
  unfold tailWord_7872050
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779312782728690987211401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191411500753943175965897069 71779312782728690987211401)
  ·
    refine ⟨53834484587046518240408551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71779312782728690987211401 53834484587046518240408551)
    ·
      refine ⟨80751726880569777360612827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53834484587046518240408551 80751726880569777360612827)
      ·
        refine ⟨121127590320854666040919241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80751726880569777360612827 121127590320854666040919241)
        ·
          refine ⟨90845692740640999530689431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121127590320854666040919241 90845692740640999530689431)
          ·
            refine ⟨136268539110961499296034147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90845692740640999530689431 136268539110961499296034147)
            ·
              refine ⟨204402808666442248944051221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136268539110961499296034147 204402808666442248944051221)
              ·
                refine ⟨9581381656239480419252401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204402808666442248944051221 9581381656239480419252401)
                ·
                  refine ⟨7186036242179610314439301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9581381656239480419252401 7186036242179610314439301)
                  ·
                    refine ⟨1347381795408676933957369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186036242179610314439301 1347381795408676933957369)
                    ·
                      rfl

theorem cell23_7872050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_7872050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872050 prefixEnd_7872050 := by exact prefixLift 7872050
  have htrace : WordTrace (prefixWord ++ tailWord_7872050) baseStart_7872050 baseEnd_7872050 := by
    simpa [prefixWord, tailWord_7872050, baseEnd_7872050] using wordTrace_append hprefix tailTrace_7872050
  have hstable : (prefixWord ++ tailWord_7872050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872050).length < 2 ^ (prefixWord ++ tailWord_7872050).sum := by decide
  have hdescent : baseEnd_7872050 < baseStart_7872050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872053 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7872053 : Nat := 118140960795 + 7872053 * 2 ^ 59
def prefixEnd_7872053 : Nat := 4983230072969 + 3 ^ 40 * 7872053 * 2
def baseEnd_7872053 : Nat := 4042146926667994290134593

theorem tailTrace_7872053 : CollatzResearch.WordTrace tailWord_7872053 prefixEnd_7872053 4042146926667994290134593 := by
  unfold tailWord_7872053
  simp only [CollatzResearch.WordTrace]
  refine ⟨287117360549903895461204813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191411573699935930307469875 287117360549903895461204813)
  ·
    refine ⟨107669010206213960797951805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287117360549903895461204813 107669010206213960797951805)
    ·
      refine ⟨40375878827330235299231927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107669010206213960797951805 40375878827330235299231927)
      ·
        refine ⟨60563818240995352948847891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40375878827330235299231927 60563818240995352948847891)
        ·
          refine ⟨90845727361493029423271837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60563818240995352948847891 90845727361493029423271837)
          ·
            refine ⟨34067147760559886033726939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90845727361493029423271837 34067147760559886033726939)
            ·
              refine ⟨51100721640839829050590409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34067147760559886033726939 51100721640839829050590409)
              ·
                refine ⟨38325541230629871787942807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51100721640839829050590409 38325541230629871787942807)
                ·
                  refine ⟨57488311845944807681914211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38325541230629871787942807 57488311845944807681914211)
                  ·
                    refine ⟨86232467768917211522871317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57488311845944807681914211 86232467768917211522871317)
                    ·
                      refine ⟨4042146926667994290134593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86232467768917211522871317 4042146926667994290134593)
                      ·
                        rfl

theorem cell23_7872053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7872053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872053 prefixEnd_7872053 := by exact prefixLift 7872053
  have htrace : WordTrace (prefixWord ++ tailWord_7872053) baseStart_7872053 baseEnd_7872053 := by
    simpa [prefixWord, tailWord_7872053, baseEnd_7872053] using wordTrace_append hprefix tailTrace_7872053
  have hstable : (prefixWord ++ tailWord_7872053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872053).length < 2 ^ (prefixWord ++ tailWord_7872053).sum := by decide
  have hdescent : baseEnd_7872053 < baseStart_7872053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872063 : List Nat := [1, 1, 2, 2, 3, 4, 2, 8]
def baseStart_7872063 : Nat := 118140960795 + 7872063 * 2 ^ 59
def prefixEnd_7872063 : Nat := 4983230072969 + 3 ^ 40 * 7872063 * 2
def baseEnd_7872063 : Nat := 149709335610168120407761

theorem tailTrace_7872063 : CollatzResearch.WordTrace tailWord_7872063 prefixEnd_7872063 149709335610168120407761 := by
  unfold tailWord_7872063
  simp only [CollatzResearch.WordTrace]
  refine ⟨287117725279867667169068843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191411816853245111446045895 287117725279867667169068843)
  ·
    refine ⟨430676587919801500753603265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287117725279867667169068843 430676587919801500753603265)
    ·
      refine ⟨323007440939851125565202449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430676587919801500753603265 323007440939851125565202449)
      ·
        refine ⟨242255580704888344173901837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323007440939851125565202449 242255580704888344173901837)
        ·
          refine ⟨90845842764333129065213189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242255580704888344173901837 90845842764333129065213189)
          ·
            refine ⟨17033595518312461699727473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90845842764333129065213189 17033595518312461699727473)
            ·
              refine ⟨12775196638734346274795605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17033595518312461699727473 12775196638734346274795605)
              ·
                refine ⟨149709335610168120407761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12775196638734346274795605 149709335610168120407761)
                ·
                  rfl

theorem cell23_7872063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 8].length) (baseStart_7872063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872063 prefixEnd_7872063 := by exact prefixLift 7872063
  have htrace : WordTrace (prefixWord ++ tailWord_7872063) baseStart_7872063 baseEnd_7872063 := by
    simpa [prefixWord, tailWord_7872063, baseEnd_7872063] using wordTrace_append hprefix tailTrace_7872063
  have hstable : (prefixWord ++ tailWord_7872063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872063).length < 2 ^ (prefixWord ++ tailWord_7872063).sum := by decide
  have hdescent : baseEnd_7872063 < baseStart_7872063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872073 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_7872073 : Nat := 118140960795 + 7872073 * 2 ^ 59
def prefixEnd_7872073 : Nat := 4983230072969 + 3 ^ 40 * 7872073 * 2
def baseEnd_7872073 : Nat := 4042157196281084211884501

theorem tailTrace_7872073 : CollatzResearch.WordTrace tailWord_7872073 prefixEnd_7872073 4042157196281084211884501 := by
  unfold tailWord_7872073
  simp only [CollatzResearch.WordTrace]
  refine ⟨287118090009831438876932873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191412060006554292584621915 287118090009831438876932873)
  ·
    refine ⟨215338567507373579157699655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287118090009831438876932873 215338567507373579157699655)
    ·
      refine ⟨323007851261060368736549483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215338567507373579157699655 323007851261060368736549483)
      ·
        refine ⟨484511776891590553104824225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323007851261060368736549483 484511776891590553104824225)
        ·
          refine ⟨363383832668692914828618169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484511776891590553104824225 363383832668692914828618169)
          ·
            refine ⟨272537874501519686121463627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363383832668692914828618169 272537874501519686121463627)
            ·
              refine ⟨408806811752279529182195441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272537874501519686121463627 408806811752279529182195441)
              ·
                refine ⟨306605108814209646886646581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408806811752279529182195441 306605108814209646886646581)
                ·
                  refine ⟨28744228951332154395623117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306605108814209646886646581 28744228951332154395623117)
                  ·
                    refine ⟨10779085856749557898358669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28744228951332154395623117 10779085856749557898358669)
                    ·
                      refine ⟨4042157196281084211884501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779085856749557898358669 4042157196281084211884501)
                      ·
                        rfl

theorem cell23_7872073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_7872073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872073 prefixEnd_7872073 := by exact prefixLift 7872073
  have htrace : WordTrace (prefixWord ++ tailWord_7872073) baseStart_7872073 baseEnd_7872073 := by
    simpa [prefixWord, tailWord_7872073, baseEnd_7872073] using wordTrace_append hprefix tailTrace_7872073
  have hstable : (prefixWord ++ tailWord_7872073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872073).length < 2 ^ (prefixWord ++ tailWord_7872073).sum := by decide
  have hdescent : baseEnd_7872073 < baseStart_7872073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872090 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_7872090 : Nat := 118140960795 + 7872090 * 2 ^ 59
def prefixEnd_7872090 : Nat := 4983230072969 + 3 ^ 40 * 7872090 * 2
def baseEnd_7872090 : Nat := 4042165925452210645371923

theorem tailTrace_7872090 : CollatzResearch.WordTrace tailWord_7872090 prefixEnd_7872090 4042165925452210645371923 := by
  unfold tailWord_7872090
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779677512692462695075431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191412473367179900520201149 71779677512692462695075431)
  ·
    refine ⟨107669516269038694042613147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71779677512692462695075431 107669516269038694042613147)
    ·
      refine ⟨161504274403558041063919721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107669516269038694042613147 161504274403558041063919721)
      ·
        refine ⟨121128205802668530797939791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161504274403558041063919721 121128205802668530797939791)
        ·
          refine ⟨181692308704002796196909687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121128205802668530797939791 181692308704002796196909687)
          ·
            refine ⟨272538463056004194295364531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181692308704002796196909687 272538463056004194295364531)
            ·
              refine ⟨408807694584006291443046797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272538463056004194295364531 408807694584006291443046797)
              ·
                refine ⟨153302885469002359291142549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408807694584006291443046797 153302885469002359291142549)
                ·
                  refine ⟨7186072756359485591772307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153302885469002359291142549 7186072756359485591772307)
                  ·
                    refine ⟨10779109134539228387658461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7186072756359485591772307 10779109134539228387658461)
                    ·
                      refine ⟨4042165925452210645371923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779109134539228387658461 4042165925452210645371923)
                      ·
                        rfl

theorem cell23_7872090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_7872090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872090 prefixEnd_7872090 := by exact prefixLift 7872090
  have htrace : WordTrace (prefixWord ++ tailWord_7872090) baseStart_7872090 baseEnd_7872090 := by
    simpa [prefixWord, tailWord_7872090, baseEnd_7872090] using wordTrace_append hprefix tailTrace_7872090
  have hstable : (prefixWord ++ tailWord_7872090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872090).length < 2 ^ (prefixWord ++ tailWord_7872090).sum := by decide
  have hdescent : baseEnd_7872090 < baseStart_7872090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872103 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_7872103 : Nat := 118140960795 + 7872103 * 2 ^ 59
def prefixEnd_7872103 : Nat := 4983230072969 + 3 ^ 40 * 7872103 * 2
def baseEnd_7872103 : Nat := 4042172600700719094509363

theorem tailTrace_7872103 : CollatzResearch.WordTrace tailWord_7872103 prefixEnd_7872103 4042172600700719094509363 := by
  unfold tailWord_7872103
  simp only [CollatzResearch.WordTrace]
  refine ⟨287119184199722754000524963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191412789466481836000349975 287119184199722754000524963)
  ·
    refine ⟨430678776299584131000787445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287119184199722754000524963 430678776299584131000787445)
    ·
      refine ⟨40376135278086012281323823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430678776299584131000787445 40376135278086012281323823)
      ·
        refine ⟨60564202917129018421985735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40376135278086012281323823 60564202917129018421985735)
        ·
          refine ⟨90846304375693527632978603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60564202917129018421985735 90846304375693527632978603)
          ·
            refine ⟨136269456563540291449467905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90846304375693527632978603 136269456563540291449467905)
            ·
              refine ⟨102202092422655218587100929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136269456563540291449467905 102202092422655218587100929)
              ·
                refine ⟨76651569316991413940325697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102202092422655218587100929 76651569316991413940325697)
                ·
                  refine ⟨57488676987743560455244273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76651569316991413940325697 57488676987743560455244273)
                  ·
                    refine ⟨43116507740807670341433205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57488676987743560455244273 43116507740807670341433205)
                    ·
                      refine ⟨4042172600700719094509363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43116507740807670341433205 4042172600700719094509363)
                      ·
                        rfl

theorem cell23_7872103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_7872103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872103 prefixEnd_7872103 := by exact prefixLift 7872103
  have htrace : WordTrace (prefixWord ++ tailWord_7872103) baseStart_7872103 baseEnd_7872103 := by
    simpa [prefixWord, tailWord_7872103, baseEnd_7872103] using wordTrace_append hprefix tailTrace_7872103
  have hstable : (prefixWord ++ tailWord_7872103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872103).length < 2 ^ (prefixWord ++ tailWord_7872103).sum := by decide
  have hdescent : baseEnd_7872103 < baseStart_7872103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872123 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 2, 6]
def baseStart_7872123 : Nat := 118140960795 + 7872123 * 2 ^ 59
def prefixEnd_7872123 : Nat := 4983230072969 + 3 ^ 40 * 7872123 * 2
def baseEnd_7872123 : Nat := 1347394290104603005419757

theorem tailTrace_7872123 : CollatzResearch.WordTrace tailWord_7872123 prefixEnd_7872123 1347394290104603005419757 := by
  unfold tailWord_7872123
  simp only [CollatzResearch.WordTrace]
  refine ⟨287119913659650297416253023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191413275773100198277502015 287119913659650297416253023)
  ·
    refine ⟨430679870489475446124379535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287119913659650297416253023 430679870489475446124379535)
    ·
      refine ⟨646019805734213169186569303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430679870489475446124379535 646019805734213169186569303)
      ·
        refine ⟨969029708601319753779853955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646019805734213169186569303 969029708601319753779853955)
        ·
          refine ⟨1453544562901979630669780933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969029708601319753779853955 1453544562901979630669780933)
          ·
            refine ⟨272539605544121180750583925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1453544562901979630669780933 272539605544121180750583925)
            ·
              refine ⟨25550588019761360695367243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272539605544121180750583925 25550588019761360695367243)
              ·
                refine ⟨38325882029642041043050865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25550588019761360695367243 38325882029642041043050865)
                ·
                  refine ⟨28744411522231530782288149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38325882029642041043050865 28744411522231530782288149)
                  ·
                    refine ⟨1347394290104603005419757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28744411522231530782288149 1347394290104603005419757)
                    ·
                      rfl

theorem cell23_7872123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_7872123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872123 prefixEnd_7872123 := by exact prefixLift 7872123
  have htrace : WordTrace (prefixWord ++ tailWord_7872123) baseStart_7872123 baseEnd_7872123 := by
    simpa [prefixWord, tailWord_7872123, baseEnd_7872123] using wordTrace_append hprefix tailTrace_7872123
  have hstable : (prefixWord ++ tailWord_7872123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872123).length < 2 ^ (prefixWord ++ tailWord_7872123).sum := by decide
  have hdescent : baseEnd_7872123 < baseStart_7872123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872143 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_7872143 : Nat := 118140960795 + 7872143 * 2 ^ 59
def prefixEnd_7872143 : Nat := 4983230072969 + 3 ^ 40 * 7872143 * 2
def baseEnd_7872143 : Nat := 4042193139926898938009179

theorem tailTrace_7872143 : CollatzResearch.WordTrace tailWord_7872143 prefixEnd_7872143 4042193139926898938009179 := by
  unfold tailWord_7872143
  simp only [CollatzResearch.WordTrace]
  refine ⟨287120643119577840831981083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191413762079718560554654055 287120643119577840831981083)
  ·
    refine ⟨430680964679366761247971625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287120643119577840831981083 430680964679366761247971625)
    ·
      refine ⟨323010723509525070935978719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430680964679366761247971625 323010723509525070935978719)
      ·
        refine ⟨484516085264287606403968079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323010723509525070935978719 484516085264287606403968079)
        ·
          refine ⟨726774127896431409605952119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484516085264287606403968079 726774127896431409605952119)
          ·
            refine ⟨1090161191844647114408928179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726774127896431409605952119 1090161191844647114408928179)
            ·
              refine ⟨1635241787766970671613392269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090161191844647114408928179 1635241787766970671613392269)
              ·
                refine ⟨613215670412614001855022101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635241787766970671613392269 613215670412614001855022101)
                ·
                  refine ⟨28744484550591281336954161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 613215670412614001855022101 28744484550591281336954161)
                  ·
                    refine ⟨21558363412943461002715621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28744484550591281336954161 21558363412943461002715621)
                    ·
                      refine ⟨4042193139926898938009179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21558363412943461002715621 4042193139926898938009179)
                      ·
                        rfl

theorem cell23_7872143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_7872143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872143 prefixEnd_7872143 := by exact prefixLift 7872143
  have htrace : WordTrace (prefixWord ++ tailWord_7872143) baseStart_7872143 baseEnd_7872143 := by
    simpa [prefixWord, tailWord_7872143, baseEnd_7872143] using wordTrace_append hprefix tailTrace_7872143
  have hstable : (prefixWord ++ tailWord_7872143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872143).length < 2 ^ (prefixWord ++ tailWord_7872143).sum := by decide
  have hdescent : baseEnd_7872143 < baseStart_7872143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872151 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 1, 3, 2]
def baseStart_7872151 : Nat := 118140960795 + 7872151 * 2 ^ 59
def prefixEnd_7872151 : Nat := 4983230072969 + 3 ^ 40 * 7872151 * 2
def baseEnd_7872151 : Nat := 4042197247772134906709143

theorem tailTrace_7872151 : CollatzResearch.WordTrace tailWord_7872151 prefixEnd_7872151 4042197247772134906709143 := by
  unfold tailWord_7872151
  simp only [CollatzResearch.WordTrace]
  refine ⟨287120934903548858198272307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191413956602365905465514871 287120934903548858198272307)
  ·
    refine ⟨430681402355323287297408461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287120934903548858198272307 430681402355323287297408461)
    ·
      refine ⟨161505525883246232736528173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430681402355323287297408461 161505525883246232736528173)
      ·
        refine ⟨60564572206217337276198065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161505525883246232736528173 60564572206217337276198065)
        ·
          refine ⟨45423429154663002957148549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60564572206217337276198065 45423429154663002957148549)
          ·
            refine ⟨8516892966499313054465353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45423429154663002957148549 8516892966499313054465353)
            ·
              refine ⟨6387669724874484790849015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8516892966499313054465353 6387669724874484790849015)
              ·
                refine ⟨9581504587311727186273523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387669724874484790849015 9581504587311727186273523)
                ·
                  refine ⟨14372256880967590779410285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581504587311727186273523 14372256880967590779410285)
                  ·
                    refine ⟨5389596330362846542278857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14372256880967590779410285 5389596330362846542278857)
                    ·
                      refine ⟨4042197247772134906709143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389596330362846542278857 4042197247772134906709143)
                      ·
                        rfl

theorem cell23_7872151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_7872151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872151 prefixEnd_7872151 := by exact prefixLift 7872151
  have htrace : WordTrace (prefixWord ++ tailWord_7872151) baseStart_7872151 baseEnd_7872151 := by
    simpa [prefixWord, tailWord_7872151, baseEnd_7872151] using wordTrace_append hprefix tailTrace_7872151
  have hstable : (prefixWord ++ tailWord_7872151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872151).length < 2 ^ (prefixWord ++ tailWord_7872151).sum := by decide
  have hdescent : baseEnd_7872151 < baseStart_7872151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872160 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_7872160 : Nat := 118140960795 + 7872160 * 2 ^ 59
def prefixEnd_7872160 : Nat := 4983230072969 + 3 ^ 40 * 7872160 * 2
def baseEnd_7872160 : Nat := 4042201869098025371496601

theorem tailTrace_7872160 : CollatzResearch.WordTrace tailWord_7872160 prefixEnd_7872160 4042201869098025371496601 := by
  unfold tailWord_7872160
  simp only [CollatzResearch.WordTrace]
  refine ⟨143560631580258126367674967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191414175440344168490233289 143560631580258126367674967)
  ·
    refine ⟨215340947370387189551512451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143560631580258126367674967 215340947370387189551512451)
    ·
      refine ⟨323011421055580784327268677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215340947370387189551512451 323011421055580784327268677)
      ·
        refine ⟨60564641447921397061362877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323011421055580784327268677 60564641447921397061362877)
        ·
          refine ⟨22711740542970523898011079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60564641447921397061362877 22711740542970523898011079)
          ·
            refine ⟨34067610814455785847016619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22711740542970523898011079 34067610814455785847016619)
            ·
              refine ⟨51101416221683678770524929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34067610814455785847016619 51101416221683678770524929)
              ·
                refine ⟨38326062166262759077893697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51101416221683678770524929 38326062166262759077893697)
                ·
                  refine ⟨28744546624697069308420273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38326062166262759077893697 28744546624697069308420273)
                  ·
                    refine ⟨21558409968522801981315205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28744546624697069308420273 21558409968522801981315205)
                    ·
                      refine ⟨4042201869098025371496601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21558409968522801981315205 4042201869098025371496601)
                      ·
                        rfl

theorem cell23_7872160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_7872160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872160 prefixEnd_7872160 := by exact prefixLift 7872160
  have htrace : WordTrace (prefixWord ++ tailWord_7872160) baseStart_7872160 baseEnd_7872160 := by
    simpa [prefixWord, tailWord_7872160, baseEnd_7872160] using wordTrace_append hprefix tailTrace_7872160
  have hstable : (prefixWord ++ tailWord_7872160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872160).length < 2 ^ (prefixWord ++ tailWord_7872160).sum := by decide
  have hdescent : baseEnd_7872160 < baseStart_7872160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872164 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_7872164 : Nat := 118140960795 + 7872164 * 2 ^ 59
def prefixEnd_7872164 : Nat := 4983230072969 + 3 ^ 40 * 7872164 * 2
def baseEnd_7872164 : Nat := 4042203923020643355846583

theorem tailTrace_7872164 : CollatzResearch.WordTrace tailWord_7872164 prefixEnd_7872164 4042203923020643355846583 := by
  unfold tailWord_7872164
  simp only [CollatzResearch.WordTrace]
  refine ⟨143560704526250880709247773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191414272701667840945663697 143560704526250880709247773)
  ·
    refine ⟨53835264197344080265967915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143560704526250880709247773 53835264197344080265967915)
    ·
      refine ⟨80752896296016120398951873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53835264197344080265967915 80752896296016120398951873)
      ·
        refine ⟨60564672222012090299213905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80752896296016120398951873 60564672222012090299213905)
        ·
          refine ⟨45423504166509067724410429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60564672222012090299213905 45423504166509067724410429)
          ·
            refine ⟨17033814062440900396653911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45423504166509067724410429 17033814062440900396653911)
            ·
              refine ⟨25550721093661350594980867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17033814062440900396653911 25550721093661350594980867)
              ·
                refine ⟨38326081640492025892471301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25550721093661350594980867 38326081640492025892471301)
                ·
                  refine ⟨7186140307592254854838369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38326081640492025892471301 7186140307592254854838369)
                  ·
                    refine ⟨5389605230694191141128777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7186140307592254854838369 5389605230694191141128777)
                    ·
                      refine ⟨4042203923020643355846583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389605230694191141128777 4042203923020643355846583)
                      ·
                        rfl

theorem cell23_7872164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_7872164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872164 prefixEnd_7872164 := by exact prefixLift 7872164
  have htrace : WordTrace (prefixWord ++ tailWord_7872164) baseStart_7872164 baseEnd_7872164 := by
    simpa [prefixWord, tailWord_7872164, baseEnd_7872164] using wordTrace_append hprefix tailTrace_7872164
  have hstable : (prefixWord ++ tailWord_7872164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872164).length < 2 ^ (prefixWord ++ tailWord_7872164).sum := by decide
  have hdescent : baseEnd_7872164 < baseStart_7872164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872181 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7872181 : Nat := 118140960795 + 7872181 * 2 ^ 59
def prefixEnd_7872181 : Nat := 4983230072969 + 3 ^ 40 * 7872181 * 2
def baseEnd_7872181 : Nat := 4042212652191769789334005

theorem tailTrace_7872181 : CollatzResearch.WordTrace tailWord_7872181 prefixEnd_7872181 4042212652191769789334005 := by
  unfold tailWord_7872181
  simp only [CollatzResearch.WordTrace]
  refine ⟨287122029093440173321864397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191414686062293448881242931 287122029093440173321864397)
  ·
    refine ⟨107670760910040064995699149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287122029093440173321864397 107670760910040064995699149)
    ·
      refine ⟨40376535341265024373387181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107670760910040064995699149 40376535341265024373387181)
      ·
        refine ⟨15141200752974384140020193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40376535341265024373387181 15141200752974384140020193)
        ·
          refine ⟨11355900564730788105015145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15141200752974384140020193 11355900564730788105015145)
          ·
            refine ⟨8516925423548091078761359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11355900564730788105015145 8516925423548091078761359)
            ·
              refine ⟨12775388135322136618142039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516925423548091078761359 12775388135322136618142039)
              ·
                refine ⟨19163082202983204927213059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12775388135322136618142039 19163082202983204927213059)
                ·
                  refine ⟨28744623304474807390819589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19163082202983204927213059 28744623304474807390819589)
                  ·
                    refine ⟨5389616869589026385778673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28744623304474807390819589 5389616869589026385778673)
                    ·
                      refine ⟨4042212652191769789334005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389616869589026385778673 4042212652191769789334005)
                      ·
                        rfl

theorem cell23_7872181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7872181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872181 prefixEnd_7872181 := by exact prefixLift 7872181
  have htrace : WordTrace (prefixWord ++ tailWord_7872181) baseStart_7872181 baseEnd_7872181 := by
    simpa [prefixWord, tailWord_7872181, baseEnd_7872181] using wordTrace_append hprefix tailTrace_7872181
  have hstable : (prefixWord ++ tailWord_7872181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872181).length < 2 ^ (prefixWord ++ tailWord_7872181).sum := by decide
  have hdescent : baseEnd_7872181 < baseStart_7872181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872198 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7872198 : Nat := 118140960795 + 7872198 * 2 ^ 59
def prefixEnd_7872198 : Nat := 4983230072969 + 3 ^ 40 * 7872198 * 2
def baseEnd_7872198 : Nat := 4042221381362896222821427

theorem tailTrace_7872198 : CollatzResearch.WordTrace tailWord_7872198 prefixEnd_7872198 4042221381362896222821427 := by
  unfold tailWord_7872198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972582785449330788288539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191415099422919056816822165 8972582785449330788288539)
  ·
    refine ⟨13458874178173996182432809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8972582785449330788288539 13458874178173996182432809)
    ·
      refine ⟨10094155633630497136824607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13458874178173996182432809 10094155633630497136824607)
      ·
        refine ⟨15141233450445745705236911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094155633630497136824607 15141233450445745705236911)
        ·
          refine ⟨22711850175668618557855367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15141233450445745705236911 22711850175668618557855367)
          ·
            refine ⟨34067775263502927836783051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22711850175668618557855367 34067775263502927836783051)
            ·
              refine ⟨51101662895254391755174577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34067775263502927836783051 51101662895254391755174577)
              ·
                refine ⟨38326247171440793816380933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51101662895254391755174577 38326247171440793816380933)
                ·
                  refine ⟨7186171344645148840571425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38326247171440793816380933 7186171344645148840571425)
                  ·
                    refine ⟨5389628508483861630428569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7186171344645148840571425 5389628508483861630428569)
                    ·
                      refine ⟨4042221381362896222821427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389628508483861630428569 4042221381362896222821427)
                      ·
                        rfl

theorem cell23_7872198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7872198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872198 prefixEnd_7872198 := by exact prefixLift 7872198
  have htrace : WordTrace (prefixWord ++ tailWord_7872198) baseStart_7872198 baseEnd_7872198 := by
    simpa [prefixWord, tailWord_7872198, baseEnd_7872198] using wordTrace_append hprefix tailTrace_7872198
  have hstable : (prefixWord ++ tailWord_7872198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872198).length < 2 ^ (prefixWord ++ tailWord_7872198).sum := by decide
  have hdescent : baseEnd_7872198 < baseStart_7872198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872200 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_7872200 : Nat := 118140960795 + 7872200 * 2 ^ 59
def prefixEnd_7872200 : Nat := 4983230072969 + 3 ^ 40 * 7872200 * 2
def baseEnd_7872200 : Nat := 1347407469441401738332139

theorem tailTrace_7872200 : CollatzResearch.WordTrace tailWord_7872200 prefixEnd_7872200 1347407469441401738332139 := by
  unfold tailWord_7872200
  simp only [CollatzResearch.WordTrace]
  refine ⟨143561361040185669783403027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191415148053580893044537369 143561361040185669783403027)
  ·
    refine ⟨215342041560278504675104541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143561361040185669783403027 215342041560278504675104541)
    ·
      refine ⟨80753265585104439253164203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215342041560278504675104541 80753265585104439253164203)
      ·
        refine ⟨121129898377656658879746305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80753265585104439253164203 121129898377656658879746305)
        ·
          refine ⟨90847423783242494159809729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121129898377656658879746305 90847423783242494159809729)
          ·
            refine ⟨68135567837431870619857297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90847423783242494159809729 68135567837431870619857297)
            ·
              refine ⟨51101675878073902964892973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68135567837431870619857297 51101675878073902964892973)
              ·
                refine ⟨19163128454277713611834865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51101675878073902964892973 19163128454277713611834865)
                ·
                  refine ⟨14372346340708285208876149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19163128454277713611834865 14372346340708285208876149)
                  ·
                    refine ⟨1347407469441401738332139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14372346340708285208876149 1347407469441401738332139)
                    ·
                      rfl

theorem cell23_7872200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_7872200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872200 prefixEnd_7872200 := by exact prefixLift 7872200
  have htrace : WordTrace (prefixWord ++ tailWord_7872200) baseStart_7872200 baseEnd_7872200 := by
    simpa [prefixWord, tailWord_7872200, baseEnd_7872200] using wordTrace_append hprefix tailTrace_7872200
  have hstable : (prefixWord ++ tailWord_7872200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872200).length < 2 ^ (prefixWord ++ tailWord_7872200).sum := by decide
  have hdescent : baseEnd_7872200 < baseStart_7872200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872221 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 7]
def baseStart_7872221 : Nat := 118140960795 + 7872221 * 2 ^ 59
def prefixEnd_7872221 : Nat := 4983230072969 + 3 ^ 40 * 7872221 * 2
def baseEnd_7872221 : Nat := 449137021268661070314869

theorem tailTrace_7872221 : CollatzResearch.WordTrace tailWord_7872221 prefixEnd_7872221 449137021268661070314869 := by
  unfold tailWord_7872221
  simp only [CollatzResearch.WordTrace]
  refine ⟨287123488013295260153320517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191415658675530173435547011 287123488013295260153320517)
  ·
    refine ⟨53835654002492861278747597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287123488013295260153320517 53835654002492861278747597)
    ·
      refine ⟨20188370250934822979530349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53835654002492861278747597 20188370250934822979530349)
      ·
        refine ⟨7570638844100558617323881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20188370250934822979530349 7570638844100558617323881)
        ·
          refine ⟨5677979133075418962992911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7570638844100558617323881 5677979133075418962992911)
          ·
            refine ⟨8516968699613128444489367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677979133075418962992911 8516968699613128444489367)
            ·
              refine ⟨12775453049419692666734051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516968699613128444489367 12775453049419692666734051)
              ·
                refine ⟨19163179574129539000101077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12775453049419692666734051 19163179574129539000101077)
                ·
                  refine ⟨449137021268661070314869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19163179574129539000101077 449137021268661070314869)
                  ·
                    rfl

theorem cell23_7872221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_7872221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872221 prefixEnd_7872221 := by exact prefixLift 7872221
  have htrace : WordTrace (prefixWord ++ tailWord_7872221) baseStart_7872221 baseEnd_7872221 := by
    simpa [prefixWord, tailWord_7872221, baseEnd_7872221] using wordTrace_append hprefix tailTrace_7872221
  have hstable : (prefixWord ++ tailWord_7872221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872221).length < 2 ^ (prefixWord ++ tailWord_7872221).sum := by decide
  have hdescent : baseEnd_7872221 < baseStart_7872221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872227 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7872227 : Nat := 118140960795 + 7872227 * 2 ^ 59
def prefixEnd_7872227 : Nat := 4983230072969 + 3 ^ 40 * 7872227 * 2
def baseEnd_7872227 : Nat := 4042236272301876609358793

theorem tailTrace_7872227 : CollatzResearch.WordTrace tailWord_7872227 prefixEnd_7872227 4042236272301876609358793 := by
  unfold tailWord_7872227
  simp only [CollatzResearch.WordTrace]
  refine ⟨287123706851273523178038935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191415804567515682118692623 287123706851273523178038935)
  ·
    refine ⟨430685560276910284767058403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287123706851273523178038935 430685560276910284767058403)
    ·
      refine ⟨646028340415365427150587605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430685560276910284767058403 646028340415365427150587605)
      ·
        refine ⟨15141289228485127198841897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 646028340415365427150587605 15141289228485127198841897)
        ·
          refine ⟨11355966921363845399131423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15141289228485127198841897 11355966921363845399131423)
          ·
            refine ⟨17033950382045768098697135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355966921363845399131423 17033950382045768098697135)
            ·
              refine ⟨25550925573068652148045703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17033950382045768098697135 25550925573068652148045703)
              ·
                refine ⟨38326388359602978222068555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25550925573068652148045703 38326388359602978222068555)
                ·
                  refine ⟨57489582539404467333102833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38326388359602978222068555 57489582539404467333102833)
                  ·
                    refine ⟨43117186904553350499827125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57489582539404467333102833 43117186904553350499827125)
                    ·
                      refine ⟨4042236272301876609358793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43117186904553350499827125 4042236272301876609358793)
                      ·
                        rfl

theorem cell23_7872227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7872227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872227 prefixEnd_7872227 := by exact prefixLift 7872227
  have htrace : WordTrace (prefixWord ++ tailWord_7872227) baseStart_7872227 baseEnd_7872227 := by
    simpa [prefixWord, tailWord_7872227, baseEnd_7872227] using wordTrace_append hprefix tailTrace_7872227
  have hstable : (prefixWord ++ tailWord_7872227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872227).length < 2 ^ (prefixWord ++ tailWord_7872227).sum := by decide
  have hdescent : baseEnd_7872227 < baseStart_7872227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872240 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_7872240 : Nat := 118140960795 + 7872240 * 2 ^ 59
def prefixEnd_7872240 : Nat := 4983230072969 + 3 ^ 40 * 7872240 * 2
def baseEnd_7872240 : Nat := 4042242947550385058496233

theorem tailTrace_7872240 : CollatzResearch.WordTrace tailWord_7872240 prefixEnd_7872240 4042242947550385058496233 := by
  unfold tailWord_7872240
  simp only [CollatzResearch.WordTrace]
  refine ⟨143562090500113213199131087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191416120666817617598841449 143562090500113213199131087)
  ·
    refine ⟨215343135750169819798696631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143562090500113213199131087 215343135750169819798696631)
    ·
      refine ⟨323014703625254729698044947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215343135750169819798696631 323014703625254729698044947)
      ·
        refine ⟨484522055437882094547067421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323014703625254729698044947 484522055437882094547067421)
        ·
          refine ⟨181695770789205785455150283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484522055437882094547067421 181695770789205785455150283)
          ·
            refine ⟨272543656183808678182725425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181695770789205785455150283 272543656183808678182725425)
            ·
              refine ⟨204407742137856508637044069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272543656183808678182725425 204407742137856508637044069)
              ·
                refine ⟨38326451650848095369445763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204407742137856508637044069 38326451650848095369445763)
                ·
                  refine ⟨57489677476272143054168645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38326451650848095369445763 57489677476272143054168645)
                  ·
                    refine ⟨10779314526801026822656621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57489677476272143054168645 10779314526801026822656621)
                    ·
                      refine ⟨4042242947550385058496233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779314526801026822656621 4042242947550385058496233)
                      ·
                        rfl

theorem cell23_7872240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_7872240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872240 prefixEnd_7872240 := by exact prefixLift 7872240
  have htrace : WordTrace (prefixWord ++ tailWord_7872240) baseStart_7872240 baseEnd_7872240 := by
    simpa [prefixWord, tailWord_7872240, baseEnd_7872240] using wordTrace_append hprefix tailTrace_7872240
  have hstable : (prefixWord ++ tailWord_7872240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872240).length < 2 ^ (prefixWord ++ tailWord_7872240).sum := by decide
  have hdescent : baseEnd_7872240 < baseStart_7872240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872257 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_7872257 : Nat := 118140960795 + 7872257 * 2 ^ 59
def prefixEnd_7872257 : Nat := 4983230072969 + 3 ^ 40 * 7872257 * 2
def baseEnd_7872257 : Nat := 4042251676721511491983655

theorem tailTrace_7872257 : CollatzResearch.WordTrace tailWord_7872257 prefixEnd_7872257 4042251676721511491983655 := by
  unfold tailWord_7872257
  simp only [CollatzResearch.WordTrace]
  refine ⟨287124801041164838301631025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191416534027443225534420683 287124801041164838301631025)
  ·
    refine ⟨215343600780873628726223269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287124801041164838301631025 215343600780873628726223269)
    ·
      refine ⟨40376925146413805386166863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215343600780873628726223269 40376925146413805386166863)
      ·
        refine ⟨60565387719620708079250295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40376925146413805386166863 60565387719620708079250295)
        ·
          refine ⟨90848081579431062118875443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60565387719620708079250295 90848081579431062118875443)
          ·
            refine ⟨136272122369146593178313165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90848081579431062118875443 136272122369146593178313165)
            ·
              refine ⟨51102045888429972441867437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136272122369146593178313165 51102045888429972441867437)
              ·
                refine ⟨19163267208161239665700289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51102045888429972441867437 19163267208161239665700289)
                ·
                  refine ⟨14372450406120929749275217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19163267208161239665700289 14372450406120929749275217)
                  ·
                    refine ⟨10779337804590697311956413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14372450406120929749275217 10779337804590697311956413)
                    ·
                      refine ⟨4042251676721511491983655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779337804590697311956413 4042251676721511491983655)
                      ·
                        rfl

theorem cell23_7872257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_7872257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872257 prefixEnd_7872257 := by exact prefixLift 7872257
  have htrace : WordTrace (prefixWord ++ tailWord_7872257) baseStart_7872257 baseEnd_7872257 := by
    simpa [prefixWord, tailWord_7872257, baseEnd_7872257] using wordTrace_append hprefix tailTrace_7872257
  have hstable : (prefixWord ++ tailWord_7872257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872257).length < 2 ^ (prefixWord ++ tailWord_7872257).sum := by decide
  have hdescent : baseEnd_7872257 < baseStart_7872257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872264 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 1, 4]
def baseStart_7872264 : Nat := 118140960795 + 7872264 * 2 ^ 59
def prefixEnd_7872264 : Nat := 4983230072969 + 3 ^ 40 * 7872264 * 2
def baseEnd_7872264 : Nat := 1347418423695364321532041

theorem tailTrace_7872264 : CollatzResearch.WordTrace tailWord_7872264 prefixEnd_7872264 1347418423695364321532041 := by
  unfold tailWord_7872264
  simp only [CollatzResearch.WordTrace]
  refine ⟨143562528176069739248567923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191416704234759652331423897 143562528176069739248567923)
  ·
    refine ⟨215343792264104608872851885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143562528176069739248567923 215343792264104608872851885)
    ·
      refine ⟨80753922099039228327319457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215343792264104608872851885 80753922099039228327319457)
      ·
        refine ⟨60565441574279421245489593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80753922099039228327319457 60565441574279421245489593)
        ·
          refine ⟨45424081180709565934117195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60565441574279421245489593 45424081180709565934117195)
          ·
            refine ⟨68136121771064348901175793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45424081180709565934117195 68136121771064348901175793)
            ·
              refine ⟨51102091328298261675881845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68136121771064348901175793 51102091328298261675881845)
              ·
                refine ⟨4790821062027962032113923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51102091328298261675881845 4790821062027962032113923)
                ·
                  refine ⟨7186231593041943048170885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790821062027962032113923 7186231593041943048170885)
                  ·
                    refine ⟨1347418423695364321532041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186231593041943048170885 1347418423695364321532041)
                    ·
                      rfl

theorem cell23_7872264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_7872264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872264 prefixEnd_7872264 := by exact prefixLift 7872264
  have htrace : WordTrace (prefixWord ++ tailWord_7872264) baseStart_7872264 baseEnd_7872264 := by
    simpa [prefixWord, tailWord_7872264, baseEnd_7872264] using wordTrace_append hprefix tailTrace_7872264
  have hstable : (prefixWord ++ tailWord_7872264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872264).length < 2 ^ (prefixWord ++ tailWord_7872264).sum := by decide
  have hdescent : baseEnd_7872264 < baseStart_7872264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872277 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 6]
def baseStart_7872277 : Nat := 118140960795 + 7872277 * 2 ^ 59
def prefixEnd_7872277 : Nat := 4983230072969 + 3 ^ 40 * 7872277 * 2
def baseEnd_7872277 : Nat := 449140216259400157081507

theorem tailTrace_7872277 : CollatzResearch.WordTrace tailWord_7872277 prefixEnd_7872277 449140216259400157081507 := by
  unfold tailWord_7872277
  simp only [CollatzResearch.WordTrace]
  refine ⟨287125530501092381717359085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191417020334061587811572723 287125530501092381717359085)
  ·
    refine ⟨107672073937909643144009657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287125530501092381717359085 107672073937909643144009657)
    ·
      refine ⟨80754055453432232358007243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107672073937909643144009657 80754055453432232358007243)
      ·
        refine ⟨121131083180148348537010865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80754055453432232358007243 121131083180148348537010865)
        ·
          refine ⟨90848312385111261402758149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121131083180148348537010865 90848312385111261402758149)
          ·
            refine ⟨17034058572208361513017153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90848312385111261402758149 17034058572208361513017153)
            ·
              refine ⟨12775543929156271134762865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17034058572208361513017153 12775543929156271134762865)
              ·
                refine ⟨9581657946867203351072149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12775543929156271134762865 9581657946867203351072149)
                ·
                  refine ⟨449140216259400157081507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9581657946867203351072149 449140216259400157081507)
                  ·
                    rfl

theorem cell23_7872277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_7872277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872277 prefixEnd_7872277 := by exact prefixLift 7872277
  have htrace : WordTrace (prefixWord ++ tailWord_7872277) baseStart_7872277 baseEnd_7872277 := by
    simpa [prefixWord, tailWord_7872277, baseEnd_7872277] using wordTrace_append hprefix tailTrace_7872277
  have hstable : (prefixWord ++ tailWord_7872277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872277).length < 2 ^ (prefixWord ++ tailWord_7872277).sum := by decide
  have hdescent : baseEnd_7872277 < baseStart_7872277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872314 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2]
def baseStart_7872314 : Nat := 118140960795 + 7872314 * 2 ^ 59
def prefixEnd_7872314 : Nat := 4983230072969 + 3 ^ 40 * 7872314 * 2
def baseEnd_7872314 : Nat := 4042280945118817768970893

theorem tailTrace_7872314 : CollatzResearch.WordTrace tailWord_7872314 prefixEnd_7872314 4042280945118817768970893 := by
  unfold tailWord_7872314
  simp only [CollatzResearch.WordTrace]
  refine ⟨71781720000489584259113999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191417920001305558024303997 71781720000489584259113999)
  ·
    refine ⟨107672580000734376388670999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71781720000489584259113999 107672580000734376388670999)
    ·
      refine ⟨161508870001101564583006499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107672580000734376388670999 161508870001101564583006499)
      ·
        refine ⟨242263305001652346874509749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161508870001101564583006499 242263305001652346874509749)
        ·
          refine ⟨22712184843904907519485289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242263305001652346874509749 22712184843904907519485289)
          ·
            refine ⟨17034138632928680639613967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22712184843904907519485289 17034138632928680639613967)
            ·
              refine ⟨25551207949393020959420951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17034138632928680639613967 25551207949393020959420951)
              ·
                refine ⟨38326811924089531439131427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25551207949393020959420951 38326811924089531439131427)
                ·
                  refine ⟨57490217886134297158697141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38326811924089531439131427 57490217886134297158697141)
                  ·
                    refine ⟨5389707926825090358627857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57490217886134297158697141 5389707926825090358627857)
                    ·
                      refine ⟨4042280945118817768970893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389707926825090358627857 4042280945118817768970893)
                      ·
                        rfl

theorem cell23_7872314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_7872314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872314 prefixEnd_7872314 := by exact prefixLift 7872314
  have htrace : WordTrace (prefixWord ++ tailWord_7872314) baseStart_7872314 baseEnd_7872314 := by
    simpa [prefixWord, tailWord_7872314, baseEnd_7872314] using wordTrace_append hprefix tailTrace_7872314
  have hstable : (prefixWord ++ tailWord_7872314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872314).length < 2 ^ (prefixWord ++ tailWord_7872314).sum := by decide
  have hdescent : baseEnd_7872314 < baseStart_7872314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872354 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7872354 : Nat := 118140960795 + 7872354 * 2 ^ 59
def prefixEnd_7872354 : Nat := 4983230072969 + 3 ^ 40 * 7872354 * 2
def baseEnd_7872354 : Nat := 1347433828114999204156903

theorem tailTrace_7872354 : CollatzResearch.WordTrace tailWord_7872354 prefixEnd_7872354 1347433828114999204156903 := by
  unfold tailWord_7872354
  simp only [CollatzResearch.WordTrace]
  refine ⟨71782084730453355966978029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191418892614542282578608077 71782084730453355966978029)
  ·
    refine ⟨26918281773920008487616761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71782084730453355966978029 26918281773920008487616761)
    ·
      refine ⟨20188711330440006365712571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26918281773920008487616761 20188711330440006365712571)
      ·
        refine ⟨30283066995660009548568857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20188711330440006365712571 30283066995660009548568857)
        ·
          refine ⟨22712300246745007161426643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30283066995660009548568857 22712300246745007161426643)
          ·
            refine ⟨34068450370117510742139965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22712300246745007161426643 34068450370117510742139965)
            ·
              refine ⟨12775668888794066528302487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34068450370117510742139965 12775668888794066528302487)
              ·
                refine ⟨19163503333191099792453731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12775668888794066528302487 19163503333191099792453731)
                ·
                  refine ⟨28745254999786649688680597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19163503333191099792453731 28745254999786649688680597)
                  ·
                    refine ⟨1347433828114999204156903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28745254999786649688680597 1347433828114999204156903)
                    ·
                      rfl

theorem cell23_7872354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7872354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872354 prefixEnd_7872354 := by exact prefixLift 7872354
  have htrace : WordTrace (prefixWord ++ tailWord_7872354) baseStart_7872354 baseEnd_7872354 := by
    simpa [prefixWord, tailWord_7872354, baseEnd_7872354] using wordTrace_append hprefix tailTrace_7872354
  have hstable : (prefixWord ++ tailWord_7872354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872354).length < 2 ^ (prefixWord ++ tailWord_7872354).sum := by decide
  have hdescent : baseEnd_7872354 < baseStart_7872354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872364 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_7872364 : Nat := 118140960795 + 7872364 * 2 ^ 59
def prefixEnd_7872364 : Nat := 4983230072969 + 3 ^ 40 * 7872364 * 2
def baseEnd_7872364 : Nat := 4042306619151542573345663

theorem tailTrace_7872364 : CollatzResearch.WordTrace tailWord_7872364 prefixEnd_7872364 4042306619151542573345663 := by
  unfold tailWord_7872364
  simp only [CollatzResearch.WordTrace]
  refine ⟨143564351825888597787888073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191419135767851463717184097 143564351825888597787888073)
  ·
    refine ⟨107673263869416448340916055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143564351825888597787888073 107673263869416448340916055)
    ·
      refine ⟨161509895804124672511374083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107673263869416448340916055 161509895804124672511374083)
      ·
        refine ⟨242264843706187008767061125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161509895804124672511374083 242264843706187008767061125)
        ·
          refine ⟨45424658194910064143823961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242264843706187008767061125 45424658194910064143823961)
          ·
            refine ⟨34068493646182548107867971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45424658194910064143823961 34068493646182548107867971)
            ·
              refine ⟨51102740469273822161801957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34068493646182548107867971 51102740469273822161801957)
              ·
                refine ⟨9581763837988841655337867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51102740469273822161801957 9581763837988841655337867)
                ·
                  refine ⟨14372645756983262483006801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581763837988841655337867 14372645756983262483006801)
                  ·
                    refine ⟨10779484317737446862255101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14372645756983262483006801 10779484317737446862255101)
                    ·
                      refine ⟨4042306619151542573345663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779484317737446862255101 4042306619151542573345663)
                      ·
                        rfl

theorem cell23_7872364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_7872364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872364 prefixEnd_7872364 := by exact prefixLift 7872364
  have htrace : WordTrace (prefixWord ++ tailWord_7872364) baseStart_7872364 baseEnd_7872364 := by
    simpa [prefixWord, tailWord_7872364, baseEnd_7872364] using wordTrace_append hprefix tailTrace_7872364
  have hstable : (prefixWord ++ tailWord_7872364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872364).length < 2 ^ (prefixWord ++ tailWord_7872364).sum := by decide
  have hdescent : baseEnd_7872364 < baseStart_7872364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872377 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_7872377 : Nat := 118140960795 + 7872377 * 2 ^ 59
def prefixEnd_7872377 : Nat := 4983230072969 + 3 ^ 40 * 7872377 * 2
def baseEnd_7872377 : Nat := 4042313294400051022483103

theorem tailTrace_7872377 : CollatzResearch.WordTrace tailWord_7872377 prefixEnd_7872377 4042313294400051022483103 := by
  unfold tailWord_7872377
  simp only [CollatzResearch.WordTrace]
  refine ⟨287129177800730098795999385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191419451867153399197332923 287129177800730098795999385)
  ·
    refine ⟨215346883350547574096999539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287129177800730098795999385 215346883350547574096999539)
    ·
      refine ⟨323020325025821361145499309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215346883350547574096999539 323020325025821361145499309)
      ·
        refine ⟨121132621884683010429562241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323020325025821361145499309 121132621884683010429562241)
        ·
          refine ⟨90849466413512257822171681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121132621884683010429562241 90849466413512257822171681)
          ·
            refine ⟨68137099810134193366628761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90849466413512257822171681 68137099810134193366628761)
            ·
              refine ⟨51102824857600645024971571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68137099810134193366628761 51102824857600645024971571)
              ·
                refine ⟨76654237286400967537457357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51102824857600645024971571 76654237286400967537457357)
                ·
                  refine ⟨28745338982400362826546509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76654237286400967537457357 28745338982400362826546509)
                  ·
                    refine ⟨10779502118400136059954941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28745338982400362826546509 10779502118400136059954941)
                    ·
                      refine ⟨4042313294400051022483103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779502118400136059954941 4042313294400051022483103)
                      ·
                        rfl

theorem cell23_7872377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_7872377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872377 prefixEnd_7872377 := by exact prefixLift 7872377
  have htrace : WordTrace (prefixWord ++ tailWord_7872377) baseStart_7872377 baseEnd_7872377 := by
    simpa [prefixWord, tailWord_7872377, baseEnd_7872377] using wordTrace_append hprefix tailTrace_7872377
  have hstable : (prefixWord ++ tailWord_7872377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872377).length < 2 ^ (prefixWord ++ tailWord_7872377).sum := by decide
  have hdescent : baseEnd_7872377 < baseStart_7872377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872378 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2]
def baseStart_7872378 : Nat := 118140960795 + 7872378 * 2 ^ 59
def prefixEnd_7872378 : Nat := 4983230072969 + 3 ^ 40 * 7872378 * 2
def baseEnd_7872378 : Nat := 4042313807880705518570599

theorem tailTrace_7872378 : CollatzResearch.WordTrace tailWord_7872378 prefixEnd_7872378 4042313807880705518570599 := by
  unfold tailWord_7872378
  simp only [CollatzResearch.WordTrace]
  refine ⟨71782303568431618991696447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191419476182484317311190525 71782303568431618991696447)
  ·
    refine ⟨107673455352647428487544671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71782303568431618991696447 107673455352647428487544671)
    ·
      refine ⟨161510183028971142731317007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107673455352647428487544671 161510183028971142731317007)
      ·
        refine ⟨242265274543456714096975511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161510183028971142731317007 242265274543456714096975511)
        ·
          refine ⟨363397911815185071145463267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242265274543456714096975511 363397911815185071145463267)
          ·
            refine ⟨545096867722777606718194901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363397911815185071145463267 545096867722777606718194901)
            ·
              refine ⟨12775707837252600157457693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 545096867722777606718194901 12775707837252600157457693)
              ·
                refine ⟨4790890438969725059046635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12775707837252600157457693 4790890438969725059046635)
                ·
                  refine ⟨7186335658454587588569953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790890438969725059046635 7186335658454587588569953)
                  ·
                    refine ⟨5389751743840940691427465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7186335658454587588569953 5389751743840940691427465)
                    ·
                      refine ⟨4042313807880705518570599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389751743840940691427465 4042313807880705518570599)
                      ·
                        rfl

theorem cell23_7872378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_7872378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872378 prefixEnd_7872378 := by exact prefixLift 7872378
  have htrace : WordTrace (prefixWord ++ tailWord_7872378) baseStart_7872378 baseEnd_7872378 := by
    simpa [prefixWord, tailWord_7872378, baseEnd_7872378] using wordTrace_append hprefix tailTrace_7872378
  have hstable : (prefixWord ++ tailWord_7872378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872378).length < 2 ^ (prefixWord ++ tailWord_7872378).sum := by decide
  have hdescent : baseEnd_7872378 < baseStart_7872378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872380 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_7872380 : Nat := 118140960795 + 7872380 * 2 ^ 59
def prefixEnd_7872380 : Nat := 4983230072969 + 3 ^ 40 * 7872380 * 2
def baseEnd_7872380 : Nat := 1347438278280671503581863

theorem tailTrace_7872380 : CollatzResearch.WordTrace tailWord_7872380 prefixEnd_7872380 1347438278280671503581863 := by
  unfold tailWord_7872380
  simp only [CollatzResearch.WordTrace]
  refine ⟨143564643609859615154179297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191419524813146153538905729 143564643609859615154179297)
  ·
    refine ⟨107673482707394711365634473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143564643609859615154179297 107673482707394711365634473)
    ·
      refine ⟨80755112030546033524225855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107673482707394711365634473 80755112030546033524225855)
      ·
        refine ⟨121132668045819050286338783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80755112030546033524225855 121132668045819050286338783)
        ·
          refine ⟨181699002068728575429508175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121132668045819050286338783 181699002068728575429508175)
          ·
            refine ⟨272548503103092863144262263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181699002068728575429508175 272548503103092863144262263)
            ·
              refine ⟨408822754654639294716393395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272548503103092863144262263 408822754654639294716393395)
              ·
                refine ⟨613234131981958942074590093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408822754654639294716393395 613234131981958942074590093)
                ·
                  refine ⟨229962799493234603277971285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613234131981958942074590093 229962799493234603277971285)
                  ·
                    refine ⟨1347438278280671503581863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 229962799493234603277971285 1347438278280671503581863)
                    ·
                      rfl

theorem cell23_7872380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_7872380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872380 prefixEnd_7872380 := by exact prefixLift 7872380
  have htrace : WordTrace (prefixWord ++ tailWord_7872380) baseStart_7872380 baseEnd_7872380 := by
    simpa [prefixWord, tailWord_7872380, baseEnd_7872380] using wordTrace_append hprefix tailTrace_7872380
  have hstable : (prefixWord ++ tailWord_7872380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872380).length < 2 ^ (prefixWord ++ tailWord_7872380).sum := by decide
  have hdescent : baseEnd_7872380 < baseStart_7872380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872447 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_7872447 : Nat := 118140960795 + 7872447 * 2 ^ 59
def prefixEnd_7872447 : Nat := 4983230072969 + 3 ^ 40 * 7872447 * 2
def baseEnd_7872447 : Nat := 4042349238045865748607781

theorem tailTrace_7872447 : CollatzResearch.WordTrace tailWord_7872447 prefixEnd_7872447 4042349238045865748607781 := by
  unfold tailWord_7872447
  simp only [CollatzResearch.WordTrace]
  refine ⟨287131730910476500751047595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191421153940317667167365063 287131730910476500751047595)
  ·
    refine ⟨430697596365714751126571393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287131730910476500751047595 430697596365714751126571393)
    ·
      refine ⟨323023197274286063344928545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430697596365714751126571393 323023197274286063344928545)
      ·
        refine ⟨242267397955714547508696409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323023197274286063344928545 242267397955714547508696409)
        ·
          refine ⟨181700548466785910631522307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242267397955714547508696409 181700548466785910631522307)
          ·
            refine ⟨272550822700178865947283461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181700548466785910631522307 272550822700178865947283461)
            ·
              refine ⟨51103279256283537365115649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272550822700178865947283461 51103279256283537365115649)
              ·
                refine ⟨38327459442212653023836737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51103279256283537365115649 38327459442212653023836737)
                ·
                  refine ⟨28745594581659489767877553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38327459442212653023836737 28745594581659489767877553)
                  ·
                    refine ⟨21559195936244617325908165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28745594581659489767877553 21559195936244617325908165)
                    ·
                      refine ⟨4042349238045865748607781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21559195936244617325908165 4042349238045865748607781)
                      ·
                        rfl

theorem cell23_7872447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_7872447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872447 prefixEnd_7872447 := by exact prefixLift 7872447
  have htrace : WordTrace (prefixWord ++ tailWord_7872447) baseStart_7872447 baseEnd_7872447 := by
    simpa [prefixWord, tailWord_7872447, baseEnd_7872447] using wordTrace_append hprefix tailTrace_7872447
  have hstable : (prefixWord ++ tailWord_7872447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872447).length < 2 ^ (prefixWord ++ tailWord_7872447).sum := by decide
  have hdescent : baseEnd_7872447 < baseStart_7872447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872468 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_7872468 : Nat := 118140960795 + 7872468 * 2 ^ 59
def prefixEnd_7872468 : Nat := 4983230072969 + 3 ^ 40 * 7872468 * 2
def baseEnd_7872468 : Nat := 4042360021139610166445185

theorem tailTrace_7872468 : CollatzResearch.WordTrace tailWord_7872468 prefixEnd_7872468 4042360021139610166445185 := by
  unfold tailWord_7872468
  simp only [CollatzResearch.WordTrace]
  refine ⟨143566248421700210668781029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191421664562266947558374705 143566248421700210668781029)
  ·
    refine ⟨26918671579068789500396443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143566248421700210668781029 26918671579068789500396443)
    ·
      refine ⟨40378007368603184250594665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26918671579068789500396443 40378007368603184250594665)
      ·
        refine ⟨30283505526452388187945999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40378007368603184250594665 30283505526452388187945999)
        ·
          refine ⟨45425258289678582281918999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30283505526452388187945999 45425258289678582281918999)
          ·
            refine ⟨68137887434517873422878499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45425258289678582281918999 68137887434517873422878499)
            ·
              refine ⟨102206831151776810134317749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68137887434517873422878499 102206831151776810134317749)
              ·
                refine ⟨9581890420479075950092289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102206831151776810134317749 9581890420479075950092289)
                ·
                  refine ⟨7186417815359306962569217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9581890420479075950092289 7186417815359306962569217)
                  ·
                    refine ⟨5389813361519480221926913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7186417815359306962569217 5389813361519480221926913)
                    ·
                      refine ⟨4042360021139610166445185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389813361519480221926913 4042360021139610166445185)
                      ·
                        rfl

theorem cell23_7872468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_7872468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872468 prefixEnd_7872468 := by exact prefixLift 7872468
  have htrace : WordTrace (prefixWord ++ tailWord_7872468) baseStart_7872468 baseEnd_7872468 := by
    simpa [prefixWord, tailWord_7872468, baseEnd_7872468] using wordTrace_append hprefix tailTrace_7872468
  have hstable : (prefixWord ++ tailWord_7872468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872468).length < 2 ^ (prefixWord ++ tailWord_7872468).sum := by decide
  have hdescent : baseEnd_7872468 < baseStart_7872468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872474 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_7872474 : Nat := 118140960795 + 7872474 * 2 ^ 59
def prefixEnd_7872474 : Nat := 4983230072969 + 3 ^ 40 * 7872474 * 2
def baseEnd_7872474 : Nat := 449151455780393015885573

theorem tailTrace_7872474 : CollatzResearch.WordTrace tailWord_7872474 prefixEnd_7872474 449151455780393015885573 := by
  unfold tailWord_7872474
  simp only [CollatzResearch.WordTrace]
  refine ⟨71783178920344671090570119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191421810454252456241520317 71783178920344671090570119)
  ·
    refine ⟨107674768380517006635855179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71783178920344671090570119 107674768380517006635855179)
    ·
      refine ⟨161512152570775509953782769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107674768380517006635855179 161512152570775509953782769)
      ·
        refine ⟨121134114428081632465337077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161512152570775509953782769 121134114428081632465337077)
        ·
          refine ⟨11356323227632653043625351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121134114428081632465337077 11356323227632653043625351)
          ·
            refine ⟨17034484841448979565438027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356323227632653043625351 17034484841448979565438027)
            ·
              refine ⟨25551727262173469348157041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17034484841448979565438027 25551727262173469348157041)
              ·
                refine ⟨19163795446630102011117781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25551727262173469348157041 19163795446630102011117781)
                ·
                  refine ⟨449151455780393015885573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19163795446630102011117781 449151455780393015885573)
                  ·
                    rfl

theorem cell23_7872474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_7872474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872474 prefixEnd_7872474 := by exact prefixLift 7872474
  have htrace : WordTrace (prefixWord ++ tailWord_7872474) baseStart_7872474 baseEnd_7872474 := by
    simpa [prefixWord, tailWord_7872474, baseEnd_7872474] using wordTrace_append hprefix tailTrace_7872474
  have hstable : (prefixWord ++ tailWord_7872474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872474).length < 2 ^ (prefixWord ++ tailWord_7872474).sum := by decide
  have hdescent : baseEnd_7872474 < baseStart_7872474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872502 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_7872502 : Nat := 118140960795 + 7872502 * 2 ^ 59
def prefixEnd_7872502 : Nat := 4983230072969 + 3 ^ 40 * 7872502 * 2
def baseEnd_7872502 : Nat := 4042377479481863033420029

theorem tailTrace_7872502 : CollatzResearch.WordTrace tailWord_7872502 prefixEnd_7872502 4042377479481863033420029 := by
  unfold tailWord_7872502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17945858557829827821518735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191422491283518163429533173 17945858557829827821518735)
  ·
    refine ⟨26918787836744741732278103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17945858557829827821518735 26918787836744741732278103)
    ·
      refine ⟨40378181755117112598417155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26918787836744741732278103 40378181755117112598417155)
      ·
        refine ⟨60567272632675668897625733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40378181755117112598417155 60567272632675668897625733)
        ·
          refine ⟨11356363618626687918304825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60567272632675668897625733 11356363618626687918304825)
          ·
            refine ⟨8517272713970015938728619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11356363618626687918304825 8517272713970015938728619)
            ·
              refine ⟨12775909070955023908092929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517272713970015938728619 12775909070955023908092929)
              ·
                refine ⟨9581931803216267931069697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12775909070955023908092929 9581931803216267931069697)
                ·
                  refine ⟨7186448852412200948302273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9581931803216267931069697 7186448852412200948302273)
                  ·
                    refine ⟨5389836639309150711226705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7186448852412200948302273 5389836639309150711226705)
                    ·
                      refine ⟨4042377479481863033420029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389836639309150711226705 4042377479481863033420029)
                      ·
                        rfl

theorem cell23_7872502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_7872502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872502 prefixEnd_7872502 := by exact prefixLift 7872502
  have htrace : WordTrace (prefixWord ++ tailWord_7872502) baseStart_7872502 baseEnd_7872502 := by
    simpa [prefixWord, tailWord_7872502, baseEnd_7872502] using wordTrace_append hprefix tailTrace_7872502
  have hstable : (prefixWord ++ tailWord_7872502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872502).length < 2 ^ (prefixWord ++ tailWord_7872502).sum := by decide
  have hdescent : baseEnd_7872502 < baseStart_7872502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872537 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_7872537 : Nat := 118140960795 + 7872537 * 2 ^ 59
def prefixEnd_7872537 : Nat := 4983230072969 + 3 ^ 40 * 7872537 * 2
def baseEnd_7872537 : Nat := 4042395451304770396482367

theorem tailTrace_7872537 : CollatzResearch.WordTrace tailWord_7872537 prefixEnd_7872537 4042395451304770396482367 := by
  unfold tailWord_7872537
  simp only [CollatzResearch.WordTrace]
  refine ⟨287135013480150446121823865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191423342320100297414549243 287135013480150446121823865)
  ·
    refine ⟨215351260110112834591367899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287135013480150446121823865 215351260110112834591367899)
    ·
      refine ⟨323026890165169251887051849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215351260110112834591367899 323026890165169251887051849)
      ·
        refine ⟨242270167623876938915288887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323026890165169251887051849 242270167623876938915288887)
        ·
          refine ⟨363405251435815408372933331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242270167623876938915288887 363405251435815408372933331)
          ·
            refine ⟨545107877153723112559399997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363405251435815408372933331 545107877153723112559399997)
            ·
              refine ⟨204415453932646167209774999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545107877153723112559399997 204415453932646167209774999)
              ·
                refine ⟨306623180898969250814662499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204415453932646167209774999 306623180898969250814662499)
                ·
                  refine ⟨459934771348453876221993749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306623180898969250814662499 459934771348453876221993749)
                  ·
                    refine ⟨21559442406958775447905957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 459934771348453876221993749 21559442406958775447905957)
                    ·
                      refine ⟨4042395451304770396482367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21559442406958775447905957 4042395451304770396482367)
                      ·
                        rfl

theorem cell23_7872537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_7872537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872537 prefixEnd_7872537 := by exact prefixLift 7872537
  have htrace : WordTrace (prefixWord ++ tailWord_7872537) baseStart_7872537 baseEnd_7872537 := by
    simpa [prefixWord, tailWord_7872537, baseEnd_7872537] using wordTrace_append hprefix tailTrace_7872537
  have hstable : (prefixWord ++ tailWord_7872537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872537).length < 2 ^ (prefixWord ++ tailWord_7872537).sum := by decide
  have hdescent : baseEnd_7872537 < baseStart_7872537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872547 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 10]
def baseStart_7872547 : Nat := 118140960795 + 7872547 * 2 ^ 59
def prefixEnd_7872547 : Nat := 4983230072969 + 3 ^ 40 * 7872547 * 2
def baseEnd_7872547 : Nat := 449155620679035039706369

theorem tailTrace_7872547 : CollatzResearch.WordTrace tailWord_7872547 prefixEnd_7872547 449155620679035039706369 := by
  unfold tailWord_7872547
  simp only [CollatzResearch.WordTrace]
  refine ⟨287135378210114217829687895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191423585473409478553125263 287135378210114217829687895)
  ·
    refine ⟨430703067315171326744531843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287135378210114217829687895 430703067315171326744531843)
    ·
      refine ⟨646054600972756990116797765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430703067315171326744531843 646054600972756990116797765)
      ·
        refine ⟨121135237682391935646899581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 646054600972756990116797765 121135237682391935646899581)
        ·
          refine ⟨45425714130896975867587343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121135237682391935646899581 45425714130896975867587343)
          ·
            refine ⟨68138571196345463801381015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45425714130896975867587343 68138571196345463801381015)
            ·
              refine ⟨102207856794518195702071523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68138571196345463801381015 102207856794518195702071523)
              ·
                refine ⟨153311785191777293553107285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102207856794518195702071523 153311785191777293553107285)
                ·
                  refine ⟨449155620679035039706369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153311785191777293553107285 449155620679035039706369)
                  ·
                    rfl

theorem cell23_7872547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 10].length) (baseStart_7872547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872547 prefixEnd_7872547 := by exact prefixLift 7872547
  have htrace : WordTrace (prefixWord ++ tailWord_7872547) baseStart_7872547 baseEnd_7872547 := by
    simpa [prefixWord, tailWord_7872547, baseEnd_7872547] using wordTrace_append hprefix tailTrace_7872547
  have hstable : (prefixWord ++ tailWord_7872547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872547).length < 2 ^ (prefixWord ++ tailWord_7872547).sum := by decide
  have hdescent : baseEnd_7872547 < baseStart_7872547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872561 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_7872561 : Nat := 118140960795 + 7872561 * 2 ^ 59
def prefixEnd_7872561 : Nat := 4983230072969 + 3 ^ 40 * 7872561 * 2
def baseEnd_7872561 : Nat := 4042407774840478302582257

theorem tailTrace_7872561 : CollatzResearch.WordTrace tailWord_7872561 prefixEnd_7872561 4042407774840478302582257 := by
  unfold tailWord_7872561
  simp only [CollatzResearch.WordTrace]
  refine ⟨287135888832063498220697537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191423925888042332147131691 287135888832063498220697537)
  ·
    refine ⟨215351916624047623665523153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287135888832063498220697537 215351916624047623665523153)
    ·
      refine ⟨161513937468035717749142365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215351916624047623665523153 161513937468035717749142365)
      ·
        refine ⟨60567726550513394155928387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161513937468035717749142365 60567726550513394155928387)
        ·
          refine ⟨90851589825770091233892581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60567726550513394155928387 90851589825770091233892581)
          ·
            refine ⟨17034673092331892106354859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90851589825770091233892581 17034673092331892106354859)
            ·
              refine ⟨25552009638497838159532289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17034673092331892106354859 25552009638497838159532289)
              ·
                refine ⟨19164007228873378619649217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25552009638497838159532289 19164007228873378619649217)
                ·
                  refine ⟨14373005421655033964736913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19164007228873378619649217 14373005421655033964736913)
                  ·
                    refine ⟨10779754066241275473552685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14373005421655033964736913 10779754066241275473552685)
                    ·
                      refine ⟨4042407774840478302582257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779754066241275473552685 4042407774840478302582257)
                      ·
                        rfl

theorem cell23_7872561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_7872561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872561 prefixEnd_7872561 := by exact prefixLift 7872561
  have htrace : WordTrace (prefixWord ++ tailWord_7872561) baseStart_7872561 baseEnd_7872561 := by
    simpa [prefixWord, tailWord_7872561, baseEnd_7872561] using wordTrace_append hprefix tailTrace_7872561
  have hstable : (prefixWord ++ tailWord_7872561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872561).length < 2 ^ (prefixWord ++ tailWord_7872561).sum := by decide
  have hdescent : baseEnd_7872561 < baseStart_7872561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872567 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_7872567 : Nat := 118140960795 + 7872567 * 2 ^ 59
def prefixEnd_7872567 : Nat := 4983230072969 + 3 ^ 40 * 7872567 * 2
def baseEnd_7872567 : Nat := 4042410855724405279107229

theorem tailTrace_7872567 : CollatzResearch.WordTrace tailWord_7872567 prefixEnd_7872567 4042410855724405279107229 := by
  unfold tailWord_7872567
  simp only [CollatzResearch.WordTrace]
  refine ⟨287136107670041761245415955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191424071780027840830277303 287136107670041761245415955)
  ·
    refine ⟨430704161505062641868123933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287136107670041761245415955 430704161505062641868123933)
    ·
      refine ⟨161514060564398490700546475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430704161505062641868123933 161514060564398490700546475)
      ·
        refine ⟨242271090846597736050819713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161514060564398490700546475 242271090846597736050819713)
        ·
          refine ⟨181703318134948302038114785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242271090846597736050819713 181703318134948302038114785)
          ·
            refine ⟨136277488601211226528586089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181703318134948302038114785 136277488601211226528586089)
            ·
              refine ⟨102208116450908419896439567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136277488601211226528586089 102208116450908419896439567)
              ·
                refine ⟨153312174676362629844659351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102208116450908419896439567 153312174676362629844659351)
                ·
                  refine ⟨229968262014543944766989027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153312174676362629844659351 229968262014543944766989027)
                  ·
                    refine ⟨344952393021815917150483541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229968262014543944766989027 344952393021815917150483541)
                    ·
                      refine ⟨4042410855724405279107229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 344952393021815917150483541 4042410855724405279107229)
                      ·
                        rfl

theorem cell23_7872567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_7872567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872567 prefixEnd_7872567 := by exact prefixLift 7872567
  have htrace : WordTrace (prefixWord ++ tailWord_7872567) baseStart_7872567 baseEnd_7872567 := by
    simpa [prefixWord, tailWord_7872567, baseEnd_7872567] using wordTrace_append hprefix tailTrace_7872567
  have hstable : (prefixWord ++ tailWord_7872567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872567).length < 2 ^ (prefixWord ++ tailWord_7872567).sum := by decide
  have hdescent : baseEnd_7872567 < baseStart_7872567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872568 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 3, 4]
def baseStart_7872568 : Nat := 118140960795 + 7872568 * 2 ^ 59
def prefixEnd_7872568 : Nat := 4983230072969 + 3 ^ 40 * 7872568 * 2
def baseEnd_7872568 : Nat := 1347470456401686591731575

theorem tailTrace_7872568 : CollatzResearch.WordTrace tailWord_7872568 prefixEnd_7872568 1347470456401686591731575 := by
  unfold tailWord_7872568
  simp only [CollatzResearch.WordTrace]
  refine ⟨143568072071519069208101179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191424096095358758944134905 143568072071519069208101179)
  ·
    refine ⟨215352108107278603812151769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143568072071519069208101179 215352108107278603812151769)
    ·
      refine ⟨161514081080458952859113827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215352108107278603812151769 161514081080458952859113827)
      ·
        refine ⟨242271121620688429288670741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161514081080458952859113827 242271121620688429288670741)
        ·
          refine ⟨11356458825969770122906441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242271121620688429288670741 11356458825969770122906441)
          ·
            refine ⟨8517344119477327592179831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11356458825969770122906441 8517344119477327592179831)
            ·
              refine ⟨12776016179215991388269747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517344119477327592179831 12776016179215991388269747)
              ·
                refine ⟨19164024268823987082404621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12776016179215991388269747 19164024268823987082404621)
                ·
                  refine ⟨7186509100808995155901733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19164024268823987082404621 7186509100808995155901733)
                  ·
                    refine ⟨1347470456401686591731575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186509100808995155901733 1347470456401686591731575)
                    ·
                      rfl

theorem cell23_7872568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_7872568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872568 prefixEnd_7872568 := by exact prefixLift 7872568
  have htrace : WordTrace (prefixWord ++ tailWord_7872568) baseStart_7872568 baseEnd_7872568 := by
    simpa [prefixWord, tailWord_7872568, baseEnd_7872568] using wordTrace_append hprefix tailTrace_7872568
  have hstable : (prefixWord ++ tailWord_7872568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872568).length < 2 ^ (prefixWord ++ tailWord_7872568).sum := by decide
  have hdescent : baseEnd_7872568 < baseStart_7872568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872587 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_7872587 : Nat := 118140960795 + 7872587 * 2 ^ 59
def prefixEnd_7872587 : Nat := 4983230072969 + 3 ^ 40 * 7872587 * 2
def baseEnd_7872587 : Nat := 4042421125337495200857137

theorem tailTrace_7872587 : CollatzResearch.WordTrace tailWord_7872587 prefixEnd_7872587 4042421125337495200857137 := by
  unfold tailWord_7872587
  simp only [CollatzResearch.WordTrace]
  refine ⟨287136837129969304661144015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191424558086646203107429343 287136837129969304661144015)
  ·
    refine ⟨430705255694953956991716023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287136837129969304661144015 430705255694953956991716023)
    ·
      refine ⟨646057883542430935487574035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430705255694953956991716023 646057883542430935487574035)
      ·
        refine ⟨969086825313646403231361053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646057883542430935487574035 969086825313646403231361053)
        ·
          refine ⟨363407559492617401211760395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 969086825313646403231361053 363407559492617401211760395)
          ·
            refine ⟨545111339238926101817640593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363407559492617401211760395 545111339238926101817640593)
            ·
              refine ⟨408833504429194576363230445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545111339238926101817640593 408833504429194576363230445)
              ·
                refine ⟨153312564160947966136211417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408833504429194576363230445 153312564160947966136211417)
                ·
                  refine ⟨114984423120710974602158563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153312564160947966136211417 114984423120710974602158563)
                  ·
                    refine ⟨172476634681066461903237845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114984423120710974602158563 172476634681066461903237845)
                    ·
                      refine ⟨4042421125337495200857137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172476634681066461903237845 4042421125337495200857137)
                      ·
                        rfl

theorem cell23_7872587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_7872587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872587 prefixEnd_7872587 := by exact prefixLift 7872587
  have htrace : WordTrace (prefixWord ++ tailWord_7872587) baseStart_7872587 baseEnd_7872587 := by
    simpa [prefixWord, tailWord_7872587, baseEnd_7872587] using wordTrace_append hprefix tailTrace_7872587
  have hstable : (prefixWord ++ tailWord_7872587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872587).length < 2 ^ (prefixWord ++ tailWord_7872587).sum := by decide
  have hdescent : baseEnd_7872587 < baseStart_7872587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872668 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7872668 : Nat := 118140960795 + 7872668 * 2 ^ 59
def prefixEnd_7872668 : Nat := 4983230072969 + 3 ^ 40 * 7872668 * 2
def baseEnd_7872668 : Nat := 4042462717270509383944265

theorem tailTrace_7872668 : CollatzResearch.WordTrace tailWord_7872668 prefixEnd_7872668 4042462717270509383944265 := by
  unfold tailWord_7872668
  simp only [CollatzResearch.WordTrace]
  refine ⟨143569895721337927747421329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191426527628450570329895105 143569895721337927747421329)
  ·
    refine ⟨107677421791003445810565997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143569895721337927747421329 107677421791003445810565997)
    ·
      refine ⟨40379033171626292178962249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107677421791003445810565997 40379033171626292178962249)
      ·
        refine ⟨30284274878719719134221687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40379033171626292178962249 30284274878719719134221687)
        ·
          refine ⟨45426412318079578701332531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30284274878719719134221687 45426412318079578701332531)
          ·
            refine ⟨68139618477119368051998797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45426412318079578701332531 68139618477119368051998797)
            ·
              refine ⟨25552356928919763019499549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68139618477119368051998797 25552356928919763019499549)
              ·
                refine ⟨9582133848344911132312331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25552356928919763019499549 9582133848344911132312331)
                ·
                  refine ⟨14373200772517366698468497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582133848344911132312331 14373200772517366698468497)
                  ·
                    refine ⟨10779900579388025023851373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14373200772517366698468497 10779900579388025023851373)
                    ·
                      refine ⟨4042462717270509383944265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779900579388025023851373 4042462717270509383944265)
                      ·
                        rfl

theorem cell23_7872668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7872668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872668 prefixEnd_7872668 := by exact prefixLift 7872668
  have htrace : WordTrace (prefixWord ++ tailWord_7872668) baseStart_7872668 baseEnd_7872668 := by
    simpa [prefixWord, tailWord_7872668, baseEnd_7872668] using wordTrace_append hprefix tailTrace_7872668
  have hstable : (prefixWord ++ tailWord_7872668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872668).length < 2 ^ (prefixWord ++ tailWord_7872668).sum := by decide
  have hdescent : baseEnd_7872668 < baseStart_7872668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872698 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_7872698 : Nat := 118140960795 + 7872698 * 2 ^ 59
def prefixEnd_7872698 : Nat := 4983230072969 + 3 ^ 40 * 7872698 * 2
def baseEnd_7872698 : Nat := 4042478121690144266569127

theorem tailTrace_7872698 : CollatzResearch.WordTrace tailWord_7872698 prefixEnd_7872698 4042478121690144266569127 := by
  unfold tailWord_7872698
  simp only [CollatzResearch.WordTrace]
  refine ⟨71785221408141792654608687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191427257088378113745623165 71785221408141792654608687)
  ·
    refine ⟨107677832112212688981913031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71785221408141792654608687 107677832112212688981913031)
    ·
      refine ⟨161516748168319033472869547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107677832112212688981913031 161516748168319033472869547)
      ·
        refine ⟨242275122252478550209304321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161516748168319033472869547 242275122252478550209304321)
        ·
          refine ⟨181706341689358912656978241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242275122252478550209304321 181706341689358912656978241)
          ·
            refine ⟨136279756267019184492733681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181706341689358912656978241 136279756267019184492733681)
            ·
              refine ⟨102209817200264388369550261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136279756267019184492733681 102209817200264388369550261)
              ·
                refine ⟨9582170362524786409645337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102209817200264388369550261 9582170362524786409645337)
                ·
                  refine ⟨7186627771893589807234003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582170362524786409645337 7186627771893589807234003)
                  ·
                    refine ⟨10779941657840384710851005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7186627771893589807234003 10779941657840384710851005)
                    ·
                      refine ⟨4042478121690144266569127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10779941657840384710851005 4042478121690144266569127)
                      ·
                        rfl

theorem cell23_7872698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_7872698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872698 prefixEnd_7872698 := by exact prefixLift 7872698
  have htrace : WordTrace (prefixWord ++ tailWord_7872698) baseStart_7872698 baseEnd_7872698 := by
    simpa [prefixWord, tailWord_7872698, baseEnd_7872698] using wordTrace_append hprefix tailTrace_7872698
  have hstable : (prefixWord ++ tailWord_7872698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872698).length < 2 ^ (prefixWord ++ tailWord_7872698).sum := by decide
  have hdescent : baseEnd_7872698 < baseStart_7872698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872705 : List Nat := [1, 2, 6, 1, 2, 2, 2, 7]
def baseStart_7872705 : Nat := 118140960795 + 7872705 * 2 ^ 59
def prefixEnd_7872705 : Nat := 4983230072969 + 3 ^ 40 * 7872705 * 2
def baseEnd_7872705 : Nat := 149721545039063916265985

theorem tailTrace_7872705 : CollatzResearch.WordTrace tailWord_7872705 prefixEnd_7872705 149721545039063916265985 := by
  unfold tailWord_7872705
  simp only [CollatzResearch.WordTrace]
  refine ⟨287141140943541810813939569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191427427295694540542626379 287141140943541810813939569)
  ·
    refine ⟨215355855707656358110454677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287141140943541810813939569 215355855707656358110454677)
    ·
      refine ⟨10094805736296391786427563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215355855707656358110454677 10094805736296391786427563)
      ·
        refine ⟨15142208604444587679641345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094805736296391786427563 15142208604444587679641345)
        ·
          refine ⟨11356656453333440759731009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15142208604444587679641345 11356656453333440759731009)
          ·
            refine ⟨8517492340000080569798257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11356656453333440759731009 8517492340000080569798257)
            ·
              refine ⟨6388119255000060427348693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8517492340000080569798257 6388119255000060427348693)
              ·
                refine ⟨149721545039063916265985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6388119255000060427348693 149721545039063916265985)
                ·
                  rfl

theorem cell23_7872705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 7].length) (baseStart_7872705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872705 prefixEnd_7872705 := by exact prefixLift 7872705
  have htrace : WordTrace (prefixWord ++ tailWord_7872705) baseStart_7872705 baseEnd_7872705 := by
    simpa [prefixWord, tailWord_7872705, baseEnd_7872705] using wordTrace_append hprefix tailTrace_7872705
  have hstable : (prefixWord ++ tailWord_7872705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872705).length < 2 ^ (prefixWord ++ tailWord_7872705).sum := by decide
  have hdescent : baseEnd_7872705 < baseStart_7872705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872716 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7872716 : Nat := 118140960795 + 7872716 * 2 ^ 59
def prefixEnd_7872716 : Nat := 4983230072969 + 3 ^ 40 * 7872716 * 2
def baseEnd_7872716 : Nat := 4042487364341925196144045

theorem tailTrace_7872716 : CollatzResearch.WordTrace tailWord_7872716 prefixEnd_7872716 4042487364341925196144045 := by
  unfold tailWord_7872716
  simp only [CollatzResearch.WordTrace]
  refine ⟨143570771073250979846295001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191427694764334639795060001 143570771073250979846295001)
  ·
    refine ⟨107678078304938234884721251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143570771073250979846295001 107678078304938234884721251)
    ·
      refine ⟨161517117457407352327081877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107678078304938234884721251 161517117457407352327081877)
      ·
        refine ⟨7571114880815969640331963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161517117457407352327081877 7571114880815969640331963)
        ·
          refine ⟨11356672321223954460497945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7571114880815969640331963 11356672321223954460497945)
          ·
            refine ⟨8517504240917965845373459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11356672321223954460497945 8517504240917965845373459)
            ·
              refine ⟨12776256361376948768060189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517504240917965845373459 12776256361376948768060189)
              ·
                refine ⟨4791096135516355788022571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12776256361376948768060189 4791096135516355788022571)
                ·
                  refine ⟨7186644203274533682033857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791096135516355788022571 7186644203274533682033857)
                  ·
                    refine ⟨5389983152455900261525393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7186644203274533682033857 5389983152455900261525393)
                    ·
                      refine ⟨4042487364341925196144045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389983152455900261525393 4042487364341925196144045)
                      ·
                        rfl

theorem cell23_7872716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7872716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872716 prefixEnd_7872716 := by exact prefixLift 7872716
  have htrace : WordTrace (prefixWord ++ tailWord_7872716) baseStart_7872716 baseEnd_7872716 := by
    simpa [prefixWord, tailWord_7872716, baseEnd_7872716] using wordTrace_append hprefix tailTrace_7872716
  have hstable : (prefixWord ++ tailWord_7872716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872716).length < 2 ^ (prefixWord ++ tailWord_7872716).sum := by decide
  have hdescent : baseEnd_7872716 < baseStart_7872716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872749 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_7872749 : Nat := 118140960795 + 7872749 * 2 ^ 59
def prefixEnd_7872749 : Nat := 4983230072969 + 3 ^ 40 * 7872749 * 2
def baseEnd_7872749 : Nat := 4042504309203523567031393

theorem tailTrace_7872749 : CollatzResearch.WordTrace tailWord_7872749 prefixEnd_7872749 4042504309203523567031393 := by
  unfold tailWord_7872749
  simp only [CollatzResearch.WordTrace]
  refine ⟨287142745755382406328541301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191428497170254937552360867 287142745755382406328541301)
  ·
    refine ⟨26919632414567100593300747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287142745755382406328541301 26919632414567100593300747)
    ·
      refine ⟨40379448621850650889951121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26919632414567100593300747 40379448621850650889951121)
      ·
        refine ⟨30284586466387988167463341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40379448621850650889951121 30284586466387988167463341)
        ·
          refine ⟨11356719924895495562798753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30284586466387988167463341 11356719924895495562798753)
          ·
            refine ⟨8517539943671621672099065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11356719924895495562798753 8517539943671621672099065)
            ·
              refine ⟨6388154957753716254074299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8517539943671621672099065 6388154957753716254074299)
              ·
                refine ⟨9582232436630574381111449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388154957753716254074299 9582232436630574381111449)
                ·
                  refine ⟨7186674327472930785833587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582232436630574381111449 7186674327472930785833587)
                  ·
                    refine ⟨10780011491209396178750381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7186674327472930785833587 10780011491209396178750381)
                    ·
                      refine ⟨4042504309203523567031393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780011491209396178750381 4042504309203523567031393)
                      ·
                        rfl

theorem cell23_7872749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_7872749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872749 prefixEnd_7872749 := by exact prefixLift 7872749
  have htrace : WordTrace (prefixWord ++ tailWord_7872749) baseStart_7872749 baseEnd_7872749 := by
    simpa [prefixWord, tailWord_7872749, baseEnd_7872749] using wordTrace_append hprefix tailTrace_7872749
  have hstable : (prefixWord ++ tailWord_7872749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872749).length < 2 ^ (prefixWord ++ tailWord_7872749).sum := by decide
  have hdescent : baseEnd_7872749 < baseStart_7872749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872755 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 2, 2, 2]
def baseStart_7872755 : Nat := 118140960795 + 7872755 * 2 ^ 59
def prefixEnd_7872755 : Nat := 4983230072969 + 3 ^ 40 * 7872755 * 2
def baseEnd_7872755 : Nat := 4042507390087450543556365

theorem tailTrace_7872755 : CollatzResearch.WordTrace tailWord_7872755 prefixEnd_7872755 4042507390087450543556365 := by
  unfold tailWord_7872755
  simp only [CollatzResearch.WordTrace]
  refine ⟨287142964593360669353259719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191428643062240446235506479 287142964593360669353259719)
  ·
    refine ⟨430714446890041004029889579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287142964593360669353259719 430714446890041004029889579)
    ·
      refine ⟨646071670335061506044834369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430714446890041004029889579 646071670335061506044834369)
      ·
        refine ⟨484553752751296129533625777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646071670335061506044834369 484553752751296129533625777)
        ·
          refine ⟨363415314563472097150219333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484553752751296129533625777 363415314563472097150219333)
          ·
            refine ⟨68140371480651018215666125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363415314563472097150219333 68140371480651018215666125)
            ·
              refine ⟨25552639305244131830874797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68140371480651018215666125 25552639305244131830874797)
              ·
                refine ⟨9582239739466549436578049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25552639305244131830874797 9582239739466549436578049)
                ·
                  refine ⟨7186679804599912077433537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582239739466549436578049 7186679804599912077433537)
                  ·
                    refine ⟨5390009853449934058075153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7186679804599912077433537 5390009853449934058075153)
                    ·
                      refine ⟨4042507390087450543556365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390009853449934058075153 4042507390087450543556365)
                      ·
                        rfl

theorem cell23_7872755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 2, 2].length) (baseStart_7872755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872755 prefixEnd_7872755 := by exact prefixLift 7872755
  have htrace : WordTrace (prefixWord ++ tailWord_7872755) baseStart_7872755 baseEnd_7872755 := by
    simpa [prefixWord, tailWord_7872755, baseEnd_7872755] using wordTrace_append hprefix tailTrace_7872755
  have hstable : (prefixWord ++ tailWord_7872755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872755).length < 2 ^ (prefixWord ++ tailWord_7872755).sum := by decide
  have hdescent : baseEnd_7872755 < baseStart_7872755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872784 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_7872784 : Nat := 118140960795 + 7872784 * 2 ^ 59
def prefixEnd_7872784 : Nat := 4983230072969 + 3 ^ 40 * 7872784 * 2
def baseEnd_7872784 : Nat := 4042522281026430930093731

theorem tailTrace_7872784 : CollatzResearch.WordTrace tailWord_7872784 prefixEnd_7872784 4042522281026430930093731 := by
  unfold tailWord_7872784
  simp only [CollatzResearch.WordTrace]
  refine ⟨143572011155127803653032703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191429348206837071537376937 143572011155127803653032703)
  ·
    refine ⟨215358016732691705479549055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143572011155127803653032703 215358016732691705479549055)
    ·
      refine ⟨323037025099037558219323583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215358016732691705479549055 323037025099037558219323583)
      ·
        refine ⟨484555537648556337328985375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323037025099037558219323583 484555537648556337328985375)
        ·
          refine ⟨726833306472834505993478063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484555537648556337328985375 726833306472834505993478063)
          ·
            refine ⟨1090249959709251758990217095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726833306472834505993478063 1090249959709251758990217095)
            ·
              refine ⟨1635374939563877638485325643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090249959709251758990217095 1635374939563877638485325643)
              ·
                refine ⟨2453062409345816457727988465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635374939563877638485325643 2453062409345816457727988465)
                ·
                  refine ⟨1839796807009362343295991349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453062409345816457727988465 1839796807009362343295991349)
                  ·
                    refine ⟨172480950657127719683999189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1839796807009362343295991349 172480950657127719683999189)
                    ·
                      refine ⟨4042522281026430930093731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172480950657127719683999189 4042522281026430930093731)
                      ·
                        rfl

theorem cell23_7872784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_7872784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872784 prefixEnd_7872784 := by exact prefixLift 7872784
  have htrace : WordTrace (prefixWord ++ tailWord_7872784) baseStart_7872784 baseEnd_7872784 := by
    simpa [prefixWord, tailWord_7872784, baseEnd_7872784] using wordTrace_append hprefix tailTrace_7872784
  have hstable : (prefixWord ++ tailWord_7872784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872784).length < 2 ^ (prefixWord ++ tailWord_7872784).sum := by decide
  have hdescent : baseEnd_7872784 < baseStart_7872784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872801 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7872801 : Nat := 118140960795 + 7872801 * 2 ^ 59
def prefixEnd_7872801 : Nat := 4983230072969 + 3 ^ 40 * 7872801 * 2
def baseEnd_7872801 : Nat := 4042531010197557363581153

theorem tailTrace_7872801 : CollatzResearch.WordTrace tailWord_7872801 prefixEnd_7872801 4042531010197557363581153 := by
  unfold tailWord_7872801
  simp only [CollatzResearch.WordTrace]
  refine ⟨287144642351194019209434257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191429761567462679472956171 287144642351194019209434257)
  ·
    refine ⟨215358481763395514407075693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287144642351194019209434257 215358481763395514407075693)
    ·
      refine ⟨80759430661273317902653385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215358481763395514407075693 80759430661273317902653385)
      ·
        refine ⟨60569572995954988426990039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80759430661273317902653385 60569572995954988426990039)
        ·
          refine ⟨90854359493932482640485059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60569572995954988426990039 90854359493932482640485059)
          ·
            refine ⟨136281539240898723960727589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90854359493932482640485059 136281539240898723960727589)
            ·
              refine ⟨25552788607668510742636423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136281539240898723960727589 25552788607668510742636423)
              ·
                refine ⟨38329182911502766113954635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25552788607668510742636423 38329182911502766113954635)
                ·
                  refine ⟨57493774367254149170931953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38329182911502766113954635 57493774367254149170931953)
                  ·
                    refine ⟨43120330775440611878198965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57493774367254149170931953 43120330775440611878198965)
                    ·
                      refine ⟨4042531010197557363581153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43120330775440611878198965 4042531010197557363581153)
                      ·
                        rfl

theorem cell23_7872801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7872801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872801 prefixEnd_7872801 := by exact prefixLift 7872801
  have htrace : WordTrace (prefixWord ++ tailWord_7872801) baseStart_7872801 baseEnd_7872801 := by
    simpa [prefixWord, tailWord_7872801, baseEnd_7872801] using wordTrace_append hprefix tailTrace_7872801
  have hstable : (prefixWord ++ tailWord_7872801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872801).length < 2 ^ (prefixWord ++ tailWord_7872801).sum := by decide
  have hdescent : baseEnd_7872801 < baseStart_7872801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872825 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 2, 5]
def baseStart_7872825 : Nat := 118140960795 + 7872825 * 2 ^ 59
def prefixEnd_7872825 : Nat := 4983230072969 + 3 ^ 40 * 7872825 * 2
def baseEnd_7872825 : Nat := 1347514444577755089893681

theorem tailTrace_7872825 : CollatzResearch.WordTrace tailWord_7872825 prefixEnd_7872825 1347514444577755089893681 := by
  unfold tailWord_7872825
  simp only [CollatzResearch.WordTrace]
  refine ⟨287145517703107071308307929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191430345135404714205538619 287145517703107071308307929)
  ·
    refine ⟨215359138277330303481230947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287145517703107071308307929 215359138277330303481230947)
    ·
      refine ⟨323038707415995455221846421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215359138277330303481230947 323038707415995455221846421)
      ·
        refine ⟨15142439410124786963524051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323038707415995455221846421 15142439410124786963524051)
        ·
          refine ⟨22713659115187180445286077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142439410124786963524051 22713659115187180445286077)
          ·
            refine ⟨8517622168195192666982279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22713659115187180445286077 8517622168195192666982279)
            ·
              refine ⟨12776433252292789000473419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517622168195192666982279 12776433252292789000473419)
              ·
                refine ⟨19164649878439183500710129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12776433252292789000473419 19164649878439183500710129)
                ·
                  refine ⟨14373487408829387625532597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19164649878439183500710129 14373487408829387625532597)
                  ·
                    refine ⟨1347514444577755089893681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14373487408829387625532597 1347514444577755089893681)
                    ·
                      rfl

theorem cell23_7872825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_7872825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872825 prefixEnd_7872825 := by exact prefixLift 7872825
  have htrace : WordTrace (prefixWord ++ tailWord_7872825) baseStart_7872825 baseEnd_7872825 := by
    simpa [prefixWord, tailWord_7872825, baseEnd_7872825] using wordTrace_append hprefix tailTrace_7872825
  have hstable : (prefixWord ++ tailWord_7872825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872825).length < 2 ^ (prefixWord ++ tailWord_7872825).sum := by decide
  have hdescent : baseEnd_7872825 < baseStart_7872825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872828 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_7872828 : Nat := 118140960795 + 7872828 * 2 ^ 59
def prefixEnd_7872828 : Nat := 4983230072969 + 3 ^ 40 * 7872828 * 2
def baseEnd_7872828 : Nat := 4042544874175228757943529

theorem tailTrace_7872828 : CollatzResearch.WordTrace tailWord_7872828 prefixEnd_7872828 4042544874175228757943529 := by
  unfold tailWord_7872828
  simp only [CollatzResearch.WordTrace]
  refine ⟨143572813561048101410333569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191430418081397468547111425 143572813561048101410333569)
  ·
    refine ⟨107679610170786076057750177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143572813561048101410333569 107679610170786076057750177)
    ·
      refine ⟨80759707628089557043312633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107679610170786076057750177 80759707628089557043312633)
      ·
        refine ⟨60569780721067167782484475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80759707628089557043312633 60569780721067167782484475)
        ·
          refine ⟨90854671081600751673726713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60569780721067167782484475 90854671081600751673726713)
          ·
            refine ⟨68141003311200563755295035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90854671081600751673726713 68141003311200563755295035)
            ·
              refine ⟨102211504966800845632942553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68141003311200563755295035 102211504966800845632942553)
              ·
                refine ⟨76658628725100634224706915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102211504966800845632942553 76658628725100634224706915)
                ·
                  refine ⟨114987943087650951337060373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76658628725100634224706915 114987943087650951337060373)
                  ·
                    refine ⟨5390059832233638343924705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114987943087650951337060373 5390059832233638343924705)
                    ·
                      refine ⟨4042544874175228757943529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390059832233638343924705 4042544874175228757943529)
                      ·
                        rfl

theorem cell23_7872828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_7872828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872828 prefixEnd_7872828 := by exact prefixLift 7872828
  have htrace : WordTrace (prefixWord ++ tailWord_7872828) baseStart_7872828 baseEnd_7872828 := by
    simpa [prefixWord, tailWord_7872828, baseEnd_7872828] using wordTrace_append hprefix tailTrace_7872828
  have hstable : (prefixWord ++ tailWord_7872828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872828).length < 2 ^ (prefixWord ++ tailWord_7872828).sum := by decide
  have hdescent : baseEnd_7872828 < baseStart_7872828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872851 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 6]
def baseStart_7872851 : Nat := 118140960795 + 7872851 * 2 ^ 59
def prefixEnd_7872851 : Nat := 4983230072969 + 3 ^ 40 * 7872851 * 2
def baseEnd_7872851 : Nat := 449172964914475796439547

theorem tailTrace_7872851 : CollatzResearch.WordTrace tailWord_7872851 prefixEnd_7872851 449172964914475796439547 := by
  unfold tailWord_7872851
  simp only [CollatzResearch.WordTrace]
  refine ⟨287146466001012877748754407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191430977334008585165836271 287146466001012877748754407)
  ·
    refine ⟨430719699001519316623131611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287146466001012877748754407 430719699001519316623131611)
    ·
      refine ⟨646079548502278974934697417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430719699001519316623131611 646079548502278974934697417)
      ·
        refine ⟨484559661376709231201023063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646079548502278974934697417 484559661376709231201023063)
        ·
          refine ⟨726839492065063846801534595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484559661376709231201023063 726839492065063846801534595)
          ·
            refine ⟨1090259238097595770202301893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726839492065063846801534595 1090259238097595770202301893)
            ·
              refine ⟨204423607143299206912931605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1090259238097595770202301893 204423607143299206912931605)
              ·
                refine ⟨9582356584842150324043669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204423607143299206912931605 9582356584842150324043669)
                ·
                  refine ⟨449172964914475796439547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9582356584842150324043669 449172964914475796439547)
                  ·
                    rfl

theorem cell23_7872851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 6].length) (baseStart_7872851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872851 prefixEnd_7872851 := by exact prefixLift 7872851
  have htrace : WordTrace (prefixWord ++ tailWord_7872851) baseStart_7872851 baseEnd_7872851 := by
    simpa [prefixWord, tailWord_7872851, baseEnd_7872851] using wordTrace_append hprefix tailTrace_7872851
  have hstable : (prefixWord ++ tailWord_7872851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872851).length < 2 ^ (prefixWord ++ tailWord_7872851).sum := by decide
  have hdescent : baseEnd_7872851 < baseStart_7872851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872855 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 1, 4]
def baseStart_7872855 : Nat := 118140960795 + 7872855 * 2 ^ 59
def prefixEnd_7872855 : Nat := 4983230072969 + 3 ^ 40 * 7872855 * 2
def baseEnd_7872855 : Nat := 1347519579384300050768635

theorem tailTrace_7872855 : CollatzResearch.WordTrace tailWord_7872855 prefixEnd_7872855 1347519579384300050768635 := by
  unfold tailWord_7872855
  simp only [CollatzResearch.WordTrace]
  refine ⟨287146611892998386431900019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191431074595332257621266679 287146611892998386431900019)
  ·
    refine ⟨430719917839497579647850029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287146611892998386431900019 430719917839497579647850029)
    ·
      refine ⟨161519969189811592367943761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430719917839497579647850029 161519969189811592367943761)
      ·
        refine ⟨121139976892358694275957821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161519969189811592367943761 121139976892358694275957821)
        ·
          refine ⟨45427491334634510353484183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121139976892358694275957821 45427491334634510353484183)
          ·
            refine ⟨68141237001951765530226275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45427491334634510353484183 68141237001951765530226275)
            ·
              refine ⟨102211855502927648295339413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68141237001951765530226275 102211855502927648295339413)
              ·
                refine ⟨4791180726699733513844035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102211855502927648295339413 4791180726699733513844035)
                ·
                  refine ⟨7186771090049600270766053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791180726699733513844035 7186771090049600270766053)
                  ·
                    refine ⟨1347519579384300050768635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186771090049600270766053 1347519579384300050768635)
                    ·
                      rfl

theorem cell23_7872855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_7872855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872855 prefixEnd_7872855 := by exact prefixLift 7872855
  have htrace : WordTrace (prefixWord ++ tailWord_7872855) baseStart_7872855 baseEnd_7872855 := by
    simpa [prefixWord, tailWord_7872855, baseEnd_7872855] using wordTrace_append hprefix tailTrace_7872855
  have hstable : (prefixWord ++ tailWord_7872855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872855).length < 2 ^ (prefixWord ++ tailWord_7872855).sum := by decide
  have hdescent : baseEnd_7872855 < baseStart_7872855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872905 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 4, 3, 2]
def baseStart_7872905 : Nat := 118140960795 + 7872905 * 2 ^ 59
def prefixEnd_7872905 : Nat := 4983230072969 + 3 ^ 40 * 7872905 * 2
def baseEnd_7872905 : Nat := 4042584412185624956680675

theorem tailTrace_7872905 : CollatzResearch.WordTrace tailWord_7872905 prefixEnd_7872905 4042584412185624956680675 := by
  unfold tailWord_7872905
  simp only [CollatzResearch.WordTrace]
  refine ⟨287148435542817244971220169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191432290361878163314146779 287148435542817244971220169)
  ·
    refine ⟨215361326657112933728415127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287148435542817244971220169 215361326657112933728415127)
    ·
      refine ⟨323041989985669400592622691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215361326657112933728415127 323041989985669400592622691)
      ·
        refine ⟨484562984978504100888934037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323041989985669400592622691 484562984978504100888934037)
        ·
          refine ⟨22713889920867379729168783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 484562984978504100888934037 22713889920867379729168783)
          ·
            refine ⟨34070834881301069593753175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22713889920867379729168783 34070834881301069593753175)
            ·
              refine ⟨51106252321951604390629763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34070834881301069593753175 51106252321951604390629763)
              ·
                refine ⟨76659378482927406585944645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51106252321951604390629763 76659378482927406585944645)
                ·
                  refine ⟨14373633465548888734864621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76659378482927406585944645 14373633465548888734864621)
                  ·
                    refine ⟨5390112549580833275574233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14373633465548888734864621 5390112549580833275574233)
                    ·
                      refine ⟨4042584412185624956680675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390112549580833275574233 4042584412185624956680675)
                      ·
                        rfl

theorem cell23_7872905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 3, 2].length) (baseStart_7872905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872905 prefixEnd_7872905 := by exact prefixLift 7872905
  have htrace : WordTrace (prefixWord ++ tailWord_7872905) baseStart_7872905 baseEnd_7872905 := by
    simpa [prefixWord, tailWord_7872905, baseEnd_7872905] using wordTrace_append hprefix tailTrace_7872905
  have hstable : (prefixWord ++ tailWord_7872905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872905).length < 2 ^ (prefixWord ++ tailWord_7872905).sum := by decide
  have hdescent : baseEnd_7872905 < baseStart_7872905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872906 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_7872906 : Nat := 118140960795 + 7872906 * 2 ^ 59
def prefixEnd_7872906 : Nat := 4983230072969 + 3 ^ 40 * 7872906 * 2
def baseEnd_7872906 : Nat := 1347528308555426484256057

theorem tailTrace_7872906 : CollatzResearch.WordTrace tailWord_7872906 prefixEnd_7872906 1347528308555426484256057 := by
  unfold tailWord_7872906
  simp only [CollatzResearch.WordTrace]
  refine ⟨71787118003953405535501643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191432314677209081428004381 71787118003953405535501643)
  ·
    refine ⟨107680677005930108303252465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71787118003953405535501643 107680677005930108303252465)
    ·
      refine ⟨80760507754447581227439349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107680677005930108303252465 80760507754447581227439349)
      ·
        refine ⟨7571297601979460740072439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80760507754447581227439349 7571297601979460740072439)
        ·
          refine ⟨11356946402969191110108659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7571297601979460740072439 11356946402969191110108659)
          ·
            refine ⟨17035419604453786665162989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356946402969191110108659 17035419604453786665162989)
            ·
              refine ⟨6388282351670169999436121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17035419604453786665162989 6388282351670169999436121)
              ·
                refine ⟨4791211763752627499577091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6388282351670169999436121 4791211763752627499577091)
                ·
                  refine ⟨7186817645628941249365637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791211763752627499577091 7186817645628941249365637)
                  ·
                    refine ⟨1347528308555426484256057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186817645628941249365637 1347528308555426484256057)
                    ·
                      rfl

theorem cell23_7872906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_7872906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872906 prefixEnd_7872906 := by exact prefixLift 7872906
  have htrace : WordTrace (prefixWord ++ tailWord_7872906) baseStart_7872906 baseEnd_7872906 := by
    simpa [prefixWord, tailWord_7872906, baseEnd_7872906] using wordTrace_append hprefix tailTrace_7872906
  have hstable : (prefixWord ++ tailWord_7872906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872906).length < 2 ^ (prefixWord ++ tailWord_7872906).sum := by decide
  have hdescent : baseEnd_7872906 < baseStart_7872906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872935 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7872935 : Nat := 118140960795 + 7872935 * 2 ^ 59
def prefixEnd_7872935 : Nat := 4983230072969 + 3 ^ 40 * 7872935 * 2
def baseEnd_7872935 : Nat := 4042599816605259839305537

theorem tailTrace_7872935 : CollatzResearch.WordTrace tailWord_7872935 prefixEnd_7872935 4042599816605259839305537 := by
  unfold tailWord_7872935
  simp only [CollatzResearch.WordTrace]
  refine ⟨287149529732708560094812259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191433019821805706729874839 287149529732708560094812259)
  ·
    refine ⟨430724294599062840142218389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287149529732708560094812259 430724294599062840142218389)
    ·
      refine ⟨20190201309331070631666487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 430724294599062840142218389 20190201309331070631666487)
      ·
        refine ⟨30285301963996605947499731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20190201309331070631666487 30285301963996605947499731)
        ·
          refine ⟨45427952945994908921249597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30285301963996605947499731 45427952945994908921249597)
          ·
            refine ⟨17035482354748090845468599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45427952945994908921249597 17035482354748090845468599)
            ·
              refine ⟨25553223532122136268202899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17035482354748090845468599 25553223532122136268202899)
              ·
                refine ⟨38329835298183204402304349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25553223532122136268202899 38329835298183204402304349)
                ·
                  refine ⟨14373688236818701650864131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38329835298183204402304349 14373688236818701650864131)
                  ·
                    refine ⟨21560532355228052476296197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14373688236818701650864131 21560532355228052476296197)
                    ·
                      refine ⟨4042599816605259839305537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21560532355228052476296197 4042599816605259839305537)
                      ·
                        rfl

theorem cell23_7872935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7872935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872935 prefixEnd_7872935 := by exact prefixLift 7872935
  have htrace : WordTrace (prefixWord ++ tailWord_7872935) baseStart_7872935 baseEnd_7872935 := by
    simpa [prefixWord, tailWord_7872935, baseEnd_7872935] using wordTrace_append hprefix tailTrace_7872935
  have hstable : (prefixWord ++ tailWord_7872935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872935).length < 2 ^ (prefixWord ++ tailWord_7872935).sum := by decide
  have hdescent : baseEnd_7872935 < baseStart_7872935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872982 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_7872982 : Nat := 118140960795 + 7872982 * 2 ^ 59
def prefixEnd_7872982 : Nat := 4983230072969 + 3 ^ 40 * 7872982 * 2
def baseEnd_7872982 : Nat := 4042623950196021155417821

theorem tailTrace_7872982 : CollatzResearch.WordTrace tailWord_7872982 prefixEnd_7872982 4042623950196021155417821 := by
  unfold tailWord_7872982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946952747721142945110825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191434162642358858081182133 17946952747721142945110825)
  ·
    refine ⟨13460214560790857208833119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17946952747721142945110825 13460214560790857208833119)
    ·
      refine ⟨20190321841186285813249679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13460214560790857208833119 20190321841186285813249679)
      ·
        refine ⟨30285482761779428719874519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20190321841186285813249679 30285482761779428719874519)
        ·
          refine ⟨45428224142669143079811779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30285482761779428719874519 45428224142669143079811779)
          ·
            refine ⟨68142336214003714619717669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45428224142669143079811779 68142336214003714619717669)
            ·
              refine ⟨12776688040125696491197063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68142336214003714619717669 12776688040125696491197063)
              ·
                refine ⟨19165032060188544736795595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12776688040125696491197063 19165032060188544736795595)
                ·
                  refine ⟨28747548090282817105193393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19165032060188544736795595 28747548090282817105193393)
                  ·
                    refine ⟨21560661067712112828895045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28747548090282817105193393 21560661067712112828895045)
                    ·
                      refine ⟨4042623950196021155417821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21560661067712112828895045 4042623950196021155417821)
                      ·
                        rfl

theorem cell23_7872982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_7872982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872982 prefixEnd_7872982 := by exact prefixLift 7872982
  have htrace : WordTrace (prefixWord ++ tailWord_7872982) baseStart_7872982 baseEnd_7872982 := by
    simpa [prefixWord, tailWord_7872982, baseEnd_7872982] using wordTrace_append hprefix tailTrace_7872982
  have hstable : (prefixWord ++ tailWord_7872982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872982).length < 2 ^ (prefixWord ++ tailWord_7872982).sum := by decide
  have hdescent : baseEnd_7872982 < baseStart_7872982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7872985 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_7872985 : Nat := 118140960795 + 7872985 * 2 ^ 59
def prefixEnd_7872985 : Nat := 4983230072969 + 3 ^ 40 * 7872985 * 2
def baseEnd_7872985 : Nat := 4042625490637984643680307

theorem tailTrace_7872985 : CollatzResearch.WordTrace tailWord_7872985 prefixEnd_7872985 4042625490637984643680307 := by
  unfold tailWord_7872985
  simp only [CollatzResearch.WordTrace]
  refine ⟨287151353382527418634132409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191434235588351612422754939 287151353382527418634132409)
  ·
    refine ⟨215363515036895563975599307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287151353382527418634132409 215363515036895563975599307)
    ·
      refine ⟨323045272555343345963398961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215363515036895563975599307 323045272555343345963398961)
      ·
        refine ⟨242283954416507509472549221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323045272555343345963398961 242283954416507509472549221)
        ·
          refine ⟨45428241453095158026102979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242283954416507509472549221 45428241453095158026102979)
          ·
            refine ⟨68142362179642737039154469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45428241453095158026102979 68142362179642737039154469)
            ·
              refine ⟨12776692908683013194841463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68142362179642737039154469 12776692908683013194841463)
              ·
                refine ⟨19165039363024519792262195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12776692908683013194841463 19165039363024519792262195)
                ·
                  refine ⟨28747559044536779688393293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19165039363024519792262195 28747559044536779688393293)
                  ·
                    refine ⟨10780334641701292383147485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28747559044536779688393293 10780334641701292383147485)
                    ·
                      refine ⟨4042625490637984643680307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780334641701292383147485 4042625490637984643680307)
                      ·
                        rfl

theorem cell23_7872985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_7872985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7872985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7872985 prefixEnd_7872985 := by exact prefixLift 7872985
  have htrace : WordTrace (prefixWord ++ tailWord_7872985) baseStart_7872985 baseEnd_7872985 := by
    simpa [prefixWord, tailWord_7872985, baseEnd_7872985] using wordTrace_append hprefix tailTrace_7872985
  have hstable : (prefixWord ++ tailWord_7872985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7872985).length < 2 ^ (prefixWord ++ tailWord_7872985).sum := by decide
  have hdescent : baseEnd_7872985 < baseStart_7872985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7872985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873088 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_7873088 : Nat := 118140960795 + 7873088 * 2 ^ 59
def prefixEnd_7873088 : Nat := 4983230072969 + 3 ^ 40 * 7873088 * 2
def baseEnd_7873088 : Nat := 4042678379145397740692333

theorem tailTrace_7873088 : CollatzResearch.WordTrace tailWord_7873088 prefixEnd_7873088 4042678379145397740692333 := by
  unfold tailWord_7873088
  simp only [CollatzResearch.WordTrace]
  refine ⟨143577555050577133612565959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191436740067436178150087945 143577555050577133612565959)
  ·
    refine ⟨215366332575865700418848939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143577555050577133612565959 215366332575865700418848939)
    ·
      refine ⟨323049498863798550628273409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215366332575865700418848939 323049498863798550628273409)
      ·
        refine ⟨242287124147848912971205057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323049498863798550628273409 242287124147848912971205057)
        ·
          refine ⟨181715343110886684728403793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242287124147848912971205057 181715343110886684728403793)
          ·
            refine ⟨136286507333165013546302845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181715343110886684728403793 136286507333165013546302845)
            ·
              refine ⟨51107440249936880079863567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136286507333165013546302845 51107440249936880079863567)
              ·
                refine ⟨76661160374905320119795351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51107440249936880079863567 76661160374905320119795351)
                ·
                  refine ⟨114991740562357980179693027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76661160374905320119795351 114991740562357980179693027)
                  ·
                    refine ⟨172487610843536970269539541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114991740562357980179693027 172487610843536970269539541)
                    ·
                      refine ⟨4042678379145397740692333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172487610843536970269539541 4042678379145397740692333)
                      ·
                        rfl

theorem cell23_7873088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_7873088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873088 prefixEnd_7873088 := by exact prefixLift 7873088
  have htrace : WordTrace (prefixWord ++ tailWord_7873088) baseStart_7873088 baseEnd_7873088 := by
    simpa [prefixWord, tailWord_7873088, baseEnd_7873088] using wordTrace_append hprefix tailTrace_7873088
  have hstable : (prefixWord ++ tailWord_7873088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873088).length < 2 ^ (prefixWord ++ tailWord_7873088).sum := by decide
  have hdescent : baseEnd_7873088 < baseStart_7873088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873149 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_7873149 : Nat := 118140960795 + 7873149 * 2 ^ 59
def prefixEnd_7873149 : Nat := 4983230072969 + 3 ^ 40 * 7873149 * 2
def baseEnd_7873149 : Nat := 4042709701465322002029553

theorem tailTrace_7873149 : CollatzResearch.WordTrace tailWord_7873149 prefixEnd_7873149 4042709701465322002029553 := by
  unfold tailWord_7873149
  simp only [CollatzResearch.WordTrace]
  refine ⟨287157334953933274643102501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191438223302622183095401667 287157334953933274643102501)
  ·
    refine ⟨53842000303862488995581719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287157334953933274643102501 53842000303862488995581719)
    ·
      refine ⟨80763000455793733493372579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53842000303862488995581719 80763000455793733493372579)
      ·
        refine ⟨121144500683690600240058869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80763000455793733493372579 121144500683690600240058869)
        ·
          refine ⟨11357296939095993772505519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121144500683690600240058869 11357296939095993772505519)
          ·
            refine ⟨17035945408643990658758279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11357296939095993772505519 17035945408643990658758279)
            ·
              refine ⟨25553918112965985988137419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17035945408643990658758279 25553918112965985988137419)
              ·
                refine ⟨38330877169448978982206129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25553918112965985988137419 38330877169448978982206129)
                ·
                  refine ⟨28748157877086734236654597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38330877169448978982206129 28748157877086734236654597)
                  ·
                    refine ⟨5390279601953762669372737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28748157877086734236654597 5390279601953762669372737)
                    ·
                      refine ⟨4042709701465322002029553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390279601953762669372737 4042709701465322002029553)
                      ·
                        rfl

theorem cell23_7873149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_7873149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873149 prefixEnd_7873149 := by exact prefixLift 7873149
  have htrace : WordTrace (prefixWord ++ tailWord_7873149) baseStart_7873149 baseEnd_7873149 := by
    simpa [prefixWord, tailWord_7873149, baseEnd_7873149] using wordTrace_append hprefix tailTrace_7873149
  have hstable : (prefixWord ++ tailWord_7873149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873149).length < 2 ^ (prefixWord ++ tailWord_7873149).sum := by decide
  have hdescent : baseEnd_7873149 < baseStart_7873149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873155 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 6]
def baseStart_7873155 : Nat := 118140960795 + 7873155 * 2 ^ 59
def prefixEnd_7873155 : Nat := 4983230072969 + 3 ^ 40 * 7873155 * 2
def baseEnd_7873155 : Nat := 449190309149916553172725

theorem tailTrace_7873155 : CollatzResearch.WordTrace tailWord_7873155 prefixEnd_7873155 449190309149916553172725 := by
  unfold tailWord_7873155
  simp only [CollatzResearch.WordTrace]
  refine ⟨287157553791911537667820919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191438369194607691778547279 287157553791911537667820919)
  ·
    refine ⟨430736330687867306501731379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287157553791911537667820919 430736330687867306501731379)
    ·
      refine ⟨646104496031800959752597069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430736330687867306501731379 646104496031800959752597069)
      ·
        refine ⟨242289186011925359907223901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646104496031800959752597069 242289186011925359907223901)
        ·
          refine ⟨90858444754472009965208963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242289186011925359907223901 90858444754472009965208963)
          ·
            refine ⟨136287667131708014947813445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90858444754472009965208963 136287667131708014947813445)
            ·
              refine ⟨25553937587195252802715021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136287667131708014947813445 25553937587195252802715021)
              ·
                refine ⟨9582726595198219801018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25553937587195252802715021 9582726595198219801018133)
                ·
                  refine ⟨449190309149916553172725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9582726595198219801018133 449190309149916553172725)
                  ·
                    rfl

theorem cell23_7873155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 6].length) (baseStart_7873155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873155 prefixEnd_7873155 := by exact prefixLift 7873155
  have htrace : WordTrace (prefixWord ++ tailWord_7873155) baseStart_7873155 baseEnd_7873155 := by
    simpa [prefixWord, tailWord_7873155, baseEnd_7873155] using wordTrace_append hprefix tailTrace_7873155
  have hstable : (prefixWord ++ tailWord_7873155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873155).length < 2 ^ (prefixWord ++ tailWord_7873155).sum := by decide
  have hdescent : baseEnd_7873155 < baseStart_7873155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873199 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 3]
def baseStart_7873199 : Nat := 118140960795 + 7873199 * 2 ^ 59
def prefixEnd_7873199 : Nat := 4983230072969 + 3 ^ 40 * 7873199 * 2
def baseEnd_7873199 : Nat := 4042735375498046806404323

theorem tailTrace_7873199 : CollatzResearch.WordTrace tailWord_7873199 prefixEnd_7873199 4042735375498046806404323 := by
  unfold tailWord_7873199
  simp only [CollatzResearch.WordTrace]
  refine ⟨287159158603752133182422651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191439439069168088788281767 287159158603752133182422651)
  ·
    refine ⟨430738737905628199773633977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287159158603752133182422651 430738737905628199773633977)
    ·
      refine ⟨323054053429221149830225483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430738737905628199773633977 323054053429221149830225483)
      ·
        refine ⟨484581080143831724745338225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323054053429221149830225483 484581080143831724745338225)
        ·
          refine ⟨363435810107873793559003669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484581080143831724745338225 363435810107873793559003669)
          ·
            refine ⟨17036053598806584073078297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 363435810107873793559003669 17036053598806584073078297)
            ·
              refine ⟨12777040199104938054808723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17036053598806584073078297 12777040199104938054808723)
              ·
                refine ⟨19165560298657407082213085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12777040199104938054808723 19165560298657407082213085)
                ·
                  refine ⟨7187085111996527655829907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19165560298657407082213085 7187085111996527655829907)
                  ·
                    refine ⟨10780627667994791483744861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187085111996527655829907 10780627667994791483744861)
                    ·
                      refine ⟨4042735375498046806404323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780627667994791483744861 4042735375498046806404323)
                      ·
                        rfl

theorem cell23_7873199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_7873199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873199 prefixEnd_7873199 := by exact prefixLift 7873199
  have htrace : WordTrace (prefixWord ++ tailWord_7873199) baseStart_7873199 baseEnd_7873199 := by
    simpa [prefixWord, tailWord_7873199, baseEnd_7873199] using wordTrace_append hprefix tailTrace_7873199
  have hstable : (prefixWord ++ tailWord_7873199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873199).length < 2 ^ (prefixWord ++ tailWord_7873199).sum := by decide
  have hdescent : baseEnd_7873199 < baseStart_7873199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873225 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_7873225 : Nat := 118140960795 + 7873225 * 2 ^ 59
def prefixEnd_7873225 : Nat := 4983230072969 + 3 ^ 40 * 7873225 * 2
def baseEnd_7873225 : Nat := 4042748725995063704679203

theorem tailTrace_7873225 : CollatzResearch.WordTrace tailWord_7873225 prefixEnd_7873225 4042748725995063704679203 := by
  unfold tailWord_7873225
  simp only [CollatzResearch.WordTrace]
  refine ⟨287160106901657939622869129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191440071267771959748579419 287160106901657939622869129)
  ·
    refine ⟨215370080176243454717151847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287160106901657939622869129 215370080176243454717151847)
    ·
      refine ⟨323055120264365182075727771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215370080176243454717151847 323055120264365182075727771)
      ·
        refine ⟨484582680396547773113591657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323055120264365182075727771 484582680396547773113591657)
        ·
          refine ⟨363437010297410829835193743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484582680396547773113591657 363437010297410829835193743)
          ·
            refine ⟨545155515446116244752790615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363437010297410829835193743 545155515446116244752790615)
            ·
              refine ⟨817733273169174367129185923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545155515446116244752790615 817733273169174367129185923)
              ·
                refine ⟨1226599909753761550693778885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817733273169174367129185923 1226599909753761550693778885)
                ·
                  refine ⟨229987483078830290755083541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226599909753761550693778885 229987483078830290755083541)
                  ·
                    refine ⟨10780663269320169879144541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 229987483078830290755083541 10780663269320169879144541)
                    ·
                      refine ⟨4042748725995063704679203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780663269320169879144541 4042748725995063704679203)
                      ·
                        rfl

theorem cell23_7873225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_7873225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873225 prefixEnd_7873225 := by exact prefixLift 7873225
  have htrace : WordTrace (prefixWord ++ tailWord_7873225) baseStart_7873225 baseEnd_7873225 := by
    simpa [prefixWord, tailWord_7873225, baseEnd_7873225] using wordTrace_append hprefix tailTrace_7873225
  have hstable : (prefixWord ++ tailWord_7873225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873225).length < 2 ^ (prefixWord ++ tailWord_7873225).sum := by decide
  have hdescent : baseEnd_7873225 < baseStart_7873225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873242 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_7873242 : Nat := 118140960795 + 7873242 * 2 ^ 59
def prefixEnd_7873242 : Nat := 4983230072969 + 3 ^ 40 * 7873242 * 2
def baseEnd_7873242 : Nat := 4042757455166190138166625

theorem tailTrace_7873242 : CollatzResearch.WordTrace tailWord_7873242 prefixEnd_7873242 4042757455166190138166625 := by
  unfold tailWord_7873242
  simp only [CollatzResearch.WordTrace]
  refine ⟨71790181735649087881559495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191440484628397567684158653 71790181735649087881559495)
  ·
    refine ⟨107685272603473631822339243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71790181735649087881559495 107685272603473631822339243)
    ·
      refine ⟨161527908905210447733508865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107685272603473631822339243 161527908905210447733508865)
      ·
        refine ⟨121145931678907835800131649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161527908905210447733508865 121145931678907835800131649)
        ·
          refine ⟨90859448759180876850098737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121145931678907835800131649 90859448759180876850098737)
          ·
            refine ⟨68144586569385657637574053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90859448759180876850098737 68144586569385657637574053)
            ·
              refine ⟨12777109981759810807045135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68144586569385657637574053 12777109981759810807045135)
              ·
                refine ⟨19165664972639716210567703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12777109981759810807045135 19165664972639716210567703)
                ·
                  refine ⟨28748497458959574315851555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19165664972639716210567703 28748497458959574315851555)
                  ·
                    refine ⟨43122746188439361473777333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28748497458959574315851555 43122746188439361473777333)
                    ·
                      refine ⟨4042757455166190138166625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43122746188439361473777333 4042757455166190138166625)
                      ·
                        rfl

theorem cell23_7873242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_7873242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873242 prefixEnd_7873242 := by exact prefixLift 7873242
  have htrace : WordTrace (prefixWord ++ tailWord_7873242) baseStart_7873242 baseEnd_7873242 := by
    simpa [prefixWord, tailWord_7873242, baseEnd_7873242] using wordTrace_append hprefix tailTrace_7873242
  have hstable : (prefixWord ++ tailWord_7873242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873242).length < 2 ^ (prefixWord ++ tailWord_7873242).sum := by decide
  have hdescent : baseEnd_7873242 < baseStart_7873242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873262 : List Nat := [4, 1, 2, 1, 1, 4, 2, 8]
def baseStart_7873262 : Nat := 118140960795 + 7873262 * 2 ^ 59
def prefixEnd_7873262 : Nat := 4983230072969 + 3 ^ 40 * 7873262 * 2
def baseEnd_7873262 : Nat := 149732137954788150367279

theorem tailTrace_7873262 : CollatzResearch.WordTrace tailWord_7873262 prefixEnd_7873262 149732137954788150367279 := by
  unfold tailWord_7873262
  simp only [CollatzResearch.WordTrace]
  refine ⟨35895182050315486867745755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191440970935015929961310693 35895182050315486867745755)
  ·
    refine ⟨53842773075473230301618633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35895182050315486867745755 53842773075473230301618633)
    ·
      refine ⟨40382079806604922726213975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53842773075473230301618633 40382079806604922726213975)
      ·
        refine ⟨60573119709907384089320963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40382079806604922726213975 60573119709907384089320963)
        ·
          refine ⟨90859679564861076133981445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60573119709907384089320963 90859679564861076133981445)
          ·
            refine ⟨17036189918411451775121521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90859679564861076133981445 17036189918411451775121521)
            ·
              refine ⟨12777142438808588831341141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17036189918411451775121521 12777142438808588831341141)
              ·
                refine ⟨149732137954788150367279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12777142438808588831341141 149732137954788150367279)
                ·
                  rfl

theorem cell23_7873262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_7873262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873262 prefixEnd_7873262 := by exact prefixLift 7873262
  have htrace : WordTrace (prefixWord ++ tailWord_7873262) baseStart_7873262 baseEnd_7873262 := by
    simpa [prefixWord, tailWord_7873262, baseEnd_7873262] using wordTrace_append hprefix tailTrace_7873262
  have hstable : (prefixWord ++ tailWord_7873262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873262).length < 2 ^ (prefixWord ++ tailWord_7873262).sum := by decide
  have hdescent : baseEnd_7873262 < baseStart_7873262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873265 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_7873265 : Nat := 118140960795 + 7873265 * 2 ^ 59
def prefixEnd_7873265 : Nat := 4983230072969 + 3 ^ 40 * 7873265 * 2
def baseEnd_7873265 : Nat := 4042769265221243548179019

theorem tailTrace_7873265 : CollatzResearch.WordTrace tailWord_7873265 prefixEnd_7873265 4042769265221243548179019 := by
  unfold tailWord_7873265
  simp only [CollatzResearch.WordTrace]
  refine ⟨287161565821513026454325249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191441043881008684302883499 287161565821513026454325249)
  ·
    refine ⟨215371174366134769840743937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287161565821513026454325249 215371174366134769840743937)
    ·
      refine ⟨161528380774601077380557953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215371174366134769840743937 161528380774601077380557953)
      ·
        refine ⟨121146285580950808035418465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161528380774601077380557953 121146285580950808035418465)
        ·
          refine ⟨90859714185713106026563849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121146285580950808035418465 90859714185713106026563849)
          ·
            refine ⟨68144785639284829519922887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90859714185713106026563849 68144785639284829519922887)
            ·
              refine ⟨102217178458927244279884331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68144785639284829519922887 102217178458927244279884331)
              ·
                refine ⟨153325767688390866419826497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102217178458927244279884331 153325767688390866419826497)
                ·
                  refine ⟨114994325766293149814869873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153325767688390866419826497 114994325766293149814869873)
                  ·
                    refine ⟨86245744324719862361152405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114994325766293149814869873 86245744324719862361152405)
                    ·
                      refine ⟨4042769265221243548179019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86245744324719862361152405 4042769265221243548179019)
                      ·
                        rfl

theorem cell23_7873265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_7873265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873265 prefixEnd_7873265 := by exact prefixLift 7873265
  have htrace : WordTrace (prefixWord ++ tailWord_7873265) baseStart_7873265 baseEnd_7873265 := by
    simpa [prefixWord, tailWord_7873265, baseEnd_7873265] using wordTrace_append hprefix tailTrace_7873265
  have hstable : (prefixWord ++ tailWord_7873265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873265).length < 2 ^ (prefixWord ++ tailWord_7873265).sum := by decide
  have hdescent : baseEnd_7873265 < baseStart_7873265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873266 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_7873266 : Nat := 118140960795 + 7873266 * 2 ^ 59
def prefixEnd_7873266 : Nat := 4983230072969 + 3 ^ 40 * 7873266 * 2
def baseEnd_7873266 : Nat := 1347589926233966014755505

theorem tailTrace_7873266 : CollatzResearch.WordTrace tailWord_7873266 prefixEnd_7873266 1347589926233966014755505 := by
  unfold tailWord_7873266
  simp only [CollatzResearch.WordTrace]
  refine ⟨71790400573627350906277913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191441068196339602416741101 71790400573627350906277913)
  ·
    refine ⟨53842800430220513179708435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71790400573627350906277913 53842800430220513179708435)
    ·
      refine ⟨80764200645330769769562653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53842800430220513179708435 80764200645330769769562653)
      ·
        refine ⟨30286575241999038663585995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80764200645330769769562653 30286575241999038663585995)
        ·
          refine ⟨45429862862998557995378993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30286575241999038663585995 45429862862998557995378993)
          ·
            refine ⟨34072397147248918496534245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45429862862998557995378993 34072397147248918496534245)
            ·
              refine ⟨6388574465109172218100171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34072397147248918496534245 6388574465109172218100171)
              ·
                refine ⟨9582861697663758327150257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388574465109172218100171 9582861697663758327150257)
                ·
                  refine ⟨7187146273247818745362693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582861697663758327150257 7187146273247818745362693)
                  ·
                    refine ⟨1347589926233966014755505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7187146273247818745362693 1347589926233966014755505)
                    ·
                      rfl

theorem cell23_7873266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_7873266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873266 prefixEnd_7873266 := by exact prefixLift 7873266
  have htrace : WordTrace (prefixWord ++ tailWord_7873266) baseStart_7873266 baseEnd_7873266 := by
    simpa [prefixWord, tailWord_7873266, baseEnd_7873266] using wordTrace_append hprefix tailTrace_7873266
  have hstable : (prefixWord ++ tailWord_7873266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873266).length < 2 ^ (prefixWord ++ tailWord_7873266).sum := by decide
  have hdescent : baseEnd_7873266 < baseStart_7873266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873272 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_7873272 : Nat := 118140960795 + 7873272 * 2 ^ 59
def prefixEnd_7873272 : Nat := 4983230072969 + 3 ^ 40 * 7873272 * 2
def baseEnd_7873272 : Nat := 4042772859585825020791487

theorem tailTrace_7873272 : CollatzResearch.WordTrace tailWord_7873272 prefixEnd_7873272 4042772859585825020791487 := by
  unfold tailWord_7873272
  simp only [CollatzResearch.WordTrace]
  refine ⟨143580910566243833324915035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191441214088325111099886713 143580910566243833324915035)
  ·
    refine ⟨215371365849365749987372553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143580910566243833324915035 215371365849365749987372553)
    ·
      refine ⟨161528524387024312490529415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215371365849365749987372553 161528524387024312490529415)
      ·
        refine ⟨242292786580536468735794123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161528524387024312490529415 242292786580536468735794123)
        ·
          refine ⟨363439179870804703103691185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242292786580536468735794123 363439179870804703103691185)
          ·
            refine ⟨272579384903103527327768389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363439179870804703103691185 272579384903103527327768389)
            ·
              refine ⟨51108634669331911373956573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272579384903103527327768389 51108634669331911373956573)
              ·
                refine ⟨19165738000999466765233715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51108634669331911373956573 19165738000999466765233715)
                ·
                  refine ⟨28748607001499200147850573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19165738000999466765233715 28748607001499200147850573)
                  ·
                    refine ⟨10780727625562200055443965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28748607001499200147850573 10780727625562200055443965)
                    ·
                      refine ⟨4042772859585825020791487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780727625562200055443965 4042772859585825020791487)
                      ·
                        rfl

theorem cell23_7873272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_7873272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873272 prefixEnd_7873272 := by exact prefixLift 7873272
  have htrace : WordTrace (prefixWord ++ tailWord_7873272) baseStart_7873272 baseEnd_7873272 := by
    simpa [prefixWord, tailWord_7873272, baseEnd_7873272] using wordTrace_append hprefix tailTrace_7873272
  have hstable : (prefixWord ++ tailWord_7873272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873272).length < 2 ^ (prefixWord ++ tailWord_7873272).sum := by decide
  have hdescent : baseEnd_7873272 < baseStart_7873272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873276 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_7873276 : Nat := 118140960795 + 7873276 * 2 ^ 59
def prefixEnd_7873276 : Nat := 4983230072969 + 3 ^ 40 * 7873276 * 2
def baseEnd_7873276 : Nat := 4042774913508443005141469

theorem tailTrace_7873276 : CollatzResearch.WordTrace tailWord_7873276 prefixEnd_7873276 4042774913508443005141469 := by
  unfold tailWord_7873276
  simp only [CollatzResearch.WordTrace]
  refine ⟨143580983512236587666487841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191441311349648783555317121 143580983512236587666487841)
  ·
    refine ⟨107685737634177440749865881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143580983512236587666487841 107685737634177440749865881)
    ·
      refine ⟨80764303225633080562399411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107685737634177440749865881 80764303225633080562399411)
      ·
        refine ⟨121146454838449620843599117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80764303225633080562399411 121146454838449620843599117)
        ·
          refine ⟨45429920564418607816349669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121146454838449620843599117 45429920564418607816349669)
          ·
            refine ⟨8518110105828488965565563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45429920564418607816349669 8518110105828488965565563)
            ·
              refine ⟨12777165158742733448348345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518110105828488965565563 12777165158742733448348345)
              ·
                refine ⟨9582873869057050086261259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12777165158742733448348345 9582873869057050086261259)
                ·
                  refine ⟨14374310803585575129391889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582873869057050086261259 14374310803585575129391889)
                  ·
                    refine ⟨10780733102689181347043917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14374310803585575129391889 10780733102689181347043917)
                    ·
                      refine ⟨4042774913508443005141469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780733102689181347043917 4042774913508443005141469)
                      ·
                        rfl

theorem cell23_7873276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_7873276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873276 prefixEnd_7873276 := by exact prefixLift 7873276
  have htrace : WordTrace (prefixWord ++ tailWord_7873276) baseStart_7873276 baseEnd_7873276 := by
    simpa [prefixWord, tailWord_7873276, baseEnd_7873276] using wordTrace_append hprefix tailTrace_7873276
  have hstable : (prefixWord ++ tailWord_7873276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873276).length < 2 ^ (prefixWord ++ tailWord_7873276).sum := by decide
  have hdescent : baseEnd_7873276 < baseStart_7873276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873285 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_7873285 : Nat := 118140960795 + 7873285 * 2 ^ 59
def prefixEnd_7873285 : Nat := 4983230072969 + 3 ^ 40 * 7873285 * 2
def baseEnd_7873285 : Nat := 4042779534834333469928927

theorem tailTrace_7873285 : CollatzResearch.WordTrace tailWord_7873285 prefixEnd_7873285 4042779534834333469928927 := by
  unfold tailWord_7873285
  simp only [CollatzResearch.WordTrace]
  refine ⟨287162295281440569870053309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191441530187627046580035539 287162295281440569870053309)
  ·
    refine ⟨107685860730540213701269991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287162295281440569870053309 107685860730540213701269991)
    ·
      refine ⟨161528791095810320551904987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107685860730540213701269991 161528791095810320551904987)
      ·
        refine ⟨242293186643715480827857481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161528791095810320551904987 242293186643715480827857481)
        ·
          refine ⟨181719889982786610620893111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242293186643715480827857481 181719889982786610620893111)
          ·
            refine ⟨272579834974179915931339667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181719889982786610620893111 272579834974179915931339667)
            ·
              refine ⟨408869752461269873897009501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272579834974179915931339667 408869752461269873897009501)
              ·
                refine ⟨153326157172976202711378563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408869752461269873897009501 153326157172976202711378563)
                ·
                  refine ⟨229989235759464304067067845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153326157172976202711378563 229989235759464304067067845)
                  ·
                    refine ⟨43122981704899557012575221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229989235759464304067067845 43122981704899557012575221)
                    ·
                      refine ⟨4042779534834333469928927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43122981704899557012575221 4042779534834333469928927)
                      ·
                        rfl

theorem cell23_7873285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_7873285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873285 prefixEnd_7873285 := by exact prefixLift 7873285
  have htrace : WordTrace (prefixWord ++ tailWord_7873285) baseStart_7873285 baseEnd_7873285 := by
    simpa [prefixWord, tailWord_7873285, baseEnd_7873285] using wordTrace_append hprefix tailTrace_7873285
  have hstable : (prefixWord ++ tailWord_7873285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873285).length < 2 ^ (prefixWord ++ tailWord_7873285).sum := by decide
  have hdescent : baseEnd_7873285 < baseStart_7873285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873306 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_7873306 : Nat := 118140960795 + 7873306 * 2 ^ 59
def prefixEnd_7873306 : Nat := 4983230072969 + 3 ^ 40 * 7873306 * 2
def baseEnd_7873306 : Nat := 4042790317928077887766331

theorem tailTrace_7873306 : CollatzResearch.WordTrace tailWord_7873306 prefixEnd_7873306 4042790317928077887766331 := by
  unfold tailWord_7873306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71790765303591122614141943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191442040809576326971045181 71790765303591122614141943)
  ·
    refine ⟨107686147955386683921212915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71790765303591122614141943 107686147955386683921212915)
    ·
      refine ⟨161529221933080025881819373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107686147955386683921212915 161529221933080025881819373)
      ·
        refine ⟨60573458224905009705682265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161529221933080025881819373 60573458224905009705682265)
        ·
          refine ⟨45430093668678757279261699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60573458224905009705682265 45430093668678757279261699)
          ·
            refine ⟨68145140503018135918892549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45430093668678757279261699 68145140503018135918892549)
            ·
              refine ⟨12777213844315900484792353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68145140503018135918892549 12777213844315900484792353)
              ·
                refine ⟨9582910383236925363594265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12777213844315900484792353 9582910383236925363594265)
                ·
                  refine ⟨7187182787427694022695699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582910383236925363594265 7187182787427694022695699)
                  ·
                    refine ⟨10780774181141541034043549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187182787427694022695699 10780774181141541034043549)
                    ·
                      refine ⟨4042790317928077887766331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780774181141541034043549 4042790317928077887766331)
                      ·
                        rfl

theorem cell23_7873306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_7873306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873306 prefixEnd_7873306 := by exact prefixLift 7873306
  have htrace : WordTrace (prefixWord ++ tailWord_7873306) baseStart_7873306 baseEnd_7873306 := by
    simpa [prefixWord, tailWord_7873306, baseEnd_7873306] using wordTrace_append hprefix tailTrace_7873306
  have hstable : (prefixWord ++ tailWord_7873306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873306).length < 2 ^ (prefixWord ++ tailWord_7873306).sum := by decide
  have hdescent : baseEnd_7873306 < baseStart_7873306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873312 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7873312 : Nat := 118140960795 + 7873312 * 2 ^ 59
def prefixEnd_7873312 : Nat := 4983230072969 + 3 ^ 40 * 7873312 * 2
def baseEnd_7873312 : Nat := 4042793398812004864291303

theorem tailTrace_7873312 : CollatzResearch.WordTrace tailWord_7873312 prefixEnd_7873312 4042793398812004864291303 := by
  unfold tailWord_7873312
  simp only [CollatzResearch.WordTrace]
  refine ⟨143581640026171376740643095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191442186701561835654190793 143581640026171376740643095)
  ·
    refine ⟨215372460039257065110964643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143581640026171376740643095 215372460039257065110964643)
    ·
      refine ⟨323058690058885597666446965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215372460039257065110964643 323058690058885597666446965)
      ·
        refine ⟨30286752193020524781229403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323058690058885597666446965 30286752193020524781229403)
        ·
          refine ⟨45430128289530787171844105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30286752193020524781229403 45430128289530787171844105)
          ·
            refine ⟨34072596217148090378883079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45430128289530787171844105 34072596217148090378883079)
            ·
              refine ⟨51108894325722135568324619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34072596217148090378883079 51108894325722135568324619)
              ·
                refine ⟨76663341488583203352486929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51108894325722135568324619 76663341488583203352486929)
                ·
                  refine ⟨57497506116437402514365197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76663341488583203352486929 57497506116437402514365197)
                  ·
                    refine ⟨21561564793664025942886949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57497506116437402514365197 21561564793664025942886949)
                    ·
                      refine ⟨4042793398812004864291303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21561564793664025942886949 4042793398812004864291303)
                      ·
                        rfl

theorem cell23_7873312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7873312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873312 prefixEnd_7873312 := by exact prefixLift 7873312
  have htrace : WordTrace (prefixWord ++ tailWord_7873312) baseStart_7873312 baseEnd_7873312 := by
    simpa [prefixWord, tailWord_7873312, baseEnd_7873312] using wordTrace_append hprefix tailTrace_7873312
  have hstable : (prefixWord ++ tailWord_7873312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873312).length < 2 ^ (prefixWord ++ tailWord_7873312).sum := by decide
  have hdescent : baseEnd_7873312 < baseStart_7873312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873357 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7873357 : Nat := 118140960795 + 7873357 * 2 ^ 59
def prefixEnd_7873357 : Nat := 4983230072969 + 3 ^ 40 * 7873357 * 2
def baseEnd_7873357 : Nat := 4042816505441457188228597

theorem tailTrace_7873357 : CollatzResearch.WordTrace tailWord_7873357 prefixEnd_7873357 4042816505441457188228597 := by
  unfold tailWord_7873357
  simp only [CollatzResearch.WordTrace]
  refine ⟨287164921337179726166674325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191443280891453150777782883 287164921337179726166674325)
  ·
    refine ⟨13460855687680299664062859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287164921337179726166674325 13460855687680299664062859)
    ·
      refine ⟨20191283531520449496094289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13460855687680299664062859 20191283531520449496094289)
      ·
        refine ⟨15143462648640337122070717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20191283531520449496094289 15143462648640337122070717)
        ·
          refine ⟨5678798493240126420776519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15143462648640337122070717 5678798493240126420776519)
          ·
            refine ⟨8518197739860189631164779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678798493240126420776519 8518197739860189631164779)
            ·
              refine ⟨12777296609790284446747169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518197739860189631164779 12777296609790284446747169)
              ·
                refine ⟨9582972457342713335060377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12777296609790284446747169 9582972457342713335060377)
                ·
                  refine ⟨7187229343007035001295283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582972457342713335060377 7187229343007035001295283)
                  ·
                    refine ⟨10780844014510552501942925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187229343007035001295283 10780844014510552501942925)
                    ·
                      refine ⟨4042816505441457188228597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780844014510552501942925 4042816505441457188228597)
                      ·
                        rfl

theorem cell23_7873357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7873357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873357 prefixEnd_7873357 := by exact prefixLift 7873357
  have htrace : WordTrace (prefixWord ++ tailWord_7873357) baseStart_7873357 baseEnd_7873357 := by
    simpa [prefixWord, tailWord_7873357, baseEnd_7873357] using wordTrace_append hprefix tailTrace_7873357
  have hstable : (prefixWord ++ tailWord_7873357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873357).length < 2 ^ (prefixWord ++ tailWord_7873357).sum := by decide
  have hdescent : baseEnd_7873357 < baseStart_7873357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873369 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 5]
def baseStart_7873369 : Nat := 118140960795 + 7873369 * 2 ^ 59
def prefixEnd_7873369 : Nat := 4983230072969 + 3 ^ 40 * 7873369 * 2
def baseEnd_7873369 : Nat := 449202518578812349030949

theorem tailTrace_7873369 : CollatzResearch.WordTrace tailWord_7873369 prefixEnd_7873369 449202518578812349030949 := by
  unfold tailWord_7873369
  simp only [CollatzResearch.WordTrace]
  refine ⟨287165359013136252216111161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191443572675424168144074107 287165359013136252216111161)
  ·
    refine ⟨215374019259852189162083371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287165359013136252216111161 215374019259852189162083371)
    ·
      refine ⟨323061028889778283743125057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215374019259852189162083371 323061028889778283743125057)
      ·
        refine ⟨242295771667333712807343793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323061028889778283743125057 242295771667333712807343793)
        ·
          refine ⟨181721828750500284605507845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242295771667333712807343793 181721828750500284605507845)
          ·
            refine ⟨34072842890718803363532721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181721828750500284605507845 34072842890718803363532721)
            ·
              refine ⟨25554632168039102522649541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34072842890718803363532721 25554632168039102522649541)
              ·
                refine ⟨4791493531507331722996789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25554632168039102522649541 4791493531507331722996789)
                ·
                  refine ⟨449202518578812349030949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791493531507331722996789 449202518578812349030949)
                  ·
                    rfl

theorem cell23_7873369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 5].length) (baseStart_7873369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873369 prefixEnd_7873369 := by exact prefixLift 7873369
  have htrace : WordTrace (prefixWord ++ tailWord_7873369) baseStart_7873369 baseEnd_7873369 := by
    simpa [prefixWord, tailWord_7873369, baseEnd_7873369] using wordTrace_append hprefix tailTrace_7873369
  have hstable : (prefixWord ++ tailWord_7873369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873369).length < 2 ^ (prefixWord ++ tailWord_7873369).sum := by decide
  have hdescent : baseEnd_7873369 < baseStart_7873369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873379 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 3]
def baseStart_7873379 : Nat := 118140960795 + 7873379 * 2 ^ 59
def prefixEnd_7873379 : Nat := 4983230072969 + 3 ^ 40 * 7873379 * 2
def baseEnd_7873379 : Nat := 4042827802015856102153495

theorem tailTrace_7873379 : CollatzResearch.WordTrace tailWord_7873379 prefixEnd_7873379 4042827802015856102153495 := by
  unfold tailWord_7873379
  simp only [CollatzResearch.WordTrace]
  refine ⟨287165723743100023923975191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191443815828733349282650127 287165723743100023923975191)
  ·
    refine ⟨430748585614650035885962787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287165723743100023923975191 430748585614650035885962787)
    ·
      refine ⟨646122878421975053828944181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430748585614650035885962787 646122878421975053828944181)
      ·
        refine ⟨60574019852060161296463517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 646122878421975053828944181 60574019852060161296463517)
        ·
          refine ⟨22715257444522560486173819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60574019852060161296463517 22715257444522560486173819)
          ·
            refine ⟨34072886166783840729260729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22715257444522560486173819 34072886166783840729260729)
            ·
              refine ⟨25554664625087880546945547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34072886166783840729260729 25554664625087880546945547)
              ·
                refine ⟨38331996937631820820418321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25554664625087880546945547 38331996937631820820418321)
                ·
                  refine ⟨28748997703223865615313741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38331996937631820820418321 28748997703223865615313741)
                  ·
                    refine ⟨10780874138708949605742653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28748997703223865615313741 10780874138708949605742653)
                    ·
                      refine ⟨4042827802015856102153495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10780874138708949605742653 4042827802015856102153495)
                      ·
                        rfl

theorem cell23_7873379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_7873379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873379 prefixEnd_7873379 := by exact prefixLift 7873379
  have htrace : WordTrace (prefixWord ++ tailWord_7873379) baseStart_7873379 baseEnd_7873379 := by
    simpa [prefixWord, tailWord_7873379, baseEnd_7873379] using wordTrace_append hprefix tailTrace_7873379
  have hstable : (prefixWord ++ tailWord_7873379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873379).length < 2 ^ (prefixWord ++ tailWord_7873379).sum := by decide
  have hdescent : baseEnd_7873379 < baseStart_7873379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873380 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_7873380 : Nat := 118140960795 + 7873380 * 2 ^ 59
def prefixEnd_7873380 : Nat := 4983230072969 + 3 ^ 40 * 7873380 * 2
def baseEnd_7873380 : Nat := 4042828315496510598240991

theorem tailTrace_7873380 : CollatzResearch.WordTrace tailWord_7873380 prefixEnd_7873380 4042828315496510598240991 := by
  unfold tailWord_7873380
  simp only [CollatzResearch.WordTrace]
  refine ⟨143582880108048200547380797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191443840144064267396507729 143582880108048200547380797)
  ·
    refine ⟨53843580040518075205267799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143582880108048200547380797 53843580040518075205267799)
    ·
      refine ⟨80765370060777112807901699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53843580040518075205267799 80765370060777112807901699)
      ·
        refine ⟨121148055091165669211852549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80765370060777112807901699 121148055091165669211852549)
        ·
          refine ⟨22715260329593562977222353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121148055091165669211852549 22715260329593562977222353)
          ·
            refine ⟨17036445247195172232916765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22715260329593562977222353 17036445247195172232916765)
            ·
              refine ⟨6388666967698189587343787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17036445247195172232916765 6388666967698189587343787)
              ·
                refine ⟨9583000451547284381015681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388666967698189587343787 9583000451547284381015681)
                ·
                  refine ⟨7187250338660463285761761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583000451547284381015681 7187250338660463285761761)
                  ·
                    refine ⟨5390437753995347464321321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7187250338660463285761761 5390437753995347464321321)
                    ·
                      refine ⟨4042828315496510598240991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390437753995347464321321 4042828315496510598240991)
                      ·
                        rfl

theorem cell23_7873380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_7873380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873380 prefixEnd_7873380 := by exact prefixLift 7873380
  have htrace : WordTrace (prefixWord ++ tailWord_7873380) baseStart_7873380 baseEnd_7873380 := by
    simpa [prefixWord, tailWord_7873380, baseEnd_7873380] using wordTrace_append hprefix tailTrace_7873380
  have hstable : (prefixWord ++ tailWord_7873380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873380).length < 2 ^ (prefixWord ++ tailWord_7873380).sum := by decide
  have hdescent : baseEnd_7873380 < baseStart_7873380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873419 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 4, 4, 2]
def baseStart_7873419 : Nat := 118140960795 + 7873419 * 2 ^ 59
def prefixEnd_7873419 : Nat := 4983230072969 + 3 ^ 40 * 7873419 * 2
def baseEnd_7873419 : Nat := 4042848341242035945653311

theorem tailTrace_7873419 : CollatzResearch.WordTrace tailWord_7873419 prefixEnd_7873419 4042848341242035945653311 := by
  unfold tailWord_7873419
  simp only [CollatzResearch.WordTrace]
  refine ⟨287167182662955110755431311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191444788441970073836954207 287167182662955110755431311)
  ·
    refine ⟨430750773994432666133146967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287167182662955110755431311 430750773994432666133146967)
    ·
      refine ⟨646126160991648999199720451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430750773994432666133146967 646126160991648999199720451)
      ·
        refine ⟨969189241487473498799580677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646126160991648999199720451 969189241487473498799580677)
        ·
          refine ⟨181722982778901281024921377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 969189241487473498799580677 181722982778901281024921377)
          ·
            refine ⟨136292237084175960768691033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181722982778901281024921377 136292237084175960768691033)
            ·
              refine ⟨102219177813131970576518275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136292237084175960768691033 102219177813131970576518275)
              ·
                refine ⟨153328766719697955864777413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102219177813131970576518275 153328766719697955864777413)
                ·
                  refine ⟨28749143759943366724645765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153328766719697955864777413 28749143759943366724645765)
                  ·
                    refine ⟨5390464454989381260871081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28749143759943366724645765 5390464454989381260871081)
                    ·
                      refine ⟨4042848341242035945653311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390464454989381260871081 4042848341242035945653311)
                      ·
                        rfl

theorem cell23_7873419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 4, 2].length) (baseStart_7873419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873419 prefixEnd_7873419 := by exact prefixLift 7873419
  have htrace : WordTrace (prefixWord ++ tailWord_7873419) baseStart_7873419 baseEnd_7873419 := by
    simpa [prefixWord, tailWord_7873419, baseEnd_7873419] using wordTrace_append hprefix tailTrace_7873419
  have hstable : (prefixWord ++ tailWord_7873419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873419).length < 2 ^ (prefixWord ++ tailWord_7873419).sum := by decide
  have hdescent : baseEnd_7873419 < baseStart_7873419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873426 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7873426 : Nat := 118140960795 + 7873426 * 2 ^ 59
def prefixEnd_7873426 : Nat := 4983230072969 + 3 ^ 40 * 7873426 * 2
def baseEnd_7873426 : Nat := 4042851935606617418265779

theorem tailTrace_7873426 : CollatzResearch.WordTrace tailWord_7873426 prefixEnd_7873426 4042851935606617418265779 := by
  unfold tailWord_7873426
  simp only [CollatzResearch.WordTrace]
  refine ⟨71791859493482437737734033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191444958649286500633957421 71791859493482437737734033)
  ·
    refine ⟨53843894620111828303300525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71791859493482437737734033 53843894620111828303300525)
    ·
      refine ⟨20191460482541935613737697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53843894620111828303300525 20191460482541935613737697)
      ·
        refine ⟨15143595361906451710303273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20191460482541935613737697 15143595361906451710303273)
        ·
          refine ⟨11357696521429838782727455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15143595361906451710303273 11357696521429838782727455)
          ·
            refine ⟨17036544782144758174091183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11357696521429838782727455 17036544782144758174091183)
            ·
              refine ⟨25554817173217137261136775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17036544782144758174091183 25554817173217137261136775)
              ·
                refine ⟨38332225759825705891705163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25554817173217137261136775 38332225759825705891705163)
                ·
                  refine ⟨57498338639738558837557745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38332225759825705891705163 57498338639738558837557745)
                  ·
                    refine ⟨43123753979803919128168309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57498338639738558837557745 43123753979803919128168309)
                    ·
                      refine ⟨4042851935606617418265779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43123753979803919128168309 4042851935606617418265779)
                      ·
                        rfl

theorem cell23_7873426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7873426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873426 prefixEnd_7873426 := by exact prefixLift 7873426
  have htrace : WordTrace (prefixWord ++ tailWord_7873426) baseStart_7873426 baseEnd_7873426 := by
    simpa [prefixWord, tailWord_7873426, baseEnd_7873426] using wordTrace_append hprefix tailTrace_7873426
  have hstable : (prefixWord ++ tailWord_7873426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873426).length < 2 ^ (prefixWord ++ tailWord_7873426).sum := by decide
  have hdescent : baseEnd_7873426 < baseStart_7873426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873503 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 3]
def baseStart_7873503 : Nat := 118140960795 + 7873503 * 2 ^ 59
def prefixEnd_7873503 : Nat := 4983230072969 + 3 ^ 40 * 7873503 * 2
def baseEnd_7873503 : Nat := 4042891473617013617002925

theorem tailTrace_7873503 : CollatzResearch.WordTrace tailWord_7873503 prefixEnd_7873503 4042891473617013617002925 := by
  unfold tailWord_7873503
  simp only [CollatzResearch.WordTrace]
  refine ⟨287170246394650793101489163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191446830929767195400992775 287170246394650793101489163)
  ·
    refine ⟨430755369591976189652233745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287170246394650793101489163 430755369591976189652233745)
    ·
      refine ⟨323066527193982142239175309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430755369591976189652233745 323066527193982142239175309)
      ·
        refine ⟨121149947697743303339690741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323066527193982142239175309 121149947697743303339690741)
        ·
          refine ⟨11357807596663434688096007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121149947697743303339690741 11357807596663434688096007)
          ·
            refine ⟨17036711394995152032144011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11357807596663434688096007 17036711394995152032144011)
            ·
              refine ⟨25555067092492728048216017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17036711394995152032144011 25555067092492728048216017)
              ·
                refine ⟨19166300319369546036162013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25555067092492728048216017 19166300319369546036162013)
                ·
                  refine ⟨7187362619763579763560755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19166300319369546036162013 7187362619763579763560755)
                  ·
                    refine ⟨10781043929645369645341133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187362619763579763560755 10781043929645369645341133)
                    ·
                      refine ⟨4042891473617013617002925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781043929645369645341133 4042891473617013617002925)
                      ·
                        rfl

theorem cell23_7873503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_7873503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873503 prefixEnd_7873503 := by exact prefixLift 7873503
  have htrace : WordTrace (prefixWord ++ tailWord_7873503) baseStart_7873503 baseEnd_7873503 := by
    simpa [prefixWord, tailWord_7873503, baseEnd_7873503] using wordTrace_append hprefix tailTrace_7873503
  have hstable : (prefixWord ++ tailWord_7873503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873503).length < 2 ^ (prefixWord ++ tailWord_7873503).sum := by decide
  have hdescent : baseEnd_7873503 < baseStart_7873503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873519 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 1, 6]
def baseStart_7873519 : Nat := 118140960795 + 7873519 * 2 ^ 59
def prefixEnd_7873519 : Nat := 4983230072969 + 3 ^ 40 * 7873519 * 2
def baseEnd_7873519 : Nat := 1347633229769161851467617

theorem tailTrace_7873519 : CollatzResearch.WordTrace tailWord_7873519 prefixEnd_7873519 1347633229769161851467617 := by
  unfold tailWord_7873519
  simp only [CollatzResearch.WordTrace]
  refine ⟨287170829962592827834071611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191447219975061885222714407 287170829962592827834071611)
  ·
    refine ⟨430756244943889241751107417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287170829962592827834071611 430756244943889241751107417)
    ·
      refine ⟨323067183707916931313330563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430756244943889241751107417 323067183707916931313330563)
      ·
        refine ⟨484600775561875396969995845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323067183707916931313330563 484600775561875396969995845)
        ·
          refine ⟨90862645417851636931874221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484600775561875396969995845 90862645417851636931874221)
          ·
            refine ⟨34073492031694363849452833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90862645417851636931874221 34073492031694363849452833)
            ·
              refine ⟨25555119023770772887089625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34073492031694363849452833 25555119023770772887089625)
              ·
                refine ⟨19166339267828079665317219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25555119023770772887089625 19166339267828079665317219)
                ·
                  refine ⟨28749508901742119497975829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19166339267828079665317219 28749508901742119497975829)
                  ·
                    refine ⟨1347633229769161851467617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28749508901742119497975829 1347633229769161851467617)
                    ·
                      rfl

theorem cell23_7873519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_7873519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873519 prefixEnd_7873519 := by exact prefixLift 7873519
  have htrace : WordTrace (prefixWord ++ tailWord_7873519) baseStart_7873519 baseEnd_7873519 := by
    simpa [prefixWord, tailWord_7873519, baseEnd_7873519] using wordTrace_append hprefix tailTrace_7873519
  have hstable : (prefixWord ++ tailWord_7873519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873519).length < 2 ^ (prefixWord ++ tailWord_7873519).sum := by decide
  have hdescent : baseEnd_7873519 < baseStart_7873519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873529 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_7873529 : Nat := 118140960795 + 7873529 * 2 ^ 59
def prefixEnd_7873529 : Nat := 4983230072969 + 3 ^ 40 * 7873529 * 2
def baseEnd_7873529 : Nat := 4042904824114030515277805

theorem tailTrace_7873529 : CollatzResearch.WordTrace tailWord_7873529 prefixEnd_7873529 4042904824114030515277805 := by
  unfold tailWord_7873529
  simp only [CollatzResearch.WordTrace]
  refine ⟨287171194692556599541935641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191447463128371066361290427 287171194692556599541935641)
  ·
    refine ⟨215378396019417449656451731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287171194692556599541935641 215378396019417449656451731)
    ·
      refine ⟨323067594029126174484677597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215378396019417449656451731 323067594029126174484677597)
      ·
        refine ⟨121150347760922315431754099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323067594029126174484677597 121150347760922315431754099)
        ·
          refine ⟨181725521641383473147631149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121150347760922315431754099 181725521641383473147631149)
          ·
            refine ⟨68147070615518802430361681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181725521641383473147631149 68147070615518802430361681)
            ·
              refine ⟨51110302961639101822771261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68147070615518802430361681 51110302961639101822771261)
              ·
                refine ⟨19166363610614663183539223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51110302961639101822771261 19166363610614663183539223)
                ·
                  refine ⟨28749545415921994775308835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19166363610614663183539223 28749545415921994775308835)
                  ·
                    refine ⟨43124318123882992162963253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28749545415921994775308835 43124318123882992162963253)
                    ·
                      refine ⟨4042904824114030515277805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43124318123882992162963253 4042904824114030515277805)
                      ·
                        rfl

theorem cell23_7873529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_7873529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873529 prefixEnd_7873529 := by exact prefixLift 7873529
  have htrace : WordTrace (prefixWord ++ tailWord_7873529) baseStart_7873529 baseEnd_7873529 := by
    simpa [prefixWord, tailWord_7873529, baseEnd_7873529] using wordTrace_append hprefix tailTrace_7873529
  have hstable : (prefixWord ++ tailWord_7873529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873529).length < 2 ^ (prefixWord ++ tailWord_7873529).sum := by decide
  have hdescent : baseEnd_7873529 < baseStart_7873529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873546 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7873546 : Nat := 118140960795 + 7873546 * 2 ^ 59
def prefixEnd_7873546 : Nat := 4983230072969 + 3 ^ 40 * 7873546 * 2
def baseEnd_7873546 : Nat := 4042913553285156948765227

theorem tailTrace_7873546 : CollatzResearch.WordTrace tailWord_7873546 prefixEnd_7873546 4042913553285156948765227 := by
  unfold tailWord_7873546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71792953683373752861326123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191447876488996674296869661 71792953683373752861326123)
  ·
    refine ⟨107689430525060629291989185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71792953683373752861326123 107689430525060629291989185)
    ·
      refine ⟨80767072893795471968991889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107689430525060629291989185 80767072893795471968991889)
      ·
        refine ⟨60575304670346603976743917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80767072893795471968991889 60575304670346603976743917)
        ·
          refine ⟨22715739251379976491278969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60575304670346603976743917 22715739251379976491278969)
          ·
            refine ⟨17036804438534982368459227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22715739251379976491278969 17036804438534982368459227)
            ·
              refine ⟨25555206657802473552688841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17036804438534982368459227 25555206657802473552688841)
              ·
                refine ⟨19166404993351855164516631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25555206657802473552688841 19166404993351855164516631)
                ·
                  refine ⟨28749607490027782746774947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19166404993351855164516631 28749607490027782746774947)
                  ·
                    refine ⟨43124411235041674120162421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28749607490027782746774947 43124411235041674120162421)
                    ·
                      refine ⟨4042913553285156948765227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43124411235041674120162421 4042913553285156948765227)
                      ·
                        rfl

theorem cell23_7873546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7873546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873546 prefixEnd_7873546 := by exact prefixLift 7873546
  have htrace : WordTrace (prefixWord ++ tailWord_7873546) baseStart_7873546 baseEnd_7873546 := by
    simpa [prefixWord, tailWord_7873546, baseEnd_7873546] using wordTrace_append hprefix tailTrace_7873546
  have hstable : (prefixWord ++ tailWord_7873546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873546).length < 2 ^ (prefixWord ++ tailWord_7873546).sum := by decide
  have hdescent : baseEnd_7873546 < baseStart_7873546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873589 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7873589 : Nat := 118140960795 + 7873589 * 2 ^ 59
def prefixEnd_7873589 : Nat := 4983230072969 + 3 ^ 40 * 7873589 * 2
def baseEnd_7873589 : Nat := 4042935632953300280527529

theorem tailTrace_7873589 : CollatzResearch.WordTrace tailWord_7873589 prefixEnd_7873589 4042935632953300280527529 := by
  unfold tailWord_7873589
  simp only [CollatzResearch.WordTrace]
  refine ⟨287173383072339229789119821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191448922048226153192746547 287173383072339229789119821)
  ·
    refine ⟨107690018652127211170919933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287173383072339229789119821 107690018652127211170919933)
    ·
      refine ⟨40383756994547704189094975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107690018652127211170919933 40383756994547704189094975)
      ·
        refine ⟨60575635491821556283642463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40383756994547704189094975 60575635491821556283642463)
        ·
          refine ⟨90863453237732334425463695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60575635491821556283642463 90863453237732334425463695)
          ·
            refine ⟨136295179856598501638195543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90863453237732334425463695 136295179856598501638195543)
            ·
              refine ⟨204442769784897752457293315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136295179856598501638195543 204442769784897752457293315)
              ·
                refine ⟨306664154677346628685939973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204442769784897752457293315 306664154677346628685939973)
                ·
                  refine ⟨57499529002002492878613745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306664154677346628685939973 57499529002002492878613745)
                  ·
                    refine ⟨43124646751501869658960309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57499529002002492878613745 43124646751501869658960309)
                    ·
                      refine ⟨4042935632953300280527529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43124646751501869658960309 4042935632953300280527529)
                      ·
                        rfl

theorem cell23_7873589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7873589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873589 prefixEnd_7873589 := by exact prefixLift 7873589
  have htrace : WordTrace (prefixWord ++ tailWord_7873589) baseStart_7873589 baseEnd_7873589 := by
    simpa [prefixWord, tailWord_7873589, baseEnd_7873589] using wordTrace_append hprefix tailTrace_7873589
  have hstable : (prefixWord ++ tailWord_7873589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873589).length < 2 ^ (prefixWord ++ tailWord_7873589).sum := by decide
  have hdescent : baseEnd_7873589 < baseStart_7873589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873593 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7873593 : Nat := 118140960795 + 7873593 * 2 ^ 59
def prefixEnd_7873593 : Nat := 4983230072969 + 3 ^ 40 * 7873593 * 2
def baseEnd_7873593 : Nat := 4042937686875918264877511

theorem tailTrace_7873593 : CollatzResearch.WordTrace tailWord_7873593 prefixEnd_7873593 4042937686875918264877511 := by
  unfold tailWord_7873593
  simp only [CollatzResearch.WordTrace]
  refine ⟨287173528964324738472265433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191449019309549825648176955 287173528964324738472265433)
  ·
    refine ⟨215380146723243553854199075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287173528964324738472265433 215380146723243553854199075)
    ·
      refine ⟨323070220084865330781298613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215380146723243553854199075 323070220084865330781298613)
      ·
        refine ⟨30287833132956124760746745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323070220084865330781298613 30287833132956124760746745)
        ·
          refine ⟨22715874849717093570560059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30287833132956124760746745 22715874849717093570560059)
          ·
            refine ⟨34073812274575640355840089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22715874849717093570560059 34073812274575640355840089)
            ·
              refine ⟨25555359205931730266880067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34073812274575640355840089 25555359205931730266880067)
              ·
                refine ⟨38333038808897595400320101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25555359205931730266880067 38333038808897595400320101)
                ·
                  refine ⟨7187444776668299137560019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38333038808897595400320101 7187444776668299137560019)
                  ·
                    refine ⟨10781167165002448706340029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187444776668299137560019 10781167165002448706340029)
                    ·
                      refine ⟨4042937686875918264877511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781167165002448706340029 4042937686875918264877511)
                      ·
                        rfl

theorem cell23_7873593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7873593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873593 prefixEnd_7873593 := by exact prefixLift 7873593
  have htrace : WordTrace (prefixWord ++ tailWord_7873593) baseStart_7873593 baseEnd_7873593 := by
    simpa [prefixWord, tailWord_7873593, baseEnd_7873593] using wordTrace_append hprefix tailTrace_7873593
  have hstable : (prefixWord ++ tailWord_7873593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873593).length < 2 ^ (prefixWord ++ tailWord_7873593).sum := by decide
  have hdescent : baseEnd_7873593 < baseStart_7873593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873599 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_7873599 : Nat := 118140960795 + 7873599 * 2 ^ 59
def prefixEnd_7873599 : Nat := 4983230072969 + 3 ^ 40 * 7873599 * 2
def baseEnd_7873599 : Nat := 4042940767759845241402483

theorem tailTrace_7873599 : CollatzResearch.WordTrace tailWord_7873599 prefixEnd_7873599 4042940767759845241402483 := by
  unfold tailWord_7873599
  simp only [CollatzResearch.WordTrace]
  refine ⟨287173747802303001496983851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191449165201535334331322567 287173747802303001496983851)
  ·
    refine ⟨430760621703454502245475777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287173747802303001496983851 430760621703454502245475777)
    ·
      refine ⟨323070466277590876684106833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430760621703454502245475777 323070466277590876684106833)
      ·
        refine ⟨242302849708193157513080125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323070466277590876684106833 242302849708193157513080125)
        ·
          refine ⟨90863568640572434067405047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242302849708193157513080125 90863568640572434067405047)
          ·
            refine ⟨136295352960858651101107571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90863568640572434067405047 136295352960858651101107571)
            ·
              refine ⟨204443029441287976651661357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136295352960858651101107571 204443029441287976651661357)
              ·
                refine ⟨76666136040482991244373009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204443029441287976651661357 76666136040482991244373009)
                ·
                  refine ⟨57499602030362243433279757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76666136040482991244373009 57499602030362243433279757)
                  ·
                    refine ⟨21562350761385841287479909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57499602030362243433279757 21562350761385841287479909)
                    ·
                      refine ⟨4042940767759845241402483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21562350761385841287479909 4042940767759845241402483)
                      ·
                        rfl

theorem cell23_7873599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_7873599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873599 prefixEnd_7873599 := by exact prefixLift 7873599
  have htrace : WordTrace (prefixWord ++ tailWord_7873599) baseStart_7873599 baseEnd_7873599 := by
    simpa [prefixWord, tailWord_7873599, baseEnd_7873599] using wordTrace_append hprefix tailTrace_7873599
  have hstable : (prefixWord ++ tailWord_7873599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873599).length < 2 ^ (prefixWord ++ tailWord_7873599).sum := by decide
  have hdescent : baseEnd_7873599 < baseStart_7873599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873610 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_7873610 : Nat := 118140960795 + 7873610 * 2 ^ 59
def prefixEnd_7873610 : Nat := 4983230072969 + 3 ^ 40 * 7873610 * 2
def baseEnd_7873610 : Nat := 4042946416047044698364933

theorem tailTrace_7873610 : CollatzResearch.WordTrace tailWord_7873610 prefixEnd_7873610 4042946416047044698364933 := by
  unfold tailWord_7873610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71793537251315787593908571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191449432670175433583756189 71793537251315787593908571)
  ·
    refine ⟨107690305876973681390862857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71793537251315787593908571 107690305876973681390862857)
    ·
      refine ⟨80767729407730261043147143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107690305876973681390862857 80767729407730261043147143)
      ·
        refine ⟨121151594111595391564720715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80767729407730261043147143 121151594111595391564720715)
        ·
          refine ⟨181727391167393087347081073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121151594111595391564720715 181727391167393087347081073)
          ·
            refine ⟨136295543375544815510310805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181727391167393087347081073 136295543375544815510310805)
            ·
              refine ⟨6388853595728663227045819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136295543375544815510310805 6388853595728663227045819)
              ·
                refine ⟨9583280393592994840568729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388853595728663227045819 9583280393592994840568729)
                ·
                  refine ⟨7187460295194746130426547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583280393592994840568729 7187460295194746130426547)
                  ·
                    refine ⟨10781190442792119195639821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187460295194746130426547 10781190442792119195639821)
                    ·
                      refine ⟨4042946416047044698364933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781190442792119195639821 4042946416047044698364933)
                      ·
                        rfl

theorem cell23_7873610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_7873610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873610 prefixEnd_7873610 := by exact prefixLift 7873610
  have htrace : WordTrace (prefixWord ++ tailWord_7873610) baseStart_7873610 baseEnd_7873610 := by
    simpa [prefixWord, tailWord_7873610, baseEnd_7873610] using wordTrace_append hprefix tailTrace_7873610
  have hstable : (prefixWord ++ tailWord_7873610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873610).length < 2 ^ (prefixWord ++ tailWord_7873610).sum := by decide
  have hdescent : baseEnd_7873610 < baseStart_7873610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873616 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 5, 4, 2]
def baseStart_7873616 : Nat := 118140960795 + 7873616 * 2 ^ 59
def prefixEnd_7873616 : Nat := 4983230072969 + 3 ^ 40 * 7873616 * 2
def baseEnd_7873616 : Nat := 4042949496930971674889905

theorem tailTrace_7873616 : CollatzResearch.WordTrace tailWord_7873616 prefixEnd_7873616 4042949496930971674889905 := by
  unfold tailWord_7873616
  simp only [CollatzResearch.WordTrace]
  refine ⟨143587183921620706700176351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191449578562160942266901801 143587183921620706700176351)
  ·
    refine ⟨215380775882431060050264527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143587183921620706700176351 215380775882431060050264527)
    ·
      refine ⟨323071163823646590075396791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215380775882431060050264527 323071163823646590075396791)
      ·
        refine ⟨484606745735469885113095187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323071163823646590075396791 484606745735469885113095187)
        ·
          refine ⟨726910118603204827669642781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484606745735469885113095187 726910118603204827669642781)
          ·
            refine ⟨272591294476201810376116043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726910118603204827669642781 272591294476201810376116043)
            ·
              refine ⟨408886941714302715564174065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272591294476201810376116043 408886941714302715564174065)
              ·
                refine ⟨306665206285727036673130549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408886941714302715564174065 306665206285727036673130549)
                ·
                  refine ⟨28749863089286909688105989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306665206285727036673130549 28749863089286909688105989)
                  ·
                    refine ⟨5390599329241295566519873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28749863089286909688105989 5390599329241295566519873)
                    ·
                      refine ⟨4042949496930971674889905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390599329241295566519873 4042949496930971674889905)
                      ·
                        rfl

theorem cell23_7873616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 4, 2].length) (baseStart_7873616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873616 prefixEnd_7873616 := by exact prefixLift 7873616
  have htrace : WordTrace (prefixWord ++ tailWord_7873616) baseStart_7873616 baseEnd_7873616 := by
    simpa [prefixWord, tailWord_7873616, baseEnd_7873616] using wordTrace_append hprefix tailTrace_7873616
  have hstable : (prefixWord ++ tailWord_7873616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873616).length < 2 ^ (prefixWord ++ tailWord_7873616).sum := by decide
  have hdescent : baseEnd_7873616 < baseStart_7873616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873619 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5]
def baseStart_7873619 : Nat := 118140960795 + 7873619 * 2 ^ 59
def prefixEnd_7873619 : Nat := 4983230072969 + 3 ^ 40 * 7873619 * 2
def baseEnd_7873619 : Nat := 4042951037372935163152391

theorem tailTrace_7873619 : CollatzResearch.WordTrace tailWord_7873619 prefixEnd_7873619 4042951037372935163152391 := by
  unfold tailWord_7873619
  simp only [CollatzResearch.WordTrace]
  refine ⟨287174477262230544912711911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191449651508153696608474607 287174477262230544912711911)
  ·
    refine ⟨430761715893345817369067867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287174477262230544912711911 430761715893345817369067867)
    ·
      refine ⟨646142573840018726053601801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430761715893345817369067867 646142573840018726053601801)
      ·
        refine ⟨484606930380014044540201351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646142573840018726053601801 484606930380014044540201351)
        ·
          refine ⟨726910395570021066810302027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484606930380014044540201351 726910395570021066810302027)
          ·
            refine ⟨1090365593355031600215453041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726910395570021066810302027 1090365593355031600215453041)
            ·
              refine ⟨817774195016273700161589781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090365593355031600215453041 817774195016273700161589781)
              ·
                refine ⟨38333165391387829695074521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 817774195016273700161589781 38333165391387829695074521)
                ·
                  refine ⟨28749874043540872271305891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38333165391387829695074521 28749874043540872271305891)
                  ·
                    refine ⟨43124811065311308406958837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28749874043540872271305891 43124811065311308406958837)
                    ·
                      refine ⟨4042951037372935163152391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43124811065311308406958837 4042951037372935163152391)
                      ·
                        rfl

theorem cell23_7873619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_7873619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873619 prefixEnd_7873619 := by exact prefixLift 7873619
  have htrace : WordTrace (prefixWord ++ tailWord_7873619) baseStart_7873619 baseEnd_7873619 := by
    simpa [prefixWord, tailWord_7873619, baseEnd_7873619] using wordTrace_append hprefix tailTrace_7873619
  have hstable : (prefixWord ++ tailWord_7873619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873619).length < 2 ^ (prefixWord ++ tailWord_7873619).sum := by decide
  have hdescent : baseEnd_7873619 < baseStart_7873619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873620 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_7873620 : Nat := 118140960795 + 7873620 * 2 ^ 59
def prefixEnd_7873620 : Nat := 4983230072969 + 3 ^ 40 * 7873620 * 2
def baseEnd_7873620 : Nat := 4042951550853589659239887

theorem tailTrace_7873620 : CollatzResearch.WordTrace tailWord_7873620 prefixEnd_7873620 4042951550853589659239887 := by
  unfold tailWord_7873620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143587256867613461041749157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191449675823484614722332209 143587256867613461041749157)
  ·
    refine ⟨26922610662677523945327967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143587256867613461041749157 26922610662677523945327967)
    ·
      refine ⟨40383915994016285917991951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26922610662677523945327967 40383915994016285917991951)
      ·
        refine ⟨60575873991024428876987927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40383915994016285917991951 60575873991024428876987927)
        ·
          refine ⟨90863810986536643315481891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60575873991024428876987927 90863810986536643315481891)
          ·
            refine ⟨136295716479804964973222837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90863810986536643315481891 136295716479804964973222837)
            ·
              refine ⟨12777723419981715466239641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136295716479804964973222837 12777723419981715466239641)
              ·
                refine ⟨9583292564986286599679731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12777723419981715466239641 9583292564986286599679731)
                ·
                  refine ⟨14374938847479429899519597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9583292564986286599679731 14374938847479429899519597)
                  ·
                    refine ⟨5390602067804786212319849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14374938847479429899519597 5390602067804786212319849)
                    ·
                      refine ⟨4042951550853589659239887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390602067804786212319849 4042951550853589659239887)
                      ·
                        rfl

theorem cell23_7873620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_7873620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873620 prefixEnd_7873620 := by exact prefixLift 7873620
  have htrace : WordTrace (prefixWord ++ tailWord_7873620) baseStart_7873620 baseEnd_7873620 := by
    simpa [prefixWord, tailWord_7873620, baseEnd_7873620] using wordTrace_append hprefix tailTrace_7873620
  have hstable : (prefixWord ++ tailWord_7873620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873620).length < 2 ^ (prefixWord ++ tailWord_7873620).sum := by decide
  have hdescent : baseEnd_7873620 < baseStart_7873620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873633 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_7873633 : Nat := 118140960795 + 7873633 * 2 ^ 59
def prefixEnd_7873633 : Nat := 4983230072969 + 3 ^ 40 * 7873633 * 2
def baseEnd_7873633 : Nat := 4042958226102098108377327

theorem tailTrace_7873633 : CollatzResearch.WordTrace tailWord_7873633 prefixEnd_7873633 4042958226102098108377327 := by
  unfold tailWord_7873633
  simp only [CollatzResearch.WordTrace]
  refine ⟨287174987884179825303721553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191449991922786550202481035 287174987884179825303721553)
  ·
    refine ⟨215381240913134868977791165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287174987884179825303721553 215381240913134868977791165)
    ·
      refine ⟨80767965342425575866671687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215381240913134868977791165 80767965342425575866671687)
      ·
        refine ⟨121151948013638363800007531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80767965342425575866671687 121151948013638363800007531)
        ·
          refine ⟨181727922020457545700011297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121151948013638363800007531 181727922020457545700011297)
          ·
            refine ⟨136295941515343159275008473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181727922020457545700011297 136295941515343159275008473)
            ·
              refine ⟨102221956136507369456256355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136295941515343159275008473 102221956136507369456256355)
              ·
                refine ⟨153332934204761054184384533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102221956136507369456256355 153332934204761054184384533)
                ·
                  refine ⟨7187481290848174414893025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153332934204761054184384533 7187481290848174414893025)
                  ·
                    refine ⟨5390610968136130811169769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7187481290848174414893025 5390610968136130811169769)
                    ·
                      refine ⟨4042958226102098108377327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390610968136130811169769 4042958226102098108377327)
                      ·
                        rfl

theorem cell23_7873633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_7873633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873633 prefixEnd_7873633 := by exact prefixLift 7873633
  have htrace : WordTrace (prefixWord ++ tailWord_7873633) baseStart_7873633 baseEnd_7873633 := by
    simpa [prefixWord, tailWord_7873633, baseEnd_7873633] using wordTrace_append hprefix tailTrace_7873633
  have hstable : (prefixWord ++ tailWord_7873633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873633).length < 2 ^ (prefixWord ++ tailWord_7873633).sum := by decide
  have hdescent : baseEnd_7873633 < baseStart_7873633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873690 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_7873690 : Nat := 118140960795 + 7873690 * 2 ^ 59
def prefixEnd_7873690 : Nat := 4983230072969 + 3 ^ 40 * 7873690 * 2
def baseEnd_7873690 : Nat := 449220832722156042818285

theorem tailTrace_7873690 : CollatzResearch.WordTrace tailWord_7873690 prefixEnd_7873690 449220832722156042818285 := by
  unfold tailWord_7873690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71794266711243331009636631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191451377896648882692364349 71794266711243331009636631)
  ·
    refine ⟨107691400066864996514454947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71794266711243331009636631 107691400066864996514454947)
    ·
      refine ⟨161537100100297494771682421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107691400066864996514454947 161537100100297494771682421)
      ·
        refine ⟨15144103134402890134845227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161537100100297494771682421 15144103134402890134845227)
        ·
          refine ⟨22716154701604335202267841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15144103134402890134845227 22716154701604335202267841)
          ·
            refine ⟨17037116026203251401700881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22716154701604335202267841 17037116026203251401700881)
            ·
              refine ⟨12777837019652438551275661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17037116026203251401700881 12777837019652438551275661)
              ·
                refine ⟨4791688882369664456728373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12777837019652438551275661 4791688882369664456728373)
                ·
                  refine ⟨449220832722156042818285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791688882369664456728373 449220832722156042818285)
                  ·
                    rfl

theorem cell23_7873690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_7873690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873690 prefixEnd_7873690 := by exact prefixLift 7873690
  have htrace : WordTrace (prefixWord ++ tailWord_7873690) baseStart_7873690 baseEnd_7873690 := by
    simpa [prefixWord, tailWord_7873690, baseEnd_7873690] using wordTrace_append hprefix tailTrace_7873690
  have hstable : (prefixWord ++ tailWord_7873690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873690).length < 2 ^ (prefixWord ++ tailWord_7873690).sum := by decide
  have hdescent : baseEnd_7873690 < baseStart_7873690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873699 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 10]
def baseStart_7873699 : Nat := 118140960795 + 7873699 * 2 ^ 59
def prefixEnd_7873699 : Nat := 4983230072969 + 3 ^ 40 * 7873699 * 2
def baseEnd_7873699 : Nat := 1347664038608431616717341

theorem tailTrace_7873699 : CollatzResearch.WordTrace tailWord_7873699 prefixEnd_7873699 1347664038608431616717341 := by
  unfold tailWord_7873699
  simp only [CollatzResearch.WordTrace]
  refine ⟨287177395101940718575624151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191451596734627145717082767 287177395101940718575624151)
  ·
    refine ⟨430766092652911077863436227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287177395101940718575624151 430766092652911077863436227)
    ·
      refine ⟨646149138979366616795154341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430766092652911077863436227 646149138979366616795154341)
      ·
        refine ⟨121152963558631240649091439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 646149138979366616795154341 121152963558631240649091439)
        ·
          refine ⟨181729445337946860973637159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121152963558631240649091439 181729445337946860973637159)
          ·
            refine ⟨272594168006920291460455739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181729445337946860973637159 272594168006920291460455739)
            ·
              refine ⟨408891252010380437190683609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272594168006920291460455739 408891252010380437190683609)
              ·
                refine ⟨306668439007785327893012707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408891252010380437190683609 306668439007785327893012707)
                ·
                  refine ⟨460002658511677991839519061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306668439007785327893012707 460002658511677991839519061)
                  ·
                    refine ⟨1347664038608431616717341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 460002658511677991839519061 1347664038608431616717341)
                    ·
                      rfl

theorem cell23_7873699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_7873699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873699 prefixEnd_7873699 := by exact prefixLift 7873699
  have htrace : WordTrace (prefixWord ++ tailWord_7873699) baseStart_7873699 baseEnd_7873699 := by
    simpa [prefixWord, tailWord_7873699, baseEnd_7873699] using wordTrace_append hprefix tailTrace_7873699
  have hstable : (prefixWord ++ tailWord_7873699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873699).length < 2 ^ (prefixWord ++ tailWord_7873699).sum := by decide
  have hdescent : baseEnd_7873699 < baseStart_7873699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873718 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7873718 : Nat := 118140960795 + 7873718 * 2 ^ 59
def prefixEnd_7873718 : Nat := 4983230072969 + 3 ^ 40 * 7873718 * 2
def baseEnd_7873718 : Nat := 4043001871957730275814437

theorem tailTrace_7873718 : CollatzResearch.WordTrace tailWord_7873718 prefixEnd_7873718 4043001871957730275814437 := by
  unfold tailWord_7873718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948630505554492801285363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191452058725914589880377205 17948630505554492801285363)
  ·
    refine ⟨26922945758331739201928045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948630505554492801285363 26922945758331739201928045)
    ·
      refine ⟨10096104659374402200723017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26922945758331739201928045 10096104659374402200723017)
      ·
        refine ⟨7572078494530801650542263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10096104659374402200723017 7572078494530801650542263)
        ·
          refine ⟨11358117741796202475813395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572078494530801650542263 11358117741796202475813395)
          ·
            refine ⟨17037176612694303713720093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11358117741796202475813395 17037176612694303713720093)
            ·
              refine ⟨6388941229760363892645035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17037176612694303713720093 6388941229760363892645035)
              ·
                refine ⟨9583411844640545838967553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388941229760363892645035 9583411844640545838967553)
                ·
                  refine ⟨7187558883480409379225665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583411844640545838967553 7187558883480409379225665)
                  ·
                    refine ⟨5390669162610307034419249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7187558883480409379225665 5390669162610307034419249)
                    ·
                      refine ⟨4043001871957730275814437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390669162610307034419249 4043001871957730275814437)
                      ·
                        rfl

theorem cell23_7873718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7873718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873718 prefixEnd_7873718 := by exact prefixLift 7873718
  have htrace : WordTrace (prefixWord ++ tailWord_7873718) baseStart_7873718 baseEnd_7873718 := by
    simpa [prefixWord, tailWord_7873718, baseEnd_7873718] using wordTrace_append hprefix tailTrace_7873718
  have hstable : (prefixWord ++ tailWord_7873718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873718).length < 2 ^ (prefixWord ++ tailWord_7873718).sum := by decide
  have hdescent : baseEnd_7873718 < baseStart_7873718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873741 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7873741 : Nat := 118140960795 + 7873741 * 2 ^ 59
def prefixEnd_7873741 : Nat := 4983230072969 + 3 ^ 40 * 7873741 * 2
def baseEnd_7873741 : Nat := 449223742445864853980759

theorem tailTrace_7873741 : CollatzResearch.WordTrace tailWord_7873741 prefixEnd_7873741 449223742445864853980759 := by
  unfold tailWord_7873741
  simp only [CollatzResearch.WordTrace]
  refine ⟨287178926967788559748653077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191452617978525706499102051 287178926967788559748653077)
  ·
    refine ⟨13461512201615088738218113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287178926967788559748653077 13461512201615088738218113)
    ·
      refine ⟨10096134151211316553663585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13461512201615088738218113 10096134151211316553663585)
      ·
        refine ⟨7572100613408487415247689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10096134151211316553663585 7572100613408487415247689)
        ·
          refine ⟨5679075460056365561435767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7572100613408487415247689 5679075460056365561435767)
          ·
            refine ⟨8518613190084548342153651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679075460056365561435767 8518613190084548342153651)
            ·
              refine ⟨12777919785126822513230477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518613190084548342153651 12777919785126822513230477)
              ·
                refine ⟨4791719919422558442461429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12777919785126822513230477 4791719919422558442461429)
                ·
                  refine ⟨449223742445864853980759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791719919422558442461429 449223742445864853980759)
                  ·
                    rfl

theorem cell23_7873741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7873741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873741 prefixEnd_7873741 := by exact prefixLift 7873741
  have htrace : WordTrace (prefixWord ++ tailWord_7873741) baseStart_7873741 baseEnd_7873741 := by
    simpa [prefixWord, tailWord_7873741, baseEnd_7873741] using wordTrace_append hprefix tailTrace_7873741
  have hstable : (prefixWord ++ tailWord_7873741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873741).length < 2 ^ (prefixWord ++ tailWord_7873741).sum := by decide
  have hdescent : baseEnd_7873741 < baseStart_7873741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873746 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_7873746 : Nat := 118140960795 + 7873746 * 2 ^ 59
def prefixEnd_7873746 : Nat := 4983230072969 + 3 ^ 40 * 7873746 * 2
def baseEnd_7873746 : Nat := 449224027712895129584923

theorem tailTrace_7873746 : CollatzResearch.WordTrace tailWord_7873746 prefixEnd_7873746 449224027712895129584923 := by
  unfold tailWord_7873746
  simp only [CollatzResearch.WordTrace]
  refine ⟨71794777333192611400646273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191452739555180297068390061 71794777333192611400646273)
  ·
    refine ⟨53846082999894458550484705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71794777333192611400646273 53846082999894458550484705)
    ·
      refine ⟨40384562249920843912863529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53846082999894458550484705 40384562249920843912863529)
      ·
        refine ⟨30288421687440632934647647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40384562249920843912863529 30288421687440632934647647)
        ·
          refine ⟨45432632531160949401971471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30288421687440632934647647 45432632531160949401971471)
          ·
            refine ⟨68148948796741424102957207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45432632531160949401971471 68148948796741424102957207)
            ·
              refine ⟨102223423195112136154435811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68148948796741424102957207 102223423195112136154435811)
              ·
                refine ⟨153335134792668204231653717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102223423195112136154435811 153335134792668204231653717)
                ·
                  refine ⟨449224027712895129584923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153335134792668204231653717 449224027712895129584923)
                  ·
                    rfl

theorem cell23_7873746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_7873746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873746 prefixEnd_7873746 := by exact prefixLift 7873746
  have htrace : WordTrace (prefixWord ++ tailWord_7873746) baseStart_7873746 baseEnd_7873746 := by
    simpa [prefixWord, tailWord_7873746, baseEnd_7873746] using wordTrace_append hprefix tailTrace_7873746
  have hstable : (prefixWord ++ tailWord_7873746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873746).length < 2 ^ (prefixWord ++ tailWord_7873746).sum := by decide
  have hdescent : baseEnd_7873746 < baseStart_7873746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873767 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 3, 4]
def baseStart_7873767 : Nat := 118140960795 + 7873767 * 2 ^ 59
def prefixEnd_7873767 : Nat := 4983230072969 + 3 ^ 40 * 7873767 * 2
def baseEnd_7873767 : Nat := 1347675677503266861367237

theorem tailTrace_7873767 : CollatzResearch.WordTrace tailWord_7873767 prefixEnd_7873767 1347675677503266861367237 := by
  unfold tailWord_7873767
  simp only [CollatzResearch.WordTrace]
  refine ⟨287179875265694366189099555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191453250177129577459399703 287179875265694366189099555)
  ·
    refine ⟨430769812898541549283649333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287179875265694366189099555 430769812898541549283649333)
    ·
      refine ⟨40384669959238270245342125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430769812898541549283649333 40384669959238270245342125)
      ·
        refine ⟨15144251234714351342003297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40384669959238270245342125 15144251234714351342003297)
        ·
          refine ⟨11358188426035763506502473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15144251234714351342003297 11358188426035763506502473)
          ·
            refine ⟨8518641319526822629876855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358188426035763506502473 8518641319526822629876855)
            ·
              refine ⟨12777961979290233944815283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518641319526822629876855 12777961979290233944815283)
              ·
                refine ⟨19166942968935350917222925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12777961979290233944815283 19166942968935350917222925)
                ·
                  refine ⟨7187603613350756593958597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19166942968935350917222925 7187603613350756593958597)
                  ·
                    refine ⟨1347675677503266861367237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7187603613350756593958597 1347675677503266861367237)
                    ·
                      rfl

theorem cell23_7873767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_7873767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873767 prefixEnd_7873767 := by exact prefixLift 7873767
  have htrace : WordTrace (prefixWord ++ tailWord_7873767) baseStart_7873767 baseEnd_7873767 := by
    simpa [prefixWord, tailWord_7873767, baseEnd_7873767] using wordTrace_append hprefix tailTrace_7873767
  have hstable : (prefixWord ++ tailWord_7873767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873767).length < 2 ^ (prefixWord ++ tailWord_7873767).sum := by decide
  have hdescent : baseEnd_7873767 < baseStart_7873767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873793 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_7873793 : Nat := 118140960795 + 7873793 * 2 ^ 59
def prefixEnd_7873793 : Nat := 4983230072969 + 3 ^ 40 * 7873793 * 2
def baseEnd_7873793 : Nat := 1347680127668939160792197

theorem tailTrace_7873793 : CollatzResearch.WordTrace tailWord_7873793 prefixEnd_7873793 1347680127668939160792197 := by
  unfold tailWord_7873793
  simp only [CollatzResearch.WordTrace]
  refine ⟨287180823563600172629546033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191453882375733448419697355 287180823563600172629546033)
  ·
    refine ⟨215385617672700129472159525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287180823563600172629546033 215385617672700129472159525)
    ·
      refine ⟨40384803313631274276029911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215385617672700129472159525 40384803313631274276029911)
      ·
        refine ⟨60577204970446911414044867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40384803313631274276029911 60577204970446911414044867)
        ·
          refine ⟨90865807455670367121067301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60577204970446911414044867 90865807455670367121067301)
          ·
            refine ⟨17037338897938193835200119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90865807455670367121067301 17037338897938193835200119)
            ·
              refine ⟨25556008346907290752800179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17037338897938193835200119 25556008346907290752800179)
              ·
                refine ⟨38334012520360936129200269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25556008346907290752800179 38334012520360936129200269)
                ·
                  refine ⟨14375254695135351048450101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38334012520360936129200269 14375254695135351048450101)
                  ·
                    refine ⟨1347680127668939160792197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14375254695135351048450101 1347680127668939160792197)
                    ·
                      rfl

theorem cell23_7873793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_7873793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873793 prefixEnd_7873793 := by exact prefixLift 7873793
  have htrace : WordTrace (prefixWord ++ tailWord_7873793) baseStart_7873793 baseEnd_7873793 := by
    simpa [prefixWord, tailWord_7873793, baseEnd_7873793] using wordTrace_append hprefix tailTrace_7873793
  have hstable : (prefixWord ++ tailWord_7873793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873793).length < 2 ^ (prefixWord ++ tailWord_7873793).sum := by decide
  have hdescent : baseEnd_7873793 < baseStart_7873793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873824 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 1, 1, 3]
def baseStart_7873824 : Nat := 118140960795 + 7873824 * 2 ^ 59
def prefixEnd_7873824 : Nat := 4983230072969 + 3 ^ 40 * 7873824 * 2
def baseEnd_7873824 : Nat := 4043056300907106861088949

theorem tailTrace_7873824 : CollatzResearch.WordTrace tailWord_7873824 prefixEnd_7873824 4043056300907106861088949 := by
  unfold tailWord_7873824
  simp only [CollatzResearch.WordTrace]
  refine ⟨143590977113243932461962263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191454636150991909949283017 143590977113243932461962263)
  ·
    refine ⟨215386465669865898692943395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143590977113243932461962263 215386465669865898692943395)
    ·
      refine ⟨323079698504798848039415093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215386465669865898692943395 323079698504798848039415093)
      ·
        refine ⟨30288721734824892003695165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323079698504798848039415093 30288721734824892003695165)
        ·
          refine ⟨11358270650559334501385687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30288721734824892003695165 11358270650559334501385687)
          ·
            refine ⟨17037405975839001752078531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11358270650559334501385687 17037405975839001752078531)
            ·
              refine ⟨25556108963758502628117797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17037405975839001752078531 25556108963758502628117797)
              ·
                refine ⟨4791770430704719242772087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25556108963758502628117797 4791770430704719242772087)
                ·
                  refine ⟨7187655646057078864158131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791770430704719242772087 7187655646057078864158131)
                  ·
                    refine ⟨10781483469085618296237197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187655646057078864158131 10781483469085618296237197)
                    ·
                      refine ⟨4043056300907106861088949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781483469085618296237197 4043056300907106861088949)
                      ·
                        rfl

theorem cell23_7873824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_7873824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873824 prefixEnd_7873824 := by exact prefixLift 7873824
  have htrace : WordTrace (prefixWord ++ tailWord_7873824) baseStart_7873824 baseEnd_7873824 := by
    simpa [prefixWord, tailWord_7873824, baseEnd_7873824] using wordTrace_append hprefix tailTrace_7873824
  have hstable : (prefixWord ++ tailWord_7873824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873824).length < 2 ^ (prefixWord ++ tailWord_7873824).sum := by decide
  have hdescent : baseEnd_7873824 < baseStart_7873824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873843 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4]
def baseStart_7873843 : Nat := 118140960795 + 7873843 * 2 ^ 59
def prefixEnd_7873843 : Nat := 4983230072969 + 3 ^ 40 * 7873843 * 2
def baseEnd_7873843 : Nat := 4043066057039542286751361

theorem tailTrace_7873843 : CollatzResearch.WordTrace tailWord_7873843 prefixEnd_7873843 4043066057039542286751361 := by
  unfold tailWord_7873843
  simp only [CollatzResearch.WordTrace]
  refine ⟨287182647213419031168866183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191455098142279354112577455 287182647213419031168866183)
  ·
    refine ⟨430773970820128546753299275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287182647213419031168866183 430773970820128546753299275)
    ·
      refine ⟨646160956230192820129948913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430773970820128546753299275 646160956230192820129948913)
      ·
        refine ⟨484620717172644615097461685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646160956230192820129948913 484620717172644615097461685)
        ·
          refine ⟨45433192234935432665387033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484620717172644615097461685 45433192234935432665387033)
          ·
            refine ⟨34074894176201574499040275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45433192234935432665387033 34074894176201574499040275)
            ·
              refine ⟨51112341264302361748560413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34074894176201574499040275 51112341264302361748560413)
              ·
                refine ⟨19167127974113385655710155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51112341264302361748560413 19167127974113385655710155)
                ·
                  refine ⟨28750691961170078483565233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19167127974113385655710155 28750691961170078483565233)
                  ·
                    refine ⟨21563018970877558862673925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28750691961170078483565233 21563018970877558862673925)
                    ·
                      refine ⟨4043066057039542286751361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21563018970877558862673925 4043066057039542286751361)
                      ·
                        rfl

theorem cell23_7873843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_7873843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873843 prefixEnd_7873843 := by exact prefixLift 7873843
  have htrace : WordTrace (prefixWord ++ tailWord_7873843) baseStart_7873843 baseEnd_7873843 := by
    simpa [prefixWord, tailWord_7873843, baseEnd_7873843] using wordTrace_append hprefix tailTrace_7873843
  have hstable : (prefixWord ++ tailWord_7873843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873843).length < 2 ^ (prefixWord ++ tailWord_7873843).sum := by decide
  have hdescent : baseEnd_7873843 < baseStart_7873843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873850 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_7873850 : Nat := 118140960795 + 7873850 * 2 ^ 59
def prefixEnd_7873850 : Nat := 4983230072969 + 3 ^ 40 * 7873850 * 2
def baseEnd_7873850 : Nat := 4043069651404123759363829

theorem tailTrace_7873850 : CollatzResearch.WordTrace tailWord_7873850 prefixEnd_7873850 4043069651404123759363829 := by
  unfold tailWord_7873850
  simp only [CollatzResearch.WordTrace]
  refine ⟨71795725631098417841092751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191455268349595780909580669 71795725631098417841092751)
  ·
    refine ⟨107693588446647626761639127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71795725631098417841092751 107693588446647626761639127)
    ·
      refine ⟨161540382669971440142458691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107693588446647626761639127 161540382669971440142458691)
      ·
        refine ⟨242310574004957160213688037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161540382669971440142458691 242310574004957160213688037)
        ·
          refine ⟨45433232625929467540066507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242310574004957160213688037 45433232625929467540066507)
          ·
            refine ⟨68149848938894201310099761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45433232625929467540066507 68149848938894201310099761)
            ·
              refine ⟨51112386704170650982574821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68149848938894201310099761 51112386704170650982574821)
              ·
                refine ⟨9583572507031997059232779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51112386704170650982574821 9583572507031997059232779)
                ·
                  refine ⟨14375358760547995588849169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9583572507031997059232779 14375358760547995588849169)
                  ·
                    refine ⟨10781519070410996691636877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14375358760547995588849169 10781519070410996691636877)
                    ·
                      refine ⟨4043069651404123759363829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781519070410996691636877 4043069651404123759363829)
                      ·
                        rfl

theorem cell23_7873850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_7873850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873850 prefixEnd_7873850 := by exact prefixLift 7873850
  have htrace : WordTrace (prefixWord ++ tailWord_7873850) baseStart_7873850 baseEnd_7873850 := by
    simpa [prefixWord, tailWord_7873850, baseEnd_7873850] using wordTrace_append hprefix tailTrace_7873850
  have hstable : (prefixWord ++ tailWord_7873850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873850).length < 2 ^ (prefixWord ++ tailWord_7873850).sum := by decide
  have hdescent : baseEnd_7873850 < baseStart_7873850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873880 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_7873880 : Nat := 118140960795 + 7873880 * 2 ^ 59
def prefixEnd_7873880 : Nat := 4983230072969 + 3 ^ 40 * 7873880 * 2
def baseEnd_7873880 : Nat := 4043085055823758641988691

theorem tailTrace_7873880 : CollatzResearch.WordTrace tailWord_7873880 prefixEnd_7873880 4043085055823758641988691 := by
  unfold tailWord_7873880
  simp only [CollatzResearch.WordTrace]
  refine ⟨143591998357142493243981547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191455997809523324325308729 143591998357142493243981547)
  ·
    refine ⟨215387997535713739865972321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143591998357142493243981547 215387997535713739865972321)
    ·
      refine ⟨161540998151785304899479241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215387997535713739865972321 161540998151785304899479241)
      ·
        refine ⟨121155748613838978674609431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161540998151785304899479241 121155748613838978674609431)
        ·
          refine ⟨181733622920758468011914147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121155748613838978674609431 181733622920758468011914147)
          ·
            refine ⟨272600434381137702017871221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181733622920758468011914147 272600434381137702017871221)
            ·
              refine ⟨25556290723231659564175427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272600434381137702017871221 25556290723231659564175427)
              ·
                refine ⟨38334436084847489346263141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25556290723231659564175427 38334436084847489346263141)
                ·
                  refine ⟨7187706765908904252424339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38334436084847489346263141 7187706765908904252424339)
                  ·
                    refine ⟨10781560148863356378636509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187706765908904252424339 10781560148863356378636509)
                    ·
                      refine ⟨4043085055823758641988691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781560148863356378636509 4043085055823758641988691)
                      ·
                        rfl

theorem cell23_7873880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_7873880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873880 prefixEnd_7873880 := by exact prefixLift 7873880
  have htrace : WordTrace (prefixWord ++ tailWord_7873880) baseStart_7873880 baseEnd_7873880 := by
    simpa [prefixWord, tailWord_7873880, baseEnd_7873880] using wordTrace_append hprefix tailTrace_7873880
  have hstable : (prefixWord ++ tailWord_7873880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873880).length < 2 ^ (prefixWord ++ tailWord_7873880).sum := by decide
  have hdescent : baseEnd_7873880 < baseStart_7873880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873920 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 1, 4, 2]
def baseStart_7873920 : Nat := 118140960795 + 7873920 * 2 ^ 59
def prefixEnd_7873920 : Nat := 4983230072969 + 3 ^ 40 * 7873920 * 2
def baseEnd_7873920 : Nat := 4043105595049938485488507

theorem tailTrace_7873920 : CollatzResearch.WordTrace tailWord_7873920 prefixEnd_7873920 4043105595049938485488507 := by
  unfold tailWord_7873920
  simp only [CollatzResearch.WordTrace]
  refine ⟨143592727817070036659709607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191456970422760048879612809 143592727817070036659709607)
  ·
    refine ⟨215389091725605054989564411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143592727817070036659709607 215389091725605054989564411)
    ·
      refine ⟨323083637588407582484346617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215389091725605054989564411 323083637588407582484346617)
      ·
        refine ⟨242312728191305686863259963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323083637588407582484346617 242312728191305686863259963)
        ·
          refine ⟨363469092286958530294889945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242312728191305686863259963 363469092286958530294889945)
          ·
            refine ⟨272601819215218897721167459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363469092286958530294889945 272601819215218897721167459)
            ·
              refine ⟨408902728822828346581751189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272601819215218897721167459 408902728822828346581751189)
              ·
                refine ⟨19167315413570078746019587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408902728822828346581751189 19167315413570078746019587)
                ·
                  refine ⟨28750973120355118119029381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19167315413570078746019587 28750973120355118119029381)
                  ·
                    refine ⟨5390807460066584647318009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28750973120355118119029381 5390807460066584647318009)
                    ·
                      refine ⟨4043105595049938485488507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390807460066584647318009 4043105595049938485488507)
                      ·
                        rfl

theorem cell23_7873920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_7873920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873920 prefixEnd_7873920 := by exact prefixLift 7873920
  have htrace : WordTrace (prefixWord ++ tailWord_7873920) baseStart_7873920 baseEnd_7873920 := by
    simpa [prefixWord, tailWord_7873920, baseEnd_7873920] using wordTrace_append hprefix tailTrace_7873920
  have hstable : (prefixWord ++ tailWord_7873920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873920).length < 2 ^ (prefixWord ++ tailWord_7873920).sum := by decide
  have hdescent : baseEnd_7873920 < baseStart_7873920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873923 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5]
def baseStart_7873923 : Nat := 118140960795 + 7873923 * 2 ^ 59
def prefixEnd_7873923 : Nat := 4983230072969 + 3 ^ 40 * 7873923 * 2
def baseEnd_7873923 : Nat := 4043107135491901973750993

theorem tailTrace_7873923 : CollatzResearch.WordTrace tailWord_7873923 prefixEnd_7873923 4043107135491901973750993 := by
  unfold tailWord_7873923
  simp only [CollatzResearch.WordTrace]
  refine ⟨287185565053129204831778423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191457043368752803221185615 287185565053129204831778423)
  ·
    refine ⟨430778347579693807247667635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287185565053129204831778423 430778347579693807247667635)
    ·
      refine ⟨646167521369540710871501453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430778347579693807247667635 646167521369540710871501453)
      ·
        refine ⟨242312820513577766576813045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646167521369540710871501453 242312820513577766576813045)
        ·
          refine ⟨22716826923147915616576223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242312820513577766576813045 22716826923147915616576223)
          ·
            refine ⟨34075240384721873424864335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22716826923147915616576223 34075240384721873424864335)
            ·
              refine ⟨51112860577082810137296503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34075240384721873424864335 51112860577082810137296503)
              ·
                refine ⟨76669290865624215205944755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51112860577082810137296503 76669290865624215205944755)
                ·
                  refine ⟨115003936298436322808917133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76669290865624215205944755 115003936298436322808917133)
                  ·
                    refine ⟨43126476111913621053343925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115003936298436322808917133 43126476111913621053343925)
                    ·
                      refine ⟨4043107135491901973750993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43126476111913621053343925 4043107135491901973750993)
                      ·
                        rfl

theorem cell23_7873923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_7873923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873923 prefixEnd_7873923 := by exact prefixLift 7873923
  have htrace : WordTrace (prefixWord ++ tailWord_7873923) baseStart_7873923 baseEnd_7873923 := by
    simpa [prefixWord, tailWord_7873923, baseEnd_7873923] using wordTrace_append hprefix tailTrace_7873923
  have hstable : (prefixWord ++ tailWord_7873923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873923).length < 2 ^ (prefixWord ++ tailWord_7873923).sum := by decide
  have hdescent : baseEnd_7873923 < baseStart_7873923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873948 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7873948 : Nat := 118140960795 + 7873948 * 2 ^ 59
def prefixEnd_7873948 : Nat := 4983230072969 + 3 ^ 40 * 7873948 * 2
def baseEnd_7873948 : Nat := 4043119972508264375938379

theorem tailTrace_7873948 : CollatzResearch.WordTrace tailWord_7873948 prefixEnd_7873948 4043119972508264375938379 := by
  unfold tailWord_7873948
  simp only [CollatzResearch.WordTrace]
  refine ⟨143593238439019317050719249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191457651252025756067625665 143593238439019317050719249)
  ·
    refine ⟨107694928829264487788039437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143593238439019317050719249 107694928829264487788039437)
    ·
      refine ⟨40385598310974182920514789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107694928829264487788039437 40385598310974182920514789)
      ·
        refine ⟨7572299683307659297596523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40385598310974182920514789 7572299683307659297596523)
        ·
          refine ⟨11358449524961488946394785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572299683307659297596523 11358449524961488946394785)
          ·
            refine ⟨8518837143721116709796089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358449524961488946394785 8518837143721116709796089)
            ·
              refine ⟨6389127857790837532347067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518837143721116709796089 6389127857790837532347067)
              ·
                refine ⟨9583691786686256298520601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389127857790837532347067 9583691786686256298520601)
                ·
                  refine ⟨7187768840014692223890451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583691786686256298520601 7187768840014692223890451)
                  ·
                    refine ⟨10781653260022038335835677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7187768840014692223890451 10781653260022038335835677)
                    ·
                      refine ⟨4043119972508264375938379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781653260022038335835677 4043119972508264375938379)
                      ·
                        rfl

theorem cell23_7873948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7873948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873948 prefixEnd_7873948 := by exact prefixLift 7873948
  have htrace : WordTrace (prefixWord ++ tailWord_7873948) baseStart_7873948 baseEnd_7873948 := by
    simpa [prefixWord, tailWord_7873948, baseEnd_7873948] using wordTrace_append hprefix tailTrace_7873948
  have hstable : (prefixWord ++ tailWord_7873948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873948).length < 2 ^ (prefixWord ++ tailWord_7873948).sum := by decide
  have hdescent : baseEnd_7873948 < baseStart_7873948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873993 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_7873993 : Nat := 118140960795 + 7873993 * 2 ^ 59
def prefixEnd_7873993 : Nat := 4983230072969 + 3 ^ 40 * 7873993 * 2
def baseEnd_7873993 : Nat := 4043143079137716699875671

theorem tailTrace_7873993 : CollatzResearch.WordTrace tailWord_7873993 prefixEnd_7873993 4043143079137716699875671 := by
  unfold tailWord_7873993
  simp only [CollatzResearch.WordTrace]
  refine ⟨287188118162875606786826633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191458745441917071191217755 287188118162875606786826633)
  ·
    refine ⟨215391088622156705090119975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287188118162875606786826633 215391088622156705090119975)
    ·
      refine ⟨323086632933235057635179963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215391088622156705090119975 323086632933235057635179963)
      ·
        refine ⟨484629949399852586452769945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323086632933235057635179963 484629949399852586452769945)
        ·
          refine ⟨363472462049889439839577459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484629949399852586452769945 363472462049889439839577459)
          ·
            refine ⟨545208693074834159759366189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363472462049889439839577459 545208693074834159759366189)
            ·
              refine ⟨204453259903062809909762321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545208693074834159759366189 204453259903062809909762321)
              ·
                refine ⟨153339944927297107432321741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204453259903062809909762321 153339944927297107432321741)
                ·
                  refine ⟨57502479347736415287120653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153339944927297107432321741 57502479347736415287120653)
                  ·
                    refine ⟨21563429755401155732670245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57502479347736415287120653 21563429755401155732670245)
                    ·
                      refine ⟨4043143079137716699875671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21563429755401155732670245 4043143079137716699875671)
                      ·
                        rfl

theorem cell23_7873993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_7873993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873993 prefixEnd_7873993 := by exact prefixLift 7873993
  have htrace : WordTrace (prefixWord ++ tailWord_7873993) baseStart_7873993 baseEnd_7873993 := by
    simpa [prefixWord, tailWord_7873993, baseEnd_7873993] using wordTrace_append hprefix tailTrace_7873993
  have hstable : (prefixWord ++ tailWord_7873993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873993).length < 2 ^ (prefixWord ++ tailWord_7873993).sum := by decide
  have hdescent : baseEnd_7873993 < baseStart_7873993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7873994 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_7873994 : Nat := 118140960795 + 7873994 * 2 ^ 59
def prefixEnd_7873994 : Nat := 4983230072969 + 3 ^ 40 * 7873994 * 2
def baseEnd_7873994 : Nat := 449238176957596799551463

theorem tailTrace_7873994 : CollatzResearch.WordTrace tailWord_7873994 prefixEnd_7873994 449238176957596799551463 := by
  unfold tailWord_7873994
  simp only [CollatzResearch.WordTrace]
  refine ⟨71797038658967995989403259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191458769757247989305075357 71797038658967995989403259)
  ·
    refine ⟨107695557988451993984104889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71797038658967995989403259 107695557988451993984104889)
    ·
      refine ⟨80771668491338995488078667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107695557988451993984104889 80771668491338995488078667)
      ·
        refine ⟨121157502737008493232118001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80771668491338995488078667 121157502737008493232118001)
        ·
          refine ⟨90868127052756369924088501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121157502737008493232118001 90868127052756369924088501)
          ·
            refine ⟨8518886911195909680383297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90868127052756369924088501 8518886911195909680383297)
            ·
              refine ⟨6389165183396932260287473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518886911195909680383297 6389165183396932260287473)
              ·
                refine ⟨4791873887547699195215605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6389165183396932260287473 4791873887547699195215605)
                ·
                  refine ⟨449238176957596799551463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791873887547699195215605 449238176957596799551463)
                  ·
                    rfl

theorem cell23_7873994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_7873994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7873994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7873994 prefixEnd_7873994 := by exact prefixLift 7873994
  have htrace : WordTrace (prefixWord ++ tailWord_7873994) baseStart_7873994 baseEnd_7873994 := by
    simpa [prefixWord, tailWord_7873994, baseEnd_7873994] using wordTrace_append hprefix tailTrace_7873994
  have hstable : (prefixWord ++ tailWord_7873994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7873994).length < 2 ^ (prefixWord ++ tailWord_7873994).sum := by decide
  have hdescent : baseEnd_7873994 < baseStart_7873994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7873994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874067 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 6]
def baseStart_7874067 : Nat := 118140960795 + 7874067 * 2 ^ 59
def prefixEnd_7874067 : Nat := 4983230072969 + 3 ^ 40 * 7874067 * 2
def baseEnd_7874067 : Nat := 449242341856238823372259

theorem tailTrace_7874067 : CollatzResearch.WordTrace tailWord_7874067 prefixEnd_7874067 449242341856238823372259 := by
  unfold tailWord_7874067
  simp only [CollatzResearch.WordTrace]
  refine ⟨287190817164607517425020455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191460544776405011616680303 287190817164607517425020455)
  ·
    refine ⟨430786225746911276137530683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287190817164607517425020455 430786225746911276137530683)
    ·
      refine ⟨646179338620366914206296025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430786225746911276137530683 646179338620366914206296025)
      ·
        refine ⟨484634503965275185654722019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646179338620366914206296025 484634503965275185654722019)
        ·
          refine ⟨726951755947912778482083029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484634503965275185654722019 726951755947912778482083029)
          ·
            refine ⟨17037931780029205745673821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 726951755947912778482083029 17037931780029205745673821)
            ·
              refine ⟨6389224417510952154627683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17037931780029205745673821 6389224417510952154627683)
              ·
                refine ⟨9583836626266428231941525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389224417510952154627683 9583836626266428231941525)
                ·
                  refine ⟨449242341856238823372259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9583836626266428231941525 449242341856238823372259)
                  ·
                    rfl

theorem cell23_7874067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 6].length) (baseStart_7874067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874067 prefixEnd_7874067 := by exact prefixLift 7874067
  have htrace : WordTrace (prefixWord ++ tailWord_7874067) baseStart_7874067 baseEnd_7874067 := by
    simpa [prefixWord, tailWord_7874067, baseEnd_7874067] using wordTrace_append hprefix tailTrace_7874067
  have hstable : (prefixWord ++ tailWord_7874067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874067).length < 2 ^ (prefixWord ++ tailWord_7874067).sum := by decide
  have hdescent : baseEnd_7874067 < baseStart_7874067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874088 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7874088 : Nat := 118140960795 + 7874088 * 2 ^ 59
def prefixEnd_7874088 : Nat := 4983230072969 + 3 ^ 40 * 7874088 * 2
def baseEnd_7874088 : Nat := 1347730619933297942729245

theorem tailTrace_7874088 : CollatzResearch.WordTrace tailWord_7874088 prefixEnd_7874088 1347730619933297942729245 := by
  unfold tailWord_7874088
  simp only [CollatzResearch.WordTrace]
  refine ⟨143595791548765719005767459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191461055398354292007689945 143595791548765719005767459)
  ·
    refine ⟨215393687323148578508651189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143595791548765719005767459 215393687323148578508651189)
    ·
      refine ⟨20193158186545179235186049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215393687323148578508651189 20193158186545179235186049)
      ·
        refine ⟨15144868639908884426389537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20193158186545179235186049 15144868639908884426389537)
        ·
          refine ⟨11358651479931663319792153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15144868639908884426389537 11358651479931663319792153)
          ·
            refine ⟨8518988609948747489844115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358651479931663319792153 8518988609948747489844115)
            ·
              refine ⟨12778482914923121234766173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518988609948747489844115 12778482914923121234766173)
              ·
                refine ⟨4791931093096170463037315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12778482914923121234766173 4791931093096170463037315)
                ·
                  refine ⟨7187896639644255694555973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791931093096170463037315 7187896639644255694555973)
                  ·
                    refine ⟨1347730619933297942729245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7187896639644255694555973 1347730619933297942729245)
                    ·
                      rfl

theorem cell23_7874088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7874088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874088 prefixEnd_7874088 := by exact prefixLift 7874088
  have htrace : WordTrace (prefixWord ++ tailWord_7874088) baseStart_7874088 baseEnd_7874088 := by
    simpa [prefixWord, tailWord_7874088, baseEnd_7874088] using wordTrace_append hprefix tailTrace_7874088
  have hstable : (prefixWord ++ tailWord_7874088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874088).length < 2 ^ (prefixWord ++ tailWord_7874088).sum := by decide
  have hdescent : baseEnd_7874088 < baseStart_7874088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874104 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 2, 3, 2]
def baseStart_7874104 : Nat := 118140960795 + 7874104 * 2 ^ 59
def prefixEnd_7874104 : Nat := 4983230072969 + 3 ^ 40 * 7874104 * 2
def baseEnd_7874104 : Nat := 4043200075490365765587661

theorem tailTrace_7874104 : CollatzResearch.WordTrace tailWord_7874104 prefixEnd_7874104 4043200075490365765587661 := by
  unfold tailWord_7874104
  simp only [CollatzResearch.WordTrace]
  refine ⟨143596083332736736372058683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191461444443648981829411577 143596083332736736372058683)
  ·
    refine ⟨215394124999105104558088025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143596083332736736372058683 215394124999105104558088025)
    ·
      refine ⟨161545593749328828418566019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215394124999105104558088025 161545593749328828418566019)
      ·
        refine ⟨242318390623993242627849029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161545593749328828418566019 242318390623993242627849029)
        ·
          refine ⟨45434698241998732992721693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242318390623993242627849029 45434698241998732992721693)
          ·
            refine ⟨17038011840749524872270635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45434698241998732992721693 17038011840749524872270635)
            ·
              refine ⟨25557017761124287308405953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038011840749524872270635 25557017761124287308405953)
              ·
                refine ⟨19167763320843215481304465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25557017761124287308405953 19167763320843215481304465)
                ·
                  refine ⟨14375822490632411610978349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19167763320843215481304465 14375822490632411610978349)
                  ·
                    refine ⟨5390933433987154354116881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14375822490632411610978349 5390933433987154354116881)
                    ·
                      refine ⟨4043200075490365765587661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5390933433987154354116881 4043200075490365765587661)
                      ·
                        rfl

theorem cell23_7874104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_7874104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874104 prefixEnd_7874104 := by exact prefixLift 7874104
  have htrace : WordTrace (prefixWord ++ tailWord_7874104) baseStart_7874104 baseEnd_7874104 := by
    simpa [prefixWord, tailWord_7874104, baseEnd_7874104] using wordTrace_append hprefix tailTrace_7874104
  have hstable : (prefixWord ++ tailWord_7874104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874104).length < 2 ^ (prefixWord ++ tailWord_7874104).sum := by decide
  have hdescent : baseEnd_7874104 < baseStart_7874104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874118 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_7874118 : Nat := 118140960795 + 7874118 * 2 ^ 59
def prefixEnd_7874118 : Nat := 4983230072969 + 3 ^ 40 * 7874118 * 2
def baseEnd_7874118 : Nat := 449245251579947634534733

theorem tailTrace_7874118 : CollatzResearch.WordTrace tailWord_7874118 prefixEnd_7874118 449245251579947634534733 := by
  unfold tailWord_7874118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974771165231961035472719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191461784858281835423418005 8974771165231961035472719)
  ·
    refine ⟨13462156747847941553209079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8974771165231961035472719 13462156747847941553209079)
    ·
      refine ⟨20193235121771912329813619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13462156747847941553209079 20193235121771912329813619)
      ·
        refine ⟨30289852682657868494720429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20193235121771912329813619 30289852682657868494720429)
        ·
          refine ⟨11358694755996700685520161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30289852682657868494720429 11358694755996700685520161)
          ·
            refine ⟨8519021066997525514140121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358694755996700685520161 8519021066997525514140121)
            ·
              refine ⟨6389265800248144135605091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8519021066997525514140121 6389265800248144135605091)
              ·
                refine ⟨9583898700372216203407637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389265800248144135605091 9583898700372216203407637)
                ·
                  refine ⟨449245251579947634534733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9583898700372216203407637 449245251579947634534733)
                  ·
                    rfl

theorem cell23_7874118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_7874118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874118 prefixEnd_7874118 := by exact prefixLift 7874118
  have htrace : WordTrace (prefixWord ++ tailWord_7874118) baseStart_7874118 baseEnd_7874118 := by
    simpa [prefixWord, tailWord_7874118, baseEnd_7874118] using wordTrace_append hprefix tailTrace_7874118
  have hstable : (prefixWord ++ tailWord_7874118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874118).length < 2 ^ (prefixWord ++ tailWord_7874118).sum := by decide
  have hdescent : baseEnd_7874118 < baseStart_7874118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874120 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_7874120 : Nat := 118140960795 + 7874120 * 2 ^ 59
def prefixEnd_7874120 : Nat := 4983230072969 + 3 ^ 40 * 7874120 * 2
def baseEnd_7874120 : Nat := 4043208291180837702987587

theorem tailTrace_7874120 : CollatzResearch.WordTrace tailWord_7874120 prefixEnd_7874120 4043208291180837702987587 := by
  unfold tailWord_7874120
  simp only [CollatzResearch.WordTrace]
  refine ⟨143596375116707753738349907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191461833488943671651133209 143596375116707753738349907)
  ·
    refine ⟨215394562675061630607524861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143596375116707753738349907 215394562675061630607524861)
    ·
      refine ⟨80772961003148111477821823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215394562675061630607524861 80772961003148111477821823)
      ·
        refine ⟨121159441504722167216732735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80772961003148111477821823 121159441504722167216732735)
        ·
          refine ⟨181739162257083250825099103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121159441504722167216732735 181739162257083250825099103)
          ·
            refine ⟨272608743385624876237648655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181739162257083250825099103 272608743385624876237648655)
            ·
              refine ⟨408913115078437314356472983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272608743385624876237648655 408913115078437314356472983)
              ·
                refine ⟨613369672617655971534709475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408913115078437314356472983 613369672617655971534709475)
                ·
                  refine ⟨920054508926483957302064213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613369672617655971534709475 920054508926483957302064213)
                  ·
                    refine ⟨10781888776482233874633565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 920054508926483957302064213 10781888776482233874633565)
                    ·
                      refine ⟨4043208291180837702987587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10781888776482233874633565 4043208291180837702987587)
                      ·
                        rfl

theorem cell23_7874120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_7874120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874120 prefixEnd_7874120 := by exact prefixLift 7874120
  have htrace : WordTrace (prefixWord ++ tailWord_7874120) baseStart_7874120 baseEnd_7874120 := by
    simpa [prefixWord, tailWord_7874120, baseEnd_7874120] using wordTrace_append hprefix tailTrace_7874120
  have hstable : (prefixWord ++ tailWord_7874120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874120).length < 2 ^ (prefixWord ++ tailWord_7874120).sum := by decide
  have hdescent : baseEnd_7874120 < baseStart_7874120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874147 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7874147 : Nat := 118140960795 + 7874147 * 2 ^ 59
def prefixEnd_7874147 : Nat := 4983230072969 + 3 ^ 40 * 7874147 * 2
def baseEnd_7874147 : Nat := 4043222155158509097349963

theorem tailTrace_7874147 : CollatzResearch.WordTrace tailWord_7874147 prefixEnd_7874147 4043222155158509097349963 := by
  unfold tailWord_7874147
  simp only [CollatzResearch.WordTrace]
  refine ⟨287193735004317691087932695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191462490002878460725288463 287193735004317691087932695)
  ·
    refine ⟨430790602506476536631899043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287193735004317691087932695 430790602506476536631899043)
    ·
      refine ⟨646185903759714804947848565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430790602506476536631899043 646185903759714804947848565)
      ·
        refine ⟨60579928477473262963860803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 646185903759714804947848565 60579928477473262963860803)
        ·
          refine ⟨90869892716209894445791205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60579928477473262963860803 90869892716209894445791205)
          ·
            refine ⟨17038104884289355208585851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90869892716209894445791205 17038104884289355208585851)
            ·
              refine ⟨25557157326434032812878777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038104884289355208585851 25557157326434032812878777)
              ·
                refine ⟨19167867994825524609659083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25557157326434032812878777 19167867994825524609659083)
                ·
                  refine ⟨28751801992238286914488625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19167867994825524609659083 28751801992238286914488625)
                  ·
                    refine ⟨21563851494178715185866469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28751801992238286914488625 21563851494178715185866469)
                    ·
                      refine ⟨4043222155158509097349963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21563851494178715185866469 4043222155158509097349963)
                      ·
                        rfl

theorem cell23_7874147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7874147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874147 prefixEnd_7874147 := by exact prefixLift 7874147
  have htrace : WordTrace (prefixWord ++ tailWord_7874147) baseStart_7874147 baseEnd_7874147 := by
    simpa [prefixWord, tailWord_7874147, baseEnd_7874147] using wordTrace_append hprefix tailTrace_7874147
  have hstable : (prefixWord ++ tailWord_7874147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874147).length < 2 ^ (prefixWord ++ tailWord_7874147).sum := by decide
  have hdescent : baseEnd_7874147 < baseStart_7874147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874154 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_7874154 : Nat := 118140960795 + 7874154 * 2 ^ 59
def prefixEnd_7874154 : Nat := 4983230072969 + 3 ^ 40 * 7874154 * 2
def baseEnd_7874154 : Nat := 4043225749523090569962431

theorem tailTrace_7874154 : CollatzResearch.WordTrace tailWord_7874154 prefixEnd_7874154 4043225749523090569962431 := by
  unfold tailWord_7874154
  simp only [CollatzResearch.WordTrace]
  refine ⟨71798497578823082820859379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191462660210194887522291677 71798497578823082820859379)
  ·
    refine ⟨107697746368234624231289069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71798497578823082820859379 107697746368234624231289069)
    ·
      refine ⟨40386654888087984086733401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107697746368234624231289069 40386654888087984086733401)
      ·
        refine ⟨30289991166065988065050051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40386654888087984086733401 30289991166065988065050051)
        ·
          refine ⟨45434986749098982097575077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30289991166065988065050051 45434986749098982097575077)
          ·
            refine ⟨8519060015456059143295327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45434986749098982097575077 8519060015456059143295327)
            ·
              refine ⟨12778590023184088714942991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519060015456059143295327 12778590023184088714942991)
              ·
                refine ⟨19167885034776133072414487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12778590023184088714942991 19167885034776133072414487)
                ·
                  refine ⟨28751827552164199608621731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19167885034776133072414487 28751827552164199608621731)
                  ·
                    refine ⟨43127741328246299412932597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28751827552164199608621731 43127741328246299412932597)
                    ·
                      refine ⟨4043225749523090569962431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43127741328246299412932597 4043225749523090569962431)
                      ·
                        rfl

theorem cell23_7874154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_7874154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874154 prefixEnd_7874154 := by exact prefixLift 7874154
  have htrace : WordTrace (prefixWord ++ tailWord_7874154) baseStart_7874154 baseEnd_7874154 := by
    simpa [prefixWord, tailWord_7874154, baseEnd_7874154] using wordTrace_append hprefix tailTrace_7874154
  have hstable : (prefixWord ++ tailWord_7874154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874154).length < 2 ^ (prefixWord ++ tailWord_7874154).sum := by decide
  have hdescent : baseEnd_7874154 < baseStart_7874154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874157 : List Nat := [1, 5, 1, 1, 5, 10]
def baseStart_7874157 : Nat := 118140960795 + 7874157 * 2 ^ 59
def prefixEnd_7874157 : Nat := 4983230072969 + 3 ^ 40 * 7874157 * 2
def baseEnd_7874157 : Nat := 16638795431954954972119

theorem tailTrace_7874157 : CollatzResearch.WordTrace tailWord_7874157 prefixEnd_7874157 16638795431954954972119 := by
  unfold tailWord_7874157
  simp only [CollatzResearch.WordTrace]
  refine ⟨287194099734281462795796725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191462733156187641863864483 287194099734281462795796725)
  ·
    refine ⟨26924446850088887137105943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287194099734281462795796725 26924446850088887137105943)
    ·
      refine ⟨40386670275133330705658915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26924446850088887137105943 40386670275133330705658915)
      ·
        refine ⟨60580005412699996058488373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40386670275133330705658915 60580005412699996058488373)
        ·
          refine ⟨5679375507440624630483285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60580005412699996058488373 5679375507440624630483285)
          ·
            refine ⟨16638795431954954972119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5679375507440624630483285 16638795431954954972119)
            ·
              rfl

theorem cell23_7874157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 10].length) (baseStart_7874157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874157 prefixEnd_7874157 := by exact prefixLift 7874157
  have htrace : WordTrace (prefixWord ++ tailWord_7874157) baseStart_7874157 baseEnd_7874157 := by
    simpa [prefixWord, tailWord_7874157, baseEnd_7874157] using wordTrace_append hprefix tailTrace_7874157
  have hstable : (prefixWord ++ tailWord_7874157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874157).length < 2 ^ (prefixWord ++ tailWord_7874157).sum := by decide
  have hdescent : baseEnd_7874157 < baseStart_7874157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874237 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7874237 : Nat := 118140960795 + 7874237 * 2 ^ 59
def prefixEnd_7874237 : Nat := 4983230072969 + 3 ^ 40 * 7874237 * 2
def baseEnd_7874237 : Nat := 4043268368417413745224549

theorem tailTrace_7874237 : CollatzResearch.WordTrace tailWord_7874237 prefixEnd_7874237 4043268368417413745224549 := by
  unfold tailWord_7874237
  simp only [CollatzResearch.WordTrace]
  refine ⟨287197017573991636458708965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191464678382661090972472643 287197017573991636458708965)
  ·
    refine ⟨53849440795123431836007931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287197017573991636458708965 53849440795123431836007931)
    ·
      refine ⟨80774161192685147754011897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53849440795123431836007931 80774161192685147754011897)
      ·
        refine ⟨60580620894513860815508923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80774161192685147754011897 60580620894513860815508923)
        ·
          refine ⟨90870931341770791223263385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60580620894513860815508923 90870931341770791223263385)
          ·
            refine ⟨68153198506328093417447539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90870931341770791223263385 68153198506328093417447539)
            ·
              refine ⟨102229797759492140126171309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68153198506328093417447539 102229797759492140126171309)
              ·
                refine ⟨38336174159809552547314241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102229797759492140126171309 38336174159809552547314241)
                ·
                  refine ⟨28752130619857164410485681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38336174159809552547314241 28752130619857164410485681)
                  ·
                    refine ⟨21564097964892873307864261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28752130619857164410485681 21564097964892873307864261)
                    ·
                      refine ⟨4043268368417413745224549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21564097964892873307864261 4043268368417413745224549)
                      ·
                        rfl

theorem cell23_7874237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7874237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874237 prefixEnd_7874237 := by exact prefixLift 7874237
  have htrace : WordTrace (prefixWord ++ tailWord_7874237) baseStart_7874237 baseEnd_7874237 := by
    simpa [prefixWord, tailWord_7874237, baseEnd_7874237] using wordTrace_append hprefix tailTrace_7874237
  have hstable : (prefixWord ++ tailWord_7874237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874237).length < 2 ^ (prefixWord ++ tailWord_7874237).sum := by decide
  have hdescent : baseEnd_7874237 < baseStart_7874237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874287 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_7874287 : Nat := 118140960795 + 7874287 * 2 ^ 59
def prefixEnd_7874287 : Nat := 4983230072969 + 3 ^ 40 * 7874287 * 2
def baseEnd_7874287 : Nat := 4043294042450138549599319

theorem tailTrace_7874287 : CollatzResearch.WordTrace tailWord_7874287 prefixEnd_7874287 4043294042450138549599319 := by
  unfold tailWord_7874287
  simp only [CollatzResearch.WordTrace]
  refine ⟨287198841223810494998029115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191465894149206996665352743 287198841223810494998029115)
  ·
    refine ⟨430798261835715742497043673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287198841223810494998029115 430798261835715742497043673)
    ·
      refine ⟨323098696376786806872782755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430798261835715742497043673 323098696376786806872782755)
      ·
        refine ⟨484648044565180210309174133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323098696376786806872782755 484648044565180210309174133)
        ·
          refine ⟨45435754177985644716485075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484648044565180210309174133 45435754177985644716485075)
          ·
            refine ⟨68153631266978467074727613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45435754177985644716485075 68153631266978467074727613)
            ·
              refine ⟨25557611725116925153022855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68153631266978467074727613 25557611725116925153022855)
              ·
                refine ⟨38336417587675387729534283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25557611725116925153022855 38336417587675387729534283)
                ·
                  refine ⟨57504626381513081594301425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38336417587675387729534283 57504626381513081594301425)
                  ·
                    refine ⟨43128469786134811195726069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57504626381513081594301425 43128469786134811195726069)
                    ·
                      refine ⟨4043294042450138549599319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43128469786134811195726069 4043294042450138549599319)
                      ·
                        rfl

theorem cell23_7874287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_7874287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874287 prefixEnd_7874287 := by exact prefixLift 7874287
  have htrace : WordTrace (prefixWord ++ tailWord_7874287) baseStart_7874287 baseEnd_7874287 := by
    simpa [prefixWord, tailWord_7874287, baseEnd_7874287] using wordTrace_append hprefix tailTrace_7874287
  have hstable : (prefixWord ++ tailWord_7874287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874287).length < 2 ^ (prefixWord ++ tailWord_7874287).sum := by decide
  have hdescent : baseEnd_7874287 < baseStart_7874287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874292 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7874292 : Nat := 118140960795 + 7874292 * 2 ^ 59
def prefixEnd_7874292 : Nat := 4983230072969 + 3 ^ 40 * 7874292 * 2
def baseEnd_7874292 : Nat := 4043296609853411030036797

theorem tailTrace_7874292 : CollatzResearch.WordTrace tailWord_7874292 prefixEnd_7874292 4043296609853411030036797 := by
  unfold tailWord_7874292
  simp only [CollatzResearch.WordTrace]
  refine ⟨143599511794396190425980565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191466015725861587234640753 143599511794396190425980565)
  ·
    refine ⟨6731227115362321426217839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143599511794396190425980565 6731227115362321426217839)
    ·
      refine ⟨10096840673043482139326759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6731227115362321426217839 10096840673043482139326759)
      ·
        refine ⟨15145261009565223208990139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10096840673043482139326759 15145261009565223208990139)
        ·
          refine ⟨22717891514347834813485209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15145261009565223208990139 22717891514347834813485209)
          ·
            refine ⟨17038418635760876110113907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22717891514347834813485209 17038418635760876110113907)
            ·
              refine ⟨25557627953641314165170861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038418635760876110113907 25557627953641314165170861)
              ·
                refine ⟨9584110482615492811939073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25557627953641314165170861 9584110482615492811939073)
                ·
                  refine ⟨7188082861961619608954305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9584110482615492811939073 7188082861961619608954305)
                  ·
                    refine ⟨5391062146471214706715729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7188082861961619608954305 5391062146471214706715729)
                    ·
                      refine ⟨4043296609853411030036797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391062146471214706715729 4043296609853411030036797)
                      ·
                        rfl

theorem cell23_7874292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7874292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874292 prefixEnd_7874292 := by exact prefixLift 7874292
  have htrace : WordTrace (prefixWord ++ tailWord_7874292) baseStart_7874292 baseEnd_7874292 := by
    simpa [prefixWord, tailWord_7874292, baseEnd_7874292] using wordTrace_append hprefix tailTrace_7874292
  have hstable : (prefixWord ++ tailWord_7874292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874292).length < 2 ^ (prefixWord ++ tailWord_7874292).sum := by decide
  have hdescent : baseEnd_7874292 < baseStart_7874292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874311 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 2, 5]
def baseStart_7874311 : Nat := 118140960795 + 7874311 * 2 ^ 59
def prefixEnd_7874311 : Nat := 4983230072969 + 3 ^ 40 * 7874311 * 2
def baseEnd_7874311 : Nat := 1347768788661948818566403

theorem tailTrace_7874311 : CollatzResearch.WordTrace tailWord_7874311 prefixEnd_7874311 1347768788661948818566403 := by
  unfold tailWord_7874311
  simp only [CollatzResearch.WordTrace]
  refine ⟨287199716575723547096902787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191466477717149031397935191 287199716575723547096902787)
  ·
    refine ⟨430799574863585320645354181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287199716575723547096902787 430799574863585320645354181)
    ·
      refine ⟨80774920286922247621003909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430799574863585320645354181 80774920286922247621003909)
      ·
        refine ⟨15145297553797921428938233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80774920286922247621003909 15145297553797921428938233)
        ·
          refine ⟨11358973165348441071703675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15145297553797921428938233 11358973165348441071703675)
          ·
            refine ⟨17038459748022661607555513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11358973165348441071703675 17038459748022661607555513)
            ·
              refine ⟨12778844811016996205666635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17038459748022661607555513 12778844811016996205666635)
              ·
                refine ⟨19168267216525494308499953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12778844811016996205666635 19168267216525494308499953)
                ·
                  refine ⟨14376200412394120731374965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19168267216525494308499953 14376200412394120731374965)
                  ·
                    refine ⟨1347768788661948818566403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14376200412394120731374965 1347768788661948818566403)
                    ·
                      rfl

theorem cell23_7874311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_7874311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874311 prefixEnd_7874311 := by exact prefixLift 7874311
  have htrace : WordTrace (prefixWord ++ tailWord_7874311) baseStart_7874311 baseEnd_7874311 := by
    simpa [prefixWord, tailWord_7874311, baseEnd_7874311] using wordTrace_append hprefix tailTrace_7874311
  have hstable : (prefixWord ++ tailWord_7874311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874311).length < 2 ^ (prefixWord ++ tailWord_7874311).sum := by decide
  have hdescent : baseEnd_7874311 < baseStart_7874311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874314 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7874314 : Nat := 118140960795 + 7874314 * 2 ^ 59
def prefixEnd_7874314 : Nat := 4983230072969 + 3 ^ 40 * 7874314 * 2
def baseEnd_7874314 : Nat := 4043307906427809943961695

theorem tailTrace_7874314 : CollatzResearch.WordTrace tailWord_7874314 prefixEnd_7874314 4043307906427809943961695 := by
  unfold tailWord_7874314
  simp only [CollatzResearch.WordTrace]
  refine ⟨71799956498678169652315499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191466550663141785739507997 71799956498678169652315499)
  ·
    refine ⟨107699934748017254478473249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71799956498678169652315499 107699934748017254478473249)
    ·
      refine ⟨80774951061012940858854937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107699934748017254478473249 80774951061012940858854937)
      ·
        refine ⟨60581213295759705644141203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80774951061012940858854937 60581213295759705644141203)
        ·
          refine ⟨90871819943639558466211805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60581213295759705644141203 90871819943639558466211805)
          ·
            refine ⟨34076932478864834424829427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90871819943639558466211805 34076932478864834424829427)
            ·
              refine ⟨51115398718297251637244141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34076932478864834424829427 51115398718297251637244141)
              ·
                refine ⟨19168274519361469363966553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51115398718297251637244141 19168274519361469363966553)
                ·
                  refine ⟨14376205889521102022974915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19168274519361469363966553 14376205889521102022974915)
                  ·
                    refine ⟨21564308834281653034462373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14376205889521102022974915 21564308834281653034462373)
                    ·
                      refine ⟨4043307906427809943961695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21564308834281653034462373 4043307906427809943961695)
                      ·
                        rfl

theorem cell23_7874314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7874314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874314 prefixEnd_7874314 := by exact prefixLift 7874314
  have htrace : WordTrace (prefixWord ++ tailWord_7874314) baseStart_7874314 baseEnd_7874314 := by
    simpa [prefixWord, tailWord_7874314, baseEnd_7874314] using wordTrace_append hprefix tailTrace_7874314
  have hstable : (prefixWord ++ tailWord_7874314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874314).length < 2 ^ (prefixWord ++ tailWord_7874314).sum := by decide
  have hdescent : baseEnd_7874314 < baseStart_7874314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874354 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_7874354 : Nat := 118140960795 + 7874354 * 2 ^ 59
def prefixEnd_7874354 : Nat := 4983230072969 + 3 ^ 40 * 7874354 * 2
def baseEnd_7874354 : Nat := 449258716183776643051279

theorem tailTrace_7874354 : CollatzResearch.WordTrace tailWord_7874354 prefixEnd_7874354 449258716183776643051279 := by
  unfold tailWord_7874354
  simp only [CollatzResearch.WordTrace]
  refine ⟨71800321228641941360179529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191467523276378510293812077 71800321228641941360179529)
  ·
    refine ⟨53850240921481456020134647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71800321228641941360179529 53850240921481456020134647)
    ·
      refine ⟨80775361382222184030201971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53850240921481456020134647 80775361382222184030201971)
      ·
        refine ⟨121163042073333276045302957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80775361382222184030201971 121163042073333276045302957)
        ·
          refine ⟨45436140777499978516988609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121163042073333276045302957 45436140777499978516988609)
          ·
            refine ⟨34077105583124983887741457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45436140777499978516988609 34077105583124983887741457)
            ·
              refine ⟨25557829187343737915806093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34077105583124983887741457 25557829187343737915806093)
              ·
                refine ⟨9584185945253901718427285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25557829187343737915806093 9584185945253901718427285)
                ·
                  refine ⟨449258716183776643051279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9584185945253901718427285 449258716183776643051279)
                  ·
                    rfl

theorem cell23_7874354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_7874354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874354 prefixEnd_7874354 := by exact prefixLift 7874354
  have htrace : WordTrace (prefixWord ++ tailWord_7874354) baseStart_7874354 baseEnd_7874354 := by
    simpa [prefixWord, tailWord_7874354, baseEnd_7874354] using wordTrace_append hprefix tailTrace_7874354
  have hstable : (prefixWord ++ tailWord_7874354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874354).length < 2 ^ (prefixWord ++ tailWord_7874354).sum := by decide
  have hdescent : baseEnd_7874354 < baseStart_7874354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874358 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_7874358 : Nat := 118140960795 + 7874358 * 2 ^ 59
def prefixEnd_7874358 : Nat := 4983230072969 + 3 ^ 40 * 7874358 * 2
def baseEnd_7874358 : Nat := 1347776833192202590603831

theorem tailTrace_7874358 : CollatzResearch.WordTrace tailWord_7874358 prefixEnd_7874358 1347776833192202590603831 := by
  unfold tailWord_7874358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950089425409579632741483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191467620537702182749242485 17950089425409579632741483)
  ·
    refine ⟨26925134138114369449112225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17950089425409579632741483 26925134138114369449112225)
    ·
      refine ⟨20193850603585777086834169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26925134138114369449112225 20193850603585777086834169)
      ·
        refine ⟨15145387952689332815125627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20193850603585777086834169 15145387952689332815125627)
        ·
          refine ⟨22718081929033999222688441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15145387952689332815125627 22718081929033999222688441)
          ·
            refine ⟨17038561446775499417016331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22718081929033999222688441 17038561446775499417016331)
            ·
              refine ⟨25557842170163249125524497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038561446775499417016331 25557842170163249125524497)
              ·
                refine ⟨19168381627622436844143373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25557842170163249125524497 19168381627622436844143373)
                ·
                  refine ⟨7188143110358413816553765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19168381627622436844143373 7188143110358413816553765)
                  ·
                    refine ⟨1347776833192202590603831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7188143110358413816553765 1347776833192202590603831)
                    ·
                      rfl

theorem cell23_7874358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_7874358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874358 prefixEnd_7874358 := by exact prefixLift 7874358
  have htrace : WordTrace (prefixWord ++ tailWord_7874358) baseStart_7874358 baseEnd_7874358 := by
    simpa [prefixWord, tailWord_7874358, baseEnd_7874358] using wordTrace_append hprefix tailTrace_7874358
  have hstable : (prefixWord ++ tailWord_7874358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874358).length < 2 ^ (prefixWord ++ tailWord_7874358).sum := by decide
  have hdescent : baseEnd_7874358 < baseStart_7874358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874421 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_7874421 : Nat := 118140960795 + 7874421 * 2 ^ 59
def prefixEnd_7874421 : Nat := 4983230072969 + 3 ^ 40 * 7874421 * 2
def baseEnd_7874421 : Nat := 4043362848857841025323703

theorem tailTrace_7874421 : CollatzResearch.WordTrace tailWord_7874421 prefixEnd_7874421 4043362848857841025323703 := by
  unfold tailWord_7874421
  simp only [CollatzResearch.WordTrace]
  refine ⟨287203728605325035883407117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191469152403550023922271411 287203728605325035883407117)
  ·
    refine ⟨107701398226996888456277669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287203728605325035883407117 107701398226996888456277669)
    ·
      refine ⟨20194012167561916585552063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107701398226996888456277669 20194012167561916585552063)
      ·
        refine ⟨30291018251342874878328095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20194012167561916585552063 30291018251342874878328095)
        ·
          refine ⟨45436527377014312317492143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30291018251342874878328095 45436527377014312317492143)
          ·
            refine ⟨68154791065521468476238215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45436527377014312317492143 68154791065521468476238215)
            ·
              refine ⟨102232186598282202714357323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68154791065521468476238215 102232186598282202714357323)
              ·
                refine ⟨153348279897423304071535985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102232186598282202714357323 153348279897423304071535985)
                ·
                  refine ⟨115011209923067478053651989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153348279897423304071535985 115011209923067478053651989)
                  ·
                    refine ⟨5391150465143788033764937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115011209923067478053651989 5391150465143788033764937)
                    ·
                      refine ⟨4043362848857841025323703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391150465143788033764937 4043362848857841025323703)
                      ·
                        rfl

theorem cell23_7874421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_7874421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874421 prefixEnd_7874421 := by exact prefixLift 7874421
  have htrace : WordTrace (prefixWord ++ tailWord_7874421) baseStart_7874421 baseEnd_7874421 := by
    simpa [prefixWord, tailWord_7874421, baseEnd_7874421] using wordTrace_append hprefix tailTrace_7874421
  have hstable : (prefixWord ++ tailWord_7874421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874421).length < 2 ^ (prefixWord ++ tailWord_7874421).sum := by decide
  have hdescent : baseEnd_7874421 < baseStart_7874421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874424 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_7874424 : Nat := 118140960795 + 7874424 * 2 ^ 59
def prefixEnd_7874424 : Nat := 4983230072969 + 3 ^ 40 * 7874424 * 2
def baseEnd_7874424 : Nat := 4043364389299804513586189

theorem tailTrace_7874424 : CollatzResearch.WordTrace tailWord_7874424 prefixEnd_7874424 4043364389299804513586189 := by
  unfold tailWord_7874424
  simp only [CollatzResearch.WordTrace]
  refine ⟨143601919012157083697883163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191469225349542778263844217 143601919012157083697883163)
  ·
    refine ⟨215402878518235625546824745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143601919012157083697883163 215402878518235625546824745)
    ·
      refine ⟨161552158888676719160118559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215402878518235625546824745 161552158888676719160118559)
      ·
        refine ⟨242328238333015078740177839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161552158888676719160118559 242328238333015078740177839)
        ·
          refine ⟨363492357499522618110266759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242328238333015078740177839 363492357499522618110266759)
          ·
            refine ⟨545238536249283927165400139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363492357499522618110266759 545238536249283927165400139)
            ·
              refine ⟨817857804373925890748100209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545238536249283927165400139 817857804373925890748100209)
              ·
                refine ⟨613393353280444418061075157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817857804373925890748100209 613393353280444418061075157)
                ·
                  refine ⟨14376406717510416048306449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 613393353280444418061075157 14376406717510416048306449)
                  ·
                    refine ⟨10782305038132812036229837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14376406717510416048306449 10782305038132812036229837)
                    ·
                      refine ⟨4043364389299804513586189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10782305038132812036229837 4043364389299804513586189)
                      ·
                        rfl

theorem cell23_7874424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_7874424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874424 prefixEnd_7874424 := by exact prefixLift 7874424
  have htrace : WordTrace (prefixWord ++ tailWord_7874424) baseStart_7874424 baseEnd_7874424 := by
    simpa [prefixWord, tailWord_7874424, baseEnd_7874424] using wordTrace_append hprefix tailTrace_7874424
  have hstable : (prefixWord ++ tailWord_7874424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874424).length < 2 ^ (prefixWord ++ tailWord_7874424).sum := by decide
  have hdescent : baseEnd_7874424 < baseStart_7874424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874441 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 3]
def baseStart_7874441 : Nat := 118140960795 + 7874441 * 2 ^ 59
def prefixEnd_7874441 : Nat := 4983230072969 + 3 ^ 40 * 7874441 * 2
def baseEnd_7874441 : Nat := 4043373118470930947073611

theorem tailTrace_7874441 : CollatzResearch.WordTrace tailWord_7874441 prefixEnd_7874441 4043373118470930947073611 := by
  unfold tailWord_7874441
  simp only [CollatzResearch.WordTrace]
  refine ⟨287204458065252579299135177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191469638710168386199423451 287204458065252579299135177)
  ·
    refine ⟨215403343548939434474351383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287204458065252579299135177 215403343548939434474351383)
    ·
      refine ⟨323105015323409151711527075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215403343548939434474351383 323105015323409151711527075)
      ·
        refine ⟨484657522985113727567290613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323105015323409151711527075 484657522985113727567290613)
        ·
          refine ⟨45436642779854411959433495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484657522985113727567290613 45436642779854411959433495)
          ·
            refine ⟨68154964169781617939150243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45436642779854411959433495 68154964169781617939150243)
            ·
              refine ⟨102232446254672426908725365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68154964169781617939150243 102232446254672426908725365)
              ·
                refine ⟨9584291836375540022693003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102232446254672426908725365 9584291836375540022693003)
                ·
                  refine ⟨14376437754563310034039505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9584291836375540022693003 14376437754563310034039505)
                  ·
                    refine ⟨10782328315922482525529629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14376437754563310034039505 10782328315922482525529629)
                    ·
                      refine ⟨4043373118470930947073611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10782328315922482525529629 4043373118470930947073611)
                      ·
                        rfl

theorem cell23_7874441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_7874441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874441 prefixEnd_7874441 := by exact prefixLift 7874441
  have htrace : WordTrace (prefixWord ++ tailWord_7874441) baseStart_7874441 baseEnd_7874441 := by
    simpa [prefixWord, tailWord_7874441, baseEnd_7874441] using wordTrace_append hprefix tailTrace_7874441
  have hstable : (prefixWord ++ tailWord_7874441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874441).length < 2 ^ (prefixWord ++ tailWord_7874441).sum := by decide
  have hdescent : baseEnd_7874441 < baseStart_7874441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874455 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 3, 2, 2]
def baseStart_7874455 : Nat := 118140960795 + 7874455 * 2 ^ 59
def prefixEnd_7874455 : Nat := 4983230072969 + 3 ^ 40 * 7874455 * 2
def baseEnd_7874455 : Nat := 4043380307200093892298547

theorem tailTrace_7874455 : CollatzResearch.WordTrace tailWord_7874455 prefixEnd_7874455 4043380307200093892298547 := by
  unfold tailWord_7874455
  simp only [CollatzResearch.WordTrace]
  refine ⟨287204968687201859690144819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191469979124801239793429879 287204968687201859690144819)
  ·
    refine ⟨430807453030802789535217229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287204968687201859690144819 430807453030802789535217229)
    ·
      refine ⟨161552794886551046075706461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430807453030802789535217229 161552794886551046075706461)
      ·
        refine ⟨60582298082456642278389923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161552794886551046075706461 60582298082456642278389923)
        ·
          refine ⟨90873447123684963417584885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60582298082456642278389923 90873447123684963417584885)
          ·
            refine ⟨8519385667845465320398583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90873447123684963417584885 8519385667845465320398583)
            ·
              refine ⟨12779078501768197980597875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519385667845465320398583 12779078501768197980597875)
              ·
                refine ⟨19168617752652296970896813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12779078501768197980597875 19168617752652296970896813)
                ·
                  refine ⟨7188231657244611364086305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19168617752652296970896813 7188231657244611364086305)
                  ·
                    refine ⟨5391173742933458523064729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7188231657244611364086305 5391173742933458523064729)
                    ·
                      refine ⟨4043380307200093892298547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391173742933458523064729 4043380307200093892298547)
                      ·
                        rfl

theorem cell23_7874455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_7874455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874455 prefixEnd_7874455 := by exact prefixLift 7874455
  have htrace : WordTrace (prefixWord ++ tailWord_7874455) baseStart_7874455 baseEnd_7874455 := by
    simpa [prefixWord, tailWord_7874455, baseEnd_7874455] using wordTrace_append hprefix tailTrace_7874455
  have hstable : (prefixWord ++ tailWord_7874455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874455).length < 2 ^ (prefixWord ++ tailWord_7874455).sum := by decide
  have hdescent : baseEnd_7874455 < baseStart_7874455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874472 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7874472 : Nat := 118140960795 + 7874472 * 2 ^ 59
def prefixEnd_7874472 : Nat := 4983230072969 + 3 ^ 40 * 7874472 * 2
def baseEnd_7874472 : Nat := 4043389036371220325785969

theorem tailTrace_7874472 : CollatzResearch.WordTrace tailWord_7874472 prefixEnd_7874472 4043389036371220325785969 := by
  unfold tailWord_7874472
  simp only [CollatzResearch.WordTrace]
  refine ⟨143602794364070135796756835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191470392485426847729009113 143602794364070135796756835)
  ·
    refine ⟨215404191546105203695135253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143602794364070135796756835 215404191546105203695135253)
    ·
      refine ⟨10097071478723681423209465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215404191546105203695135253 10097071478723681423209465)
      ·
        refine ⟨7572803609042761067407099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10097071478723681423209465 7572803609042761067407099)
        ·
          refine ⟨11359205413564141601110649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572803609042761067407099 11359205413564141601110649)
          ·
            refine ⟨8519404060173106200832987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11359205413564141601110649 8519404060173106200832987)
            ·
              refine ⟨12779106090259659301249481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519404060173106200832987 12779106090259659301249481)
              ·
                refine ⟨9584329567694744475937111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12779106090259659301249481 9584329567694744475937111)
                ·
                  refine ⟨14376494351542116713905667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9584329567694744475937111 14376494351542116713905667)
                  ·
                    refine ⟨21564741527313175070858501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14376494351542116713905667 21564741527313175070858501)
                    ·
                      refine ⟨4043389036371220325785969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21564741527313175070858501 4043389036371220325785969)
                      ·
                        rfl

theorem cell23_7874472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7874472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874472 prefixEnd_7874472 := by exact prefixLift 7874472
  have htrace : WordTrace (prefixWord ++ tailWord_7874472) baseStart_7874472 baseEnd_7874472 := by
    simpa [prefixWord, tailWord_7874472, baseEnd_7874472] using wordTrace_append hprefix tailTrace_7874472
  have hstable : (prefixWord ++ tailWord_7874472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874472).length < 2 ^ (prefixWord ++ tailWord_7874472).sum := by decide
  have hdescent : baseEnd_7874472 < baseStart_7874472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874492 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7874492 : Nat := 118140960795 + 7874492 * 2 ^ 59
def prefixEnd_7874492 : Nat := 4983230072969 + 3 ^ 40 * 7874492 * 2
def baseEnd_7874492 : Nat := 4043399305984310247535877

theorem tailTrace_7874492 : CollatzResearch.WordTrace tailWord_7874492 prefixEnd_7874492 4043399305984310247535877 := by
  unfold tailWord_7874492
  simp only [CollatzResearch.WordTrace]
  refine ⟨143603159094033907504620865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191470878792045210006161153 143603159094033907504620865)
  ·
    refine ⟨107702369320525430628465649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143603159094033907504620865 107702369320525430628465649)
    ·
      refine ⟨80776776990394072971349237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107702369320525430628465649 80776776990394072971349237)
      ·
        refine ⟨7572822842849444341063991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80776776990394072971349237 7572822842849444341063991)
        ·
          refine ⟨11359234264274166511595987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572822842849444341063991 11359234264274166511595987)
          ·
            refine ⟨17038851396411249767393981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11359234264274166511595987 17038851396411249767393981)
            ·
              refine ⟨6389569273654218662772743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17038851396411249767393981 6389569273654218662772743)
              ·
                refine ⟨9584353910481327994159115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389569273654218662772743 9584353910481327994159115)
                ·
                  refine ⟨14376530865721991991238673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9584353910481327994159115 14376530865721991991238673)
                  ·
                    refine ⟨10782398149291493993429005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14376530865721991991238673 10782398149291493993429005)
                    ·
                      refine ⟨4043399305984310247535877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10782398149291493993429005 4043399305984310247535877)
                      ·
                        rfl

theorem cell23_7874492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7874492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874492 prefixEnd_7874492 := by exact prefixLift 7874492
  have htrace : WordTrace (prefixWord ++ tailWord_7874492) baseStart_7874492 baseEnd_7874492 := by
    simpa [prefixWord, tailWord_7874492, baseEnd_7874492] using wordTrace_append hprefix tailTrace_7874492
  have hstable : (prefixWord ++ tailWord_7874492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874492).length < 2 ^ (prefixWord ++ tailWord_7874492).sum := by decide
  have hdescent : baseEnd_7874492 < baseStart_7874492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874511 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 3, 4, 2]
def baseStart_7874511 : Nat := 118140960795 + 7874511 * 2 ^ 59
def prefixEnd_7874511 : Nat := 4983230072969 + 3 ^ 40 * 7874511 * 2
def baseEnd_7874511 : Nat := 4043409062116745673198289

theorem tailTrace_7874511 : CollatzResearch.WordTrace tailWord_7874511 prefixEnd_7874511 4043409062116745673198289 := by
  unfold tailWord_7874511
  simp only [CollatzResearch.WordTrace]
  refine ⟨287207011174998981254183387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191471340783332654169455591 287207011174998981254183387)
  ·
    refine ⟨430810516762498471881275081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287207011174998981254183387 430810516762498471881275081)
    ·
      refine ⟨323107887571873853910956311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430810516762498471881275081 323107887571873853910956311)
      ·
        refine ⟨484661831357810780866434467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323107887571873853910956311 484661831357810780866434467)
        ·
          refine ⟨726992747036716171299651701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484661831357810780866434467 726992747036716171299651701)
          ·
            refine ⟨68155570034692141059342347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 726992747036716171299651701 68155570034692141059342347)
            ·
              refine ⟨102233355052038211589013521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68155570034692141059342347 102233355052038211589013521)
              ·
                refine ⟨76675016289028658691760141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102233355052038211589013521 76675016289028658691760141)
                ·
                  refine ⟨28753131108385747009410053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76675016289028658691760141 28753131108385747009410053)
                  ·
                    refine ⟨5391212082822327564264385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28753131108385747009410053 5391212082822327564264385)
                    ·
                      refine ⟨4043409062116745673198289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391212082822327564264385 4043409062116745673198289)
                      ·
                        rfl

theorem cell23_7874511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4, 2].length) (baseStart_7874511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874511 prefixEnd_7874511 := by exact prefixLift 7874511
  have htrace : WordTrace (prefixWord ++ tailWord_7874511) baseStart_7874511 baseEnd_7874511 := by
    simpa [prefixWord, tailWord_7874511, baseEnd_7874511] using wordTrace_append hprefix tailTrace_7874511
  have hstable : (prefixWord ++ tailWord_7874511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874511).length < 2 ^ (prefixWord ++ tailWord_7874511).sum := by decide
  have hdescent : baseEnd_7874511 < baseStart_7874511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874521 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 2, 6]
def baseStart_7874521 : Nat := 118140960795 + 7874521 * 2 ^ 59
def prefixEnd_7874521 : Nat := 4983230072969 + 3 ^ 40 * 7874521 * 2
def baseEnd_7874521 : Nat := 1347804732307763544691081

theorem tailTrace_7874521 : CollatzResearch.WordTrace tailWord_7874521 prefixEnd_7874521 1347804732307763544691081 := by
  unfold tailWord_7874521
  simp only [CollatzResearch.WordTrace]
  refine ⟨287207375904962752962047417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191471583936641835308031611 287207375904962752962047417)
  ·
    refine ⟨215405531928722064721535563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287207375904962752962047417 215405531928722064721535563)
    ·
      refine ⟨323108297893083097082303345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215405531928722064721535563 323108297893083097082303345)
      ·
        refine ⟨242331223419812322811727509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323108297893083097082303345 242331223419812322811727509)
        ·
          refine ⟨11359276097803702631799727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242331223419812322811727509 11359276097803702631799727)
          ·
            refine ⟨17038914146705553947699591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11359276097803702631799727 17038914146705553947699591)
            ·
              refine ⟨25558371220058330921549387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038914146705553947699591 25558371220058330921549387)
              ·
                refine ⟨38337556830087496382324081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25558371220058330921549387 38337556830087496382324081)
                ·
                  refine ⟨28753167622565622286743061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38337556830087496382324081 28753167622565622286743061)
                  ·
                    refine ⟨1347804732307763544691081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28753167622565622286743061 1347804732307763544691081)
                    ·
                      rfl

theorem cell23_7874521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_7874521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874521 prefixEnd_7874521 := by exact prefixLift 7874521
  have htrace : WordTrace (prefixWord ++ tailWord_7874521) baseStart_7874521 baseEnd_7874521 := by
    simpa [prefixWord, tailWord_7874521, baseEnd_7874521] using wordTrace_append hprefix tailTrace_7874521
  have hstable : (prefixWord ++ tailWord_7874521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874521).length < 2 ^ (prefixWord ++ tailWord_7874521).sum := by decide
  have hdescent : baseEnd_7874521 < baseStart_7874521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874558 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7874558 : Nat := 118140960795 + 7874558 * 2 ^ 59
def prefixEnd_7874558 : Nat := 4983230072969 + 3 ^ 40 * 7874558 * 2
def baseEnd_7874558 : Nat := 4043433195707506989310573

theorem tailTrace_7874558 : CollatzResearch.WordTrace tailWord_7874558 prefixEnd_7874558 4043433195707506989310573 := by
  unfold tailWord_7874558
  simp only [CollatzResearch.WordTrace]
  refine ⟨35901090675728588535143041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191472483603885805520762885 35901090675728588535143041)
  ·
    refine ⟨26925818006796441401357281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35901090675728588535143041 26925818006796441401357281)
    ·
      refine ⟨20194363505097331051017961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26925818006796441401357281 20194363505097331051017961)
      ·
        refine ⟨15145772628822998288263471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20194363505097331051017961 15145772628822998288263471)
        ·
          refine ⟨22718658943234497432395207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15145772628822998288263471 22718658943234497432395207)
          ·
            refine ⟨34077988414851746148592811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22718658943234497432395207 34077988414851746148592811)
            ·
              refine ⟨51116982622277619222889217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34077988414851746148592811 51116982622277619222889217)
              ·
                refine ⟨38337736966708214417166913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51116982622277619222889217 38337736966708214417166913)
                ·
                  refine ⟨28753302725031160812875185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38337736966708214417166913 28753302725031160812875185)
                  ·
                    refine ⟨21564977043773370609656389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28753302725031160812875185 21564977043773370609656389)
                    ·
                      refine ⟨4043433195707506989310573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21564977043773370609656389 4043433195707506989310573)
                      ·
                        rfl

theorem cell23_7874558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7874558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874558 prefixEnd_7874558 := by exact prefixLift 7874558
  have htrace : WordTrace (prefixWord ++ tailWord_7874558) baseStart_7874558 baseEnd_7874558 := by
    simpa [prefixWord, tailWord_7874558, baseEnd_7874558] using wordTrace_append hprefix tailTrace_7874558
  have hstable : (prefixWord ++ tailWord_7874558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874558).length < 2 ^ (prefixWord ++ tailWord_7874558).sum := by decide
  have hdescent : baseEnd_7874558 < baseStart_7874558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874561 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_7874561 : Nat := 118140960795 + 7874561 * 2 ^ 59
def prefixEnd_7874561 : Nat := 4983230072969 + 3 ^ 40 * 7874561 * 2
def baseEnd_7874561 : Nat := 4043434736149470477573059

theorem tailTrace_7874561 : CollatzResearch.WordTrace tailWord_7874561 prefixEnd_7874561 4043434736149470477573059 := by
  unfold tailWord_7874561
  simp only [CollatzResearch.WordTrace]
  refine ⟨287208834824817839793503537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191472556549878559862335691 287208834824817839793503537)
  ·
    refine ⟨215406626118613379845127653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287208834824817839793503537 215406626118613379845127653)
    ·
      refine ⟨40388742397240008720961435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215406626118613379845127653 40388742397240008720961435)
      ·
        refine ⟨60583113595860013081442153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40388742397240008720961435 60583113595860013081442153)
        ·
          refine ⟨45437335196895009811081615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60583113595860013081442153 45437335196895009811081615)
          ·
            refine ⟨68156002795342514716622423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45437335196895009811081615 68156002795342514716622423)
            ·
              refine ⟨102234004193013772074933635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68156002795342514716622423 102234004193013772074933635)
              ·
                refine ⟨153351006289520658112400453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102234004193013772074933635 153351006289520658112400453)
                ·
                  refine ⟨28753313679285123396075085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153351006289520658112400453 28753313679285123396075085)
                  ·
                    refine ⟨10782492629731921273528157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28753313679285123396075085 10782492629731921273528157)
                    ·
                      refine ⟨4043434736149470477573059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10782492629731921273528157 4043434736149470477573059)
                      ·
                        rfl

theorem cell23_7874561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_7874561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874561 prefixEnd_7874561 := by exact prefixLift 7874561
  have htrace : WordTrace (prefixWord ++ tailWord_7874561) baseStart_7874561 baseEnd_7874561 := by
    simpa [prefixWord, tailWord_7874561, baseEnd_7874561] using wordTrace_append hprefix tailTrace_7874561
  have hstable : (prefixWord ++ tailWord_7874561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874561).length < 2 ^ (prefixWord ++ tailWord_7874561).sum := by decide
  have hdescent : baseEnd_7874561 < baseStart_7874561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874611 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 5, 4]
def baseStart_7874611 : Nat := 118140960795 + 7874611 * 2 ^ 59
def prefixEnd_7874611 : Nat := 4983230072969 + 3 ^ 40 * 7874611 * 2
def baseEnd_7874611 : Nat := 1347820136727398427315943

theorem tailTrace_7874611 : CollatzResearch.WordTrace tailWord_7874611 prefixEnd_7874611 1347820136727398427315943 := by
  unfold tailWord_7874611
  simp only [CollatzResearch.WordTrace]
  refine ⟨287210658474636698332823687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191473772316424465555215791 287210658474636698332823687)
  ·
    refine ⟨430815987711955047499235531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287210658474636698332823687 430815987711955047499235531)
    ·
      refine ⟨646223981567932571248853297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430815987711955047499235531 646223981567932571248853297)
      ·
        refine ⟨484667986175949428436639973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646223981567932571248853297 484667986175949428436639973)
        ·
          refine ⟨90875247407990517831869995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484667986175949428436639973 90875247407990517831869995)
          ·
            refine ⟨136312871111985776747804993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90875247407990517831869995 136312871111985776747804993)
            ·
              refine ⟨102234653333989332560853745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136312871111985776747804993 102234653333989332560853745)
              ·
                refine ⟨76675990000491999420640309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102234653333989332560853745 76675990000491999420640309)
                ·
                  refine ⟨7188374062546124945685029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76675990000491999420640309 7188374062546124945685029)
                  ·
                    refine ⟨1347820136727398427315943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7188374062546124945685029 1347820136727398427315943)
                    ·
                      rfl

theorem cell23_7874611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 4].length) (baseStart_7874611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874611 prefixEnd_7874611 := by exact prefixLift 7874611
  have htrace : WordTrace (prefixWord ++ tailWord_7874611) baseStart_7874611 baseEnd_7874611 := by
    simpa [prefixWord, tailWord_7874611, baseEnd_7874611] using wordTrace_append hprefix tailTrace_7874611
  have hstable : (prefixWord ++ tailWord_7874611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874611).length < 2 ^ (prefixWord ++ tailWord_7874611).sum := by decide
  have hdescent : baseEnd_7874611 < baseStart_7874611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874702 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7874702 : Nat := 118140960795 + 7874702 * 2 ^ 59
def prefixEnd_7874702 : Nat := 4983230072969 + 3 ^ 40 * 7874702 * 2
def baseEnd_7874702 : Nat := 4043507136921754425909911

theorem tailTrace_7874702 : CollatzResearch.WordTrace tailWord_7874702 prefixEnd_7874702 4043507136921754425909911 := by
  unfold tailWord_7874702
  simp only [CollatzResearch.WordTrace]
  refine ⟨35901747189663377609298295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191475985011538013916257573 35901747189663377609298295)
  ·
    refine ⟨53852620784495066413947443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35901747189663377609298295 53852620784495066413947443)
    ·
      refine ⟨80778931176742599620921165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53852620784495066413947443 80778931176742599620921165)
      ·
        refine ⟨30292099191278474857845437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80778931176742599620921165 30292099191278474857845437)
        ·
          refine ⟨11359537196729428071692039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30292099191278474857845437 11359537196729428071692039)
          ·
            refine ⟨17039305795094142107538059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11359537196729428071692039 17039305795094142107538059)
            ·
              refine ⟨25558958692641213161307089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17039305795094142107538059 25558958692641213161307089)
              ·
                refine ⟨19169219019480909870980317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25558958692641213161307089 19169219019480909870980317)
                ·
                  refine ⟨7188457132305341201617619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19169219019480909870980317 7188457132305341201617619)
                  ·
                    refine ⟨10782685698458011802426429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7188457132305341201617619 10782685698458011802426429)
                    ·
                      refine ⟨4043507136921754425909911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10782685698458011802426429 4043507136921754425909911)
                      ·
                        rfl

theorem cell23_7874702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7874702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874702 prefixEnd_7874702 := by exact prefixLift 7874702
  have htrace : WordTrace (prefixWord ++ tailWord_7874702) baseStart_7874702 baseEnd_7874702 := by
    simpa [prefixWord, tailWord_7874702, baseEnd_7874702] using wordTrace_append hprefix tailTrace_7874702
  have hstable : (prefixWord ++ tailWord_7874702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874702).length < 2 ^ (prefixWord ++ tailWord_7874702).sum := by decide
  have hdescent : baseEnd_7874702 < baseStart_7874702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874719 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7874719 : Nat := 118140960795 + 7874719 * 2 ^ 59
def prefixEnd_7874719 : Nat := 4983230072969 + 3 ^ 40 * 7874719 * 2
def baseEnd_7874719 : Nat := 4043515866092880859397333

theorem tailTrace_7874719 : CollatzResearch.WordTrace tailWord_7874719 prefixEnd_7874719 4043515866092880859397333 := by
  unfold tailWord_7874719
  simp only [CollatzResearch.WordTrace]
  refine ⟨287214597558245432777755211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191476398372163621851836807 287214597558245432777755211)
  ·
    refine ⟨430821896337368149166632817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287214597558245432777755211 430821896337368149166632817)
    ·
      refine ⟨323116422253026111874974613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430821896337368149166632817 323116422253026111874974613)
      ·
        refine ⟨15146082293110598994139435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323116422253026111874974613 15146082293110598994139435)
        ·
          refine ⟨22719123439665898491209153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15146082293110598994139435 22719123439665898491209153)
          ·
            refine ⟨17039342579749423868406865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22719123439665898491209153 17039342579749423868406865)
            ·
              refine ⟨12779506934812067901305149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17039342579749423868406865 12779506934812067901305149)
              ·
                refine ⟨4792315100554525462989431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12779506934812067901305149 4792315100554525462989431)
                ·
                  refine ⟨7188472650831788194484147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792315100554525462989431 7188472650831788194484147)
                  ·
                    refine ⟨10782708976247682291726221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7188472650831788194484147 10782708976247682291726221)
                    ·
                      refine ⟨4043515866092880859397333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10782708976247682291726221 4043515866092880859397333)
                      ·
                        rfl

theorem cell23_7874719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7874719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874719 prefixEnd_7874719 := by exact prefixLift 7874719
  have htrace : WordTrace (prefixWord ++ tailWord_7874719) baseStart_7874719 baseEnd_7874719 := by
    simpa [prefixWord, tailWord_7874719, baseEnd_7874719] using wordTrace_append hprefix tailTrace_7874719
  have hstable : (prefixWord ++ tailWord_7874719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874719).length < 2 ^ (prefixWord ++ tailWord_7874719).sum := by decide
  have hdescent : baseEnd_7874719 < baseStart_7874719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874722 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_7874722 : Nat := 118140960795 + 7874722 * 2 ^ 59
def prefixEnd_7874722 : Nat := 4983230072969 + 3 ^ 40 * 7874722 * 2
def baseEnd_7874722 : Nat := 1347839135511614782553273

theorem tailTrace_7874722 : CollatzResearch.WordTrace tailWord_7874722 prefixEnd_7874722 1347839135511614782553273 := by
  unfold tailWord_7874722
  simp only [CollatzResearch.WordTrace]
  refine ⟨71803676744308641072528605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191476471318156376193409613 71803676744308641072528605)
  ·
    refine ⟨26926378779115740402198227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71803676744308641072528605 26926378779115740402198227)
    ·
      refine ⟨40389568168673610603297341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26926378779115740402198227 40389568168673610603297341)
      ·
        refine ⟨15146088063252603976236503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40389568168673610603297341 15146088063252603976236503)
        ·
          refine ⟨22719132094878905964354755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15146088063252603976236503 22719132094878905964354755)
          ·
            refine ⟨34078698142318358946532133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22719132094878905964354755 34078698142318358946532133)
            ·
              refine ⟨6389755901684692302474775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34078698142318358946532133 6389755901684692302474775)
              ·
                refine ⟨9584633852527038453712163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389755901684692302474775 9584633852527038453712163)
                ·
                  refine ⟨14376950778790557680568245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9584633852527038453712163 14376950778790557680568245)
                  ·
                    refine ⟨1347839135511614782553273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14376950778790557680568245 1347839135511614782553273)
                    ·
                      rfl

theorem cell23_7874722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_7874722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874722 prefixEnd_7874722 := by exact prefixLift 7874722
  have htrace : WordTrace (prefixWord ++ tailWord_7874722) baseStart_7874722 baseEnd_7874722 := by
    simpa [prefixWord, tailWord_7874722, baseEnd_7874722] using wordTrace_append hprefix tailTrace_7874722
  have hstable : (prefixWord ++ tailWord_7874722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874722).length < 2 ^ (prefixWord ++ tailWord_7874722).sum := by decide
  have hdescent : baseEnd_7874722 < baseStart_7874722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874725 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 5, 2, 2]
def baseStart_7874725 : Nat := 118140960795 + 7874725 * 2 ^ 59
def prefixEnd_7874725 : Nat := 4983230072969 + 3 ^ 40 * 7874725 * 2
def baseEnd_7874725 : Nat := 4043518946976807835922305

theorem tailTrace_7874725 : CollatzResearch.WordTrace tailWord_7874725 prefixEnd_7874725 4043518946976807835922305 := by
  unfold tailWord_7874725
  simp only [CollatzResearch.WordTrace]
  refine ⟨287214816396223695802473629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191476544264149130534982419 287214816396223695802473629)
  ·
    refine ⟨107705556148583885925927611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287214816396223695802473629 107705556148583885925927611)
    ·
      refine ⟨161558334222875828888891417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107705556148583885925927611 161558334222875828888891417)
      ·
        refine ⟨121168750667156871666668563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161558334222875828888891417 121168750667156871666668563)
        ·
          refine ⟨181753126000735307500002845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121168750667156871666668563 181753126000735307500002845)
          ·
            refine ⟨68157422250275740312501067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181753126000735307500002845 68157422250275740312501067)
            ·
              refine ⟨102236133375413610468751601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68157422250275740312501067 102236133375413610468751601)
              ·
                refine ⟨76677100031560207851563701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102236133375413610468751601 76677100031560207851563701)
                ·
                  refine ⟨7188478127958769486084097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76677100031560207851563701 7188478127958769486084097)
                  ·
                    refine ⟨5391358595969077114563073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7188478127958769486084097 5391358595969077114563073)
                    ·
                      refine ⟨4043518946976807835922305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391358595969077114563073 4043518946976807835922305)
                      ·
                        rfl

theorem cell23_7874725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_7874725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874725 prefixEnd_7874725 := by exact prefixLift 7874725
  have htrace : WordTrace (prefixWord ++ tailWord_7874725) baseStart_7874725 baseEnd_7874725 := by
    simpa [prefixWord, tailWord_7874725, baseEnd_7874725] using wordTrace_append hprefix tailTrace_7874725
  have hstable : (prefixWord ++ tailWord_7874725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874725).length < 2 ^ (prefixWord ++ tailWord_7874725).sum := by decide
  have hdescent : baseEnd_7874725 < baseStart_7874725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874752 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 2, 4]
def baseStart_7874752 : Nat := 118140960795 + 7874752 * 2 ^ 59
def prefixEnd_7874752 : Nat := 4983230072969 + 3 ^ 40 * 7874752 * 2
def baseEnd_7874752 : Nat := 1347844270318159743428227

theorem tailTrace_7874752 : CollatzResearch.WordTrace tailWord_7874752 prefixEnd_7874752 1347844270318159743428227 := by
  unfold tailWord_7874752
  simp only [CollatzResearch.WordTrace]
  refine ⟨143607900583562939706853255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191477200778083919609137673 143607900583562939706853255)
  ·
    refine ⟨215411850875344409560279883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143607900583562939706853255 215411850875344409560279883)
    ·
      refine ⟨323117776313016614340419825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215411850875344409560279883 323117776313016614340419825)
      ·
        refine ⟨242338332234762460755314869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323117776313016614340419825 242338332234762460755314869)
        ·
          refine ⟨22719218647008980695810769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242338332234762460755314869 22719218647008980695810769)
          ·
            refine ⟨17039413985256735521858077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22719218647008980695810769 17039413985256735521858077)
            ·
              refine ⟨6389780244471275820696779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17039413985256735521858077 6389780244471275820696779)
              ·
                refine ⟨9584670366706913731045169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389780244471275820696779 9584670366706913731045169)
                ·
                  refine ⟨7188502775030185298283877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9584670366706913731045169 7188502775030185298283877)
                  ·
                    refine ⟨1347844270318159743428227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7188502775030185298283877 1347844270318159743428227)
                    ·
                      rfl

theorem cell23_7874752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 4].length) (baseStart_7874752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874752 prefixEnd_7874752 := by exact prefixLift 7874752
  have htrace : WordTrace (prefixWord ++ tailWord_7874752) baseStart_7874752 baseEnd_7874752 := by
    simpa [prefixWord, tailWord_7874752, baseEnd_7874752] using wordTrace_append hprefix tailTrace_7874752
  have hstable : (prefixWord ++ tailWord_7874752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874752).length < 2 ^ (prefixWord ++ tailWord_7874752).sum := by decide
  have hdescent : baseEnd_7874752 < baseStart_7874752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874768 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 7, 2]
def baseStart_7874768 : Nat := 118140960795 + 7874768 * 2 ^ 59
def prefixEnd_7874768 : Nat := 4983230072969 + 3 ^ 40 * 7874768 * 2
def baseEnd_7874768 : Nat := 4043541026644951167684607

theorem tailTrace_7874768 : CollatzResearch.WordTrace tailWord_7874768 prefixEnd_7874768 4043541026644951167684607 := by
  unfold tailWord_7874768
  simp only [CollatzResearch.WordTrace]
  refine ⟨143608192367533957073144479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191477589823378609430859305 143608192367533957073144479)
  ·
    refine ⟨215412288551300935609716719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143608192367533957073144479 215412288551300935609716719)
    ·
      refine ⟨323118432826951403414575079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215412288551300935609716719 323118432826951403414575079)
      ·
        refine ⟨484677649240427105121862619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323118432826951403414575079 484677649240427105121862619)
        ·
          refine ⟨727016473860640657682793929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484677649240427105121862619 727016473860640657682793929)
          ·
            refine ⟨545262355395480493262095447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727016473860640657682793929 545262355395480493262095447)
            ·
              refine ⟨817893533093220739893143171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545262355395480493262095447 817893533093220739893143171)
              ·
                refine ⟨1226840299639831109839714757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817893533093220739893143171 1226840299639831109839714757)
                ·
                  refine ⟨230032556182468333094946517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226840299639831109839714757 230032556182468333094946517)
                  ·
                    refine ⟨5391388035526601556912809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 230032556182468333094946517 5391388035526601556912809)
                    ·
                      refine ⟨4043541026644951167684607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391388035526601556912809 4043541026644951167684607)
                      ·
                        rfl

theorem cell23_7874768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 7, 2].length) (baseStart_7874768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874768 prefixEnd_7874768 := by exact prefixLift 7874768
  have htrace : WordTrace (prefixWord ++ tailWord_7874768) baseStart_7874768 baseEnd_7874768 := by
    simpa [prefixWord, tailWord_7874768, baseEnd_7874768] using wordTrace_append hprefix tailTrace_7874768
  have hstable : (prefixWord ++ tailWord_7874768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874768).length < 2 ^ (prefixWord ++ tailWord_7874768).sum := by decide
  have hdescent : baseEnd_7874768 < baseStart_7874768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874776 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 1, 2, 2]
def baseStart_7874776 : Nat := 118140960795 + 7874776 * 2 ^ 59
def prefixEnd_7874776 : Nat := 4983230072969 + 3 ^ 40 * 7874776 * 2
def baseEnd_7874776 : Nat := 4043545134490187136384571

theorem tailTrace_7874776 : CollatzResearch.WordTrace tailWord_7874776 prefixEnd_7874776 4043545134490187136384571 := by
  unfold tailWord_7874776
  simp only [CollatzResearch.WordTrace]
  refine ⟨143608338259519465756290091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191477784346025954341720121 143608338259519465756290091)
  ·
    refine ⟨215412507389279198634435137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143608338259519465756290091 215412507389279198634435137)
    ·
      refine ⟨161559380541959398975826353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215412507389279198634435137 161559380541959398975826353)
      ·
        refine ⟨121169535406469549231869765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161559380541959398975826353 121169535406469549231869765)
        ·
          refine ⟨22719287888713040480975581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121169535406469549231869765 22719287888713040480975581)
          ·
            refine ⟨8519732958267390180365843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22719287888713040480975581 8519732958267390180365843)
            ·
              refine ⟨12779599437401085270548765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519732958267390180365843 12779599437401085270548765)
              ·
                refine ⟨4792349789025406976455787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12779599437401085270548765 4792349789025406976455787)
                ·
                  refine ⟨7188524683538110464683681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792349789025406976455787 7188524683538110464683681)
                  ·
                    refine ⟨5391393512653582848512761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7188524683538110464683681 5391393512653582848512761)
                    ·
                      refine ⟨4043545134490187136384571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391393512653582848512761 4043545134490187136384571)
                      ·
                        rfl

theorem cell23_7874776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_7874776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874776 prefixEnd_7874776 := by exact prefixLift 7874776
  have htrace : WordTrace (prefixWord ++ tailWord_7874776) baseStart_7874776 baseEnd_7874776 := by
    simpa [prefixWord, tailWord_7874776, baseEnd_7874776] using wordTrace_append hprefix tailTrace_7874776
  have hstable : (prefixWord ++ tailWord_7874776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874776).length < 2 ^ (prefixWord ++ tailWord_7874776).sum := by decide
  have hdescent : baseEnd_7874776 < baseStart_7874776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874798 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7874798 : Nat := 118140960795 + 7874798 * 2 ^ 59
def prefixEnd_7874798 : Nat := 4983230072969 + 3 ^ 40 * 7874798 * 2
def baseEnd_7874798 : Nat := 4043556431064586050309469

theorem tailTrace_7874798 : CollatzResearch.WordTrace tailWord_7874798 prefixEnd_7874798 4043556431064586050309469 := by
  unfold tailWord_7874798
  simp only [CollatzResearch.WordTrace]
  refine ⟨35902184865619903658735131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191478319283306152846587365 35902184865619903658735131)
  ·
    refine ⟨53853277298429855488102697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35902184865619903658735131 53853277298429855488102697)
    ·
      refine ⟨40389957973822391616077023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53853277298429855488102697 40389957973822391616077023)
      ·
        refine ⟨60584936960733587424115535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40389957973822391616077023 60584936960733587424115535)
        ·
          refine ⟨90877405441100381136173303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60584936960733587424115535 90877405441100381136173303)
          ·
            refine ⟨136316108161650571704259955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90877405441100381136173303 136316108161650571704259955)
            ·
              refine ⟨204474162242475857556389933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136316108161650571704259955 204474162242475857556389933)
              ·
                refine ⟨76677810840928446583646225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204474162242475857556389933 76677810840928446583646225)
                ·
                  refine ⟨57508358130696334937734669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76677810840928446583646225 57508358130696334937734669)
                  ·
                    refine ⟨21565634299011125601650501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57508358130696334937734669 21565634299011125601650501)
                    ·
                      refine ⟨4043556431064586050309469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21565634299011125601650501 4043556431064586050309469)
                      ·
                        rfl

theorem cell23_7874798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7874798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874798 prefixEnd_7874798 := by exact prefixLift 7874798
  have htrace : WordTrace (prefixWord ++ tailWord_7874798) baseStart_7874798 baseEnd_7874798 := by
    simpa [prefixWord, tailWord_7874798, baseEnd_7874798] using wordTrace_append hprefix tailTrace_7874798
  have hstable : (prefixWord ++ tailWord_7874798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874798).length < 2 ^ (prefixWord ++ tailWord_7874798).sum := by decide
  have hdescent : baseEnd_7874798 < baseStart_7874798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874811 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_7874811 : Nat := 118140960795 + 7874811 * 2 ^ 59
def prefixEnd_7874811 : Nat := 4983230072969 + 3 ^ 40 * 7874811 * 2
def baseEnd_7874811 : Nat := 4043563106313094499446909

theorem tailTrace_7874811 : CollatzResearch.WordTrace tailWord_7874811 prefixEnd_7874811 4043563106313094499446909 := by
  unfold tailWord_7874811
  simp only [CollatzResearch.WordTrace]
  refine ⟨287217953073912132490104287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191478635382608088326736191 287217953073912132490104287)
  ·
    refine ⟨430826929610868198735156431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287217953073912132490104287 430826929610868198735156431)
    ·
      refine ⟨646240394416302298102734647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430826929610868198735156431 646240394416302298102734647)
      ·
        refine ⟨969360591624453447154101971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646240394416302298102734647 969360591624453447154101971)
        ·
          refine ⟨1454040887436680170731152957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969360591624453447154101971 1454040887436680170731152957)
          ·
            refine ⟨545265332788755064024182359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1454040887436680170731152957 545265332788755064024182359)
            ·
              refine ⟨817897999183132596036273539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545265332788755064024182359 817897999183132596036273539)
              ·
                refine ⟨1226846998774698894054410309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817897999183132596036273539 1226846998774698894054410309)
                ·
                  refine ⟨230033812270256042635201933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226846998774698894054410309 230033812270256042635201933)
                  ·
                    refine ⟨86262679601346015988200725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230033812270256042635201933 86262679601346015988200725)
                    ·
                      refine ⟨4043563106313094499446909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86262679601346015988200725 4043563106313094499446909)
                      ·
                        rfl

theorem cell23_7874811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_7874811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874811 prefixEnd_7874811 := by exact prefixLift 7874811
  have htrace : WordTrace (prefixWord ++ tailWord_7874811) baseStart_7874811 baseEnd_7874811 := by
    simpa [prefixWord, tailWord_7874811, baseEnd_7874811] using wordTrace_append hprefix tailTrace_7874811
  have hstable : (prefixWord ++ tailWord_7874811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874811).length < 2 ^ (prefixWord ++ tailWord_7874811).sum := by decide
  have hdescent : baseEnd_7874811 < baseStart_7874811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874815 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 1, 4, 2]
def baseStart_7874815 : Nat := 118140960795 + 7874815 * 2 ^ 59
def prefixEnd_7874815 : Nat := 4983230072969 + 3 ^ 40 * 7874815 * 2
def baseEnd_7874815 : Nat := 4043565160235712483796891

theorem tailTrace_7874815 : CollatzResearch.WordTrace tailWord_7874815 prefixEnd_7874815 4043565160235712483796891 := by
  unfold tailWord_7874815
  simp only [CollatzResearch.WordTrace]
  refine ⟨287218098965897641173249899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191478732643931760782166599 287218098965897641173249899)
  ·
    refine ⟨430827148448846461759874849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287218098965897641173249899 430827148448846461759874849)
    ·
      refine ⟨323120361336634846319906137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430827148448846461759874849 323120361336634846319906137)
      ·
        refine ⟨242340271002476134739929603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323120361336634846319906137 242340271002476134739929603)
        ·
          refine ⟨363510406503714202109894405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242340271002476134739929603 363510406503714202109894405)
          ·
            refine ⟨68158201219446412895605201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363510406503714202109894405 68158201219446412895605201)
            ·
              refine ⟨51118650914584809671703901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68158201219446412895605201 51118650914584809671703901)
              ·
                refine ⟨19169494092969303626888963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51118650914584809671703901 19169494092969303626888963)
                ·
                  refine ⟨28754241139453955440333445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19169494092969303626888963 28754241139453955440333445)
                  ·
                    refine ⟨5391420213647616645062521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28754241139453955440333445 5391420213647616645062521)
                    ·
                      refine ⟨4043565160235712483796891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391420213647616645062521 4043565160235712483796891)
                      ·
                        rfl

theorem cell23_7874815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_7874815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874815 prefixEnd_7874815 := by exact prefixLift 7874815
  have htrace : WordTrace (prefixWord ++ tailWord_7874815) baseStart_7874815 baseEnd_7874815 := by
    simpa [prefixWord, tailWord_7874815, baseEnd_7874815] using wordTrace_append hprefix tailTrace_7874815
  have hstable : (prefixWord ++ tailWord_7874815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874815).length < 2 ^ (prefixWord ++ tailWord_7874815).sum := by decide
  have hdescent : baseEnd_7874815 < baseStart_7874815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874925 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_7874925 : Nat := 118140960795 + 7874925 * 2 ^ 59
def prefixEnd_7874925 : Nat := 4983230072969 + 3 ^ 40 * 7874925 * 2
def baseEnd_7874925 : Nat := 4043621643107707053421385

theorem tailTrace_7874925 : CollatzResearch.WordTrace tailWord_7874925 prefixEnd_7874925 4043621643107707053421385 := by
  unfold tailWord_7874925
  simp only [CollatzResearch.WordTrace]
  refine ⟨287222110995499129959754229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191481407330332753306502819 287222110995499129959754229)
  ·
    refine ⟨26927072905828043433726959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287222110995499129959754229 26927072905828043433726959)
    ·
      refine ⟨40390609358742065150590439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26927072905828043433726959 40390609358742065150590439)
      ·
        refine ⟨60585914038113097725885659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40390609358742065150590439 60585914038113097725885659)
        ·
          refine ⟨90878871057169646588828489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60585914038113097725885659 90878871057169646588828489)
          ·
            refine ⟨68159153292877234941621367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90878871057169646588828489 68159153292877234941621367)
            ·
              refine ⟨102238729939315852412432051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68159153292877234941621367 102238729939315852412432051)
              ·
                refine ⟨153358094908973778618648077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102238729939315852412432051 153358094908973778618648077)
                ·
                  refine ⟨57509285590865166981993029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153358094908973778618648077 57509285590865166981993029)
                  ·
                    refine ⟨10782991048287218809123693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57509285590865166981993029 10782991048287218809123693)
                    ·
                      refine ⟨4043621643107707053421385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10782991048287218809123693 4043621643107707053421385)
                      ·
                        rfl

theorem cell23_7874925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_7874925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874925 prefixEnd_7874925 := by exact prefixLift 7874925
  have htrace : WordTrace (prefixWord ++ tailWord_7874925) baseStart_7874925 baseEnd_7874925 := by
    simpa [prefixWord, tailWord_7874925, baseEnd_7874925] using wordTrace_append hprefix tailTrace_7874925
  have hstable : (prefixWord ++ tailWord_7874925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874925).length < 2 ^ (prefixWord ++ tailWord_7874925).sum := by decide
  have hdescent : baseEnd_7874925 < baseStart_7874925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874945 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 8]
def baseStart_7874945 : Nat := 118140960795 + 7874945 * 2 ^ 59
def prefixEnd_7874945 : Nat := 4983230072969 + 3 ^ 40 * 7874945 * 2
def baseEnd_7874945 : Nat := 449292434746755219463477

theorem tailTrace_7874945 : CollatzResearch.WordTrace tailWord_7874945 prefixEnd_7874945 449292434746755219463477 := by
  unfold tailWord_7874945
  simp only [CollatzResearch.WordTrace]
  refine ⟨287222840455426673375482289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191481893636951115583654859 287222840455426673375482289)
  ·
    refine ⟨215417130341570005031611717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287222840455426673375482289 215417130341570005031611717)
    ·
      refine ⟨40390711939044375943427197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215417130341570005031611717 40390711939044375943427197)
      ·
        refine ⟨15146516977141640978785199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40390711939044375943427197 15146516977141640978785199)
        ·
          refine ⟨22719775465712461468177799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15146516977141640978785199 22719775465712461468177799)
          ·
            refine ⟨34079663198568692202266699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22719775465712461468177799 34079663198568692202266699)
            ·
              refine ⟨51119494797853038303400049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34079663198568692202266699 51119494797853038303400049)
              ·
                refine ⟨38339621098389778727550037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51119494797853038303400049 38339621098389778727550037)
                ·
                  refine ⟨449292434746755219463477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38339621098389778727550037 449292434746755219463477)
                  ·
                    rfl

theorem cell23_7874945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_7874945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874945 prefixEnd_7874945 := by exact prefixLift 7874945
  have htrace : WordTrace (prefixWord ++ tailWord_7874945) baseStart_7874945 baseEnd_7874945 := by
    simpa [prefixWord, tailWord_7874945, baseEnd_7874945] using wordTrace_append hprefix tailTrace_7874945
  have hstable : (prefixWord ++ tailWord_7874945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874945).length < 2 ^ (prefixWord ++ tailWord_7874945).sum := by decide
  have hdescent : baseEnd_7874945 < baseStart_7874945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874975 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 3, 5]
def baseStart_7874975 : Nat := 118140960795 + 7874975 * 2 ^ 59
def prefixEnd_7874975 : Nat := 4983230072969 + 3 ^ 40 * 7874975 * 2
def baseEnd_7874975 : Nat := 1347882439046810619265385

theorem tailTrace_7874975 : CollatzResearch.WordTrace tailWord_7874975 prefixEnd_7874975 1347882439046810619265385 := by
  unfold tailWord_7874975
  simp only [CollatzResearch.WordTrace]
  refine ⟨287223934645317988499074379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191482623096878658999382919 287223934645317988499074379)
  ·
    refine ⟨430835901967976982748611569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287223934645317988499074379 430835901967976982748611569)
    ·
      refine ⟨323126926475982737061458677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430835901967976982748611569 323126926475982737061458677)
      ·
        refine ⟨30293149357123381599511751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323126926475982737061458677 30293149357123381599511751)
        ·
          refine ⟨45439724035685072399267627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30293149357123381599511751 45439724035685072399267627)
          ·
            refine ⟨68159586053527608598901441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45439724035685072399267627 68159586053527608598901441)
            ·
              refine ⟨51119689540145706449176081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68159586053527608598901441 51119689540145706449176081)
              ·
                refine ⟨38339767155109279836882061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51119689540145706449176081 38339767155109279836882061)
                ·
                  refine ⟨14377412683165979938830773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38339767155109279836882061 14377412683165979938830773)
                  ·
                    refine ⟨1347882439046810619265385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14377412683165979938830773 1347882439046810619265385)
                    ·
                      rfl

theorem cell23_7874975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_7874975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874975 prefixEnd_7874975 := by exact prefixLift 7874975
  have htrace : WordTrace (prefixWord ++ tailWord_7874975) baseStart_7874975 baseEnd_7874975 := by
    simpa [prefixWord, tailWord_7874975, baseEnd_7874975] using wordTrace_append hprefix tailTrace_7874975
  have hstable : (prefixWord ++ tailWord_7874975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874975).length < 2 ^ (prefixWord ++ tailWord_7874975).sum := by decide
  have hdescent : baseEnd_7874975 < baseStart_7874975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7874999 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 2, 3, 2]
def baseStart_7874999 : Nat := 118140960795 + 7874999 * 2 ^ 59
def prefixEnd_7874999 : Nat := 4983230072969 + 3 ^ 40 * 7874999 * 2
def baseEnd_7874999 : Nat := 4043659640676139763896045

theorem tailTrace_7874999 : CollatzResearch.WordTrace tailWord_7874999 prefixEnd_7874999 4043659640676139763896045 := by
  unfold tailWord_7874999
  simp only [CollatzResearch.WordTrace]
  refine ⟨287224809997231040597948051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191483206664820693731965367 287224809997231040597948051)
  ·
    refine ⟨430837214995846560896922077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287224809997231040597948051 430837214995846560896922077)
    ·
      refine ⟨161563955623442460336345779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430837214995846560896922077 161563955623442460336345779)
      ·
        refine ⟨242345933435163690504518669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161563955623442460336345779 242345933435163690504518669)
        ·
          refine ⟨90879725038186383939194501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242345933435163690504518669 90879725038186383939194501)
          ·
            refine ⟨17039948444659946988598969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90879725038186383939194501 17039948444659946988598969)
            ·
              refine ⟨12779961333494960241449227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17039948444659946988598969 12779961333494960241449227)
              ·
                refine ⟨19169942000242440362173841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12779961333494960241449227 19169942000242440362173841)
                ·
                  refine ⟨14377456500181830271630381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19169942000242440362173841 14377456500181830271630381)
                  ·
                    refine ⟨5391546187568186351861393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14377456500181830271630381 5391546187568186351861393)
                    ·
                      refine ⟨4043659640676139763896045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391546187568186351861393 4043659640676139763896045)
                      ·
                        rfl

theorem cell23_7874999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_7874999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7874999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7874999 prefixEnd_7874999 := by exact prefixLift 7874999
  have htrace : WordTrace (prefixWord ++ tailWord_7874999) baseStart_7874999 baseEnd_7874999 := by
    simpa [prefixWord, tailWord_7874999, baseEnd_7874999] using wordTrace_append hprefix tailTrace_7874999
  have hstable : (prefixWord ++ tailWord_7874999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7874999).length < 2 ^ (prefixWord ++ tailWord_7874999).sum := by decide
  have hdescent : baseEnd_7874999 < baseStart_7874999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7874999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875005 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_7875005 : Nat := 118140960795 + 7875005 * 2 ^ 59
def prefixEnd_7875005 : Nat := 4983230072969 + 3 ^ 40 * 7875005 * 2
def baseEnd_7875005 : Nat := 1347887573853355580140339

theorem tailTrace_7875005 : CollatzResearch.WordTrace tailWord_7875005 prefixEnd_7875005 1347887573853355580140339 := by
  unfold tailWord_7875005
  simp only [CollatzResearch.WordTrace]
  refine ⟨287225028835209303622666469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191483352556806202415110979 287225028835209303622666469)
  ·
    refine ⟨53854692906601744429249963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287225028835209303622666469 53854692906601744429249963)
    ·
      refine ⟨80782039359902616643874945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53854692906601744429249963 80782039359902616643874945)
      ·
        refine ⟨60586529519926962482906209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80782039359902616643874945 60586529519926962482906209)
        ·
          refine ⟨45439897139945221862179657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60586529519926962482906209 45439897139945221862179657)
          ·
            refine ⟨34079922854958916396634743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45439897139945221862179657 34079922854958916396634743)
            ·
              refine ⟨51119884282438374594952115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34079922854958916396634743 51119884282438374594952115)
              ·
                refine ⟨76679826423657561892428173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51119884282438374594952115 76679826423657561892428173)
                ·
                  refine ⟨28754934908871585709660565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76679826423657561892428173 28754934908871585709660565)
                  ·
                    refine ⟨1347887573853355580140339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28754934908871585709660565 1347887573853355580140339)
                    ·
                      rfl

theorem cell23_7875005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_7875005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875005 prefixEnd_7875005 := by exact prefixLift 7875005
  have htrace : WordTrace (prefixWord ++ tailWord_7875005) baseStart_7875005 baseEnd_7875005 := by
    simpa [prefixWord, tailWord_7875005, baseEnd_7875005] using wordTrace_append hprefix tailTrace_7875005
  have hstable : (prefixWord ++ tailWord_7875005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875005).length < 2 ^ (prefixWord ++ tailWord_7875005).sum := by decide
  have hdescent : baseEnd_7875005 < baseStart_7875005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875115 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4]
def baseStart_7875115 : Nat := 118140960795 + 7875115 * 2 ^ 59
def prefixEnd_7875115 : Nat := 4983230072969 + 3 ^ 40 * 7875115 * 2
def baseEnd_7875115 : Nat := 4043719204432061310045511

theorem tailTrace_7875115 : CollatzResearch.WordTrace tailWord_7875115 prefixEnd_7875115 4043719204432061310045511 := by
  unfold tailWord_7875115
  simp only [CollatzResearch.WordTrace]
  refine ⟨287229040864810792409170799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191486027243207194939447199 287229040864810792409170799)
  ·
    refine ⟨430843561297216188613756199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287229040864810792409170799 430843561297216188613756199)
    ·
      refine ⟨646265341945824282920634299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430843561297216188613756199 646265341945824282920634299)
      ·
        refine ⟨969398012918736424380951449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646265341945824282920634299 969398012918736424380951449)
        ·
          refine ⟨727048509689052318285713587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969398012918736424380951449 727048509689052318285713587)
          ·
            refine ⟨1090572764533578477428570381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727048509689052318285713587 1090572764533578477428570381)
            ·
              refine ⟨408964786700091929035713893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090572764533578477428570381 408964786700091929035713893)
              ·
                refine ⟨76680897506267236694196355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408964786700091929035713893 76680897506267236694196355)
                ·
                  refine ⟨115021346259400855041294533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76680897506267236694196355 115021346259400855041294533)
                  ·
                    refine ⟨21566502423637660320242725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115021346259400855041294533 21566502423637660320242725)
                    ·
                      refine ⟨4043719204432061310045511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21566502423637660320242725 4043719204432061310045511)
                      ·
                        rfl

theorem cell23_7875115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_7875115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875115 prefixEnd_7875115 := by exact prefixLift 7875115
  have htrace : WordTrace (prefixWord ++ tailWord_7875115) baseStart_7875115 baseEnd_7875115 := by
    simpa [prefixWord, tailWord_7875115, baseEnd_7875115] using wordTrace_append hprefix tailTrace_7875115
  have hstable : (prefixWord ++ tailWord_7875115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875115).length < 2 ^ (prefixWord ++ tailWord_7875115).sum := by decide
  have hdescent : baseEnd_7875115 < baseStart_7875115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875135 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_7875135 : Nat := 118140960795 + 7875135 * 2 ^ 59
def prefixEnd_7875135 : Nat := 4983230072969 + 3 ^ 40 * 7875135 * 2
def baseEnd_7875135 : Nat := 4043729474045151231795419

theorem tailTrace_7875135 : CollatzResearch.WordTrace tailWord_7875135 prefixEnd_7875135 4043729474045151231795419 := by
  unfold tailWord_7875135
  simp only [CollatzResearch.WordTrace]
  refine ⟨287229770324738335824898859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191486513549825557216599239 287229770324738335824898859)
  ·
    refine ⟨430844655487107503737348289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287229770324738335824898859 430844655487107503737348289)
    ·
      refine ⟨323133491615330627803011217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430844655487107503737348289 323133491615330627803011217)
      ·
        refine ⟨242350118711497970852258413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323133491615330627803011217 242350118711497970852258413)
        ·
          refine ⟨90881294516811739069596905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242350118711497970852258413 90881294516811739069596905)
          ·
            refine ⟨68160970887608804302197679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90881294516811739069596905 68160970887608804302197679)
            ·
              refine ⟨102241456331413206453296519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68160970887608804302197679 102241456331413206453296519)
              ·
                refine ⟨153362184497119809679944779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102241456331413206453296519 153362184497119809679944779)
                ·
                  refine ⟨230043276745679714519917169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153362184497119809679944779 230043276745679714519917169)
                  ·
                    refine ⟨172532457559259785889937877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230043276745679714519917169 172532457559259785889937877)
                    ·
                      refine ⟨4043729474045151231795419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172532457559259785889937877 4043729474045151231795419)
                      ·
                        rfl

theorem cell23_7875135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_7875135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875135 prefixEnd_7875135 := by exact prefixLift 7875135
  have htrace : WordTrace (prefixWord ++ tailWord_7875135) baseStart_7875135 baseEnd_7875135 := by
    simpa [prefixWord, tailWord_7875135, baseEnd_7875135] using wordTrace_append hprefix tailTrace_7875135
  have hstable : (prefixWord ++ tailWord_7875135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875135).length < 2 ^ (prefixWord ++ tailWord_7875135).sum := by decide
  have hdescent : baseEnd_7875135 < baseStart_7875135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875153 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 2, 2, 2]
def baseStart_7875153 : Nat := 118140960795 + 7875153 * 2 ^ 59
def prefixEnd_7875153 : Nat := 4983230072969 + 3 ^ 40 * 7875153 * 2
def baseEnd_7875153 : Nat := 4043738716696932161370337

theorem tailTrace_7875153 : CollatzResearch.WordTrace tailWord_7875153 prefixEnd_7875153 4043738716696932161370337 := by
  unfold tailWord_7875153
  simp only [CollatzResearch.WordTrace]
  refine ⟨287230426838673124899054113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191486951225782083266036075 287230426838673124899054113)
  ·
    refine ⟨215422820129004843674290585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287230426838673124899054113 215422820129004843674290585)
    ·
      refine ⟨161567115096753632755717939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215422820129004843674290585 161567115096753632755717939)
      ·
        refine ⟨242350672645130449133576909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161567115096753632755717939 242350672645130449133576909)
        ·
          refine ⟨90881502241923918425091341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242350672645130449133576909 90881502241923918425091341)
          ·
            refine ⟨34080563340721469409409253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90881502241923918425091341 34080563340721469409409253)
            ·
              refine ⟨6390105626385275514264235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34080563340721469409409253 6390105626385275514264235)
              ·
                refine ⟨9585158439577913271396353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390105626385275514264235 9585158439577913271396353)
                ·
                  refine ⟨7188868829683434953547265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9585158439577913271396353 7188868829683434953547265)
                  ·
                    refine ⟨5391651622262576215160449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7188868829683434953547265 5391651622262576215160449)
                    ·
                      refine ⟨4043738716696932161370337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391651622262576215160449 4043738716696932161370337)
                      ·
                        rfl

theorem cell23_7875153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_7875153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875153 prefixEnd_7875153 := by exact prefixLift 7875153
  have htrace : WordTrace (prefixWord ++ tailWord_7875153) baseStart_7875153 baseEnd_7875153 := by
    simpa [prefixWord, tailWord_7875153, baseEnd_7875153] using wordTrace_append hprefix tailTrace_7875153
  have hstable : (prefixWord ++ tailWord_7875153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875153).length < 2 ^ (prefixWord ++ tailWord_7875153).sum := by decide
  have hdescent : baseEnd_7875153 < baseStart_7875153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875226 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7875226 : Nat := 118140960795 + 7875226 * 2 ^ 59
def prefixEnd_7875226 : Nat := 4983230072969 + 3 ^ 40 * 7875226 * 2
def baseEnd_7875226 : Nat := 4043776200784710375757501

theorem tailTrace_7875226 : CollatzResearch.WordTrace tailWord_7875226 prefixEnd_7875226 4043776200784710375757501 := by
  unfold tailWord_7875226
  simp only [CollatzResearch.WordTrace]
  refine ⟨71808272341852164591615383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191488726244939105577641021 71808272341852164591615383)
  ·
    refine ⟨107712408512778246887423075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71808272341852164591615383 107712408512778246887423075)
    ·
      refine ⟨161568612769167370331134613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107712408512778246887423075 161568612769167370331134613)
      ·
        refine ⟨7573528723554720484271935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161568612769167370331134613 7573528723554720484271935)
        ·
          refine ⟨11360293085332080726407903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573528723554720484271935 11360293085332080726407903)
          ·
            refine ⟨17040439627998121089611855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11360293085332080726407903 17040439627998121089611855)
            ·
              refine ⟨25560659441997181634417783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17040439627998121089611855 25560659441997181634417783)
              ·
                refine ⟨38340989162995772451626675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25560659441997181634417783 38340989162995772451626675)
                ·
                  refine ⟨57511483744493658677440013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38340989162995772451626675 57511483744493658677440013)
                  ·
                    refine ⟨21566806404185122004040005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57511483744493658677440013 21566806404185122004040005)
                    ·
                      refine ⟨4043776200784710375757501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21566806404185122004040005 4043776200784710375757501)
                      ·
                        rfl

theorem cell23_7875226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7875226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875226 prefixEnd_7875226 := by exact prefixLift 7875226
  have htrace : WordTrace (prefixWord ++ tailWord_7875226) baseStart_7875226 baseEnd_7875226 := by
    simpa [prefixWord, tailWord_7875226, baseEnd_7875226] using wordTrace_append hprefix tailTrace_7875226
  have hstable : (prefixWord ++ tailWord_7875226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875226).length < 2 ^ (prefixWord ++ tailWord_7875226).sum := by decide
  have hdescent : baseEnd_7875226 < baseStart_7875226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875253 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7875253 : Nat := 118140960795 + 7875253 * 2 ^ 59
def prefixEnd_7875253 : Nat := 4983230072969 + 3 ^ 40 * 7875253 * 2
def baseEnd_7875253 : Nat := 1347930021587460590039959

theorem tailTrace_7875253 : CollatzResearch.WordTrace tailWord_7875253 prefixEnd_7875253 1347930021587460590039959 := by
  unfold tailWord_7875253
  simp only [CollatzResearch.WordTrace]
  refine ⟨287234074138310841977694413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191489382758873894651796275 287234074138310841977694413)
  ·
    refine ⟨107712777801866565741635405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287234074138310841977694413 107712777801866565741635405)
    ·
      refine ⟨40392291675699962153113277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107712777801866565741635405 40392291675699962153113277)
      ·
        refine ⟨15147109378387485807417479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40392291675699962153113277 15147109378387485807417479)
        ·
          refine ⟨22720664067581228711126219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15147109378387485807417479 22720664067581228711126219)
          ·
            refine ⟨34080996101371843066689329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22720664067581228711126219 34080996101371843066689329)
            ·
              refine ⟨25560747076028882300016997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34080996101371843066689329 25560747076028882300016997)
              ·
                refine ⟨4792640076755415431253187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25560747076028882300016997 4792640076755415431253187)
                ·
                  refine ⟨7188960115133123146879781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792640076755415431253187 7188960115133123146879781)
                  ·
                    refine ⟨1347930021587460590039959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7188960115133123146879781 1347930021587460590039959)
                    ·
                      rfl

theorem cell23_7875253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7875253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875253 prefixEnd_7875253 := by exact prefixLift 7875253
  have htrace : WordTrace (prefixWord ++ tailWord_7875253) baseStart_7875253 baseEnd_7875253 := by
    simpa [prefixWord, tailWord_7875253, baseEnd_7875253] using wordTrace_append hprefix tailTrace_7875253
  have hstable : (prefixWord ++ tailWord_7875253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875253).length < 2 ^ (prefixWord ++ tailWord_7875253).sum := by decide
  have hdescent : baseEnd_7875253 < baseStart_7875253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875312 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_7875312 : Nat := 118140960795 + 7875312 * 2 ^ 59
def prefixEnd_7875312 : Nat := 4983230072969 + 3 ^ 40 * 7875312 * 2
def baseEnd_7875312 : Nat := 4043820360120997039282105

theorem tailTrace_7875312 : CollatzResearch.WordTrace tailWord_7875312 prefixEnd_7875312 4043820360120997039282105 := by
  unfold tailWord_7875312
  simp only [CollatzResearch.WordTrace]
  refine ⟨143618113022548547527046095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191490817363398063369394793 143618113022548547527046095)
  ·
    refine ⟨215427169533822821290569143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143618113022548547527046095 215427169533822821290569143)
    ·
      refine ⟨323140754300734231935853715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215427169533822821290569143 323140754300734231935853715)
      ·
        refine ⟨484711131451101347903780573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323140754300734231935853715 484711131451101347903780573)
        ·
          refine ⟨181766674294163005463917715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484711131451101347903780573 181766674294163005463917715)
          ·
            refine ⟨272650011441244508195876573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181766674294163005463917715 272650011441244508195876573)
            ·
              refine ⟨102243754290466690573453715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272650011441244508195876573 102243754290466690573453715)
              ·
                refine ⟨153365631435700035860180573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102243754290466690573453715 153365631435700035860180573)
                ·
                  refine ⟨57512111788387513447567715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153365631435700035860180573 57512111788387513447567715)
                  ·
                    refine ⟨86268167682581270171351573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57512111788387513447567715 86268167682581270171351573)
                    ·
                      refine ⟨4043820360120997039282105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86268167682581270171351573 4043820360120997039282105)
                      ·
                        rfl

theorem cell23_7875312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_7875312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875312 prefixEnd_7875312 := by exact prefixLift 7875312
  have htrace : WordTrace (prefixWord ++ tailWord_7875312) baseStart_7875312 baseEnd_7875312 := by
    simpa [prefixWord, tailWord_7875312, baseEnd_7875312] using wordTrace_append hprefix tailTrace_7875312
  have hstable : (prefixWord ++ tailWord_7875312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875312).length < 2 ^ (prefixWord ++ tailWord_7875312).sum := by decide
  have hdescent : baseEnd_7875312 < baseStart_7875312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875317 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 6]
def baseStart_7875317 : Nat := 118140960795 + 7875317 * 2 ^ 59
def prefixEnd_7875317 : Nat := 4983230072969 + 3 ^ 40 * 7875317 * 2
def baseEnd_7875317 : Nat := 449313658613807724413287

theorem tailTrace_7875317 : CollatzResearch.WordTrace tailWord_7875317 prefixEnd_7875317 449313658613807724413287 := by
  unfold tailWord_7875317
  simp only [CollatzResearch.WordTrace]
  refine ⟨287236408410078980908024205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191490938940052653938682803 287236408410078980908024205)
  ·
    refine ⟨107713653153779617840509077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287236408410078980908024205 107713653153779617840509077)
    ·
      refine ⟨5049077491583419586273863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107713653153779617840509077 5049077491583419586273863)
      ·
        refine ⟨7573616237375129379410795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049077491583419586273863 7573616237375129379410795)
        ·
          refine ⟨11360424356062694069116193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573616237375129379410795 11360424356062694069116193)
          ·
            refine ⟨8520318267047020551837145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11360424356062694069116193 8520318267047020551837145)
            ·
              refine ⟨6390238700285265413877859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8520318267047020551837145 6390238700285265413877859)
              ·
                refine ⟨9585358050427898120816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390238700285265413877859 9585358050427898120816789)
                ·
                  refine ⟨449313658613807724413287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9585358050427898120816789 449313658613807724413287)
                  ·
                    rfl

theorem cell23_7875317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_7875317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875317 prefixEnd_7875317 := by exact prefixLift 7875317
  have htrace : WordTrace (prefixWord ++ tailWord_7875317) baseStart_7875317 baseEnd_7875317 := by
    simpa [prefixWord, tailWord_7875317, baseEnd_7875317] using wordTrace_append hprefix tailTrace_7875317
  have hstable : (prefixWord ++ tailWord_7875317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875317).length < 2 ^ (prefixWord ++ tailWord_7875317).sum := by decide
  have hdescent : baseEnd_7875317 < baseStart_7875317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875319 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_7875319 : Nat := 118140960795 + 7875319 * 2 ^ 59
def prefixEnd_7875319 : Nat := 4983230072969 + 3 ^ 40 * 7875319 * 2
def baseEnd_7875319 : Nat := 4043823954485578511894573

theorem tailTrace_7875319 : CollatzResearch.WordTrace tailWord_7875319 prefixEnd_7875319 4043823954485578511894573 := by
  unfold tailWord_7875319
  simp only [CollatzResearch.WordTrace]
  refine ⟨287236481356071735249597011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191490987570714490166398007 287236481356071735249597011)
  ·
    refine ⟨430854722034107602874395517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287236481356071735249597011 430854722034107602874395517)
    ·
      refine ⟨161570520762790351077898319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430854722034107602874395517 161570520762790351077898319)
      ·
        refine ⟨242355781144185526616847479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161570520762790351077898319 242355781144185526616847479)
        ·
          refine ⟨363533671716278289925271219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242355781144185526616847479 363533671716278289925271219)
          ·
            refine ⟨545300507574417434887906829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363533671716278289925271219 545300507574417434887906829)
            ·
              refine ⟨204487690340406538082965061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545300507574417434887906829 204487690340406538082965061)
              ·
                refine ⟨38341441938826225890555949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204487690340406538082965061 38341441938826225890555949)
                ·
                  refine ⟨14378040727059834708958481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38341441938826225890555949 14378040727059834708958481)
                  ·
                    refine ⟨10783530545294876031718861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14378040727059834708958481 10783530545294876031718861)
                    ·
                      refine ⟨4043823954485578511894573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10783530545294876031718861 4043823954485578511894573)
                      ·
                        rfl

theorem cell23_7875319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_7875319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875319 prefixEnd_7875319 := by exact prefixLift 7875319
  have htrace : WordTrace (prefixWord ++ tailWord_7875319) baseStart_7875319 baseEnd_7875319 := by
    simpa [prefixWord, tailWord_7875319, baseEnd_7875319] using wordTrace_append hprefix tailTrace_7875319
  have hstable : (prefixWord ++ tailWord_7875319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875319).length < 2 ^ (prefixWord ++ tailWord_7875319).sum := by decide
  have hdescent : baseEnd_7875319 < baseStart_7875319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875322 : List Nat := [3, 1, 1, 1, 1, 3, 3, 10]
def baseStart_7875322 : Nat := 118140960795 + 7875322 * 2 ^ 59
def prefixEnd_7875322 : Nat := 4983230072969 + 3 ^ 40 * 7875322 * 2
def baseEnd_7875322 : Nat := 149771314626946000005817

theorem tailTrace_7875322 : CollatzResearch.WordTrace tailWord_7875322 prefixEnd_7875322 149771314626946000005817 := by
  unfold tailWord_7875322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71809147693765216690489055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191491060516707244507970813 71809147693765216690489055)
  ·
    refine ⟨107713721540647825035733583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71809147693765216690489055 107713721540647825035733583)
    ·
      refine ⟨161570582310971737553600375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107713721540647825035733583 161570582310971737553600375)
      ·
        refine ⟨242355873466457606330400563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161570582310971737553600375 242355873466457606330400563)
        ·
          refine ⟨363533810199686409495600845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242355873466457606330400563 363533810199686409495600845)
          ·
            refine ⟨136325178824882403560850317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363533810199686409495600845 136325178824882403560850317)
            ·
              refine ⟨51121942059330901335318869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136325178824882403560850317 51121942059330901335318869)
              ·
                refine ⟨149771314626946000005817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51121942059330901335318869 149771314626946000005817)
                ·
                  rfl

theorem cell23_7875322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_7875322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875322 prefixEnd_7875322 := by exact prefixLift 7875322
  have htrace : WordTrace (prefixWord ++ tailWord_7875322) baseStart_7875322 baseEnd_7875322 := by
    simpa [prefixWord, tailWord_7875322, baseEnd_7875322] using wordTrace_append hprefix tailTrace_7875322
  have hstable : (prefixWord ++ tailWord_7875322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875322).length < 2 ^ (prefixWord ++ tailWord_7875322).sum := by decide
  have hdescent : baseEnd_7875322 < baseStart_7875322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875329 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7875329 : Nat := 118140960795 + 7875329 * 2 ^ 59
def prefixEnd_7875329 : Nat := 4983230072969 + 3 ^ 40 * 7875329 * 2
def baseEnd_7875329 : Nat := 4043829089292123472769527

theorem tailTrace_7875329 : CollatzResearch.WordTrace tailWord_7875329 prefixEnd_7875329 4043829089292123472769527 := by
  unfold tailWord_7875329
  simp only [CollatzResearch.WordTrace]
  refine ⟨287236846086035506957461041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191491230724023671304974027 287236846086035506957461041)
  ·
    refine ⟨215427634564526630218095781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287236846086035506957461041 215427634564526630218095781)
    ·
      refine ⟨40392681480848743165892959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215427634564526630218095781 40392681480848743165892959)
      ·
        refine ⟨60589022221273114748839439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40392681480848743165892959 60589022221273114748839439)
        ·
          refine ⟨90883533331909672123259159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60589022221273114748839439 90883533331909672123259159)
          ·
            refine ⟨136325299997864508184888739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90883533331909672123259159 136325299997864508184888739)
            ·
              refine ⟨204487949996796762277333109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136325299997864508184888739 204487949996796762277333109)
              ·
                refine ⟨19170745312199696463499979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204487949996796762277333109 19170745312199696463499979)
                ·
                  refine ⟨28756117968299544695249969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19170745312199696463499979 28756117968299544695249969)
                  ·
                    refine ⟨21567088476224658521437477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28756117968299544695249969 21567088476224658521437477)
                    ·
                      refine ⟨4043829089292123472769527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21567088476224658521437477 4043829089292123472769527)
                      ·
                        rfl

theorem cell23_7875329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7875329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875329 prefixEnd_7875329 := by exact prefixLift 7875329
  have htrace : WordTrace (prefixWord ++ tailWord_7875329) baseStart_7875329 baseEnd_7875329 := by
    simpa [prefixWord, tailWord_7875329, baseEnd_7875329] using wordTrace_append hprefix tailTrace_7875329
  have hstable : (prefixWord ++ tailWord_7875329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875329).length < 2 ^ (prefixWord ++ tailWord_7875329).sum := by decide
  have hdescent : baseEnd_7875329 < baseStart_7875329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875336 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_7875336 : Nat := 118140960795 + 7875336 * 2 ^ 59
def prefixEnd_7875336 : Nat := 4983230072969 + 3 ^ 40 * 7875336 * 2
def baseEnd_7875336 : Nat := 4043832683656704945381995

theorem tailTrace_7875336 : CollatzResearch.WordTrace tailWord_7875336 prefixEnd_7875336 4043832683656704945381995 := by
  unfold tailWord_7875336
  simp only [CollatzResearch.WordTrace]
  refine ⟨143618550698505073576482931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191491400931340098101977241 143618550698505073576482931)
  ·
    refine ⟨215427826047757610364724397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143618550698505073576482931 215427826047757610364724397)
    ·
      refine ⟨80785434767909103886771649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215427826047757610364724397 80785434767909103886771649)
      ·
        refine ⟨60589076075931827915078737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80785434767909103886771649 60589076075931827915078737)
        ·
          refine ⟨45441807056948870936309053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60589076075931827915078737 45441807056948870936309053)
          ·
            refine ⟨17040677646355826601115895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45441807056948870936309053 17040677646355826601115895)
            ·
              refine ⟨25561016469533739901673843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17040677646355826601115895 25561016469533739901673843)
              ·
                refine ⟨38341524704300609852510765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25561016469533739901673843 38341524704300609852510765)
                ·
                  refine ⟨14378071764112728694691537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38341524704300609852510765 14378071764112728694691537)
                  ·
                    refine ⟨10783553823084546521018653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14378071764112728694691537 10783553823084546521018653)
                    ·
                      refine ⟨4043832683656704945381995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10783553823084546521018653 4043832683656704945381995)
                      ·
                        rfl

theorem cell23_7875336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_7875336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875336 prefixEnd_7875336 := by exact prefixLift 7875336
  have htrace : WordTrace (prefixWord ++ tailWord_7875336) baseStart_7875336 baseEnd_7875336 := by
    simpa [prefixWord, tailWord_7875336, baseEnd_7875336] using wordTrace_append hprefix tailTrace_7875336
  have hstable : (prefixWord ++ tailWord_7875336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875336).length < 2 ^ (prefixWord ++ tailWord_7875336).sum := by decide
  have hdescent : baseEnd_7875336 < baseStart_7875336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875423 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 4, 2, 2]
def baseStart_7875423 : Nat := 118140960795 + 7875423 * 2 ^ 59
def prefixEnd_7875423 : Nat := 4983230072969 + 3 ^ 40 * 7875423 * 2
def baseEnd_7875423 : Nat := 4043877356473646104994095

theorem tailTrace_7875423 : CollatzResearch.WordTrace tailWord_7875423 prefixEnd_7875423 4043877356473646104994095 := by
  unfold tailWord_7875423
  simp only [CollatzResearch.WordTrace]
  refine ⟨287240274547694961011382923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191493516365129974007588615 287240274547694961011382923)
  ·
    refine ⟨430860411821542441517074385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287240274547694961011382923 430860411821542441517074385)
    ·
      refine ⟨323145308866156831137805789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430860411821542441517074385 323145308866156831137805789)
      ·
        refine ⟨121179490824808811676677171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323145308866156831137805789 121179490824808811676677171)
        ·
          refine ⟨181769236237213217515015757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121179490824808811676677171 181769236237213217515015757)
          ·
            refine ⟨68163463588954956568130909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181769236237213217515015757 68163463588954956568130909)
            ·
              refine ⟨25561298845858108713049091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68163463588954956568130909 25561298845858108713049091)
              ·
                refine ⟨38341948268787163069573637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25561298845858108713049091 38341948268787163069573637)
                ·
                  refine ⟨7189115300397593075545057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38341948268787163069573637 7189115300397593075545057)
                  ·
                    refine ⟨5391836475298194806658793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7189115300397593075545057 5391836475298194806658793)
                    ·
                      refine ⟨4043877356473646104994095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5391836475298194806658793 4043877356473646104994095)
                      ·
                        rfl

theorem cell23_7875423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_7875423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875423 prefixEnd_7875423 := by exact prefixLift 7875423
  have htrace : WordTrace (prefixWord ++ tailWord_7875423) baseStart_7875423 baseEnd_7875423 := by
    simpa [prefixWord, tailWord_7875423, baseEnd_7875423] using wordTrace_append hprefix tailTrace_7875423
  have hstable : (prefixWord ++ tailWord_7875423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875423).length < 2 ^ (prefixWord ++ tailWord_7875423).sum := by decide
  have hdescent : baseEnd_7875423 < baseStart_7875423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875429 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 7]
def baseStart_7875429 : Nat := 118140960795 + 7875429 * 2 ^ 59
def prefixEnd_7875429 : Nat := 4983230072969 + 3 ^ 40 * 7875429 * 2
def baseEnd_7875429 : Nat := 449320048595285897946563

theorem tailTrace_7875429 : CollatzResearch.WordTrace tailWord_7875429 prefixEnd_7875429 449320048595285897946563 := by
  unfold tailWord_7875429
  simp only [CollatzResearch.WordTrace]
  refine ⟨287240493385673224036101341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191493662257115482690734227 287240493385673224036101341)
  ·
    refine ⟨107715185019627459013538003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287240493385673224036101341 107715185019627459013538003)
    ·
      refine ⟨161572777529441188520307005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107715185019627459013538003 161572777529441188520307005)
      ·
        refine ⟨60589791573540445695115127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161572777529441188520307005 60589791573540445695115127)
        ·
          refine ⟨90884687360310668542672691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60589791573540445695115127 90884687360310668542672691)
          ·
            refine ⟨136327031040466002814009037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90884687360310668542672691 136327031040466002814009037)
            ·
              refine ⟨51122636640174751055253389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136327031040466002814009037 51122636640174751055253389)
              ·
                refine ⟨19170988740065531645720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51122636640174751055253389 19170988740065531645720021)
                ·
                  refine ⟨449320048595285897946563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19170988740065531645720021 449320048595285897946563)
                  ·
                    rfl

theorem cell23_7875429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_7875429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875429 prefixEnd_7875429 := by exact prefixLift 7875429
  have htrace : WordTrace (prefixWord ++ tailWord_7875429) baseStart_7875429 baseEnd_7875429 := by
    simpa [prefixWord, tailWord_7875429, baseEnd_7875429] using wordTrace_append hprefix tailTrace_7875429
  have hstable : (prefixWord ++ tailWord_7875429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875429).length < 2 ^ (prefixWord ++ tailWord_7875429).sum := by decide
  have hdescent : baseEnd_7875429 < baseStart_7875429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875459 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 1, 7]
def baseStart_7875459 : Nat := 118140960795 + 7875459 * 2 ^ 59
def prefixEnd_7875459 : Nat := 4983230072969 + 3 ^ 40 * 7875459 * 2
def baseEnd_7875459 : Nat := 1347965280592402654714643

theorem tailTrace_7875459 : CollatzResearch.WordTrace tailWord_7875459 prefixEnd_7875459 1347965280592402654714643 := by
  unfold tailWord_7875459
  simp only [CollatzResearch.WordTrace]
  refine ⟨287241587575564539159693431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191494391717043026106462287 287241587575564539159693431)
  ·
    refine ⟨430862381363346808739540147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287241587575564539159693431 430862381363346808739540147)
    ·
      refine ⟨646293572045020213109310221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430862381363346808739540147 646293572045020213109310221)
      ·
        refine ⟨242360089516882579915991333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646293572045020213109310221 242360089516882579915991333)
        ·
          refine ⟨45442516784415483734248375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242360089516882579915991333 45442516784415483734248375)
          ·
            refine ⟨68163775176623225601372563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45442516784415483734248375 68163775176623225601372563)
            ·
              refine ⟨102245662764934838402058845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68163775176623225601372563 102245662764934838402058845)
              ·
                refine ⟨38342123536850564400772067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102245662764934838402058845 38342123536850564400772067)
                ·
                  refine ⟨57513185305275846601158101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38342123536850564400772067 57513185305275846601158101)
                  ·
                    refine ⟨1347965280592402654714643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57513185305275846601158101 1347965280592402654714643)
                    ·
                      rfl

theorem cell23_7875459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 7].length) (baseStart_7875459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875459 prefixEnd_7875459 := by exact prefixLift 7875459
  have htrace : WordTrace (prefixWord ++ tailWord_7875459) baseStart_7875459 baseEnd_7875459 := by
    simpa [prefixWord, tailWord_7875459, baseEnd_7875459] using wordTrace_append hprefix tailTrace_7875459
  have hstable : (prefixWord ++ tailWord_7875459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875459).length < 2 ^ (prefixWord ++ tailWord_7875459).sum := by decide
  have hdescent : baseEnd_7875459 < baseStart_7875459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875463 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 5]
def baseStart_7875463 : Nat := 118140960795 + 7875463 * 2 ^ 59
def prefixEnd_7875463 : Nat := 4983230072969 + 3 ^ 40 * 7875463 * 2
def baseEnd_7875463 : Nat := 449321988411091772054879

theorem tailTrace_7875463 : CollatzResearch.WordTrace tailWord_7875463 prefixEnd_7875463 449321988411091772054879 := by
  unfold tailWord_7875463
  simp only [CollatzResearch.WordTrace]
  refine ⟨287241733467550047842839043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191494488978366698561892695 287241733467550047842839043)
  ·
    refine ⟨430862600201325071764258565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287241733467550047842839043 430862600201325071764258565)
    ·
      refine ⟨80786737537748450955798481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430862600201325071764258565 80786737537748450955798481)
      ·
        refine ⟨60590053153311338216848861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80786737537748450955798481 60590053153311338216848861)
        ·
          refine ⟨22721269932491751831318323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60590053153311338216848861 22721269932491751831318323)
          ·
            refine ⟨34081904898737627746977485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22721269932491751831318323 34081904898737627746977485)
            ·
              refine ⟨12780714337026610405116557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34081904898737627746977485 12780714337026610405116557)
              ·
                refine ⟨4792767876384978901918709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12780714337026610405116557 4792767876384978901918709)
                ·
                  refine ⟨449321988411091772054879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4792767876384978901918709 449321988411091772054879)
                  ·
                    rfl

theorem cell23_7875463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 5].length) (baseStart_7875463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875463 prefixEnd_7875463 := by exact prefixLift 7875463
  have htrace : WordTrace (prefixWord ++ tailWord_7875463) baseStart_7875463 baseEnd_7875463 := by
    simpa [prefixWord, tailWord_7875463, baseEnd_7875463] using wordTrace_append hprefix tailTrace_7875463
  have hstable : (prefixWord ++ tailWord_7875463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875463).length < 2 ^ (prefixWord ++ tailWord_7875463).sum := by decide
  have hdescent : baseEnd_7875463 < baseStart_7875463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875513 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_7875513 : Nat := 118140960795 + 7875513 * 2 ^ 59
def prefixEnd_7875513 : Nat := 4983230072969 + 3 ^ 40 * 7875513 * 2
def baseEnd_7875513 : Nat := 4043923569732550752868681

theorem tailTrace_7875513 : CollatzResearch.WordTrace tailWord_7875513 prefixEnd_7875513 4043923569732550752868681 := by
  unfold tailWord_7875513
  simp only [CollatzResearch.WordTrace]
  refine ⟨287243557117368906382159193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191495704744912604254772795 287243557117368906382159193)
  ·
    refine ⟨215432667838026679786619395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287243557117368906382159193 215432667838026679786619395)
    ·
      refine ⟨323149001757040019679929093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215432667838026679786619395 323149001757040019679929093)
      ·
        refine ⟨60590437829445003689986705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323149001757040019679929093 60590437829445003689986705)
        ·
          refine ⟨45442828372083752767490029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60590437829445003689986705 45442828372083752767490029)
          ·
            refine ⟨17041060639531407287808761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45442828372083752767490029 17041060639531407287808761)
            ·
              refine ⟨12780795479648555465856571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17041060639531407287808761 12780795479648555465856571)
              ·
                refine ⟨19171193219472833198784857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12780795479648555465856571 19171193219472833198784857)
                ·
                  refine ⟨14378394914604624899088643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19171193219472833198784857 14378394914604624899088643)
                  ·
                    refine ⟨21567592371906937348632965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14378394914604624899088643 21567592371906937348632965)
                    ·
                      refine ⟨4043923569732550752868681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21567592371906937348632965 4043923569732550752868681)
                      ·
                        rfl

theorem cell23_7875513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_7875513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875513 prefixEnd_7875513 := by exact prefixLift 7875513
  have htrace : WordTrace (prefixWord ++ tailWord_7875513) baseStart_7875513 baseEnd_7875513 := by
    simpa [prefixWord, tailWord_7875513, baseEnd_7875513] using wordTrace_append hprefix tailTrace_7875513
  have hstable : (prefixWord ++ tailWord_7875513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875513).length < 2 ^ (prefixWord ++ tailWord_7875513).sum := by decide
  have hdescent : baseEnd_7875513 < baseStart_7875513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875519 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 8]
def baseStart_7875519 : Nat := 118140960795 + 7875519 * 2 ^ 59
def prefixEnd_7875519 : Nat := 4983230072969 + 3 ^ 40 * 7875519 * 2
def baseEnd_7875519 : Nat := 449325183401830858821517

theorem tailTrace_7875519 : CollatzResearch.WordTrace tailWord_7875519 prefixEnd_7875519 449325183401830858821517 := by
  unfold tailWord_7875519
  simp only [CollatzResearch.WordTrace]
  refine ⟨287243775955347169406877611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191495850636898112937918407 287243775955347169406877611)
  ·
    refine ⟨430865663933020754110316417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287243775955347169406877611 430865663933020754110316417)
    ·
      refine ⟨323149247949765565582737313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430865663933020754110316417 323149247949765565582737313)
      ·
        refine ⟨242361935962324174187052985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323149247949765565582737313 242361935962324174187052985)
        ·
          refine ⟨181771451971743130640289739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242361935962324174187052985 181771451971743130640289739)
          ·
            refine ⟨272657177957614695960434609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181771451971743130640289739 272657177957614695960434609)
            ·
              refine ⟨204492883468211021970325957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272657177957614695960434609 204492883468211021970325957)
              ·
                refine ⟨38342415650289566619436117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204492883468211021970325957 38342415650289566619436117)
                ·
                  refine ⟨449325183401830858821517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38342415650289566619436117 449325183401830858821517)
                  ·
                    rfl

theorem cell23_7875519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 8].length) (baseStart_7875519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875519 prefixEnd_7875519 := by exact prefixLift 7875519
  have htrace : WordTrace (prefixWord ++ tailWord_7875519) baseStart_7875519 baseEnd_7875519 := by
    simpa [prefixWord, tailWord_7875519, baseEnd_7875519] using wordTrace_append hprefix tailTrace_7875519
  have hstable : (prefixWord ++ tailWord_7875519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875519).length < 2 ^ (prefixWord ++ tailWord_7875519).sum := by decide
  have hdescent : baseEnd_7875519 < baseStart_7875519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875620 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7875620 : Nat := 118140960795 + 7875620 * 2 ^ 59
def prefixEnd_7875620 : Nat := 4983230072969 + 3 ^ 40 * 7875620 * 2
def baseEnd_7875620 : Nat := 4043978512162581834230689

theorem tailTrace_7875620 : CollatzResearch.WordTrace tailWord_7875620 prefixEnd_7875620 4043978512162581834230689 := by
  unfold tailWord_7875620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143623729863990631828152157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191498306485320842437536209 143623729863990631828152157)
  ·
    refine ⟨53858898698996486935557059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143623729863990631828152157 53858898698996486935557059)
    ·
      refine ⟨80788348048494730403335589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53858898698996486935557059 80788348048494730403335589)
      ·
        refine ⟨15147815259092761950625423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80788348048494730403335589 15147815259092761950625423)
        ·
          refine ⟨22721722888639142925938135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15147815259092761950625423 22721722888639142925938135)
          ·
            refine ⟨34082584332958714388907203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22721722888639142925938135 34082584332958714388907203)
            ·
              refine ⟨51123876499438071583360805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34082584332958714388907203 51123876499438071583360805)
              ·
                refine ⟨9585726843644638421880151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51123876499438071583360805 9585726843644638421880151)
                ·
                  refine ⟨14378590265466957632820227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585726843644638421880151 14378590265466957632820227)
                  ·
                    refine ⟨21567885398200436449230341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14378590265466957632820227 21567885398200436449230341)
                    ·
                      refine ⟨4043978512162581834230689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21567885398200436449230341 4043978512162581834230689)
                      ·
                        rfl

theorem cell23_7875620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7875620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875620 prefixEnd_7875620 := by exact prefixLift 7875620
  have htrace : WordTrace (prefixWord ++ tailWord_7875620) baseStart_7875620 baseEnd_7875620 := by
    simpa [prefixWord, tailWord_7875620, baseEnd_7875620] using wordTrace_append hprefix tailTrace_7875620
  have hstable : (prefixWord ++ tailWord_7875620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875620).length < 2 ^ (prefixWord ++ tailWord_7875620).sum := by decide
  have hdescent : baseEnd_7875620 < baseStart_7875620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875640 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_7875640 : Nat := 118140960795 + 7875640 * 2 ^ 59
def prefixEnd_7875640 : Nat := 4983230072969 + 3 ^ 40 * 7875640 * 2
def baseEnd_7875640 : Nat := 4043988781775671755980597

theorem tailTrace_7875640 : CollatzResearch.WordTrace tailWord_7875640 prefixEnd_7875640 4043988781775671755980597 := by
  unfold tailWord_7875640
  simp only [CollatzResearch.WordTrace]
  refine ⟨143624094593954403536016187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191498792791939204714688249 143624094593954403536016187)
  ·
    refine ⟨215436141890931605304024281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143624094593954403536016187 215436141890931605304024281)
    ·
      refine ⟨161577106418198703978018211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215436141890931605304024281 161577106418198703978018211)
      ·
        refine ⟨242365659627298055967027317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161577106418198703978018211 242365659627298055967027317)
        ·
          refine ⟨22721780590059192746908811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242365659627298055967027317 22721780590059192746908811)
          ·
            refine ⟨34082670885088789120363217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22721780590059192746908811 34082670885088789120363217)
            ·
              refine ⟨25562003163816591840272413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34082670885088789120363217 25562003163816591840272413)
              ·
                refine ⟨9585751186431221940102155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25562003163816591840272413 9585751186431221940102155)
                ·
                  refine ⟨14378626779646832910153233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585751186431221940102155 14378626779646832910153233)
                  ·
                    refine ⟨10783970084735124682614925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14378626779646832910153233 10783970084735124682614925)
                    ·
                      refine ⟨4043988781775671755980597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10783970084735124682614925 4043988781775671755980597)
                      ·
                        rfl

theorem cell23_7875640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_7875640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875640 prefixEnd_7875640 := by exact prefixLift 7875640
  have htrace : WordTrace (prefixWord ++ tailWord_7875640) baseStart_7875640 baseEnd_7875640 := by
    simpa [prefixWord, tailWord_7875640, baseEnd_7875640] using wordTrace_append hprefix tailTrace_7875640
  have hstable : (prefixWord ++ tailWord_7875640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875640).length < 2 ^ (prefixWord ++ tailWord_7875640).sum := by decide
  have hdescent : baseEnd_7875640 < baseStart_7875640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875656 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_7875656 : Nat := 118140960795 + 7875656 * 2 ^ 59
def prefixEnd_7875656 : Nat := 4983230072969 + 3 ^ 40 * 7875656 * 2
def baseEnd_7875656 : Nat := 1347998999155381231126841

theorem tailTrace_7875656 : CollatzResearch.WordTrace tailWord_7875656 prefixEnd_7875656 1347998999155381231126841 := by
  unfold tailWord_7875656
  simp only [CollatzResearch.WordTrace]
  refine ⟨143624386377925420902307411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191499181837233894536409881 143624386377925420902307411)
  ·
    refine ⟨215436579566888131353461117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143624386377925420902307411 215436579566888131353461117)
    ·
      refine ⟨80788717337583049257547919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215436579566888131353461117 80788717337583049257547919)
      ·
        refine ⟨121183076006374573886321879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80788717337583049257547919 121183076006374573886321879)
        ·
          refine ⟨181774614009561860829482819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121183076006374573886321879 181774614009561860829482819)
          ·
            refine ⟨272661921014342791244224229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181774614009561860829482819 272661921014342791244224229)
            ·
              refine ⟨51124110190189273358292043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272661921014342791244224229 51124110190189273358292043)
              ·
                refine ⟨76686165285283910037438065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51124110190189273358292043 76686165285283910037438065)
                ·
                  refine ⟨57514623963962932528078549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76686165285283910037438065 57514623963962932528078549)
                  ·
                    refine ⟨1347998999155381231126841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57514623963962932528078549 1347998999155381231126841)
                    ·
                      rfl

theorem cell23_7875656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_7875656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875656 prefixEnd_7875656 := by exact prefixLift 7875656
  have htrace : WordTrace (prefixWord ++ tailWord_7875656) baseStart_7875656 baseEnd_7875656 := by
    simpa [prefixWord, tailWord_7875656, baseEnd_7875656] using wordTrace_append hprefix tailTrace_7875656
  have hstable : (prefixWord ++ tailWord_7875656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875656).length < 2 ^ (prefixWord ++ tailWord_7875656).sum := by decide
  have hdescent : baseEnd_7875656 < baseStart_7875656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875680 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 3, 3, 2]
def baseStart_7875680 : Nat := 118140960795 + 7875680 * 2 ^ 59
def prefixEnd_7875680 : Nat := 4983230072969 + 3 ^ 40 * 7875680 * 2
def baseEnd_7875680 : Nat := 4044009321001851599480413

theorem tailTrace_7875680 : CollatzResearch.WordTrace tailWord_7875680 prefixEnd_7875680 4044009321001851599480413 := by
  unfold tailWord_7875680
  simp only [CollatzResearch.WordTrace]
  refine ⟨143624824053881946951744247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191499765405175929268992329 143624824053881946951744247)
  ·
    refine ⟨215437236080822920427616371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143624824053881946951744247 215437236080822920427616371)
    ·
      refine ⟨323155854121234380641424557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215437236080822920427616371 323155854121234380641424557)
      ·
        refine ⟨121183445295462892740534209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323155854121234380641424557 121183445295462892740534209)
        ·
          refine ⟨90887583971597169555400657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121183445295462892740534209 90887583971597169555400657)
          ·
            refine ⟨68165687978697877166550493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90887583971597169555400657 68165687978697877166550493)
            ·
              refine ⟨25562132992011703937456435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68165687978697877166550493 25562132992011703937456435)
              ·
                refine ⟨38343199488017555906184653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25562132992011703937456435 38343199488017555906184653)
                ·
                  refine ⟨14378699808006583464819245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38343199488017555906184653 14378699808006583464819245)
                  ·
                    refine ⟨5392012428002468799307217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14378699808006583464819245 5392012428002468799307217)
                    ·
                      refine ⟨4044009321001851599480413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392012428002468799307217 4044009321001851599480413)
                      ·
                        rfl

theorem cell23_7875680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_7875680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875680 prefixEnd_7875680 := by exact prefixLift 7875680
  have htrace : WordTrace (prefixWord ++ tailWord_7875680) baseStart_7875680 baseEnd_7875680 := by
    simpa [prefixWord, tailWord_7875680, baseEnd_7875680] using wordTrace_append hprefix tailTrace_7875680
  have hstable : (prefixWord ++ tailWord_7875680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875680).length < 2 ^ (prefixWord ++ tailWord_7875680).sum := by decide
  have hdescent : baseEnd_7875680 < baseStart_7875680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875720 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 2, 6]
def baseStart_7875720 : Nat := 118140960795 + 7875720 * 2 ^ 59
def prefixEnd_7875720 : Nat := 4983230072969 + 3 ^ 40 * 7875720 * 2
def baseEnd_7875720 : Nat := 1348009953409343814326743

theorem tailTrace_7875720 : CollatzResearch.WordTrace tailWord_7875720 prefixEnd_7875720 1348009953409343814326743 := by
  unfold tailWord_7875720
  simp only [CollatzResearch.WordTrace]
  refine ⟨143625553513809490367472307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191500738018412653823296409 143625553513809490367472307)
  ·
    refine ⟨215438330270714235551208461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143625553513809490367472307 215438330270714235551208461)
    ·
      refine ⟨80789373851517838331703173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215438330270714235551208461 80789373851517838331703173)
      ·
        refine ⟨15148007597159594687194345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80789373851517838331703173 15148007597159594687194345)
        ·
          refine ⟨11361005697869696015395759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15148007597159594687194345 11361005697869696015395759)
          ·
            refine ⟨17041508546804544023093639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361005697869696015395759 17041508546804544023093639)
            ·
              refine ⟨25562262820206816034640459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17041508546804544023093639 25562262820206816034640459)
              ·
                refine ⟨38343394230310224051960689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25562262820206816034640459 38343394230310224051960689)
                ·
                  refine ⟨28757545672732668038970517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38343394230310224051960689 28757545672732668038970517)
                  ·
                    refine ⟨1348009953409343814326743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28757545672732668038970517 1348009953409343814326743)
                    ·
                      rfl

theorem cell23_7875720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_7875720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875720 prefixEnd_7875720 := by exact prefixLift 7875720
  have htrace : WordTrace (prefixWord ++ tailWord_7875720) baseStart_7875720 baseEnd_7875720 := by
    simpa [prefixWord, tailWord_7875720, baseEnd_7875720] using wordTrace_append hprefix tailTrace_7875720
  have hstable : (prefixWord ++ tailWord_7875720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875720).length < 2 ^ (prefixWord ++ tailWord_7875720).sum := by decide
  have hdescent : baseEnd_7875720 < baseStart_7875720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875761 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7875761 : Nat := 118140960795 + 7875761 * 2 ^ 59
def prefixEnd_7875761 : Nat := 4983230072969 + 3 ^ 40 * 7875761 * 2
def baseEnd_7875761 : Nat := 4044050912934865782567541

theorem tailTrace_7875761 : CollatzResearch.WordTrace tailWord_7875761 prefixEnd_7875761 4044050912934865782567541 := by
  unfold tailWord_7875761
  simp only [CollatzResearch.WordTrace]
  refine ⟨287252602420470444737187137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191501734946980296491458091 287252602420470444737187137)
  ·
    refine ⟨215439451815352833552890353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287252602420470444737187137 215439451815352833552890353)
    ·
      refine ⟨161579588861514625164667765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215439451815352833552890353 161579588861514625164667765)
      ·
        refine ⟨15148086455766996109187603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161579588861514625164667765 15148086455766996109187603)
        ·
          refine ⟨22722129683650494163781405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15148086455766996109187603 22722129683650494163781405)
          ·
            refine ⟨8520798631368935311418027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22722129683650494163781405 8520798631368935311418027)
            ·
              refine ⟨12781197947053402967127041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8520798631368935311418027 12781197947053402967127041)
              ·
                refine ⟨9585898460290052225345281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12781197947053402967127041 9585898460290052225345281)
                ·
                  refine ⟨7189423845217539169008961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9585898460290052225345281 7189423845217539169008961)
                  ·
                    refine ⟨5392067883913154376756721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7189423845217539169008961 5392067883913154376756721)
                    ·
                      refine ⟨4044050912934865782567541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392067883913154376756721 4044050912934865782567541)
                      ·
                        rfl

theorem cell23_7875761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7875761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875761 prefixEnd_7875761 := by exact prefixLift 7875761
  have htrace : WordTrace (prefixWord ++ tailWord_7875761) baseStart_7875761 baseEnd_7875761 := by
    simpa [prefixWord, tailWord_7875761, baseEnd_7875761] using wordTrace_append hprefix tailTrace_7875761
  have hstable : (prefixWord ++ tailWord_7875761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875761).length < 2 ^ (prefixWord ++ tailWord_7875761).sum := by decide
  have hdescent : baseEnd_7875761 < baseStart_7875761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875763 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 2, 5]
def baseStart_7875763 : Nat := 118140960795 + 7875763 * 2 ^ 59
def prefixEnd_7875763 : Nat := 4983230072969 + 3 ^ 40 * 7875763 * 2
def baseEnd_7875763 : Nat := 1348017313298724924914177

theorem tailTrace_7875763 : CollatzResearch.WordTrace tailWord_7875763 prefixEnd_7875763 1348017313298724924914177 := by
  unfold tailWord_7875763
  simp only [CollatzResearch.WordTrace]
  refine ⟨287252675366463199078759943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191501783577642132719173295 287252675366463199078759943)
  ·
    refine ⟨430879013049694798618139915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287252675366463199078759943 430879013049694798618139915)
    ·
      refine ⟨646318519574542197927209873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430879013049694798618139915 646318519574542197927209873)
      ·
        refine ⟨484738889680906648445407405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646318519574542197927209873 484738889680906648445407405)
        ·
          refine ⟨181777083630339993167027777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484738889680906648445407405 181777083630339993167027777)
          ·
            refine ⟨136332812722754994875270833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181777083630339993167027777 136332812722754994875270833)
            ·
              refine ⟨102249609542066246156453125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136332812722754994875270833 102249609542066246156453125)
              ·
                refine ⟨19171801789137421154334961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102249609542066246156453125 19171801789137421154334961)
                ·
                  refine ⟨14378851341853065865751221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19171801789137421154334961 14378851341853065865751221)
                  ·
                    refine ⟨1348017313298724924914177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14378851341853065865751221 1348017313298724924914177)
                    ·
                      rfl

theorem cell23_7875763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 5].length) (baseStart_7875763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875763 prefixEnd_7875763 := by exact prefixLift 7875763
  have htrace : WordTrace (prefixWord ++ tailWord_7875763) baseStart_7875763 baseEnd_7875763 := by
    simpa [prefixWord, tailWord_7875763, baseEnd_7875763] using wordTrace_append hprefix tailTrace_7875763
  have hstable : (prefixWord ++ tailWord_7875763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875763).length < 2 ^ (prefixWord ++ tailWord_7875763).sum := by decide
  have hdescent : baseEnd_7875763 < baseStart_7875763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875773 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7875773 : Nat := 118140960795 + 7875773 * 2 ^ 59
def prefixEnd_7875773 : Nat := 4983230072969 + 3 ^ 40 * 7875773 * 2
def baseEnd_7875773 : Nat := 4044057074702719735617485

theorem tailTrace_7875773 : CollatzResearch.WordTrace tailWord_7875773 prefixEnd_7875773 4044057074702719735617485 := by
  unfold tailWord_7875773
  simp only [CollatzResearch.WordTrace]
  refine ⟨287253040096426970786623973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191502026730951313857749315 287253040096426970786623973)
  ·
    refine ⟨53859945018080057022491995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287253040096426970786623973 53859945018080057022491995)
    ·
      refine ⟨80789917527120085533737993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53859945018080057022491995 80789917527120085533737993)
      ·
        refine ⟨60592438145340064150303495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80789917527120085533737993 60592438145340064150303495)
        ·
          refine ⟨90888657218010096225455243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60592438145340064150303495 90888657218010096225455243)
          ·
            refine ⟨136332985827015144338182865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90888657218010096225455243 136332985827015144338182865)
            ·
              refine ⟨102249739370261358253637149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136332985827015144338182865 102249739370261358253637149)
              ·
                refine ⟨38343652263848009345113931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102249739370261358253637149 38343652263848009345113931)
                ·
                  refine ⟨57515478395772014017670897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38343652263848009345113931 57515478395772014017670897)
                  ·
                    refine ⟨43136608796829010513253173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57515478395772014017670897 43136608796829010513253173)
                    ·
                      refine ⟨4044057074702719735617485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43136608796829010513253173 4044057074702719735617485)
                      ·
                        rfl

theorem cell23_7875773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7875773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875773 prefixEnd_7875773 := by exact prefixLift 7875773
  have htrace : WordTrace (prefixWord ++ tailWord_7875773) baseStart_7875773 baseEnd_7875773 := by
    simpa [prefixWord, tailWord_7875773, baseEnd_7875773] using wordTrace_append hprefix tailTrace_7875773
  have hstable : (prefixWord ++ tailWord_7875773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875773).length < 2 ^ (prefixWord ++ tailWord_7875773).sum := by decide
  have hdescent : baseEnd_7875773 < baseStart_7875773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875777 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7875777 : Nat := 118140960795 + 7875777 * 2 ^ 59
def prefixEnd_7875777 : Nat := 4983230072969 + 3 ^ 40 * 7875777 * 2
def baseEnd_7875777 : Nat := 4044059128625337719967467

theorem tailTrace_7875777 : CollatzResearch.WordTrace tailWord_7875777 prefixEnd_7875777 4044059128625337719967467 := by
  unfold tailWord_7875777
  simp only [CollatzResearch.WordTrace]
  refine ⟨287253185988412479469769585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191502123992274986313179723 287253185988412479469769585)
  ·
    refine ⟨215439889491309359602327189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287253185988412479469769585 215439889491309359602327189)
    ·
      refine ⟨10098744819905126231359087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215439889491309359602327189 10098744819905126231359087)
      ·
        refine ⟨15148117229857689347038631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10098744819905126231359087 15148117229857689347038631)
        ·
          refine ⟨22722175844786534020557947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15148117229857689347038631 22722175844786534020557947)
          ·
            refine ⟨34083263767179801030836921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22722175844786534020557947 34083263767179801030836921)
            ·
              refine ⟨25562447825384850773127691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34083263767179801030836921 25562447825384850773127691)
              ·
                refine ⟨38343671738077276159691537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25562447825384850773127691 38343671738077276159691537)
                ·
                  refine ⟨28757753803557957119768653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38343671738077276159691537 28757753803557957119768653)
                  ·
                    refine ⟨10784157676334233919913245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28757753803557957119768653 10784157676334233919913245)
                    ·
                      refine ⟨4044059128625337719967467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10784157676334233919913245 4044059128625337719967467)
                      ·
                        rfl

theorem cell23_7875777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7875777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875777 prefixEnd_7875777 := by exact prefixLift 7875777
  have htrace : WordTrace (prefixWord ++ tailWord_7875777) baseStart_7875777 baseEnd_7875777 := by
    simpa [prefixWord, tailWord_7875777, baseEnd_7875777] using wordTrace_append hprefix tailTrace_7875777
  have hstable : (prefixWord ++ tailWord_7875777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875777).length < 2 ^ (prefixWord ++ tailWord_7875777).sum := by decide
  have hdescent : baseEnd_7875777 < baseStart_7875777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875778 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7875778 : Nat := 118140960795 + 7875778 * 2 ^ 59
def prefixEnd_7875778 : Nat := 4983230072969 + 3 ^ 40 * 7875778 * 2
def baseEnd_7875778 : Nat := 4044059642105992216054963

theorem tailTrace_7875778 : CollatzResearch.WordTrace tailWord_7875778 prefixEnd_7875778 4044059642105992216054963 := by
  unfold tailWord_7875778
  simp only [CollatzResearch.WordTrace]
  refine ⟨71813305615352214160138997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191502148307605904427037325 71813305615352214160138997)
  ·
    refine ⟨6732497401439270077513031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71813305615352214160138997 6732497401439270077513031)
    ·
      refine ⟨10098746102158905116269547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6732497401439270077513031 10098746102158905116269547)
      ·
        refine ⟨15148119153238357674404321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10098746102158905116269547 15148119153238357674404321)
        ·
          refine ⟨11361089364928768255803241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15148119153238357674404321 11361089364928768255803241)
          ·
            refine ⟨8520817023696576191852431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11361089364928768255803241 8520817023696576191852431)
            ·
              refine ⟨12781225535544864287778647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8520817023696576191852431 12781225535544864287778647)
              ·
                refine ⟨19171838303317296431667971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12781225535544864287778647 19171838303317296431667971)
                ·
                  refine ⟨28757757454975944647501957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19171838303317296431667971 28757757454975944647501957)
                  ·
                    refine ⟨5392079522807989621406617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28757757454975944647501957 5392079522807989621406617)
                    ·
                      refine ⟨4044059642105992216054963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392079522807989621406617 4044059642105992216054963)
                      ·
                        rfl

theorem cell23_7875778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7875778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875778 prefixEnd_7875778 := by exact prefixLift 7875778
  have htrace : WordTrace (prefixWord ++ tailWord_7875778) baseStart_7875778 baseEnd_7875778 := by
    simpa [prefixWord, tailWord_7875778, baseEnd_7875778] using wordTrace_append hprefix tailTrace_7875778
  have hstable : (prefixWord ++ tailWord_7875778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875778).length < 2 ^ (prefixWord ++ tailWord_7875778).sum := by decide
  have hdescent : baseEnd_7875778 < baseStart_7875778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875803 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 3]
def baseStart_7875803 : Nat := 118140960795 + 7875803 * 2 ^ 59
def prefixEnd_7875803 : Nat := 4983230072969 + 3 ^ 40 * 7875803 * 2
def baseEnd_7875803 : Nat := 4044072479122354618242347

theorem tailTrace_7875803 : CollatzResearch.WordTrace tailWord_7875803 prefixEnd_7875803 4044072479122354618242347 := by
  unfold tailWord_7875803
  simp only [CollatzResearch.WordTrace]
  refine ⟨287254134286318285910216063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191502756190878857273477375 287254134286318285910216063)
  ·
    refine ⟨430881201429477428865324095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287254134286318285910216063 430881201429477428865324095)
    ·
      refine ⟨646321802144216143297986143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430881201429477428865324095 646321802144216143297986143)
      ·
        refine ⟨969482703216324214946979215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646321802144216143297986143 969482703216324214946979215)
        ·
          refine ⟨1454224054824486322420468823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969482703216324214946979215 1454224054824486322420468823)
          ·
            refine ⟨2181336082236729483630703235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454224054824486322420468823 2181336082236729483630703235)
            ·
              refine ⟨3272004123355094225446054853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181336082236729483630703235 3272004123355094225446054853)
              ·
                refine ⟨613500773129080167271135285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3272004123355094225446054853 613500773129080167271135285)
                ·
                  refine ⟨57515697480851265681668933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 613500773129080167271135285 57515697480851265681668933)
                  ·
                    refine ⟨10784193277659612315312925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57515697480851265681668933 10784193277659612315312925)
                    ·
                      refine ⟨4044072479122354618242347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10784193277659612315312925 4044072479122354618242347)
                      ·
                        rfl

theorem cell23_7875803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 3].length) (baseStart_7875803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875803 prefixEnd_7875803 := by exact prefixLift 7875803
  have htrace : WordTrace (prefixWord ++ tailWord_7875803) baseStart_7875803 baseEnd_7875803 := by
    simpa [prefixWord, tailWord_7875803, baseEnd_7875803] using wordTrace_append hprefix tailTrace_7875803
  have hstable : (prefixWord ++ tailWord_7875803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875803).length < 2 ^ (prefixWord ++ tailWord_7875803).sum := by decide
  have hdescent : baseEnd_7875803 < baseStart_7875803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875820 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_7875820 : Nat := 118140960795 + 7875820 * 2 ^ 59
def prefixEnd_7875820 : Nat := 4983230072969 + 3 ^ 40 * 7875820 * 2
def baseEnd_7875820 : Nat := 4044081208293481051729769

theorem tailTrace_7875820 : CollatzResearch.WordTrace tailWord_7875820 prefixEnd_7875820 4044081208293481051729769 := by
  unfold tailWord_7875820
  simp only [CollatzResearch.WordTrace]
  refine ⟨143627377163628348906792457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191503169551504465209056609 143627377163628348906792457)
  ·
    refine ⟨107720532872721261680094343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143627377163628348906792457 107720532872721261680094343)
    ·
      refine ⟨161580799309081892520141515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107720532872721261680094343 161580799309081892520141515)
      ·
        refine ⟨242371198963622838780212273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161580799309081892520141515 242371198963622838780212273)
        ·
          refine ⟨181778399222717129085159205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242371198963622838780212273 181778399222717129085159205)
          ·
            refine ⟨34083449854259461703467351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181778399222717129085159205 34083449854259461703467351)
            ·
              refine ⟨51125174781389192555201027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34083449854259461703467351 51125174781389192555201027)
              ·
                refine ⟨76687762172083788832801541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51125174781389192555201027 76687762172083788832801541)
                ·
                  refine ⟨14378955407265710406150289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76687762172083788832801541 14378955407265710406150289)
                  ·
                    refine ⟨10784216555449282804612717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14378955407265710406150289 10784216555449282804612717)
                    ·
                      refine ⟨4044081208293481051729769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10784216555449282804612717 4044081208293481051729769)
                      ·
                        rfl

theorem cell23_7875820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_7875820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875820 prefixEnd_7875820 := by exact prefixLift 7875820
  have htrace : WordTrace (prefixWord ++ tailWord_7875820) baseStart_7875820 baseEnd_7875820 := by
    simpa [prefixWord, tailWord_7875820, baseEnd_7875820] using wordTrace_append hprefix tailTrace_7875820
  have hstable : (prefixWord ++ tailWord_7875820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875820).length < 2 ^ (prefixWord ++ tailWord_7875820).sum := by decide
  have hdescent : baseEnd_7875820 < baseStart_7875820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875827 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 3, 4]
def baseStart_7875827 : Nat := 118140960795 + 7875827 * 2 ^ 59
def prefixEnd_7875827 : Nat := 4983230072969 + 3 ^ 40 * 7875827 * 2
def baseEnd_7875827 : Nat := 1348028267552687508114079

theorem tailTrace_7875827 : CollatzResearch.WordTrace tailWord_7875827 prefixEnd_7875827 1348028267552687508114079 := by
  unfold tailWord_7875827
  simp only [CollatzResearch.WordTrace]
  refine ⟨287255009638231338009089735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191503339758820892006059823 287255009638231338009089735)
  ·
    refine ⟨430882514457347007013634603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287255009638231338009089735 430882514457347007013634603)
    ·
      refine ⟨646323771686020510520451905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430882514457347007013634603 646323771686020510520451905)
      ·
        refine ⟨484742828764515382890338929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646323771686020510520451905 484742828764515382890338929)
        ·
          refine ⟨363557121573386537167754197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484742828764515382890338929 363557121573386537167754197)
          ·
            refine ⟨8520870036876246964869239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 363557121573386537167754197 8520870036876246964869239)
            ·
              refine ⟨12781305055314370447303859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8520870036876246964869239 12781305055314370447303859)
              ·
                refine ⟨19171957582971555670955789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12781305055314370447303859 19171957582971555670955789)
                ·
                  refine ⟨7189484093614333376608421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19171957582971555670955789 7189484093614333376608421)
                  ·
                    refine ⟨1348028267552687508114079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7189484093614333376608421 1348028267552687508114079)
                    ·
                      rfl

theorem cell23_7875827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 4].length) (baseStart_7875827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875827 prefixEnd_7875827 := by exact prefixLift 7875827
  have htrace : WordTrace (prefixWord ++ tailWord_7875827) baseStart_7875827 baseEnd_7875827 := by
    simpa [prefixWord, tailWord_7875827, baseEnd_7875827] using wordTrace_append hprefix tailTrace_7875827
  have hstable : (prefixWord ++ tailWord_7875827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875827).length < 2 ^ (prefixWord ++ tailWord_7875827).sum := by decide
  have hdescent : baseEnd_7875827 < baseStart_7875827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875900 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_7875900 : Nat := 118140960795 + 7875900 * 2 ^ 59
def prefixEnd_7875900 : Nat := 4983230072969 + 3 ^ 40 * 7875900 * 2
def baseEnd_7875900 : Nat := 1348040762248613579576467

theorem tailTrace_7875900 : CollatzResearch.WordTrace tailWord_7875900 prefixEnd_7875900 1348040762248613579576467 := by
  unfold tailWord_7875900
  simp only [CollatzResearch.WordTrace]
  refine ⟨143628836083483435738248577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191505114777977914317664769 143628836083483435738248577)
  ·
    refine ⟨107721627062612576803686433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143628836083483435738248577 107721627062612576803686433)
    ·
      refine ⟨80791220296959432602764825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107721627062612576803686433 80791220296959432602764825)
      ·
        refine ⟨60593415222719574452073619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80791220296959432602764825 60593415222719574452073619)
        ·
          refine ⟨90890122834079361678110429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60593415222719574452073619 90890122834079361678110429)
          ·
            refine ⟨34083796062779760629291411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90890122834079361678110429 34083796062779760629291411)
            ·
              refine ⟨51125694094169640943937117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34083796062779760629291411 51125694094169640943937117)
              ·
                refine ⟨19172135285313615353976419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51125694094169640943937117 19172135285313615353976419)
                ·
                  refine ⟨28758202927970423030964629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19172135285313615353976419 28758202927970423030964629)
                  ·
                    refine ⟨1348040762248613579576467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28758202927970423030964629 1348040762248613579576467)
                    ·
                      rfl

theorem cell23_7875900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_7875900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875900 prefixEnd_7875900 := by exact prefixLift 7875900
  have htrace : WordTrace (prefixWord ++ tailWord_7875900) baseStart_7875900 baseEnd_7875900 := by
    simpa [prefixWord, tailWord_7875900, baseEnd_7875900] using wordTrace_append hprefix tailTrace_7875900
  have hstable : (prefixWord ++ tailWord_7875900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875900).length < 2 ^ (prefixWord ++ tailWord_7875900).sum := by decide
  have hdescent : baseEnd_7875900 < baseStart_7875900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875901 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7875901 : Nat := 118140960795 + 7875901 * 2 ^ 59
def prefixEnd_7875901 : Nat := 4983230072969 + 3 ^ 40 * 7875901 * 2
def baseEnd_7875901 : Nat := 4044122800226495234816897

theorem tailTrace_7875901 : CollatzResearch.WordTrace tailWord_7875901 prefixEnd_7875901 4044122800226495234816897 := by
  unfold tailWord_7875901
  simp only [CollatzResearch.WordTrace]
  refine ⟨287257708639963248647283557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191505139093308832431522371 287257708639963248647283557)
  ·
    refine ⟨53860820369993109121365667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287257708639963248647283557 53860820369993109121365667)
    ·
      refine ⟨80791230554989663682048501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53860820369993109121365667 80791230554989663682048501)
      ·
        refine ⟨7574177864530280970192047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80791230554989663682048501 7574177864530280970192047)
        ·
          refine ⟨11361266796795421455288071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7574177864530280970192047 11361266796795421455288071)
          ·
            refine ⟨17041900195193132182932107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361266796795421455288071 17041900195193132182932107)
            ·
              refine ⟨25562850292789698274398161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17041900195193132182932107 25562850292789698274398161)
              ·
                refine ⟨19172137719592273705798621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25562850292789698274398161 19172137719592273705798621)
                ·
                  refine ⟨7189551644847102639674483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19172137719592273705798621 7189551644847102639674483)
                  ·
                    refine ⟨10784327467270653959511725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7189551644847102639674483 10784327467270653959511725)
                    ·
                      refine ⟨4044122800226495234816897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10784327467270653959511725 4044122800226495234816897)
                      ·
                        rfl

theorem cell23_7875901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7875901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875901 prefixEnd_7875901 := by exact prefixLift 7875901
  have htrace : WordTrace (prefixWord ++ tailWord_7875901) baseStart_7875901 baseEnd_7875901 := by
    simpa [prefixWord, tailWord_7875901, baseEnd_7875901] using wordTrace_append hprefix tailTrace_7875901
  have hstable : (prefixWord ++ tailWord_7875901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875901).length < 2 ^ (prefixWord ++ tailWord_7875901).sum := by decide
  have hdescent : baseEnd_7875901 < baseStart_7875901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875913 : List Nat := [1, 2, 1, 1, 2, 3, 2, 11]
def baseStart_7875913 : Nat := 118140960795 + 7875913 * 2 ^ 59
def prefixEnd_7875913 : Nat := 4983230072969 + 3 ^ 40 * 7875913 * 2
def baseEnd_7875913 : Nat := 149782554147938858809883

theorem tailTrace_7875913 : CollatzResearch.WordTrace tailWord_7875913 prefixEnd_7875913 149782554147938858809883 := by
  unfold tailWord_7875913
  simp only [CollatzResearch.WordTrace]
  refine ⟨287258146315919774696720393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191505430877279849797813595 287258146315919774696720393)
  ·
    refine ⟨215443609736939831022540295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287258146315919774696720393 215443609736939831022540295)
    ·
      refine ⟨323165414605409746533810443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215443609736939831022540295 323165414605409746533810443)
      ·
        refine ⟨484748121908114619800715665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323165414605409746533810443 484748121908114619800715665)
        ·
          refine ⟨363561091431085964850536749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484748121908114619800715665 363561091431085964850536749)
          ·
            refine ⟨136335409286657236818951281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363561091431085964850536749 136335409286657236818951281)
            ·
              refine ⟨102251556964992927614213461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136335409286657236818951281 102251556964992927614213461)
              ·
                refine ⟨149782554147938858809883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 102251556964992927614213461 149782554147938858809883)
                ·
                  rfl

theorem cell23_7875913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 11].length) (baseStart_7875913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875913 prefixEnd_7875913 := by exact prefixLift 7875913
  have htrace : WordTrace (prefixWord ++ tailWord_7875913) baseStart_7875913 baseEnd_7875913 := by
    simpa [prefixWord, tailWord_7875913, baseEnd_7875913] using wordTrace_append hprefix tailTrace_7875913
  have hstable : (prefixWord ++ tailWord_7875913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875913).length < 2 ^ (prefixWord ++ tailWord_7875913).sum := by decide
  have hdescent : baseEnd_7875913 < baseStart_7875913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875920 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_7875920 : Nat := 118140960795 + 7875920 * 2 ^ 59
def prefixEnd_7875920 : Nat := 4983230072969 + 3 ^ 40 * 7875920 * 2
def baseEnd_7875920 : Nat := 4044132556358930660479309

theorem tailTrace_7875920 : CollatzResearch.WordTrace tailWord_7875920 prefixEnd_7875920 4044132556358930660479309 := by
  unfold tailWord_7875920
  simp only [CollatzResearch.WordTrace]
  refine ⟨143629200813447207446112607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191505601084596276594816809 143629200813447207446112607)
  ·
    refine ⟨215443801220170811169168911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143629200813447207446112607 215443801220170811169168911)
    ·
      refine ⟨323165701830256216753753367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215443801220170811169168911 323165701830256216753753367)
      ·
        refine ⟨484748552745384325130630051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323165701830256216753753367 484748552745384325130630051)
        ·
          refine ⟨727122829118076487695945077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484748552745384325130630051 727122829118076487695945077)
          ·
            refine ⟨68167765229819670721494851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 727122829118076487695945077 68167765229819670721494851)
            ·
              refine ⟨102251647844729506082242277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68167765229819670721494851 102251647844729506082242277)
              ·
                refine ⟨19172183970886782390420427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102251647844729506082242277 19172183970886782390420427)
                ·
                  refine ⟨28758275956330173585630641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19172183970886782390420427 28758275956330173585630641)
                  ·
                    refine ⟨21568706967247630189222981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28758275956330173585630641 21568706967247630189222981)
                    ·
                      refine ⟨4044132556358930660479309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21568706967247630189222981 4044132556358930660479309)
                      ·
                        rfl

theorem cell23_7875920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_7875920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875920 prefixEnd_7875920 := by exact prefixLift 7875920
  have htrace : WordTrace (prefixWord ++ tailWord_7875920) baseStart_7875920 baseEnd_7875920 := by
    simpa [prefixWord, tailWord_7875920, baseEnd_7875920] using wordTrace_append hprefix tailTrace_7875920
  have hstable : (prefixWord ++ tailWord_7875920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875920).length < 2 ^ (prefixWord ++ tailWord_7875920).sum := by decide
  have hdescent : baseEnd_7875920 < baseStart_7875920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875924 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_7875924 : Nat := 118140960795 + 7875924 * 2 ^ 59
def prefixEnd_7875924 : Nat := 4983230072969 + 3 ^ 40 * 7875924 * 2
def baseEnd_7875924 : Nat := 4044134610281548644829291

theorem tailTrace_7875924 : CollatzResearch.WordTrace tailWord_7875924 prefixEnd_7875924 4044134610281548644829291 := by
  unfold tailWord_7875924
  simp only [CollatzResearch.WordTrace]
  refine ⟨143629273759439961787685413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191505698345919949050247217 143629273759439961787685413)
  ·
    refine ⟨26930488829894992835191015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143629273759439961787685413 26930488829894992835191015)
    ·
      refine ⟨40395733244842489252786523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26930488829894992835191015 40395733244842489252786523)
      ·
        refine ⟨60593599867263733879179785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40395733244842489252786523 60593599867263733879179785)
        ·
          refine ⟨45445199900447800409384839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60593599867263733879179785 45445199900447800409384839)
          ·
            refine ⟨68167799850671700614077259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45445199900447800409384839 68167799850671700614077259)
            ·
              refine ⟨102251699776007550921115889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68167799850671700614077259 102251699776007550921115889)
              ·
                refine ⟨76688774832005663190836917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102251699776007550921115889 76688774832005663190836917)
                ·
                  refine ⟨7189572640500530924140961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76688774832005663190836917 7189572640500530924140961)
                  ·
                    refine ⟨5392179480375398193105721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7189572640500530924140961 5392179480375398193105721)
                    ·
                      refine ⟨4044134610281548644829291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392179480375398193105721 4044134610281548644829291)
                      ·
                        rfl

theorem cell23_7875924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_7875924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875924 prefixEnd_7875924 := by exact prefixLift 7875924
  have htrace : WordTrace (prefixWord ++ tailWord_7875924) baseStart_7875924 baseEnd_7875924 := by
    simpa [prefixWord, tailWord_7875924, baseEnd_7875924] using wordTrace_append hprefix tailTrace_7875924
  have hstable : (prefixWord ++ tailWord_7875924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875924).length < 2 ^ (prefixWord ++ tailWord_7875924).sum := by decide
  have hdescent : baseEnd_7875924 < baseStart_7875924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7875941 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 1, 2, 2]
def baseStart_7875941 : Nat := 118140960795 + 7875941 * 2 ^ 59
def prefixEnd_7875941 : Nat := 4983230072969 + 3 ^ 40 * 7875941 * 2
def baseEnd_7875941 : Nat := 4044143339452675078316713

theorem tailTrace_7875941 : CollatzResearch.WordTrace tailWord_7875941 prefixEnd_7875941 4044143339452675078316713 := by
  unfold tailWord_7875941
  simp only [CollatzResearch.WordTrace]
  refine ⟨287259167559818335478739677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191506111706545556985826451 287259167559818335478739677)
  ·
    refine ⟨107722187834931875804527379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287259167559818335478739677 107722187834931875804527379)
    ·
      refine ⟨161583281752397813706791069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107722187834931875804527379 161583281752397813706791069)
      ·
        refine ⟨60593730657149180140046651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161583281752397813706791069 60593730657149180140046651)
        ·
          refine ⟨90890595985723770210069977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60593730657149180140046651 90890595985723770210069977)
          ·
            refine ⟨68167946989292827657552483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90890595985723770210069977 68167946989292827657552483)
            ·
              refine ⟨102251920483939241486328725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68167946989292827657552483 102251920483939241486328725)
              ·
                refine ⟨4793058772684651944671659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102251920483939241486328725 4793058772684651944671659)
                ·
                  refine ⟨7189588159026977917007489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793058772684651944671659 7189588159026977917007489)
                  ·
                    refine ⟨5392191119270233437755617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7189588159026977917007489 5392191119270233437755617)
                    ·
                      refine ⟨4044143339452675078316713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392191119270233437755617 4044143339452675078316713)
                      ·
                        rfl

theorem cell23_7875941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_7875941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7875941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7875941 prefixEnd_7875941 := by exact prefixLift 7875941
  have htrace : WordTrace (prefixWord ++ tailWord_7875941) baseStart_7875941 baseEnd_7875941 := by
    simpa [prefixWord, tailWord_7875941, baseEnd_7875941] using wordTrace_append hprefix tailTrace_7875941
  have hstable : (prefixWord ++ tailWord_7875941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7875941).length < 2 ^ (prefixWord ++ tailWord_7875941).sum := by decide
  have hdescent : baseEnd_7875941 < baseStart_7875941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7875941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876000 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_7876000 : Nat := 118140960795 + 7876000 * 2 ^ 59
def prefixEnd_7876000 : Nat := 4983230072969 + 3 ^ 40 * 7876000 * 2
def baseEnd_7876000 : Nat := 4044173634811290347478941

theorem tailTrace_7876000 : CollatzResearch.WordTrace tailWord_7876000 prefixEnd_7876000 4044173634811290347478941 := by
  unfold tailWord_7876000
  simp only [CollatzResearch.WordTrace]
  refine ⟨143630659733302294277568727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191507546311069725703424969 143630659733302294277568727)
  ·
    refine ⟨215445989599953441416353091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143630659733302294277568727 215445989599953441416353091)
    ·
      refine ⟨323168984399930162124529637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215445989599953441416353091 323168984399930162124529637)
      ·
        refine ⟨60594184574986905398349307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323168984399930162124529637 60594184574986905398349307)
        ·
          refine ⟨90891276862480358097523961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60594184574986905398349307 90891276862480358097523961)
          ·
            refine ⟨68168457646860268573142971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90891276862480358097523961 68168457646860268573142971)
            ·
              refine ⟨102252686470290402859714457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68168457646860268573142971 102252686470290402859714457)
              ·
                refine ⟨76689514852717802144785843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102252686470290402859714457 76689514852717802144785843)
                ·
                  refine ⟨115034272279076703217178765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76689514852717802144785843 115034272279076703217178765)
                  ·
                    refine ⟨43137852104653763706442037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115034272279076703217178765 43137852104653763706442037)
                    ·
                      refine ⟨4044173634811290347478941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43137852104653763706442037 4044173634811290347478941)
                      ·
                        rfl

theorem cell23_7876000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_7876000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876000 prefixEnd_7876000 := by exact prefixLift 7876000
  have htrace : WordTrace (prefixWord ++ tailWord_7876000) baseStart_7876000 baseEnd_7876000 := by
    simpa [prefixWord, tailWord_7876000, baseEnd_7876000] using wordTrace_append hprefix tailTrace_7876000
  have hstable : (prefixWord ++ tailWord_7876000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876000).length < 2 ^ (prefixWord ++ tailWord_7876000).sum := by decide
  have hdescent : baseEnd_7876000 < baseStart_7876000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876008 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7876008 : Nat := 118140960795 + 7876008 * 2 ^ 59
def prefixEnd_7876008 : Nat := 4983230072969 + 3 ^ 40 * 7876008 * 2
def baseEnd_7876008 : Nat := 4044177742656526316178905

theorem tailTrace_7876008 : CollatzResearch.WordTrace tailWord_7876008 prefixEnd_7876008 4044177742656526316178905 := by
  unfold tailWord_7876008
  simp only [CollatzResearch.WordTrace]
  refine ⟨143630805625287802960714339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191507740833717070614285785 143630805625287802960714339)
  ·
    refine ⟨215446208437931704441071509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143630805625287802960714339 215446208437931704441071509)
    ·
      refine ⟨10099041020528048645675227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215446208437931704441071509 10099041020528048645675227)
      ·
        refine ⟨15148561530792072968512841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099041020528048645675227 15148561530792072968512841)
        ·
          refine ⟨11361421148094054726384631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15148561530792072968512841 11361421148094054726384631)
          ·
            refine ⟨17042131722141082089576947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361421148094054726384631 17042131722141082089576947)
            ·
              refine ⟨25563197583211623134365421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042131722141082089576947 25563197583211623134365421)
              ·
                refine ⟨9586199093704358675387033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25563197583211623134365421 9586199093704358675387033)
                ·
                  refine ⟨7189649320278269006540275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9586199093704358675387033 7189649320278269006540275)
                  ·
                    refine ⟨10784473980417403509810413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7189649320278269006540275 10784473980417403509810413)
                    ·
                      refine ⟨4044177742656526316178905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10784473980417403509810413 4044177742656526316178905)
                      ·
                        rfl

theorem cell23_7876008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7876008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876008 prefixEnd_7876008 := by exact prefixLift 7876008
  have htrace : WordTrace (prefixWord ++ tailWord_7876008) baseStart_7876008 baseEnd_7876008 := by
    simpa [prefixWord, tailWord_7876008, baseEnd_7876008] using wordTrace_append hprefix tailTrace_7876008
  have hstable : (prefixWord ++ tailWord_7876008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876008).length < 2 ^ (prefixWord ++ tailWord_7876008).sum := by decide
  have hdescent : baseEnd_7876008 < baseStart_7876008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876087 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_7876087 : Nat := 118140960795 + 7876087 * 2 ^ 59
def prefixEnd_7876087 : Nat := 4983230072969 + 3 ^ 40 * 7876087 * 2
def baseEnd_7876087 : Nat := 4044218307628231507091041

theorem tailTrace_7876087 : CollatzResearch.WordTrace tailWord_7876087 prefixEnd_7876087 4044218307628231507091041 := by
  unfold tailWord_7876087
  simp only [CollatzResearch.WordTrace]
  refine ⟨287264492617289402413554515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191509661744859601609036343 287264492617289402413554515)
  ·
    refine ⟨430896738925934103620331773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287264492617289402413554515 430896738925934103620331773)
    ·
      refine ⟨161586277097225288857624415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430896738925934103620331773 161586277097225288857624415)
      ·
        refine ⟨242379415645837933286436623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161586277097225288857624415 242379415645837933286436623)
        ·
          refine ⟨363569123468756899929654935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242379415645837933286436623 363569123468756899929654935)
          ·
            refine ⟨545353685203135349894482403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363569123468756899929654935 545353685203135349894482403)
            ·
              refine ⟨818030527804703024841723605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545353685203135349894482403 818030527804703024841723605)
              ·
                refine ⟨19172590495422727144727897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 818030527804703024841723605 19172590495422727144727897)
                ·
                  refine ⟨14379442871567045358545923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19172590495422727144727897 14379442871567045358545923)
                  ·
                    refine ⟨21569164307350568037818885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14379442871567045358545923 21569164307350568037818885)
                    ·
                      refine ⟨4044218307628231507091041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21569164307350568037818885 4044218307628231507091041)
                      ·
                        rfl

theorem cell23_7876087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_7876087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876087 prefixEnd_7876087 := by exact prefixLift 7876087
  have htrace : WordTrace (prefixWord ++ tailWord_7876087) baseStart_7876087 baseEnd_7876087 := by
    simpa [prefixWord, tailWord_7876087, baseEnd_7876087] using wordTrace_append hprefix tailTrace_7876087
  have hstable : (prefixWord ++ tailWord_7876087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876087).length < 2 ^ (prefixWord ++ tailWord_7876087).sum := by decide
  have hdescent : baseEnd_7876087 < baseStart_7876087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876104 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_7876104 : Nat := 118140960795 + 7876104 * 2 ^ 59
def prefixEnd_7876104 : Nat := 4983230072969 + 3 ^ 40 * 7876104 * 2
def baseEnd_7876104 : Nat := 4044227036799357940578463

theorem tailTrace_7876104 : CollatzResearch.WordTrace tailWord_7876104 prefixEnd_7876104 4044227036799357940578463 := by
  unfold tailWord_7876104
  simp only [CollatzResearch.WordTrace]
  refine ⟨143632556329113907158461683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191510075105485209544615577 143632556329113907158461683)
  ·
    refine ⟨215448834493670860737692525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143632556329113907158461683 215448834493670860737692525)
    ·
      refine ⟨80793312935126572776634697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215448834493670860737692525 80793312935126572776634697)
      ·
        refine ⟨60594984701344929582476023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80793312935126572776634697 60594984701344929582476023)
        ·
          refine ⟨90892477052017394373714035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60594984701344929582476023 90892477052017394373714035)
          ·
            refine ⟨136338715578026091560571053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90892477052017394373714035 136338715578026091560571053)
            ·
              refine ⟨51127018341759784335214145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136338715578026091560571053 51127018341759784335214145)
              ·
                refine ⟨38345263756319838251410609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51127018341759784335214145 38345263756319838251410609)
                ·
                  refine ⟨28758947817239878688557957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38345263756319838251410609 28758947817239878688557957)
                  ·
                    refine ⟨5392302715732477254104617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28758947817239878688557957 5392302715732477254104617)
                    ·
                      refine ⟨4044227036799357940578463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392302715732477254104617 4044227036799357940578463)
                      ·
                        rfl

theorem cell23_7876104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_7876104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876104 prefixEnd_7876104 := by exact prefixLift 7876104
  have htrace : WordTrace (prefixWord ++ tailWord_7876104) baseStart_7876104 baseEnd_7876104 := by
    simpa [prefixWord, tailWord_7876104, baseEnd_7876104] using wordTrace_append hprefix tailTrace_7876104
  have hstable : (prefixWord ++ tailWord_7876104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876104).length < 2 ^ (prefixWord ++ tailWord_7876104).sum := by decide
  have hdescent : baseEnd_7876104 < baseStart_7876104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876127 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 6]
def baseStart_7876127 : Nat := 118140960795 + 7876127 * 2 ^ 59
def prefixEnd_7876127 : Nat := 4983230072969 + 3 ^ 40 * 7876127 * 2
def baseEnd_7876127 : Nat := 449359871872712372287873

theorem tailTrace_7876127 : CollatzResearch.WordTrace tailWord_7876127 prefixEnd_7876127 449359871872712372287873 := by
  unfold tailWord_7876127
  simp only [CollatzResearch.WordTrace]
  refine ⟨287265951537144489245010635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191510634358096326163340423 287265951537144489245010635)
  ·
    refine ⟨430898927305716733867515953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287265951537144489245010635 430898927305716733867515953)
    ·
      refine ⟨323174195479287550400636965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430898927305716733867515953 323174195479287550400636965)
      ·
        refine ⟨60595161652366415700119431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323174195479287550400636965 60595161652366415700119431)
        ·
          refine ⟨90892742478549623550179147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60595161652366415700119431 90892742478549623550179147)
          ·
            refine ⟨136339113717824435325268721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90892742478549623550179147 136339113717824435325268721)
            ·
              refine ⟨102254335288368326493951541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136339113717824435325268721 102254335288368326493951541)
              ·
                refine ⟨9586343933284530608807957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102254335288368326493951541 9586343933284530608807957)
                ·
                  refine ⟨449359871872712372287873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9586343933284530608807957 449359871872712372287873)
                  ·
                    rfl

theorem cell23_7876127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 6].length) (baseStart_7876127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876127 prefixEnd_7876127 := by exact prefixLift 7876127
  have htrace : WordTrace (prefixWord ++ tailWord_7876127) baseStart_7876127 baseEnd_7876127 := by
    simpa [prefixWord, tailWord_7876127, baseEnd_7876127] using wordTrace_append hprefix tailTrace_7876127
  have hstable : (prefixWord ++ tailWord_7876127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876127).length < 2 ^ (prefixWord ++ tailWord_7876127).sum := by decide
  have hdescent : baseEnd_7876127 < baseStart_7876127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876221 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_7876221 : Nat := 118140960795 + 7876221 * 2 ^ 59
def prefixEnd_7876221 : Nat := 4983230072969 + 3 ^ 40 * 7876221 * 2
def baseEnd_7876221 : Nat := 1348095704678644660938475

theorem tailTrace_7876221 : CollatzResearch.WordTrace tailWord_7876221 prefixEnd_7876221 1348095704678644660938475 := by
  unfold tailWord_7876221
  simp only [CollatzResearch.WordTrace]
  refine ⟨287269379998803943298932517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191512919999202628865955011 287269379998803943298932517)
  ·
    refine ⟨53863008749775739368549847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287269379998803943298932517 53863008749775739368549847)
    ·
      refine ⟨80794513124663609052824771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53863008749775739368549847 80794513124663609052824771)
      ·
        refine ⟨121191769686995413579237157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80794513124663609052824771 121191769686995413579237157)
        ·
          refine ⟨22723456816311640046106967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121191769686995413579237157 22723456816311640046106967)
          ·
            refine ⟨34085185224467460069160451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22723456816311640046106967 34085185224467460069160451)
            ·
              refine ⟨51127777836701190103740677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34085185224467460069160451 51127777836701190103740677)
              ·
                refine ⟨9586458344381473144451377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51127777836701190103740677 9586458344381473144451377)
                ·
                  refine ⟨7189843758286104858338533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9586458344381473144451377 7189843758286104858338533)
                  ·
                    refine ⟨1348095704678644660938475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7189843758286104858338533 1348095704678644660938475)
                    ·
                      rfl

theorem cell23_7876221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_7876221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876221 prefixEnd_7876221 := by exact prefixLift 7876221
  have htrace : WordTrace (prefixWord ++ tailWord_7876221) baseStart_7876221 baseEnd_7876221 := by
    simpa [prefixWord, tailWord_7876221, baseEnd_7876221] using wordTrace_append hprefix tailTrace_7876221
  have hstable : (prefixWord ++ tailWord_7876221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876221).length < 2 ^ (prefixWord ++ tailWord_7876221).sum := by decide
  have hdescent : baseEnd_7876221 < baseStart_7876221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876234 : List Nat := [3, 1, 2, 3, 2, 1, 3, 8]
def baseStart_7876234 : Nat := 118140960795 + 7876234 * 2 ^ 59
def prefixEnd_7876234 : Nat := 4983230072969 + 3 ^ 40 * 7876234 * 2
def baseEnd_7876234 : Nat := 149788658862386756738995

theorem tailTrace_7876234 : CollatzResearch.WordTrace tailWord_7876234 prefixEnd_7876234 149788658862386756738995 := by
  unfold tailWord_7876234
  simp only [CollatzResearch.WordTrace]
  refine ⟨71817463536939211629788939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191513236098504564346103837 71817463536939211629788939)
  ·
    refine ⟨107726195305408817444683409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71817463536939211629788939 107726195305408817444683409)
    ·
      refine ⟨80794646479056613083512557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107726195305408817444683409 80794646479056613083512557)
      ·
        refine ⟨30297992429646229906317209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80794646479056613083512557 30297992429646229906317209)
        ·
          refine ⟨22723494322234672429737907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30297992429646229906317209 22723494322234672429737907)
          ·
            refine ⟨34085241483352008644606861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22723494322234672429737907 34085241483352008644606861)
            ·
              refine ⟨12781965556257003241727573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34085241483352008644606861 12781965556257003241727573)
              ·
                refine ⟨149788658862386756738995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12781965556257003241727573 149788658862386756738995)
                ·
                  rfl

theorem cell23_7876234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_7876234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876234 prefixEnd_7876234 := by exact prefixLift 7876234
  have htrace : WordTrace (prefixWord ++ tailWord_7876234) baseStart_7876234 baseEnd_7876234 := by
    simpa [prefixWord, tailWord_7876234, baseEnd_7876234] using wordTrace_append hprefix tailTrace_7876234
  have hstable : (prefixWord ++ tailWord_7876234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876234).length < 2 ^ (prefixWord ++ tailWord_7876234).sum := by decide
  have hdescent : baseEnd_7876234 < baseStart_7876234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876297 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_7876297 : Nat := 118140960795 + 7876297 * 2 ^ 59
def prefixEnd_7876297 : Nat := 4983230072969 + 3 ^ 40 * 7876297 * 2
def baseEnd_7876297 : Nat := 4044326138565675685465075

theorem tailTrace_7876297 : CollatzResearch.WordTrace tailWord_7876297 prefixEnd_7876297 4044326138565675685465075 := by
  unfold tailWord_7876297
  simp only [CollatzResearch.WordTrace]
  refine ⟨287272151946528608278699145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191514767964352405519132763 287272151946528608278699145)
  ·
    refine ⟨215454113959896456209024359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287272151946528608278699145 215454113959896456209024359)
    ·
      refine ⟨323181170939844684313536539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215454113959896456209024359 323181170939844684313536539)
      ·
        refine ⟨484771756409767026470304809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323181170939844684313536539 484771756409767026470304809)
        ·
          refine ⟨363578817307325269852728607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484771756409767026470304809 363578817307325269852728607)
          ·
            refine ⟨545368225960987904779092911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363578817307325269852728607 545368225960987904779092911)
            ·
              refine ⟨818052338941481857168639367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545368225960987904779092911 818052338941481857168639367)
              ·
                refine ⟨1227078508412222785752959051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818052338941481857168639367 1227078508412222785752959051)
                ·
                  refine ⟨1840617762618334178629438577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227078508412222785752959051 1840617762618334178629438577)
                  ·
                    refine ⟨1380463321963750633972078933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840617762618334178629438577 1380463321963750633972078933)
                    ·
                      refine ⟨4044326138565675685465075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1380463321963750633972078933 4044326138565675685465075)
                      ·
                        rfl

theorem cell23_7876297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_7876297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876297 prefixEnd_7876297 := by exact prefixLift 7876297
  have htrace : WordTrace (prefixWord ++ tailWord_7876297) baseStart_7876297 baseEnd_7876297 := by
    simpa [prefixWord, tailWord_7876297, baseEnd_7876297] using wordTrace_append hprefix tailTrace_7876297
  have hstable : (prefixWord ++ tailWord_7876297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876297).length < 2 ^ (prefixWord ++ tailWord_7876297).sum := by decide
  have hdescent : baseEnd_7876297 < baseStart_7876297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876307 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 13]
def baseStart_7876307 : Nat := 118140960795 + 7876307 * 2 ^ 59
def prefixEnd_7876307 : Nat := 4983230072969 + 3 ^ 40 * 7876307 * 2
def baseEnd_7876307 : Nat := 449370141485802294037781

theorem tailTrace_7876307 : CollatzResearch.WordTrace tailWord_7876307 prefixEnd_7876307 449370141485802294037781 := by
  unfold tailWord_7876307
  simp only [CollatzResearch.WordTrace]
  refine ⟨287272516676492379986563175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191515011117661586657708783 287272516676492379986563175)
  ·
    refine ⟨430908775014738569979844763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287272516676492379986563175 430908775014738569979844763)
    ·
      refine ⟨646363162522107854969767145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430908775014738569979844763 646363162522107854969767145)
      ·
        refine ⟨484772371891580891227325359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646363162522107854969767145 484772371891580891227325359)
        ·
          refine ⟨727158557837371336840988039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484772371891580891227325359 727158557837371336840988039)
          ·
            refine ⟨1090737836756057005261482059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727158557837371336840988039 1090737836756057005261482059)
            ·
              refine ⟨1636106755134085507892223089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090737836756057005261482059 1636106755134085507892223089)
              ·
                refine ⟨1227080066350564130919167317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636106755134085507892223089 1227080066350564130919167317)
                ·
                  refine ⟨449370141485802294037781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1227080066350564130919167317 449370141485802294037781)
                  ·
                    rfl

theorem cell23_7876307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 13].length) (baseStart_7876307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876307 prefixEnd_7876307 := by exact prefixLift 7876307
  have htrace : WordTrace (prefixWord ++ tailWord_7876307) baseStart_7876307 baseEnd_7876307 := by
    simpa [prefixWord, tailWord_7876307, baseEnd_7876307] using wordTrace_append hprefix tailTrace_7876307
  have hstable : (prefixWord ++ tailWord_7876307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876307).length < 2 ^ (prefixWord ++ tailWord_7876307).sum := by decide
  have hdescent : baseEnd_7876307 < baseStart_7876307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876321 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_7876321 : Nat := 118140960795 + 7876321 * 2 ^ 59
def prefixEnd_7876321 : Nat := 4983230072969 + 3 ^ 40 * 7876321 * 2
def baseEnd_7876321 : Nat := 4044338462101383591564965

theorem tailTrace_7876321 : CollatzResearch.WordTrace tailWord_7876321 prefixEnd_7876321 4044338462101383591564965 := by
  unfold tailWord_7876321
  simp only [CollatzResearch.WordTrace]
  refine ⟨287273027298441660377572817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191515351532294440251715211 287273027298441660377572817)
  ·
    refine ⟨215454770473831245283179613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287273027298441660377572817 215454770473831245283179613)
    ·
      refine ⟨80795538927686716981192355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215454770473831245283179613 80795538927686716981192355)
      ·
        refine ⟨121193308391530075471788533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80795538927686716981192355 121193308391530075471788533)
        ·
          refine ⟨11361872661705944575480175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121193308391530075471788533 11361872661705944575480175)
          ·
            refine ⟨17042808992558916863220263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361872661705944575480175 17042808992558916863220263)
            ·
              refine ⟨25564213488838375294830395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042808992558916863220263 25564213488838375294830395)
              ·
                refine ⟨38346320233257562942245593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564213488838375294830395 38346320233257562942245593)
                ·
                  refine ⟨28759740174943172206684195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38346320233257562942245593 28759740174943172206684195)
                  ·
                    refine ⟨43139610262414758310026293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28759740174943172206684195 43139610262414758310026293)
                    ·
                      refine ⟨4044338462101383591564965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43139610262414758310026293 4044338462101383591564965)
                      ·
                        rfl

theorem cell23_7876321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_7876321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876321 prefixEnd_7876321 := by exact prefixLift 7876321
  have htrace : WordTrace (prefixWord ++ tailWord_7876321) baseStart_7876321 baseEnd_7876321 := by
    simpa [prefixWord, tailWord_7876321, baseEnd_7876321] using wordTrace_append hprefix tailTrace_7876321
  have hstable : (prefixWord ++ tailWord_7876321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876321).length < 2 ^ (prefixWord ++ tailWord_7876321).sum := by decide
  have hdescent : baseEnd_7876321 < baseStart_7876321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876334 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_7876334 : Nat := 118140960795 + 7876334 * 2 ^ 59
def prefixEnd_7876334 : Nat := 4983230072969 + 3 ^ 40 * 7876334 * 2
def baseEnd_7876334 : Nat := 4044345137349892040702405

theorem tailTrace_7876334 : CollatzResearch.WordTrace tailWord_7876334 prefixEnd_7876334 4044345137349892040702405 := by
  unfold tailWord_7876334
  simp only [CollatzResearch.WordTrace]
  refine ⟨35909187680924320449724507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191515667631596375731864037 35909187680924320449724507)
  ·
    refine ⟨53863781521386480674586761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35909187680924320449724507 53863781521386480674586761)
    ·
      refine ⟨40397836141039860505940071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53863781521386480674586761 40397836141039860505940071)
      ·
        refine ⟨60596754211559790758910107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40397836141039860505940071 60596754211559790758910107)
        ·
          refine ⟨90895131317339686138365161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60596754211559790758910107 90895131317339686138365161)
          ·
            refine ⟨68171348488004764603773871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90895131317339686138365161 68171348488004764603773871)
            ·
              refine ⟨102257022732007146905660807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68171348488004764603773871 102257022732007146905660807)
              ·
                refine ⟨153385534098010720358491211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102257022732007146905660807 153385534098010720358491211)
                ·
                  refine ⟨230078301147016080537736817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153385534098010720358491211 230078301147016080537736817)
                  ·
                    refine ⟨172558725860262060403302613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230078301147016080537736817 172558725860262060403302613)
                    ·
                      refine ⟨4044345137349892040702405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172558725860262060403302613 4044345137349892040702405)
                      ·
                        rfl

theorem cell23_7876334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_7876334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876334 prefixEnd_7876334 := by exact prefixLift 7876334
  have htrace : WordTrace (prefixWord ++ tailWord_7876334) baseStart_7876334 baseEnd_7876334 := by
    simpa [prefixWord, tailWord_7876334, baseEnd_7876334] using wordTrace_append hprefix tailTrace_7876334
  have hstable : (prefixWord ++ tailWord_7876334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876334).length < 2 ^ (prefixWord ++ tailWord_7876334).sum := by decide
  have hdescent : baseEnd_7876334 < baseStart_7876334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876408 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 2, 4, 2]
def baseStart_7876408 : Nat := 118140960795 + 7876408 * 2 ^ 59
def prefixEnd_7876408 : Nat := 4983230072969 + 3 ^ 40 * 7876408 * 2
def baseEnd_7876408 : Nat := 4044383134918324751177065

theorem tailTrace_7876408 : CollatzResearch.WordTrace tailWord_7876408 prefixEnd_7876408 4044383134918324751177065 := by
  unfold tailWord_7876408
  simp only [CollatzResearch.WordTrace]
  refine ⟨143638100224563237117994939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191517466966084316157326585 143638100224563237117994939)
  ·
    refine ⟨215457150336844855676992409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143638100224563237117994939 215457150336844855676992409)
    ·
      refine ⟨161592862752633641757744307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215457150336844855676992409 161592862752633641757744307)
      ·
        refine ⟨242389294128950462636616461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161592862752633641757744307 242389294128950462636616461)
        ·
          refine ⟨90895985298356423488731173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242389294128950462636616461 90895985298356423488731173)
          ·
            refine ⟨17042997243441829404137095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90895985298356423488731173 17042997243441829404137095)
            ·
              refine ⟨25564495865162744106205643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042997243441829404137095 25564495865162744106205643)
              ·
                refine ⟨38346743797744116159308465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564495865162744106205643 38346743797744116159308465)
                ·
                  refine ⟨28760057848308087119481349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38346743797744116159308465 28760057848308087119481349)
                  ·
                    refine ⟨5392510846557766334902753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28760057848308087119481349 5392510846557766334902753)
                    ·
                      refine ⟨4044383134918324751177065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392510846557766334902753 4044383134918324751177065)
                      ·
                        rfl

theorem cell23_7876408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_7876408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876408 prefixEnd_7876408 := by exact prefixLift 7876408
  have htrace : WordTrace (prefixWord ++ tailWord_7876408) baseStart_7876408 baseEnd_7876408 := by
    simpa [prefixWord, tailWord_7876408, baseEnd_7876408] using wordTrace_append hprefix tailTrace_7876408
  have hstable : (prefixWord ++ tailWord_7876408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876408).length < 2 ^ (prefixWord ++ tailWord_7876408).sum := by decide
  have hdescent : baseEnd_7876408 < baseStart_7876408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876422 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_7876422 : Nat := 118140960795 + 7876422 * 2 ^ 59
def prefixEnd_7876422 : Nat := 4983230072969 + 3 ^ 40 * 7876422 * 2
def baseEnd_7876422 : Nat := 1348130107882495898800667

theorem tailTrace_7876422 : CollatzResearch.WordTrace tailWord_7876422 prefixEnd_7876422 1348130107882495898800667 := by
  unfold tailWord_7876422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977397220971117332093735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191517807380717169751333013 8977397220971117332093735)
  ·
    refine ⟨13466095831456675998140603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8977397220971117332093735 13466095831456675998140603)
    ·
      refine ⟨20199143747185013997210905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466095831456675998140603 20199143747185013997210905)
      ·
        refine ⟨15149357810388760497908179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20199143747185013997210905 15149357810388760497908179)
        ·
          refine ⟨22724036715583140746862269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15149357810388760497908179 22724036715583140746862269)
          ·
            refine ⟨8521513768343677780073351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22724036715583140746862269 8521513768343677780073351)
            ·
              refine ⟨12782270652515516670110027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521513768343677780073351 12782270652515516670110027)
              ·
                refine ⟨19173405978773275005165041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12782270652515516670110027 19173405978773275005165041)
                ·
                  refine ⟨14380054484079956253873781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19173405978773275005165041 14380054484079956253873781)
                  ·
                    refine ⟨1348130107882495898800667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14380054484079956253873781 1348130107882495898800667)
                    ·
                      rfl

theorem cell23_7876422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_7876422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876422 prefixEnd_7876422 := by exact prefixLift 7876422
  have htrace : WordTrace (prefixWord ++ tailWord_7876422) baseStart_7876422 baseEnd_7876422 := by
    simpa [prefixWord, tailWord_7876422, baseEnd_7876422] using wordTrace_append hprefix tailTrace_7876422
  have hstable : (prefixWord ++ tailWord_7876422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876422).length < 2 ^ (prefixWord ++ tailWord_7876422).sum := by decide
  have hdescent : baseEnd_7876422 < baseStart_7876422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876428 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_7876428 : Nat := 118140960795 + 7876428 * 2 ^ 59
def prefixEnd_7876428 : Nat := 4983230072969 + 3 ^ 40 * 7876428 * 2
def baseEnd_7876428 : Nat := 4044393404531414672926973

theorem tailTrace_7876428 : CollatzResearch.WordTrace tailWord_7876428 prefixEnd_7876428 4044393404531414672926973 := by
  unfold tailWord_7876428
  simp only [CollatzResearch.WordTrace]
  refine ⟨143638464954527008825858969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191517953272702678434478625 143638464954527008825858969)
  ·
    refine ⟨107728848715895256619394227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143638464954527008825858969 107728848715895256619394227)
    ·
      refine ⟨161593273073842884929091341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107728848715895256619394227 161593273073842884929091341)
      ·
        refine ⟨60597477402691081848409253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161593273073842884929091341 60597477402691081848409253)
        ·
          refine ⟨11362027013004577846576735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60597477402691081848409253 11362027013004577846576735)
          ·
            refine ⟨17043040519506866769865103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362027013004577846576735 17043040519506866769865103)
            ·
              refine ⟨25564560779260300154797655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043040519506866769865103 25564560779260300154797655)
              ·
                refine ⟨38346841168890450232196483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564560779260300154797655 38346841168890450232196483)
                ·
                  refine ⟨57520261753335675348294725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38346841168890450232196483 57520261753335675348294725)
                  ·
                    refine ⟨10785049078750439127805261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57520261753335675348294725 10785049078750439127805261)
                    ·
                      refine ⟨4044393404531414672926973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10785049078750439127805261 4044393404531414672926973)
                      ·
                        rfl

theorem cell23_7876428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_7876428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876428 prefixEnd_7876428 := by exact prefixLift 7876428
  have htrace : WordTrace (prefixWord ++ tailWord_7876428) baseStart_7876428 baseEnd_7876428 := by
    simpa [prefixWord, tailWord_7876428, baseEnd_7876428] using wordTrace_append hprefix tailTrace_7876428
  have hstable : (prefixWord ++ tailWord_7876428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876428).length < 2 ^ (prefixWord ++ tailWord_7876428).sum := by decide
  have hdescent : baseEnd_7876428 < baseStart_7876428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876448 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 6]
def baseStart_7876448 : Nat := 118140960795 + 7876448 * 2 ^ 59
def prefixEnd_7876448 : Nat := 4983230072969 + 3 ^ 40 * 7876448 * 2
def baseEnd_7876448 : Nat := 449378186016056066075209

theorem tailTrace_7876448 : CollatzResearch.WordTrace tailWord_7876448 prefixEnd_7876448 449378186016056066075209 := by
  unfold tailWord_7876448
  simp only [CollatzResearch.WordTrace]
  refine ⟨143638829684490780533722999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191518439579321040711630665 143638829684490780533722999)
  ·
    refine ⟨215458244526736170800584499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143638829684490780533722999 215458244526736170800584499)
    ·
      refine ⟨323187366790104256200876749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215458244526736170800584499 323187366790104256200876749)
      ·
        refine ⟨121195262546289096075328781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323187366790104256200876749 121195262546289096075328781)
        ·
          refine ⟨45448223454858411028248293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121195262546289096075328781 45448223454858411028248293)
          ·
            refine ⟨8521541897785952067796555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45448223454858411028248293 8521541897785952067796555)
            ·
              refine ⟨12782312846678928101694833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521541897785952067796555 12782312846678928101694833)
              ·
                refine ⟨9586734635009196076271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12782312846678928101694833 9586734635009196076271125)
                ·
                  refine ⟨449378186016056066075209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9586734635009196076271125 449378186016056066075209)
                  ·
                    rfl

theorem cell23_7876448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_7876448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876448 prefixEnd_7876448 := by exact prefixLift 7876448
  have htrace : WordTrace (prefixWord ++ tailWord_7876448) baseStart_7876448 baseEnd_7876448 := by
    simpa [prefixWord, tailWord_7876448, baseEnd_7876448] using wordTrace_append hprefix tailTrace_7876448
  have hstable : (prefixWord ++ tailWord_7876448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876448).length < 2 ^ (prefixWord ++ tailWord_7876448).sum := by decide
  have hdescent : baseEnd_7876448 < baseStart_7876448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876461 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_7876461 : Nat := 118140960795 + 7876461 * 2 ^ 59
def prefixEnd_7876461 : Nat := 4983230072969 + 3 ^ 40 * 7876461 * 2
def baseEnd_7876461 : Nat := 1348136783131004347938107

theorem tailTrace_7876461 : CollatzResearch.WordTrace tailWord_7876461 prefixEnd_7876461 1348136783131004347938107 := by
  unfold tailWord_7876461
  simp only [CollatzResearch.WordTrace]
  refine ⟨287278133517934464287669237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191518755678622976191779491 287278133517934464287669237)
  ·
    refine ⟨26932325017306356026968991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287278133517934464287669237 26932325017306356026968991)
    ·
      refine ⟨40398487525959534040453487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26932325017306356026968991 40398487525959534040453487)
      ·
        refine ⟨60597731288939301060680231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40398487525959534040453487 60597731288939301060680231)
        ·
          refine ⟨90896596933408951591020347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60597731288939301060680231 90896596933408951591020347)
          ·
            refine ⟨136344895400113427386530521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90896596933408951591020347 136344895400113427386530521)
            ·
              refine ⟨102258671550085070539897891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136344895400113427386530521 102258671550085070539897891)
              ·
                refine ⟨153388007325127605809846837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102258671550085070539897891 153388007325127605809846837)
                ·
                  refine ⟨14380125686730713044673141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153388007325127605809846837 14380125686730713044673141)
                  ·
                    refine ⟨1348136783131004347938107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14380125686730713044673141 1348136783131004347938107)
                    ·
                      rfl

theorem cell23_7876461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_7876461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876461 prefixEnd_7876461 := by exact prefixLift 7876461
  have htrace : WordTrace (prefixWord ++ tailWord_7876461) baseStart_7876461 baseEnd_7876461 := by
    simpa [prefixWord, tailWord_7876461, baseEnd_7876461] using wordTrace_append hprefix tailTrace_7876461
  have hstable : (prefixWord ++ tailWord_7876461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876461).length < 2 ^ (prefixWord ++ tailWord_7876461).sum := by decide
  have hdescent : baseEnd_7876461 < baseStart_7876461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876509 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_7876509 : Nat := 118140960795 + 7876509 * 2 ^ 59
def prefixEnd_7876509 : Nat := 4983230072969 + 3 ^ 40 * 7876509 * 2
def baseEnd_7876509 : Nat := 4044434996464428856014101

theorem tailTrace_7876509 : CollatzResearch.WordTrace tailWord_7876509 prefixEnd_7876509 4044434996464428856014101 := by
  unfold tailWord_7876509
  simp only [CollatzResearch.WordTrace]
  refine ⟨287279884221760568485416581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191519922814507045656944387 287279884221760568485416581)
  ·
    refine ⟨53864978291580106591015609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287279884221760568485416581 53864978291580106591015609)
    ·
      refine ⟨40398733718685079943261707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53864978291580106591015609 40398733718685079943261707)
      ·
        refine ⟨60598100578027619914892561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40398733718685079943261707 60598100578027619914892561)
        ·
          refine ⟨45448575433520714936169421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60598100578027619914892561 45448575433520714936169421)
          ·
            refine ⟨17043215787570268101063533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45448575433520714936169421 17043215787570268101063533)
            ·
              refine ⟨6391205920338850537898825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17043215787570268101063533 6391205920338850537898825)
              ·
                refine ⟨4793404440254137903424119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391205920338850537898825 4793404440254137903424119)
                ·
                  refine ⟨7190106660381206855136179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793404440254137903424119 7190106660381206855136179)
                  ·
                    refine ⟨10785159990571810282704269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7190106660381206855136179 10785159990571810282704269)
                    ·
                      refine ⟨4044434996464428856014101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10785159990571810282704269 4044434996464428856014101)
                      ·
                        rfl

theorem cell23_7876509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_7876509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876509 prefixEnd_7876509 := by exact prefixLift 7876509
  have htrace : WordTrace (prefixWord ++ tailWord_7876509) baseStart_7876509 baseEnd_7876509 := by
    simpa [prefixWord, tailWord_7876509, baseEnd_7876509] using wordTrace_append hprefix tailTrace_7876509
  have hstable : (prefixWord ++ tailWord_7876509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876509).length < 2 ^ (prefixWord ++ tailWord_7876509).sum := by decide
  have hdescent : baseEnd_7876509 < baseStart_7876509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876532 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_7876532 : Nat := 118140960795 + 7876532 * 2 ^ 59
def prefixEnd_7876532 : Nat := 4983230072969 + 3 ^ 40 * 7876532 * 2
def baseEnd_7876532 : Nat := 4044446806519482266026495

theorem tailTrace_7876532 : CollatzResearch.WordTrace tailWord_7876532 prefixEnd_7876532 4044446806519482266026495 := by
  unfold tailWord_7876532
  simp only [CollatzResearch.WordTrace]
  refine ⟨143640361550338621706751925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191520482067118162275669233 143640361550338621706751925)
  ·
    refine ⟨13466283895344245785007993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143640361550338621706751925 13466283895344245785007993)
    ·
      refine ⟨10099712921508184338755995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13466283895344245785007993 10099712921508184338755995)
      ·
        refine ⟨15149569382262276508133993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099712921508184338755995 15149569382262276508133993)
        ·
          refine ⟨11362177036696707381100495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15149569382262276508133993 11362177036696707381100495)
          ·
            refine ⟨17043265555045061071650743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362177036696707381100495 17043265555045061071650743)
            ·
              refine ⟨25564898332567591607476115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043265555045061071650743 25564898332567591607476115)
              ·
                refine ⟨38347347498851387411214173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564898332567591607476115 38347347498851387411214173)
                ·
                  refine ⟨14380255312069270279205315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38347347498851387411214173 14380255312069270279205315)
                  ·
                    refine ⟨21570382968103905418807973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14380255312069270279205315 21570382968103905418807973)
                    ·
                      refine ⟨4044446806519482266026495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21570382968103905418807973 4044446806519482266026495)
                      ·
                        rfl

theorem cell23_7876532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_7876532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876532 prefixEnd_7876532 := by exact prefixLift 7876532
  have htrace : WordTrace (prefixWord ++ tailWord_7876532) baseStart_7876532 baseEnd_7876532 := by
    simpa [prefixWord, tailWord_7876532, baseEnd_7876532] using wordTrace_append hprefix tailTrace_7876532
  have hstable : (prefixWord ++ tailWord_7876532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876532).length < 2 ^ (prefixWord ++ tailWord_7876532).sum := by decide
  have hdescent : baseEnd_7876532 < baseStart_7876532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876552 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_7876552 : Nat := 118140960795 + 7876552 * 2 ^ 59
def prefixEnd_7876552 : Nat := 4983230072969 + 3 ^ 40 * 7876552 * 2
def baseEnd_7876552 : Nat := 4044457076132572187776403

theorem tailTrace_7876552 : CollatzResearch.WordTrace tailWord_7876552 prefixEnd_7876552 4044457076132572187776403 := by
  unfold tailWord_7876552
  simp only [CollatzResearch.WordTrace]
  refine ⟨143640726280302393414615955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191520968373736524552821273 143640726280302393414615955)
  ·
    refine ⟨215461089420453590121923933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143640726280302393414615955 215461089420453590121923933)
    ·
      refine ⟨80797908532670096295721475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215461089420453590121923933 80797908532670096295721475)
      ·
        refine ⟨121196862799005144443582213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80797908532670096295721475 121196862799005144443582213)
        ·
          refine ⟨22724411774813464583171665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121196862799005144443582213 22724411774813464583171665)
          ·
            refine ⟨17043308831110098437378749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22724411774813464583171665 17043308831110098437378749)
            ·
              refine ⟨6391240811666286914017031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17043308831110098437378749 6391240811666286914017031)
              ·
                refine ⟨9586861217499430371025547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6391240811666286914017031 9586861217499430371025547)
                ·
                  refine ⟨14380291826249145556538321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9586861217499430371025547 14380291826249145556538321)
                  ·
                    refine ⟨10785218869686859167403741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14380291826249145556538321 10785218869686859167403741)
                    ·
                      refine ⟨4044457076132572187776403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10785218869686859167403741 4044457076132572187776403)
                      ·
                        rfl

theorem cell23_7876552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_7876552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876552 prefixEnd_7876552 := by exact prefixLift 7876552
  have htrace : WordTrace (prefixWord ++ tailWord_7876552) baseStart_7876552 baseEnd_7876552 := by
    simpa [prefixWord, tailWord_7876552, baseEnd_7876552] using wordTrace_append hprefix tailTrace_7876552
  have hstable : (prefixWord ++ tailWord_7876552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876552).length < 2 ^ (prefixWord ++ tailWord_7876552).sum := by decide
  have hdescent : baseEnd_7876552 < baseStart_7876552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876575 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 3, 3, 2]
def baseStart_7876575 : Nat := 118140960795 + 7876575 * 2 ^ 59
def prefixEnd_7876575 : Nat := 4983230072969 + 3 ^ 40 * 7876575 * 2
def baseEnd_7876575 : Nat := 4044468886187625597788797

theorem tailTrace_7876575 : CollatzResearch.WordTrace tailWord_7876575 prefixEnd_7876575 4044468886187625597788797 := by
  unfold tailWord_7876575
  simp only [CollatzResearch.WordTrace]
  refine ⟨287282291439521461757319179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191521527626347641171546119 287282291439521461757319179)
  ·
    refine ⟨430923437159282192635978769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287282291439521461757319179 430923437159282192635978769)
    ·
      refine ⟨323192577869461644476984077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430923437159282192635978769 323192577869461644476984077)
      ·
        refine ⟨121197216701048116678869029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323192577869461644476984077 121197216701048116678869029)
        ·
          refine ⟨22724478131446521877287943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121197216701048116678869029 22724478131446521877287943)
          ·
            refine ⟨34086717197169782815931915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22724478131446521877287943 34086717197169782815931915)
            ·
              refine ⟨51130075795754674223897873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34086717197169782815931915 51130075795754674223897873)
              ·
                refine ⟨38347556846816005667923405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51130075795754674223897873 38347556846816005667923405)
                ·
                  refine ⟨14380333817556002125471277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38347556846816005667923405 14380333817556002125471277)
                  ·
                    refine ⟨5392625181583500797051729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14380333817556002125471277 5392625181583500797051729)
                    ·
                      refine ⟨4044468886187625597788797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392625181583500797051729 4044468886187625597788797)
                      ·
                        rfl

theorem cell23_7876575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_7876575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876575 prefixEnd_7876575 := by exact prefixLift 7876575
  have htrace : WordTrace (prefixWord ++ tailWord_7876575) baseStart_7876575 baseEnd_7876575 := by
    simpa [prefixWord, tailWord_7876575, baseEnd_7876575] using wordTrace_append hprefix tailTrace_7876575
  have hstable : (prefixWord ++ tailWord_7876575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876575).length < 2 ^ (prefixWord ++ tailWord_7876575).sum := by decide
  have hdescent : baseEnd_7876575 < baseStart_7876575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876605 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_7876605 : Nat := 118140960795 + 7876605 * 2 ^ 59
def prefixEnd_7876605 : Nat := 4983230072969 + 3 ^ 40 * 7876605 * 2
def baseEnd_7876605 : Nat := 4044484290607260480413659

theorem tailTrace_7876605 : CollatzResearch.WordTrace tailWord_7876605 prefixEnd_7876605 4044484290607260480413659 := by
  unfold tailWord_7876605
  simp only [CollatzResearch.WordTrace]
  refine ⟨287283385629412776880911269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191522257086275184587274179 287283385629412776880911269)
  ·
    refine ⟨53865634805514895665170863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287283385629412776880911269 53865634805514895665170863)
    ·
      refine ⟨80798452208272343497756295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53865634805514895665170863 80798452208272343497756295)
      ·
        refine ⟨121197678312408515246634443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80798452208272343497756295 121197678312408515246634443)
        ·
          refine ⟨181796517468612772869951665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121197678312408515246634443 181796517468612772869951665)
          ·
            refine ⟨136347388101459579652463749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181796517468612772869951665 136347388101459579652463749)
            ·
              refine ⟨25565135269023671184836953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136347388101459579652463749 25565135269023671184836953)
              ·
                refine ⟨19173851451767753388627715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25565135269023671184836953 19173851451767753388627715)
                ·
                  refine ⟨28760777177651630082941573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19173851451767753388627715 28760777177651630082941573)
                  ·
                    refine ⟨5392645720809680640551545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28760777177651630082941573 5392645720809680640551545)
                    ·
                      refine ⟨4044484290607260480413659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392645720809680640551545 4044484290607260480413659)
                      ·
                        rfl

theorem cell23_7876605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_7876605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876605 prefixEnd_7876605 := by exact prefixLift 7876605
  have htrace : WordTrace (prefixWord ++ tailWord_7876605) baseStart_7876605 baseEnd_7876605 := by
    simpa [prefixWord, tailWord_7876605, baseEnd_7876605] using wordTrace_append hprefix tailTrace_7876605
  have hstable : (prefixWord ++ tailWord_7876605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876605).length < 2 ^ (prefixWord ++ tailWord_7876605).sum := by decide
  have hdescent : baseEnd_7876605 < baseStart_7876605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876622 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_7876622 : Nat := 118140960795 + 7876622 * 2 ^ 59
def prefixEnd_7876622 : Nat := 4983230072969 + 3 ^ 40 * 7876622 * 2
def baseEnd_7876622 : Nat := 4044493019778386913901081

theorem tailTrace_7876622 : CollatzResearch.WordTrace tailWord_7876622 prefixEnd_7876622 4044493019778386913901081 := by
  unfold tailWord_7876622
  simp only [CollatzResearch.WordTrace]
  refine ⟨35910500708793898598035015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191522670446900792522853413 35910500708793898598035015)
  ·
    refine ⟨53865751063190847897052523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35910500708793898598035015 53865751063190847897052523)
    ·
      refine ⟨80798626594786271845578785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53865751063190847897052523 80798626594786271845578785)
      ·
        refine ⟨60598969946089703884184089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80798626594786271845578785 60598969946089703884184089)
        ·
          refine ⟨45449227459567277913138067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60598969946089703884184089 45449227459567277913138067)
          ·
            refine ⟨68173841189350916869707101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45449227459567277913138067 68173841189350916869707101)
            ·
              refine ⟨25565190446006593826140163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68173841189350916869707101 25565190446006593826140163)
              ·
                refine ⟨38347785669009890739210245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25565190446006593826140163 38347785669009890739210245)
                ·
                  refine ⟨7190209812939354513601921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38347785669009890739210245 7190209812939354513601921)
                  ·
                    refine ⟨5392657359704515885201441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7190209812939354513601921 5392657359704515885201441)
                    ·
                      refine ⟨4044493019778386913901081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392657359704515885201441 4044493019778386913901081)
                      ·
                        rfl

theorem cell23_7876622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_7876622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876622 prefixEnd_7876622 := by exact prefixLift 7876622
  have htrace : WordTrace (prefixWord ++ tailWord_7876622) baseStart_7876622 baseEnd_7876622 := by
    simpa [prefixWord, tailWord_7876622, baseEnd_7876622] using wordTrace_append hprefix tailTrace_7876622
  have hstable : (prefixWord ++ tailWord_7876622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876622).length < 2 ^ (prefixWord ++ tailWord_7876622).sum := by decide
  have hdescent : baseEnd_7876622 < baseStart_7876622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876639 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 2, 2, 2]
def baseStart_7876639 : Nat := 118140960795 + 7876639 * 2 ^ 59
def prefixEnd_7876639 : Nat := 4983230072969 + 3 ^ 40 * 7876639 * 2
def baseEnd_7876639 : Nat := 4044501748949513347388503

theorem tailTrace_7876639 : CollatzResearch.WordTrace tailWord_7876639 prefixEnd_7876639 4044501748949513347388503 := by
  unfold tailWord_7876639
  simp only [CollatzResearch.WordTrace]
  refine ⟨287284625711289600687648971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191523083807526400458432647 287284625711289600687648971)
  ·
    refine ⟨430926938566934401031473457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287284625711289600687648971 430926938566934401031473457)
    ·
      refine ⟨323195203925200800773605093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430926938566934401031473457 323195203925200800773605093)
      ·
        refine ⟨60599100735975150145050955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323195203925200800773605093 60599100735975150145050955)
        ·
          refine ⟨90898651103962725217576433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60599100735975150145050955 90898651103962725217576433)
          ·
            refine ⟨68173988327972043913182325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90898651103962725217576433 68173988327972043913182325)
            ·
              refine ⟨6391311405747379116860843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68173988327972043913182325 6391311405747379116860843)
              ·
                refine ⟨9586967108621068675291265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6391311405747379116860843 9586967108621068675291265)
                ·
                  refine ⟨7190225331465801506468449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9586967108621068675291265 7190225331465801506468449)
                  ·
                    refine ⟨5392668998599351129851337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7190225331465801506468449 5392668998599351129851337)
                    ·
                      refine ⟨4044501748949513347388503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392668998599351129851337 4044501748949513347388503)
                      ·
                        rfl

theorem cell23_7876639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_7876639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876639 prefixEnd_7876639 := by exact prefixLift 7876639
  have htrace : WordTrace (prefixWord ++ tailWord_7876639) baseStart_7876639 baseEnd_7876639 := by
    simpa [prefixWord, tailWord_7876639, baseEnd_7876639] using wordTrace_append hprefix tailTrace_7876639
  have hstable : (prefixWord ++ tailWord_7876639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876639).length < 2 ^ (prefixWord ++ tailWord_7876639).sum := by decide
  have hdescent : baseEnd_7876639 < baseStart_7876639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876651 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_7876651 : Nat := 118140960795 + 7876651 * 2 ^ 59
def prefixEnd_7876651 : Nat := 4983230072969 + 3 ^ 40 * 7876651 * 2
def baseEnd_7876651 : Nat := 4044507910717367300438447

theorem tailTrace_7876651 : CollatzResearch.WordTrace tailWord_7876651 prefixEnd_7876651 4044507910717367300438447 := by
  unfold tailWord_7876651
  simp only [CollatzResearch.WordTrace]
  refine ⟨287285063387246126737085807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191523375591497417824723871 287285063387246126737085807)
  ·
    refine ⟨430927595080869190105628711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287285063387246126737085807 430927595080869190105628711)
    ·
      refine ⟨646391392621303785158443067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430927595080869190105628711 646391392621303785158443067)
      ·
        refine ⟨969587088931955677737664601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646391392621303785158443067 969587088931955677737664601)
        ·
          refine ⟨727190316698966758303248451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969587088931955677737664601 727190316698966758303248451)
          ·
            refine ⟨1090785475048450137454872677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727190316698966758303248451 1090785475048450137454872677)
            ·
              refine ⟨204522276571584400772788627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1090785475048450137454872677 204522276571584400772788627)
              ·
                refine ⟨306783414857376601159182941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204522276571584400772788627 306783414857376601159182941)
                ·
                  refine ⟨115043780571516225434693603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306783414857376601159182941 115043780571516225434693603)
                  ·
                    refine ⟨172565670857274338152040405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115043780571516225434693603 172565670857274338152040405)
                    ·
                      refine ⟨4044507910717367300438447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172565670857274338152040405 4044507910717367300438447)
                      ·
                        rfl

theorem cell23_7876651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_7876651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876651 prefixEnd_7876651 := by exact prefixLift 7876651
  have htrace : WordTrace (prefixWord ++ tailWord_7876651) baseStart_7876651 baseEnd_7876651 := by
    simpa [prefixWord, tailWord_7876651, baseEnd_7876651] using wordTrace_append hprefix tailTrace_7876651
  have hstable : (prefixWord ++ tailWord_7876651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876651).length < 2 ^ (prefixWord ++ tailWord_7876651).sum := by decide
  have hdescent : baseEnd_7876651 < baseStart_7876651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876658 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_7876658 : Nat := 118140960795 + 7876658 * 2 ^ 59
def prefixEnd_7876658 : Nat := 4983230072969 + 3 ^ 40 * 7876658 * 2
def baseEnd_7876658 : Nat := 1348170501693982924350305

theorem tailTrace_7876658 : CollatzResearch.WordTrace tailWord_7876658 prefixEnd_7876658 1348170501693982924350305 := by
  unfold tailWord_7876658
  simp only [CollatzResearch.WordTrace]
  refine ⟨71821329674555191733147657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191523545798813844621727085 71821329674555191733147657)
  ·
    refine ⟨53865997255916393799860743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71821329674555191733147657 53865997255916393799860743)
    ·
      refine ⟨80798995883874590699791115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53865997255916393799860743 80798995883874590699791115)
      ·
        refine ⟨121198493825811886049686673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80798995883874590699791115 121198493825811886049686673)
        ·
          refine ⟨90898870369358914537265005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121198493825811886049686673 90898870369358914537265005)
          ·
            refine ⟨34087076388509592951474377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90898870369358914537265005 34087076388509592951474377)
            ·
              refine ⟨25565307291382194713605783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34087076388509592951474377 25565307291382194713605783)
              ·
                refine ⟨38347960937073292070408675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25565307291382194713605783 38347960937073292070408675)
                ·
                  refine ⟨57521941405609938105613013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38347960937073292070408675 57521941405609938105613013)
                  ·
                    refine ⟨1348170501693982924350305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57521941405609938105613013 1348170501693982924350305)
                    ·
                      rfl

theorem cell23_7876658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_7876658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876658 prefixEnd_7876658 := by exact prefixLift 7876658
  have htrace : WordTrace (prefixWord ++ tailWord_7876658) baseStart_7876658 baseEnd_7876658 := by
    simpa [prefixWord, tailWord_7876658, baseEnd_7876658] using wordTrace_append hprefix tailTrace_7876658
  have hstable : (prefixWord ++ tailWord_7876658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876658).length < 2 ^ (prefixWord ++ tailWord_7876658).sum := by decide
  have hdescent : baseEnd_7876658 < baseStart_7876658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876668 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_7876668 : Nat := 118140960795 + 7876668 * 2 ^ 59
def prefixEnd_7876668 : Nat := 4983230072969 + 3 ^ 40 * 7876668 * 2
def baseEnd_7876668 : Nat := 4044516639888493733925869

theorem tailTrace_7876668 : CollatzResearch.WordTrace tailWord_7876668 prefixEnd_7876668 4044516639888493733925869 := by
  unfold tailWord_7876668
  simp only [CollatzResearch.WordTrace]
  refine ⟨143642841714092269320227329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191523788952123025760303105 143642841714092269320227329)
  ·
    refine ⟨107732131285569201990170497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143642841714092269320227329 107732131285569201990170497)
    ·
      refine ⟨80799098464176901492627873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107732131285569201990170497 80799098464176901492627873)
      ·
        refine ⟨60599323848132676119470905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80799098464176901492627873 60599323848132676119470905)
        ·
          refine ⟨45449492886099507089603179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60599323848132676119470905 45449492886099507089603179)
          ·
            refine ⟨68174239329149260634404769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45449492886099507089603179 68174239329149260634404769)
            ·
              refine ⟨51130679496861945475803577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68174239329149260634404769 51130679496861945475803577)
              ·
                refine ⟨38348009622646459106852683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51130679496861945475803577 38348009622646459106852683)
                ·
                  refine ⟨57522014433969688660279025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38348009622646459106852683 57522014433969688660279025)
                  ·
                    refine ⟨43141510825477266495209269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57522014433969688660279025 43141510825477266495209269)
                    ·
                      refine ⟨4044516639888493733925869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43141510825477266495209269 4044516639888493733925869)
                      ·
                        rfl

theorem cell23_7876668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_7876668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876668 prefixEnd_7876668 := by exact prefixLift 7876668
  have htrace : WordTrace (prefixWord ++ tailWord_7876668) baseStart_7876668 baseEnd_7876668 := by
    simpa [prefixWord, tailWord_7876668, baseEnd_7876668] using wordTrace_append hprefix tailTrace_7876668
  have hstable : (prefixWord ++ tailWord_7876668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876668).length < 2 ^ (prefixWord ++ tailWord_7876668).sum := by decide
  have hdescent : baseEnd_7876668 < baseStart_7876668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876685 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_7876685 : Nat := 118140960795 + 7876685 * 2 ^ 59
def prefixEnd_7876685 : Nat := 4983230072969 + 3 ^ 40 * 7876685 * 2
def baseEnd_7876685 : Nat := 4044525369059620167413291

theorem tailTrace_7876685 : CollatzResearch.WordTrace tailWord_7876685 prefixEnd_7876685 4044525369059620167413291 := by
  unfold tailWord_7876685
  simp only [CollatzResearch.WordTrace]
  refine ⟨287286303469122950543823509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191524202312748633695882339 287286303469122950543823509)
  ·
    refine ⟨13466545475115138306741727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287286303469122950543823509 13466545475115138306741727)
    ·
      refine ⟨20199818212672707460112591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466545475115138306741727 20199818212672707460112591)
      ·
        refine ⟨30299727319009061190168887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20199818212672707460112591 30299727319009061190168887)
        ·
          refine ⟨45449590978513591785253331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30299727319009061190168887 45449590978513591785253331)
          ·
            refine ⟨68174386467770387677879997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45449590978513591785253331 68174386467770387677879997)
            ·
              refine ⟨25565394925413895379204999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68174386467770387677879997 25565394925413895379204999)
              ·
                refine ⟨38348092388120843068807499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25565394925413895379204999 38348092388120843068807499)
                ·
                  refine ⟨57522138582181264603211249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38348092388120843068807499 57522138582181264603211249)
                  ·
                    refine ⟨43141603936635948452408437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57522138582181264603211249 43141603936635948452408437)
                    ·
                      refine ⟨4044525369059620167413291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43141603936635948452408437 4044525369059620167413291)
                      ·
                        rfl

theorem cell23_7876685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_7876685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876685 prefixEnd_7876685 := by exact prefixLift 7876685
  have htrace : WordTrace (prefixWord ++ tailWord_7876685) baseStart_7876685 baseEnd_7876685 := by
    simpa [prefixWord, tailWord_7876685, baseEnd_7876685] using wordTrace_append hprefix tailTrace_7876685
  have hstable : (prefixWord ++ tailWord_7876685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876685).length < 2 ^ (prefixWord ++ tailWord_7876685).sum := by decide
  have hdescent : baseEnd_7876685 < baseStart_7876685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876695 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 2, 4, 2]
def baseStart_7876695 : Nat := 118140960795 + 7876695 * 2 ^ 59
def prefixEnd_7876695 : Nat := 4983230072969 + 3 ^ 40 * 7876695 * 2
def baseEnd_7876695 : Nat := 4044530503866165128288245

theorem tailTrace_7876695 : CollatzResearch.WordTrace tailWord_7876695 prefixEnd_7876695 4044530503866165128288245 := by
  unfold tailWord_7876695
  simp only [CollatzResearch.WordTrace]
  refine ⟨287286668199086722251687539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191524445466057814834458359 287286668199086722251687539)
  ·
    refine ⟨430930002298630083377531309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287286668199086722251687539 430930002298630083377531309)
    ·
      refine ⟨161598750861986281266574241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430930002298630083377531309 161598750861986281266574241)
      ·
        refine ⟨121199063146489710949930681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161598750861986281266574241 121199063146489710949930681)
        ·
          refine ⟨90899297359867283212448011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121199063146489710949930681 90899297359867283212448011)
          ·
            refine ⟨136348946039800924818672017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90899297359867283212448011 136348946039800924818672017)
            ·
              refine ⟨102261709529850693614004013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136348946039800924818672017 102261709529850693614004013)
              ·
                refine ⟨38348141073694010105251505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102261709529850693614004013 38348141073694010105251505)
                ·
                  refine ⟨28761105805270507578938629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38348141073694010105251505 28761105805270507578938629)
                  ·
                    refine ⟨5392707338488220171050993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28761105805270507578938629 5392707338488220171050993)
                    ·
                      refine ⟨4044530503866165128288245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392707338488220171050993 4044530503866165128288245)
                      ·
                        rfl

theorem cell23_7876695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_7876695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876695 prefixEnd_7876695 := by exact prefixLift 7876695
  have htrace : WordTrace (prefixWord ++ tailWord_7876695) baseStart_7876695 baseEnd_7876695 := by
    simpa [prefixWord, tailWord_7876695, baseEnd_7876695] using wordTrace_append hprefix tailTrace_7876695
  have hstable : (prefixWord ++ tailWord_7876695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876695).length < 2 ^ (prefixWord ++ tailWord_7876695).sum := by decide
  have hdescent : baseEnd_7876695 < baseStart_7876695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876708 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_7876708 : Nat := 118140960795 + 7876708 * 2 ^ 59
def prefixEnd_7876708 : Nat := 4983230072969 + 3 ^ 40 * 7876708 * 2
def baseEnd_7876708 : Nat := 4044537179114673577425685

theorem tailTrace_7876708 : CollatzResearch.WordTrace tailWord_7876708 prefixEnd_7876708 4044537179114673577425685 := by
  unfold tailWord_7876708
  simp only [CollatzResearch.WordTrace]
  refine ⟨143643571174019812735955389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191524761565359750314607185 143643571174019812735955389)
  ·
    refine ⟨53866339190257429775983271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143643571174019812735955389 53866339190257429775983271)
    ·
      refine ⟨80799508785386144663974907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53866339190257429775983271 80799508785386144663974907)
      ·
        refine ⟨121199263178079216995962361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80799508785386144663974907 121199263178079216995962361)
        ·
          refine ⟨90899447383559412746971771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121199263178079216995962361 90899447383559412746971771)
          ·
            refine ⟨136349171075339119120457657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90899447383559412746971771 136349171075339119120457657)
            ·
              refine ⟨102261878306504339340343243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136349171075339119120457657 102261878306504339340343243)
              ·
                refine ⟨153392817459756509010514865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102261878306504339340343243 153392817459756509010514865)
                ·
                  refine ⟨115044613094817381757886149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153392817459756509010514865 115044613094817381757886149)
                  ·
                    refine ⟨21570864955278259079603653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115044613094817381757886149 21570864955278259079603653)
                    ·
                      refine ⟨4044537179114673577425685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21570864955278259079603653 4044537179114673577425685)
                      ·
                        rfl

theorem cell23_7876708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_7876708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876708 prefixEnd_7876708 := by exact prefixLift 7876708
  have htrace : WordTrace (prefixWord ++ tailWord_7876708) baseStart_7876708 baseEnd_7876708 := by
    simpa [prefixWord, tailWord_7876708, baseEnd_7876708] using wordTrace_append hprefix tailTrace_7876708
  have hstable : (prefixWord ++ tailWord_7876708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876708).length < 2 ^ (prefixWord ++ tailWord_7876708).sum := by decide
  have hdescent : baseEnd_7876708 < baseStart_7876708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876739 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 1, 4]
def baseStart_7876739 : Nat := 118140960795 + 7876739 * 2 ^ 59
def prefixEnd_7876739 : Nat := 4983230072969 + 3 ^ 40 * 7876739 * 2
def baseEnd_7876739 : Nat := 1348184365671654318712681

theorem tailTrace_7876739 : CollatzResearch.WordTrace tailWord_7876739 prefixEnd_7876739 1348184365671654318712681 := by
  unfold tailWord_7876739
  simp only [CollatzResearch.WordTrace]
  refine ⟨287288273010927317766289271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191525515340618211844192847 287288273010927317766289271)
  ·
    refine ⟨430932409516390976649433907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287288273010927317766289271 430932409516390976649433907)
    ·
      refine ⟨646398614274586464974150861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430932409516390976649433907 646398614274586464974150861)
      ·
        refine ⟨242399480352969924365306573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646398614274586464974150861 242399480352969924365306573)
        ·
          refine ⟨90899805132363721636989965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242399480352969924365306573 90899805132363721636989965)
          ·
            refine ⟨34087426924636395613871237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90899805132363721636989965 34087426924636395613871237)
            ·
              refine ⟨6391392548369324177600857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34087426924636395613871237 6391392548369324177600857)
              ·
                refine ⟨4793544411276993133200643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391392548369324177600857 4793544411276993133200643)
                ·
                  refine ⟨7190316616915489699800965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793544411276993133200643 7190316616915489699800965)
                  ·
                    refine ⟨1348184365671654318712681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190316616915489699800965 1348184365671654318712681)
                    ·
                      rfl

theorem cell23_7876739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 4].length) (baseStart_7876739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876739 prefixEnd_7876739 := by exact prefixLift 7876739
  have htrace : WordTrace (prefixWord ++ tailWord_7876739) baseStart_7876739 baseEnd_7876739 := by
    simpa [prefixWord, tailWord_7876739, baseEnd_7876739] using wordTrace_append hprefix tailTrace_7876739
  have hstable : (prefixWord ++ tailWord_7876739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876739).length < 2 ^ (prefixWord ++ tailWord_7876739).sum := by decide
  have hdescent : baseEnd_7876739 < baseStart_7876739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876755 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 1, 5, 2]
def baseStart_7876755 : Nat := 118140960795 + 7876755 * 2 ^ 59
def prefixEnd_7876755 : Nat := 4983230072969 + 3 ^ 40 * 7876755 * 2
def baseEnd_7876755 : Nat := 4044561312705434893537969

theorem tailTrace_7876755 : CollatzResearch.WordTrace tailWord_7876755 prefixEnd_7876755 4044561312705434893537969 := by
  unfold tailWord_7876755
  simp only [CollatzResearch.WordTrace]
  refine ⟨287288856578869352498871719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191525904385912901665914479 287288856578869352498871719)
  ·
    refine ⟨430933284868304028748307579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287288856578869352498871719 430933284868304028748307579)
    ·
      refine ⟨646399927302456043122461369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430933284868304028748307579 646399927302456043122461369)
      ·
        refine ⟨484799945476842032341846027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646399927302456043122461369 484799945476842032341846027)
        ·
          refine ⟨727199918215263048512769041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484799945476842032341846027 727199918215263048512769041)
          ·
            refine ⟨545399938661447286384576781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727199918215263048512769041 545399938661447286384576781)
            ·
              refine ⟨204524976998042732394216293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545399938661447286384576781 204524976998042732394216293)
              ·
                refine ⟨38348433187133012323915555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204524976998042732394216293 38348433187133012323915555)
                ·
                  refine ⟨57522649780699518485873333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38348433187133012323915555 57522649780699518485873333)
                  ·
                    refine ⟨5392748416940579858050625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57522649780699518485873333 5392748416940579858050625)
                    ·
                      refine ⟨4044561312705434893537969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392748416940579858050625 4044561312705434893537969)
                      ·
                        rfl

theorem cell23_7876755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5, 2].length) (baseStart_7876755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876755 prefixEnd_7876755 := by exact prefixLift 7876755
  have htrace : WordTrace (prefixWord ++ tailWord_7876755) baseStart_7876755 baseEnd_7876755 := by
    simpa [prefixWord, tailWord_7876755, baseEnd_7876755] using wordTrace_append hprefix tailTrace_7876755
  have hstable : (prefixWord ++ tailWord_7876755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876755).length < 2 ^ (prefixWord ++ tailWord_7876755).sum := by decide
  have hdescent : baseEnd_7876755 < baseStart_7876755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876765 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7876765 : Nat := 118140960795 + 7876765 * 2 ^ 59
def prefixEnd_7876765 : Nat := 4983230072969 + 3 ^ 40 * 7876765 * 2
def baseEnd_7876765 : Nat := 1348188815837326618137641

theorem tailTrace_7876765 : CollatzResearch.WordTrace tailWord_7876765 prefixEnd_7876765 1348188815837326618137641 := by
  unfold tailWord_7876765
  simp only [CollatzResearch.WordTrace]
  refine ⟨287289221308833124206735749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191526147539222082804490499 287289221308833124206735749)
  ·
    refine ⟨53866728995406210788762953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287289221308833124206735749 53866728995406210788762953)
    ·
      refine ⟨40400046746554658091572215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53866728995406210788762953 40400046746554658091572215)
      ·
        refine ⟨60600070119831987137358323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40400046746554658091572215 60600070119831987137358323)
        ·
          refine ⟨90900105179747980706037485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60600070119831987137358323 90900105179747980706037485)
          ·
            refine ⟨34087539442405492764764057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90900105179747980706037485 34087539442405492764764057)
            ·
              refine ⟨25565654581804119573573043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34087539442405492764764057 25565654581804119573573043)
              ·
                refine ⟨38348481872706179360359565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25565654581804119573573043 38348481872706179360359565)
                ·
                  refine ⟨14380680702264817260134837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38348481872706179360359565 14380680702264817260134837)
                  ·
                    refine ⟨1348188815837326618137641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14380680702264817260134837 1348188815837326618137641)
                    ·
                      rfl

theorem cell23_7876765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7876765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876765 prefixEnd_7876765 := by exact prefixLift 7876765
  have htrace : WordTrace (prefixWord ++ tailWord_7876765) baseStart_7876765 baseEnd_7876765 := by
    simpa [prefixWord, tailWord_7876765, baseEnd_7876765] using wordTrace_append hprefix tailTrace_7876765
  have hstable : (prefixWord ++ tailWord_7876765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876765).length < 2 ^ (prefixWord ++ tailWord_7876765).sum := by decide
  have hdescent : baseEnd_7876765 < baseStart_7876765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876766 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7876766 : Nat := 118140960795 + 7876766 * 2 ^ 59
def prefixEnd_7876766 : Nat := 4983230072969 + 3 ^ 40 * 7876766 * 2
def baseEnd_7876766 : Nat := 4044566960992634350500419

theorem tailTrace_7876766 : CollatzResearch.WordTrace tailWord_7876766 prefixEnd_7876766 4044566960992634350500419 := by
  unfold tailWord_7876766
  simp only [CollatzResearch.WordTrace]
  refine ⟨35911157222728687672190269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191526171854553000918348101 35911157222728687672190269)
  ·
    refine ⟨13466683958523257877071351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35911157222728687672190269 13466683958523257877071351)
    ·
      refine ⟨20200025937784886815607027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466683958523257877071351 20200025937784886815607027)
      ·
        refine ⟨30300038906677330223410541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20200025937784886815607027 30300038906677330223410541)
        ·
          refine ⟨11362514590003998833778953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30300038906677330223410541 11362514590003998833778953)
          ·
            refine ⟨8521885942502999125334215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11362514590003998833778953 8521885942502999125334215)
            ·
              refine ⟨12782828913754498688001323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521885942502999125334215 12782828913754498688001323)
              ·
                refine ⟨19174243370631748032001985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12782828913754498688001323 19174243370631748032001985)
                ·
                  refine ⟨14380682527973811024001489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19174243370631748032001985 14380682527973811024001489)
                  ·
                    refine ⟨10785511895980358268001117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14380682527973811024001489 10785511895980358268001117)
                    ·
                      refine ⟨4044566960992634350500419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10785511895980358268001117 4044566960992634350500419)
                      ·
                        rfl

theorem cell23_7876766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7876766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876766 prefixEnd_7876766 := by exact prefixLift 7876766
  have htrace : WordTrace (prefixWord ++ tailWord_7876766) baseStart_7876766 baseEnd_7876766 := by
    simpa [prefixWord, tailWord_7876766, baseEnd_7876766] using wordTrace_append hprefix tailTrace_7876766
  have hstable : (prefixWord ++ tailWord_7876766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876766).length < 2 ^ (prefixWord ++ tailWord_7876766).sum := by decide
  have hdescent : baseEnd_7876766 < baseStart_7876766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876795 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 4, 4]
def baseStart_7876795 : Nat := 118140960795 + 7876795 * 2 ^ 59
def prefixEnd_7876795 : Nat := 4983230072969 + 3 ^ 40 * 7876795 * 2
def baseEnd_7876795 : Nat := 1348193950643871579012595

theorem tailTrace_7876795 : CollatzResearch.WordTrace tailWord_7876795 prefixEnd_7876795 1348193950643871579012595 := by
  unfold tailWord_7876795
  simp only [CollatzResearch.WordTrace]
  refine ⟨287290315498724439330327839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191526876999149626220218559 287290315498724439330327839)
  ·
    refine ⟨430935473248086658995491759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287290315498724439330327839 430935473248086658995491759)
    ·
      refine ⟨646403209872129988493237639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430935473248086658995491759 646403209872129988493237639)
      ·
        refine ⟨969604814808194982739856459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646403209872129988493237639 969604814808194982739856459)
        ·
          refine ⟨1454407222212292474109784689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969604814808194982739856459 1454407222212292474109784689)
          ·
            refine ⟨1090805416659219355582338517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454407222212292474109784689 1090805416659219355582338517)
            ·
              refine ⟨25565751952950453646461059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1090805416659219355582338517 25565751952950453646461059)
              ·
                refine ⟨38348627929425680469691589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25565751952950453646461059 38348627929425680469691589)
                ·
                  refine ⟨7190367736767315088067173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38348627929425680469691589 7190367736767315088067173)
                  ·
                    refine ⟨1348193950643871579012595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190367736767315088067173 1348193950643871579012595)
                    ·
                      rfl

theorem cell23_7876795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 4].length) (baseStart_7876795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876795 prefixEnd_7876795 := by exact prefixLift 7876795
  have htrace : WordTrace (prefixWord ++ tailWord_7876795) baseStart_7876795 baseEnd_7876795 := by
    simpa [prefixWord, tailWord_7876795, baseEnd_7876795] using wordTrace_append hprefix tailTrace_7876795
  have hstable : (prefixWord ++ tailWord_7876795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876795).length < 2 ^ (prefixWord ++ tailWord_7876795).sum := by decide
  have hdescent : baseEnd_7876795 < baseStart_7876795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876805 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_7876805 : Nat := 118140960795 + 7876805 * 2 ^ 59
def prefixEnd_7876805 : Nat := 4983230072969 + 3 ^ 40 * 7876805 * 2
def baseEnd_7876805 : Nat := 4044586986738159697912739

theorem tailTrace_7876805 : CollatzResearch.WordTrace tailWord_7876805 prefixEnd_7876805 4044586986738159697912739 := by
  unfold tailWord_7876805
  simp only [CollatzResearch.WordTrace]
  refine ⟨287290680228688211038191869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191527120152458807358794579 287290680228688211038191869)
  ·
    refine ⟨107734005085758079139321951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287290680228688211038191869 107734005085758079139321951)
    ·
      refine ⟨161601007628637118708982927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107734005085758079139321951 161601007628637118708982927)
      ·
        refine ⟨242401511442955678063474391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161601007628637118708982927 242401511442955678063474391)
        ·
          refine ⟨363602267164433517095211587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242401511442955678063474391 363602267164433517095211587)
          ·
            refine ⟨545403400746650275642817381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363602267164433517095211587 545403400746650275642817381)
            ·
              refine ⟨102263137639996926683028259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545403400746650275642817381 102263137639996926683028259)
              ·
                refine ⟨153394706459995390024542389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102263137639996926683028259 153394706459995390024542389)
                ·
                  refine ⟨14380753730624567814800849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153394706459995390024542389 14380753730624567814800849)
                  ·
                    refine ⟨10785565297968425861100637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14380753730624567814800849 10785565297968425861100637)
                    ·
                      refine ⟨4044586986738159697912739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10785565297968425861100637 4044586986738159697912739)
                      ·
                        rfl

theorem cell23_7876805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_7876805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876805 prefixEnd_7876805 := by exact prefixLift 7876805
  have htrace : WordTrace (prefixWord ++ tailWord_7876805) baseStart_7876805 baseEnd_7876805 := by
    simpa [prefixWord, tailWord_7876805, baseEnd_7876805] using wordTrace_append hprefix tailTrace_7876805
  have hstable : (prefixWord ++ tailWord_7876805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876805).length < 2 ^ (prefixWord ++ tailWord_7876805).sum := by decide
  have hdescent : baseEnd_7876805 < baseStart_7876805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876808 : List Nat := [2, 1, 3, 1, 2, 1, 1, 12]
def baseStart_7876808 : Nat := 118140960795 + 7876808 * 2 ^ 59
def prefixEnd_7876808 : Nat := 4983230072969 + 3 ^ 40 * 7876808 * 2
def baseEnd_7876808 : Nat := 149799575080745303191675

theorem tailTrace_7876808 : CollatzResearch.WordTrace tailWord_7876808 prefixEnd_7876808 149799575080745303191675 := by
  unfold tailWord_7876808
  simp only [CollatzResearch.WordTrace]
  refine ⟨143645394823838671275275539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191527193098451561700367385 143645394823838671275275539)
  ·
    refine ⟨215468092235758006912913309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143645394823838671275275539 215468092235758006912913309)
    ·
      refine ⟨80800534588409252592342491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215468092235758006912913309 80800534588409252592342491)
      ·
        refine ⟨121200801882613878888513737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80800534588409252592342491 121200801882613878888513737)
        ·
          refine ⟨90900601411960409166385303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121200801882613878888513737 90900601411960409166385303)
          ·
            refine ⟨136350902117940613749577955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90900601411960409166385303 136350902117940613749577955)
            ·
              refine ⟨204526353176910920624366933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136350902117940613749577955 204526353176910920624366933)
              ·
                refine ⟨149799575080745303191675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 204526353176910920624366933 149799575080745303191675)
                ·
                  rfl

theorem cell23_7876808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 12].length) (baseStart_7876808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876808 prefixEnd_7876808 := by exact prefixLift 7876808
  have htrace : WordTrace (prefixWord ++ tailWord_7876808) baseStart_7876808 baseEnd_7876808 := by
    simpa [prefixWord, tailWord_7876808, baseEnd_7876808] using wordTrace_append hprefix tailTrace_7876808
  have hstable : (prefixWord ++ tailWord_7876808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876808).length < 2 ^ (prefixWord ++ tailWord_7876808).sum := by decide
  have hdescent : baseEnd_7876808 < baseStart_7876808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876825 : List Nat := [1, 2, 1, 2, 3, 1, 6, 7]
def baseStart_7876825 : Nat := 118140960795 + 7876825 * 2 ^ 59
def prefixEnd_7876825 : Nat := 4983230072969 + 3 ^ 40 * 7876825 * 2
def baseEnd_7876825 : Nat := 149799898383379615543061

theorem tailTrace_7876825 : CollatzResearch.WordTrace tailWord_7876825 prefixEnd_7876825 149799898383379615543061 := by
  unfold tailWord_7876825
  simp only [CollatzResearch.WordTrace]
  refine ⟨287291409688615754453919929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191527606459077169635946619 287291409688615754453919929)
  ·
    refine ⟨215468557266461815840439947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287291409688615754453919929 215468557266461815840439947)
    ·
      refine ⟨323202835899692723760659921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215468557266461815840439947 323202835899692723760659921)
      ·
        refine ⟨242402126924769542820494941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323202835899692723760659921 242402126924769542820494941)
        ·
          refine ⟨90900797596788578557685603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242402126924769542820494941 90900797596788578557685603)
          ·
            refine ⟨136351196395182867836528405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90900797596788578557685603 136351196395182867836528405)
            ·
              refine ⟨6391462331024196929837269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136351196395182867836528405 6391462331024196929837269)
              ·
                refine ⟨149799898383379615543061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6391462331024196929837269 149799898383379615543061)
                ·
                  rfl

theorem cell23_7876825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 7].length) (baseStart_7876825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876825 prefixEnd_7876825 := by exact prefixLift 7876825
  have htrace : WordTrace (prefixWord ++ tailWord_7876825) baseStart_7876825 baseEnd_7876825 := by
    simpa [prefixWord, tailWord_7876825, baseEnd_7876825] using wordTrace_append hprefix tailTrace_7876825
  have hstable : (prefixWord ++ tailWord_7876825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876825).length < 2 ^ (prefixWord ++ tailWord_7876825).sum := by decide
  have hdescent : baseEnd_7876825 < baseStart_7876825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876839 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7876839 : Nat := 118140960795 + 7876839 * 2 ^ 59
def prefixEnd_7876839 : Nat := 4983230072969 + 3 ^ 40 * 7876839 * 2
def baseEnd_7876839 : Nat := 4044604445080412564887583

theorem tailTrace_7876839 : CollatzResearch.WordTrace tailWord_7876839 prefixEnd_7876839 4044604445080412564887583 := by
  unfold tailWord_7876839
  simp only [CollatzResearch.WordTrace]
  refine ⟨287291920310565034844929571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191527946873710023229953047 287291920310565034844929571)
  ·
    refine ⟨430937880465847552267394357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287291920310565034844929571 430937880465847552267394357)
    ·
      refine ⟨40400426293673208025068221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430937880465847552267394357 40400426293673208025068221)
      ·
        refine ⟨15150159860127453009400583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40400426293673208025068221 15150159860127453009400583)
        ·
          refine ⟨22725239790191179514100875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15150159860127453009400583 22725239790191179514100875)
          ·
            refine ⟨34087859685286769271151313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22725239790191179514100875 34087859685286769271151313)
            ·
              refine ⟨25565894763965076953363485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34087859685286769271151313 25565894763965076953363485)
              ·
                refine ⟨9587210536486903857511307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25565894763965076953363485 9587210536486903857511307)
                ·
                  refine ⟨14380815804730355786266961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9587210536486903857511307 14380815804730355786266961)
                  ·
                    refine ⟨10785611853547766839700221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14380815804730355786266961 10785611853547766839700221)
                    ·
                      refine ⟨4044604445080412564887583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10785611853547766839700221 4044604445080412564887583)
                      ·
                        rfl

theorem cell23_7876839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7876839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876839 prefixEnd_7876839 := by exact prefixLift 7876839
  have htrace : WordTrace (prefixWord ++ tailWord_7876839) baseStart_7876839 baseEnd_7876839 := by
    simpa [prefixWord, tailWord_7876839, baseEnd_7876839] using wordTrace_append hprefix tailTrace_7876839
  have hstable : (prefixWord ++ tailWord_7876839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876839).length < 2 ^ (prefixWord ++ tailWord_7876839).sum := by decide
  have hdescent : baseEnd_7876839 < baseStart_7876839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876915 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 7]
def baseStart_7876915 : Nat := 118140960795 + 7876915 * 2 ^ 59
def prefixEnd_7876915 : Nat := 4983230072969 + 3 ^ 40 * 7876915 * 2
def baseEnd_7876915 : Nat := 449404829956683807504137

theorem tailTrace_7876915 : CollatzResearch.WordTrace tailWord_7876915 prefixEnd_7876915 449404829956683807504137 := by
  unfold tailWord_7876915
  simp only [CollatzResearch.WordTrace]
  refine ⟨287294692258289699824696199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191529794838859799883130799 287294692258289699824696199)
  ·
    refine ⟨430942038387434549737044299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287294692258289699824696199 430942038387434549737044299)
    ·
      refine ⟨646413057581151824605566449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430942038387434549737044299 646413057581151824605566449)
      ·
        refine ⟨484809793185863868454174837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646413057581151824605566449 484809793185863868454174837)
        ·
          refine ⟨45450918111174737667578891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484809793185863868454174837 45450918111174737667578891)
          ·
            refine ⟨68176377166762106501368337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45450918111174737667578891 68176377166762106501368337)
            ·
              refine ⟨51132282875071579876026253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68176377166762106501368337 51132282875071579876026253)
              ·
                refine ⟨19174606078151842453509845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51132282875071579876026253 19174606078151842453509845)
                ·
                  refine ⟨449404829956683807504137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19174606078151842453509845 449404829956683807504137)
                  ·
                    rfl

theorem cell23_7876915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 7].length) (baseStart_7876915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876915 prefixEnd_7876915 := by exact prefixLift 7876915
  have htrace : WordTrace (prefixWord ++ tailWord_7876915) baseStart_7876915 baseEnd_7876915 := by
    simpa [prefixWord, tailWord_7876915, baseEnd_7876915] using wordTrace_append hprefix tailTrace_7876915
  have hstable : (prefixWord ++ tailWord_7876915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876915).length < 2 ^ (prefixWord ++ tailWord_7876915).sum := by decide
  have hdescent : baseEnd_7876915 < baseStart_7876915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876922 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_7876922 : Nat := 118140960795 + 7876922 * 2 ^ 59
def prefixEnd_7876922 : Nat := 4983230072969 + 3 ^ 40 * 7876922 * 2
def baseEnd_7876922 : Nat := 4044647063974735740149701

theorem tailTrace_7876922 : CollatzResearch.WordTrace tailWord_7876922 prefixEnd_7876922 4044647063974735740149701 := by
  unfold tailWord_7876922
  simp only [CollatzResearch.WordTrace]
  refine ⟨71823736892316085005050255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191529965046176226680134013 71823736892316085005050255)
  ·
    refine ⟨107735605338474127507575383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71823736892316085005050255 107735605338474127507575383)
    ·
      refine ⟨161603408007711191261363075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107735605338474127507575383 161603408007711191261363075)
      ·
        refine ⟨242405112011566786892044613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161603408007711191261363075 242405112011566786892044613)
        ·
          refine ⟨45450958502168772542258365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242405112011566786892044613 45450958502168772542258365)
          ·
            refine ⟨17044109438313289703346887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45450958502168772542258365 17044109438313289703346887)
            ·
              refine ⟨25566164157469934555020331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17044109438313289703346887 25566164157469934555020331)
              ·
                refine ⟨38349246236204901832530497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25566164157469934555020331 38349246236204901832530497)
                ·
                  refine ⟨28761934677153676374397873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38349246236204901832530497 28761934677153676374397873)
                  ·
                    refine ⟨21571451007865257280798405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28761934677153676374397873 21571451007865257280798405)
                    ·
                      refine ⟨4044647063974735740149701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21571451007865257280798405 4044647063974735740149701)
                      ·
                        rfl

theorem cell23_7876922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_7876922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876922 prefixEnd_7876922 := by exact prefixLift 7876922
  have htrace : WordTrace (prefixWord ++ tailWord_7876922) baseStart_7876922 baseEnd_7876922 := by
    simpa [prefixWord, tailWord_7876922, baseEnd_7876922] using wordTrace_append hprefix tailTrace_7876922
  have hstable : (prefixWord ++ tailWord_7876922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876922).length < 2 ^ (prefixWord ++ tailWord_7876922).sum := by decide
  have hdescent : baseEnd_7876922 < baseStart_7876922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876926 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_7876926 : Nat := 118140960795 + 7876926 * 2 ^ 59
def prefixEnd_7876926 : Nat := 4983230072969 + 3 ^ 40 * 7876926 * 2
def baseEnd_7876926 : Nat := 4044649117897353724499683

theorem tailTrace_7876926 : CollatzResearch.WordTrace tailWord_7876926 prefixEnd_7876926 4044649117897353724499683 := by
  unfold tailWord_7876926
  simp only [CollatzResearch.WordTrace]
  refine ⟨35911886682656231087918329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191530062307499899135564421 35911886682656231087918329)
  ·
    refine ⟨26933915011992173315938747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35911886682656231087918329 26933915011992173315938747)
    ·
      refine ⟨40400872517988259973908121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933915011992173315938747 40400872517988259973908121)
      ·
        refine ⟨30300654388491194980431091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40400872517988259973908121 30300654388491194980431091)
        ·
          refine ⟨45450981582736792470646637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30300654388491194980431091 45450981582736792470646637)
          ·
            refine ⟨17044118093526297176492489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45450981582736792470646637 17044118093526297176492489)
            ·
              refine ⟨12783088570144722882369367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17044118093526297176492489 12783088570144722882369367)
              ·
                refine ⟨19174632855217084323554051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12783088570144722882369367 19174632855217084323554051)
                ·
                  refine ⟨28761949282825626485331077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19174632855217084323554051 28761949282825626485331077)
                  ·
                    refine ⟨5392865490529804965999577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28761949282825626485331077 5392865490529804965999577)
                    ·
                      refine ⟨4044649117897353724499683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392865490529804965999577 4044649117897353724499683)
                      ·
                        rfl

theorem cell23_7876926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_7876926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876926 prefixEnd_7876926 := by exact prefixLift 7876926
  have htrace : WordTrace (prefixWord ++ tailWord_7876926) baseStart_7876926 baseEnd_7876926 := by
    simpa [prefixWord, tailWord_7876926, baseEnd_7876926] using wordTrace_append hprefix tailTrace_7876926
  have hstable : (prefixWord ++ tailWord_7876926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876926).length < 2 ^ (prefixWord ++ tailWord_7876926).sum := by decide
  have hdescent : baseEnd_7876926 < baseStart_7876926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876952 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 7, 2]
def baseStart_7876952 : Nat := 118140960795 + 7876952 * 2 ^ 59
def prefixEnd_7876952 : Nat := 4983230072969 + 3 ^ 40 * 7876952 * 2
def baseEnd_7876952 : Nat := 4044662468394370622774563

theorem tailTrace_7876952 : CollatzResearch.WordTrace tailWord_7876952 prefixEnd_7876952 4044662468394370622774563 := by
  unfold tailWord_7876952
  simp only [CollatzResearch.WordTrace]
  refine ⟨143648020879577827571896555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191530694506103770095862073 143648020879577827571896555)
  ·
    refine ⟨215472031319366741357844833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143648020879577827571896555 215472031319366741357844833)
    ·
      refine ⟨161604023489525056018383625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215472031319366741357844833 161604023489525056018383625)
      ·
        refine ⟨121203017617143792013787719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161604023489525056018383625 121203017617143792013787719)
        ·
          refine ⟨181804526425715688020681579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121203017617143792013787719 181804526425715688020681579)
          ·
            refine ⟨272706789638573532031022369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181804526425715688020681579 272706789638573532031022369)
            ·
              refine ⟨204530092228930149023266777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272706789638573532031022369 204530092228930149023266777)
              ·
                refine ⟨153397569171697611767450083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204530092228930149023266777 153397569171697611767450083)
                ·
                  refine ⟨230096353757546417651175125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153397569171697611767450083 230096353757546417651175125)
                  ·
                    refine ⟨5392883291192494163699417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 230096353757546417651175125 5392883291192494163699417)
                    ·
                      refine ⟨4044662468394370622774563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392883291192494163699417 4044662468394370622774563)
                      ·
                        rfl

theorem cell23_7876952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_7876952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876952 prefixEnd_7876952 := by exact prefixLift 7876952
  have htrace : WordTrace (prefixWord ++ tailWord_7876952) baseStart_7876952 baseEnd_7876952 := by
    simpa [prefixWord, tailWord_7876952, baseEnd_7876952] using wordTrace_append hprefix tailTrace_7876952
  have hstable : (prefixWord ++ tailWord_7876952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876952).length < 2 ^ (prefixWord ++ tailWord_7876952).sum := by decide
  have hdescent : baseEnd_7876952 < baseStart_7876952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876960 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 2, 2, 2]
def baseStart_7876960 : Nat := 118140960795 + 7876960 * 2 ^ 59
def prefixEnd_7876960 : Nat := 4983230072969 + 3 ^ 40 * 7876960 * 2
def baseEnd_7876960 : Nat := 4044666576239606591474527

theorem tailTrace_7876960 : CollatzResearch.WordTrace tailWord_7876960 prefixEnd_7876960 4044666576239606591474527 := by
  unfold tailWord_7876960
  simp only [CollatzResearch.WordTrace]
  refine ⟨143648166771563336255042167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191530889028751115006722889 143648166771563336255042167)
  ·
    refine ⟨215472250157345004382563251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143648166771563336255042167 215472250157345004382563251)
    ·
      refine ⟨323208375236017506573844877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215472250157345004382563251 323208375236017506573844877)
      ·
        refine ⟨121203140713506564965191829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323208375236017506573844877 121203140713506564965191829)
        ·
          refine ⟨5681397220945620232743367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121203140713506564965191829 5681397220945620232743367)
          ·
            refine ⟨8522095831418430349115051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681397220945620232743367 8522095831418430349115051)
            ·
              refine ⟨12783143747127645523672577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522095831418430349115051 12783143747127645523672577)
              ·
                refine ⟨9587357810345734142754433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12783143747127645523672577 9587357810345734142754433)
                ·
                  refine ⟨7190518357759300607065825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9587357810345734142754433 7190518357759300607065825)
                  ·
                    refine ⟨5392888768319475455299369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7190518357759300607065825 5392888768319475455299369)
                    ·
                      refine ⟨4044666576239606591474527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5392888768319475455299369 4044666576239606591474527)
                      ·
                        rfl

theorem cell23_7876960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_7876960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7876960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7876960 prefixEnd_7876960 := by exact prefixLift 7876960
  have htrace : WordTrace (prefixWord ++ tailWord_7876960) baseStart_7876960 baseEnd_7876960 := by
    simpa [prefixWord, tailWord_7876960, baseEnd_7876960] using wordTrace_append hprefix tailTrace_7876960
  have hstable : (prefixWord ++ tailWord_7876960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876960).length < 2 ^ (prefixWord ++ tailWord_7876960).sum := by decide
  have hdescent : baseEnd_7876960 < baseStart_7876960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877072 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_7877072 : Nat := 118140960795 + 7877072 * 2 ^ 59
def prefixEnd_7877072 : Nat := 4983230072969 + 3 ^ 40 * 7877072 * 2
def baseEnd_7877072 : Nat := 4044724086072910153274011

theorem tailTrace_7877072 : CollatzResearch.WordTrace tailWord_7877072 prefixEnd_7877072 4044724086072910153274011 := by
  unfold tailWord_7877072
  simp only [CollatzResearch.WordTrace]
  refine ⟨143650209259360457819080735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191533612345813943758774313 143650209259360457819080735)
  ·
    refine ⟨215475313889040686728621103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143650209259360457819080735 215475313889040686728621103)
    ·
      refine ⟨323212970833561030092931655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215475313889040686728621103 323212970833561030092931655)
      ·
        refine ⟨484819456250341545139397483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323212970833561030092931655 484819456250341545139397483)
        ·
          refine ⟨727229184375512317709096225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484819456250341545139397483 727229184375512317709096225)
          ·
            refine ⟨545421888281634238281822169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727229184375512317709096225 545421888281634238281822169)
            ·
              refine ⟨409066416211225678711366627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545421888281634238281822169 409066416211225678711366627)
              ·
                refine ⟨613599624316838518067049941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409066416211225678711366627 613599624316838518067049941)
                ·
                  refine ⟨14381241194925902767196483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 613599624316838518067049941 14381241194925902767196483)
                  ·
                    refine ⟨21571861792388854150794725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14381241194925902767196483 21571861792388854150794725)
                    ·
                      refine ⟨4044724086072910153274011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21571861792388854150794725 4044724086072910153274011)
                      ·
                        rfl

theorem cell23_7877072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_7877072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877072 prefixEnd_7877072 := by exact prefixLift 7877072
  have htrace : WordTrace (prefixWord ++ tailWord_7877072) baseStart_7877072 baseEnd_7877072 := by
    simpa [prefixWord, tailWord_7877072, baseEnd_7877072] using wordTrace_append hprefix tailTrace_7877072
  have hstable : (prefixWord ++ tailWord_7877072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877072).length < 2 ^ (prefixWord ++ tailWord_7877072).sum := by decide
  have hdescent : baseEnd_7877072 < baseStart_7877072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877082 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_7877082 : Nat := 118140960795 + 7877082 * 2 ^ 59
def prefixEnd_7877082 : Nat := 4983230072969 + 3 ^ 40 * 7877082 * 2
def baseEnd_7877082 : Nat := 1348243073626485038049655

theorem tailTrace_7877082 : CollatzResearch.WordTrace tailWord_7877082 prefixEnd_7877082 1348243073626485038049655 := by
  unfold tailWord_7877082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71825195812171171836506375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191533855499123124897350333 71825195812171171836506375)
  ·
    refine ⟨107737793718256757754759563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71825195812171171836506375 107737793718256757754759563)
    ·
      refine ⟨161606690577385136632139345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107737793718256757754759563 161606690577385136632139345)
      ·
        refine ⟨121205017933038852474104509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161606690577385136632139345 121205017933038852474104509)
        ·
          refine ⟨45451881724889569677789191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121205017933038852474104509 45451881724889569677789191)
          ·
            refine ⟨68177822587334354516683787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45451881724889569677789191 68177822587334354516683787)
            ·
              refine ⟨102266733881001531775025681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68177822587334354516683787 102266733881001531775025681)
              ·
                refine ⟨76700050410751148831269261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102266733881001531775025681 76700050410751148831269261)
                ·
                  refine ⟨28762518904031680811725973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76700050410751148831269261 28762518904031680811725973)
                  ·
                    refine ⟨1348243073626485038049655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28762518904031680811725973 1348243073626485038049655)
                    ·
                      rfl

theorem cell23_7877082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_7877082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877082 prefixEnd_7877082 := by exact prefixLift 7877082
  have htrace : WordTrace (prefixWord ++ tailWord_7877082) baseStart_7877082 baseEnd_7877082 := by
    simpa [prefixWord, tailWord_7877082, baseEnd_7877082] using wordTrace_append hprefix tailTrace_7877082
  have hstable : (prefixWord ++ tailWord_7877082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877082).length < 2 ^ (prefixWord ++ tailWord_7877082).sum := by decide
  have hdescent : baseEnd_7877082 < baseStart_7877082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877099 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 2, 4]
def baseStart_7877099 : Nat := 118140960795 + 7877099 * 2 ^ 59
def prefixEnd_7877099 : Nat := 4983230072969 + 3 ^ 40 * 7877099 * 2
def baseEnd_7877099 : Nat := 1348245983350193849212129

theorem tailTrace_7877099 : CollatzResearch.WordTrace tailWord_7877099 prefixEnd_7877099 1348245983350193849212129 := by
  unfold tailWord_7877099
  simp only [CollatzResearch.WordTrace]
  refine ⟨287301403289623099249394351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191534268859748732832929567 287301403289623099249394351)
  ·
    refine ⟨430952104934434648874091527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287301403289623099249394351 430952104934434648874091527)
    ·
      refine ⟨646428157401651973311137291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430952104934434648874091527 646428157401651973311137291)
      ·
        refine ⟨969642236102477959966705937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646428157401651973311137291 969642236102477959966705937)
        ·
          refine ⟨727231677076858469975029453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969642236102477959966705937 727231677076858469975029453)
          ·
            refine ⟨272711878903821926240636045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727231677076858469975029453 272711878903821926240636045)
            ·
              refine ⟨102266954588933222340238517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272711878903821926240636045 102266954588933222340238517)
              ·
                refine ⟨9587526992712489594397361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102266954588933222340238517 9587526992712489594397361)
                ·
                  refine ⟨7190645244534367195798021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9587526992712489594397361 7190645244534367195798021)
                  ·
                    refine ⟨1348245983350193849212129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190645244534367195798021 1348245983350193849212129)
                    ·
                      rfl

theorem cell23_7877099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 4].length) (baseStart_7877099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877099 prefixEnd_7877099 := by exact prefixLift 7877099
  have htrace : WordTrace (prefixWord ++ tailWord_7877099) baseStart_7877099 baseEnd_7877099 := by
    simpa [prefixWord, tailWord_7877099, baseEnd_7877099] using wordTrace_append hprefix tailTrace_7877099
  have hstable : (prefixWord ++ tailWord_7877099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877099).length < 2 ^ (prefixWord ++ tailWord_7877099).sum := by decide
  have hdescent : baseEnd_7877099 < baseStart_7877099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877140 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7877140 : Nat := 118140960795 + 7877140 * 2 ^ 59
def prefixEnd_7877140 : Nat := 4983230072969 + 3 ^ 40 * 7877140 * 2
def baseEnd_7877140 : Nat := 4044759002757415887223699

theorem tailTrace_7877140 : CollatzResearch.WordTrace tailWord_7877140 prefixEnd_7877140 4044759002757415887223699 := by
  unfold tailWord_7877140
  simp only [CollatzResearch.WordTrace]
  refine ⟨143651449341237281625818437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191535265788316375501091249 143651449341237281625818437)
  ·
    refine ⟨26934646751481990304840957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143651449341237281625818437 26934646751481990304840957)
    ·
      refine ⟨10100492531805746364315359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26934646751481990304840957 10100492531805746364315359)
      ·
        refine ⟨15150738797708619546473039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10100492531805746364315359 15150738797708619546473039)
        ·
          refine ⟨22726108196562929319709559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15150738797708619546473039 22726108196562929319709559)
          ·
            refine ⟨34089162294844393979564339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22726108196562929319709559 34089162294844393979564339)
            ·
              refine ⟨51133743442266590969346509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34089162294844393979564339 51133743442266590969346509)
              ·
                refine ⟨19175153790849971613504941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51133743442266590969346509 19175153790849971613504941)
                ·
                  refine ⟨7190682671568739355064353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19175153790849971613504941 7190682671568739355064353)
                  ·
                    refine ⟨5393012003676554516298265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7190682671568739355064353 5393012003676554516298265)
                    ·
                      refine ⟨4044759002757415887223699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393012003676554516298265 4044759002757415887223699)
                      ·
                        rfl

theorem cell23_7877140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7877140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877140 prefixEnd_7877140 := by exact prefixLift 7877140
  have htrace : WordTrace (prefixWord ++ tailWord_7877140) baseStart_7877140 baseEnd_7877140 := by
    simpa [prefixWord, tailWord_7877140, baseEnd_7877140] using wordTrace_append hprefix tailTrace_7877140
  have hstable : (prefixWord ++ tailWord_7877140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877140).length < 2 ^ (prefixWord ++ tailWord_7877140).sum := by decide
  have hdescent : baseEnd_7877140 < baseStart_7877140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877174 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_7877174 : Nat := 118140960795 + 7877174 * 2 ^ 59
def prefixEnd_7877174 : Nat := 4983230072969 + 3 ^ 40 * 7877174 * 2
def baseEnd_7877174 : Nat := 4044776461099668754198543

theorem tailTrace_7877174 : CollatzResearch.WordTrace tailWord_7877174 prefixEnd_7877174 4044776461099668754198543 := by
  unfold tailWord_7877174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17956508672771961691148411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191536092509567591372249717 17956508672771961691148411)
  ·
    refine ⟨26934763009157942536722617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17956508672771961691148411 26934763009157942536722617)
    ·
      refine ⟨20201072256868456902541963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26934763009157942536722617 20201072256868456902541963)
      ·
        refine ⟨30301608385302685353812945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20201072256868456902541963 30301608385302685353812945)
        ·
          refine ⟨22726206288977014015359709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30301608385302685353812945 22726206288977014015359709)
          ·
            refine ⟨8522327358366380255759891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22726206288977014015359709 8522327358366380255759891)
            ·
              refine ⟨12783491037549570383639837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522327358366380255759891 12783491037549570383639837)
              ·
                refine ⟨4793809139081088893864939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12783491037549570383639837 4793809139081088893864939)
                ·
                  refine ⟨7190713708621633340797409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793809139081088893864939 7190713708621633340797409)
                  ·
                    refine ⟨5393035281466225005598057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7190713708621633340797409 5393035281466225005598057)
                    ·
                      refine ⟨4044776461099668754198543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393035281466225005598057 4044776461099668754198543)
                      ·
                        rfl

theorem cell23_7877174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_7877174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877174 prefixEnd_7877174 := by exact prefixLift 7877174
  have htrace : WordTrace (prefixWord ++ tailWord_7877174) baseStart_7877174 baseEnd_7877174 := by
    simpa [prefixWord, tailWord_7877174, baseEnd_7877174] using wordTrace_append hprefix tailTrace_7877174
  have hstable : (prefixWord ++ tailWord_7877174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877174).length < 2 ^ (prefixWord ++ tailWord_7877174).sum := by decide
  have hdescent : baseEnd_7877174 < baseStart_7877174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877190 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7877190 : Nat := 118140960795 + 7877190 * 2 ^ 59
def prefixEnd_7877190 : Nat := 4983230072969 + 3 ^ 40 * 7877190 * 2
def baseEnd_7877190 : Nat := 4044784676790140691598469

theorem tailTrace_7877190 : CollatzResearch.WordTrace tailWord_7877190 prefixEnd_7877190 4044784676790140691598469 := by
  unfold tailWord_7877190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8978272572884169430967407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191536481554862281193971349 8978272572884169430967407)
  ·
    refine ⟨13467408859326254146451111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8978272572884169430967407 13467408859326254146451111)
    ·
      refine ⟨20201113288989381219676667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13467408859326254146451111 20201113288989381219676667)
      ·
        refine ⟨30301669933484071829515001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20201113288989381219676667 30301669933484071829515001)
        ·
          refine ⟨22726252450113053872136251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30301669933484071829515001 22726252450113053872136251)
          ·
            refine ⟨34089378675169580808204377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22726252450113053872136251 34089378675169580808204377)
            ·
              refine ⟨25567034006377185606153283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34089378675169580808204377 25567034006377185606153283)
              ·
                refine ⟨38350551009565778409229925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25567034006377185606153283 38350551009565778409229925)
                ·
                  refine ⟨7190728314293583451730611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38350551009565778409229925 7190728314293583451730611)
                  ·
                    refine ⟨10786092471440375177595917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7190728314293583451730611 10786092471440375177595917)
                    ·
                      refine ⟨4044784676790140691598469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10786092471440375177595917 4044784676790140691598469)
                      ·
                        rfl

theorem cell23_7877190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7877190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877190 prefixEnd_7877190 := by exact prefixLift 7877190
  have htrace : WordTrace (prefixWord ++ tailWord_7877190) baseStart_7877190 baseEnd_7877190 := by
    simpa [prefixWord, tailWord_7877190, baseEnd_7877190] using wordTrace_append hprefix tailTrace_7877190
  have hstable : (prefixWord ++ tailWord_7877190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877190).length < 2 ^ (prefixWord ++ tailWord_7877190).sum := by decide
  have hdescent : baseEnd_7877190 < baseStart_7877190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877253 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 5]
def baseStart_7877253 : Nat := 118140960795 + 7877253 * 2 ^ 59
def prefixEnd_7877253 : Nat := 4983230072969 + 3 ^ 40 * 7877253 * 2
def baseEnd_7877253 : Nat := 449424114007930438345631

theorem tailTrace_7877253 : CollatzResearch.WordTrace tailWord_7877253 prefixEnd_7877253 449424114007930438345631 := by
  unfold tailWord_7877253
  simp only [CollatzResearch.WordTrace]
  refine ⟨287307020131065183550500413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191538013420710122367000275 287307020131065183550500413)
  ·
    refine ⟨107740132549149443831437655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287307020131065183550500413 107740132549149443831437655)
    ·
      refine ⟨161610198823724165747156483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107740132549149443831437655 161610198823724165747156483)
      ·
        refine ⟨242415298235586248620734725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161610198823724165747156483 242415298235586248620734725)
        ·
          refine ⟨45452868419172421616387761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242415298235586248620734725 45452868419172421616387761)
          ·
            refine ⟨34089651314379316212290821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45452868419172421616387761 34089651314379316212290821)
            ·
              refine ⟨6391809621446121789804529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34089651314379316212290821 6391809621446121789804529)
              ·
                refine ⟨4793857216084591342353397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391809621446121789804529 4793857216084591342353397)
                ·
                  refine ⟨449424114007930438345631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4793857216084591342353397 449424114007930438345631)
                  ·
                    rfl

theorem cell23_7877253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_7877253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877253 prefixEnd_7877253 := by exact prefixLift 7877253
  have htrace : WordTrace (prefixWord ++ tailWord_7877253) baseStart_7877253 baseEnd_7877253 := by
    simpa [prefixWord, tailWord_7877253, baseEnd_7877253] using wordTrace_append hprefix tailTrace_7877253
  have hstable : (prefixWord ++ tailWord_7877253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877253).length < 2 ^ (prefixWord ++ tailWord_7877253).sum := by decide
  have hdescent : baseEnd_7877253 < baseStart_7877253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877299 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6]
def baseStart_7877299 : Nat := 118140960795 + 7877299 * 2 ^ 59
def prefixEnd_7877299 : Nat := 4983230072969 + 3 ^ 40 * 7877299 * 2
def baseEnd_7877299 : Nat := 4044840646181480765135467

theorem tailTrace_7877299 : CollatzResearch.WordTrace tailWord_7877299 prefixEnd_7877299 4044840646181480765135467 := by
  unfold tailWord_7877299
  simp only [CollatzResearch.WordTrace]
  refine ⟨287308697888898533406674951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191539131925932355604449967 287308697888898533406674951)
  ·
    refine ⟨430963046833347800110012427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287308697888898533406674951 430963046833347800110012427)
    ·
      refine ⟨646444570250021700165018641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430963046833347800110012427 646444570250021700165018641)
      ·
        refine ⟨484833427687516275123763981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646444570250021700165018641 484833427687516275123763981)
        ·
          refine ⟨181812535382818603171411493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484833427687516275123763981 181812535382818603171411493)
          ·
            refine ⟨34089850384278488094639655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181812535382818603171411493 34089850384278488094639655)
            ·
              refine ⟨51134775576417732141959483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34089850384278488094639655 51134775576417732141959483)
              ·
                refine ⟨76702163364626598212939225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51134775576417732141959483 76702163364626598212939225)
                ·
                  refine ⟨57526622523469948659704419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76702163364626598212939225 57526622523469948659704419)
                  ·
                    refine ⟨86289933785204922989556629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57526622523469948659704419 86289933785204922989556629)
                    ·
                      refine ⟨4044840646181480765135467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86289933785204922989556629 4044840646181480765135467)
                      ·
                        rfl

theorem cell23_7877299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_7877299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877299 prefixEnd_7877299 := by exact prefixLift 7877299
  have htrace : WordTrace (prefixWord ++ tailWord_7877299) baseStart_7877299 baseEnd_7877299 := by
    simpa [prefixWord, tailWord_7877299, baseEnd_7877299] using wordTrace_append hprefix tailTrace_7877299
  have hstable : (prefixWord ++ tailWord_7877299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877299).length < 2 ^ (prefixWord ++ tailWord_7877299).sum := by decide
  have hdescent : baseEnd_7877299 < baseStart_7877299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877306 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_7877306 : Nat := 118140960795 + 7877306 * 2 ^ 59
def prefixEnd_7877306 : Nat := 4983230072969 + 3 ^ 40 * 7877306 * 2
def baseEnd_7877306 : Nat := 4044844240546062237747935

theorem tailTrace_7877306 : CollatzResearch.WordTrace tailWord_7877306 prefixEnd_7877306 4044844240546062237747935 := by
  unfold tailWord_7877306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71827238299968293400544943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191539302133248782401453181 71827238299968293400544943)
  ·
    refine ⟨107740857449952440100817415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71827238299968293400544943 107740857449952440100817415)
    ·
      refine ⟨161611286174928660151226123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107740857449952440100817415 161611286174928660151226123)
      ·
        refine ⟨242416929262392990226839185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161611286174928660151226123 242416929262392990226839185)
        ·
          refine ⟨181812696946794742670129389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242416929262392990226839185 181812696946794742670129389)
          ·
            refine ⟨68179761355048028501298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181812696946794742670129389 68179761355048028501298521)
            ·
              refine ⟨51134821016286021375973891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68179761355048028501298521 51134821016286021375973891)
              ·
                refine ⟨76702231524429032063960837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51134821016286021375973891 76702231524429032063960837)
                ·
                  refine ⟨14381668410830443511992657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76702231524429032063960837 14381668410830443511992657)
                  ·
                    refine ⟨10786251308122832633994493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14381668410830443511992657 10786251308122832633994493)
                    ·
                      refine ⟨4044844240546062237747935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10786251308122832633994493 4044844240546062237747935)
                      ·
                        rfl

theorem cell23_7877306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_7877306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877306 prefixEnd_7877306 := by exact prefixLift 7877306
  have htrace : WordTrace (prefixWord ++ tailWord_7877306) baseStart_7877306 baseEnd_7877306 := by
    simpa [prefixWord, tailWord_7877306, baseEnd_7877306] using wordTrace_append hprefix tailTrace_7877306
  have hstable : (prefixWord ++ tailWord_7877306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877306).length < 2 ^ (prefixWord ++ tailWord_7877306).sum := by decide
  have hdescent : baseEnd_7877306 < baseStart_7877306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877329 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_7877329 : Nat := 118140960795 + 7877329 * 2 ^ 59
def prefixEnd_7877329 : Nat := 4983230072969 + 3 ^ 40 * 7877329 * 2
def baseEnd_7877329 : Nat := 4044856050601115647760329

theorem tailTrace_7877329 : CollatzResearch.WordTrace tailWord_7877329 prefixEnd_7877329 4044856050601115647760329 := by
  unfold tailWord_7877329
  simp only [CollatzResearch.WordTrace]
  refine ⟨287309792078789848530267041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191539861385859899020178027 287309792078789848530267041)
  ·
    refine ⟨215482344059092386397700281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287309792078789848530267041 215482344059092386397700281)
    ·
      refine ⟨161611758044319289798275211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215482344059092386397700281 161611758044319289798275211)
      ·
        refine ⟨242417637066478934697412817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161611758044319289798275211 242417637066478934697412817)
        ·
          refine ⟨181813227799859201023059613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242417637066478934697412817 181813227799859201023059613)
          ·
            refine ⟨68179960424947200383647355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181813227799859201023059613 68179960424947200383647355)
            ·
              refine ⟨102269940637420800575471033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68179960424947200383647355 102269940637420800575471033)
              ·
                refine ⟨76702455478065600431603275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102269940637420800575471033 76702455478065600431603275)
                ·
                  refine ⟨115053683217098400647404913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76702455478065600431603275 115053683217098400647404913)
                  ·
                    refine ⟨86290262412823800485553685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115053683217098400647404913 86290262412823800485553685)
                    ·
                      refine ⟨4044856050601115647760329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86290262412823800485553685 4044856050601115647760329)
                      ·
                        rfl

theorem cell23_7877329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_7877329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877329 prefixEnd_7877329 := by exact prefixLift 7877329
  have htrace : WordTrace (prefixWord ++ tailWord_7877329) baseStart_7877329 baseEnd_7877329 := by
    simpa [prefixWord, tailWord_7877329, baseEnd_7877329] using wordTrace_append hprefix tailTrace_7877329
  have hstable : (prefixWord ++ tailWord_7877329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877329).length < 2 ^ (prefixWord ++ tailWord_7877329).sum := by decide
  have hdescent : baseEnd_7877329 < baseStart_7877329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877347 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 1, 4]
def baseStart_7877347 : Nat := 118140960795 + 7877347 * 2 ^ 59
def prefixEnd_7877347 : Nat := 4983230072969 + 3 ^ 40 * 7877347 * 2
def baseEnd_7877347 : Nat := 1348288431084298859111749

theorem tailTrace_7877347 : CollatzResearch.WordTrace tailWord_7877347 prefixEnd_7877347 1348288431084298859111749 := by
  unfold tailWord_7877347
  simp only [CollatzResearch.WordTrace]
  refine ⟨287310448592724637604422295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191540299061816425069614863 287310448592724637604422295)
  ·
    refine ⟨430965672889086956406633443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287310448592724637604422295 430965672889086956406633443)
    ·
      refine ⟨646448509333630434609950165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430965672889086956406633443 646448509333630434609950165)
      ·
        refine ⟨15151136937506963311170707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 646448509333630434609950165 15151136937506963311170707)
        ·
          refine ⟨22726705406260444966756061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151136937506963311170707 22726705406260444966756061)
          ·
            refine ⟨8522514527347666862533523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22726705406260444966756061 8522514527347666862533523)
            ·
              refine ⟨12783771791021500293800285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522514527347666862533523 12783771791021500293800285)
              ·
                refine ⟨4793914421633062610175107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12783771791021500293800285 4793914421633062610175107)
                ·
                  refine ⟨7190871632449593915262661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793914421633062610175107 7190871632449593915262661)
                  ·
                    refine ⟨1348288431084298859111749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190871632449593915262661 1348288431084298859111749)
                    ·
                      rfl

theorem cell23_7877347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 4].length) (baseStart_7877347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877347 prefixEnd_7877347 := by exact prefixLift 7877347
  have htrace : WordTrace (prefixWord ++ tailWord_7877347) baseStart_7877347 baseEnd_7877347 := by
    simpa [prefixWord, tailWord_7877347, baseEnd_7877347] using wordTrace_append hprefix tailTrace_7877347
  have hstable : (prefixWord ++ tailWord_7877347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877347).length < 2 ^ (prefixWord ++ tailWord_7877347).sum := by decide
  have hdescent : baseEnd_7877347 < baseStart_7877347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877364 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7877364 : Nat := 118140960795 + 7877364 * 2 ^ 59
def prefixEnd_7877364 : Nat := 4983230072969 + 3 ^ 40 * 7877364 * 2
def baseEnd_7877364 : Nat := 1348291340808007670274223

theorem tailTrace_7877364 : CollatzResearch.WordTrace tailWord_7877364 prefixEnd_7877364 1348291340808007670274223 := by
  unfold tailWord_7877364
  simp only [CollatzResearch.WordTrace]
  refine ⟨143655534316831524753895573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191540712422442033005194097 143655534316831524753895573)
  ·
    refine ⟨6733853171101477722838855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143655534316831524753895573 6733853171101477722838855)
    ·
      refine ⟨10100779756652216584258283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6733853171101477722838855 10100779756652216584258283)
      ·
        refine ⟨15151169634978324876387425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10100779756652216584258283 15151169634978324876387425)
        ·
          refine ⟨11363377226233743657290569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15151169634978324876387425 11363377226233743657290569)
          ·
            refine ⟨8522532919675307742967927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11363377226233743657290569 8522532919675307742967927)
            ·
              refine ⟨12783799379512961614451891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522532919675307742967927 12783799379512961614451891)
              ·
                refine ⟨19175699069269442421677837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12783799379512961614451891 19175699069269442421677837)
                ·
                  refine ⟨7190887150976040908129189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19175699069269442421677837 7190887150976040908129189)
                  ·
                    refine ⟨1348291340808007670274223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190887150976040908129189 1348291340808007670274223)
                    ·
                      rfl

theorem cell23_7877364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7877364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877364 prefixEnd_7877364 := by exact prefixLift 7877364
  have htrace : WordTrace (prefixWord ++ tailWord_7877364) baseStart_7877364 baseEnd_7877364 := by
    simpa [prefixWord, tailWord_7877364, baseEnd_7877364] using wordTrace_append hprefix tailTrace_7877364
  have hstable : (prefixWord ++ tailWord_7877364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877364).length < 2 ^ (prefixWord ++ tailWord_7877364).sum := by decide
  have hdescent : baseEnd_7877364 < baseStart_7877364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877370 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3]
def baseStart_7877370 : Nat := 118140960795 + 7877370 * 2 ^ 59
def prefixEnd_7877370 : Nat := 4983230072969 + 3 ^ 40 * 7877370 * 2
def baseEnd_7877370 : Nat := 4044877103307949987347641

theorem tailTrace_7877370 : CollatzResearch.WordTrace tailWord_7877370 prefixEnd_7877370 4044877103307949987347641 := by
  unfold tailWord_7877370
  simp only [CollatzResearch.WordTrace]
  refine ⟨71827821867910328133127391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191540858314427541688339709 71827821867910328133127391)
  ·
    refine ⟨107741732801865492199691087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71827821867910328133127391 107741732801865492199691087)
    ·
      refine ⟨161612599202798238299536631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107741732801865492199691087 161612599202798238299536631)
      ·
        refine ⟨242418898804197357449304947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161612599202798238299536631 242418898804197357449304947)
        ·
          refine ⟨363628348206296036173957421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242418898804197357449304947 363628348206296036173957421)
          ·
            refine ⟨136360630577361013565234033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363628348206296036173957421 136360630577361013565234033)
            ·
              refine ⟨102270472933020760173925525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136360630577361013565234033 102270472933020760173925525)
              ·
                refine ⟨4793928418735348133152759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102270472933020760173925525 4793928418735348133152759)
                ·
                  refine ⟨7190892628103022199729139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793928418735348133152759 7190892628103022199729139)
                  ·
                    refine ⟨10786338942154533299593709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7190892628103022199729139 10786338942154533299593709)
                    ·
                      refine ⟨4044877103307949987347641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10786338942154533299593709 4044877103307949987347641)
                      ·
                        rfl

theorem cell23_7877370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_7877370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877370 prefixEnd_7877370 := by exact prefixLift 7877370
  have htrace : WordTrace (prefixWord ++ tailWord_7877370) baseStart_7877370 baseEnd_7877370 := by
    simpa [prefixWord, tailWord_7877370, baseEnd_7877370] using wordTrace_append hprefix tailTrace_7877370
  have hstable : (prefixWord ++ tailWord_7877370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877370).length < 2 ^ (prefixWord ++ tailWord_7877370).sum := by decide
  have hdescent : baseEnd_7877370 < baseStart_7877370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877386 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_7877386 : Nat := 118140960795 + 7877386 * 2 ^ 59
def prefixEnd_7877386 : Nat := 4983230072969 + 3 ^ 40 * 7877386 * 2
def baseEnd_7877386 : Nat := 1348295106332807308249189

theorem tailTrace_7877386 : CollatzResearch.WordTrace tailWord_7877386 prefixEnd_7877386 1348295106332807308249189 := by
  unfold tailWord_7877386
  simp only [CollatzResearch.WordTrace]
  refine ⟨71827967759895836816273003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191541247359722231510061341 71827967759895836816273003)
  ·
    refine ⟨107741951639843755224409505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71827967759895836816273003 107741951639843755224409505)
    ·
      refine ⟨80806463729882816418307129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107741951639843755224409505 80806463729882816418307129)
      ·
        refine ⟨60604847797412112313730347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80806463729882816418307129 60604847797412112313730347)
        ·
          refine ⟨90907271696118168470595521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60604847797412112313730347 90907271696118168470595521)
          ·
            refine ⟨68180453772088626352946641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90907271696118168470595521 68180453772088626352946641)
            ·
              refine ⟨51135340329066469764709981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68180453772088626352946641 51135340329066469764709981)
              ·
                refine ⟨19175752623399926161766243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51135340329066469764709981 19175752623399926161766243)
                ·
                  refine ⟨28763628935099889242649365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19175752623399926161766243 28763628935099889242649365)
                  ·
                    refine ⟨1348295106332807308249189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28763628935099889242649365 1348295106332807308249189)
                    ·
                      rfl

theorem cell23_7877386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_7877386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877386 prefixEnd_7877386 := by exact prefixLift 7877386
  have htrace : WordTrace (prefixWord ++ tailWord_7877386) baseStart_7877386 baseEnd_7877386 := by
    simpa [prefixWord, tailWord_7877386, baseEnd_7877386] using wordTrace_append hprefix tailTrace_7877386
  have hstable : (prefixWord ++ tailWord_7877386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877386).length < 2 ^ (prefixWord ++ tailWord_7877386).sum := by decide
  have hdescent : baseEnd_7877386 < baseStart_7877386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877393 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_7877393 : Nat := 118140960795 + 7877393 * 2 ^ 59
def prefixEnd_7877393 : Nat := 4983230072969 + 3 ^ 40 * 7877393 * 2
def baseEnd_7877393 : Nat := 4044888913363003397360035

theorem tailTrace_7877393 : CollatzResearch.WordTrace tailWord_7877393 prefixEnd_7877393 4044888913363003397360035 := by
  unfold tailWord_7877393
  simp only [CollatzResearch.WordTrace]
  refine ⟨287312126350557987460596833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191541417567038658307064555 287312126350557987460596833)
  ·
    refine ⟨215484094762918490595447625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287312126350557987460596833 215484094762918490595447625)
    ·
      refine ⟨161613071072188867946585719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215484094762918490595447625 161613071072188867946585719)
      ·
        refine ⟨242419606608283301919878579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161613071072188867946585719 242419606608283301919878579)
        ·
          refine ⟨363629409912424952879817869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242419606608283301919878579 363629409912424952879817869)
          ·
            refine ⟨136361028717159357329931701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363629409912424952879817869 136361028717159357329931701)
            ·
              refine ⟨12783846442233689749681097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136361028717159357329931701 12783846442233689749681097)
              ·
                refine ⟨9587884831675267312260823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12783846442233689749681097 9587884831675267312260823)
                ·
                  refine ⟨14381827247512900968391235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9587884831675267312260823 14381827247512900968391235)
                  ·
                    refine ⟨21572740871269351452586853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14381827247512900968391235 21572740871269351452586853)
                    ·
                      refine ⟨4044888913363003397360035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21572740871269351452586853 4044888913363003397360035)
                      ·
                        rfl

theorem cell23_7877393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_7877393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877393 prefixEnd_7877393 := by exact prefixLift 7877393
  have htrace : WordTrace (prefixWord ++ tailWord_7877393) baseStart_7877393 baseEnd_7877393 := by
    simpa [prefixWord, tailWord_7877393, baseEnd_7877393] using wordTrace_append hprefix tailTrace_7877393
  have hstable : (prefixWord ++ tailWord_7877393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877393).length < 2 ^ (prefixWord ++ tailWord_7877393).sum := by decide
  have hdescent : baseEnd_7877393 < baseStart_7877393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877421 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7877421 : Nat := 118140960795 + 7877421 * 2 ^ 59
def prefixEnd_7877421 : Nat := 4983230072969 + 3 ^ 40 * 7877421 * 2
def baseEnd_7877421 : Nat := 4044903290821329287809907

theorem tailTrace_7877421 : CollatzResearch.WordTrace tailWord_7877421 prefixEnd_7877421 4044903290821329287809907 := by
  unfold tailWord_7877421
  simp only [CollatzResearch.WordTrace]
  refine ⟨287313147594456548242616117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191542098396304365495077411 287313147594456548242616117)
  ·
    refine ⟨26935607586980301397745261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287313147594456548242616117 26935607586980301397745261)
    ·
      refine ⟨10100852845117613024154473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26935607586980301397745261 10100852845117613024154473)
      ·
        refine ⟨7575639633838209768115855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10100852845117613024154473 7575639633838209768115855)
        ·
          refine ⟨11363459450757314652173783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575639633838209768115855 11363459450757314652173783)
          ·
            refine ⟨17045189176135971978260675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363459450757314652173783 17045189176135971978260675)
            ·
              refine ⟨25567783764203957967391013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17045189176135971978260675 25567783764203957967391013)
              ·
                refine ⟨4793959455788242118885815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25567783764203957967391013 4793959455788242118885815)
                ·
                  refine ⟨7190939183682363178328723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793959455788242118885815 7190939183682363178328723)
                  ·
                    refine ⟨10786408775523544767493085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7190939183682363178328723 10786408775523544767493085)
                    ·
                      refine ⟨4044903290821329287809907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10786408775523544767493085 4044903290821329287809907)
                      ·
                        rfl

theorem cell23_7877421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7877421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877421 prefixEnd_7877421 := by exact prefixLift 7877421
  have htrace : WordTrace (prefixWord ++ tailWord_7877421) baseStart_7877421 baseEnd_7877421 := by
    simpa [prefixWord, tailWord_7877421, baseEnd_7877421] using wordTrace_append hprefix tailTrace_7877421
  have hstable : (prefixWord ++ tailWord_7877421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877421).length < 2 ^ (prefixWord ++ tailWord_7877421).sum := by decide
  have hdescent : baseEnd_7877421 < baseStart_7877421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877443 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 3]
def baseStart_7877443 : Nat := 118140960795 + 7877443 * 2 ^ 59
def prefixEnd_7877443 : Nat := 4983230072969 + 3 ^ 40 * 7877443 * 2
def baseEnd_7877443 : Nat := 4044914587395728201734805

theorem tailTrace_7877443 : CollatzResearch.WordTrace tailWord_7877443 prefixEnd_7877443 4044914587395728201734805 := by
  unfold tailWord_7877443
  simp only [CollatzResearch.WordTrace]
  refine ⟨287313950000376845999916983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191542633333584563999944655 287313950000376845999916983)
  ·
    refine ⟨430970925000565268999875475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287313950000376845999916983 430970925000565268999875475)
    ·
      refine ⟨646456387500847903499813213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430970925000565268999875475 646456387500847903499813213)
      ·
        refine ⟨242421145312817963812429955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646456387500847903499813213 242421145312817963812429955)
        ·
          refine ⟨363631717969226945718644933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242421145312817963812429955 363631717969226945718644933)
          ·
            refine ⟨68180947119230052322245925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363631717969226945718644933 68180947119230052322245925)
            ·
              refine ⟨12783927584855634810421111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68180947119230052322245925 12783927584855634810421111)
              ·
                refine ⟨19175891377283452215631667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12783927584855634810421111 19175891377283452215631667)
                ·
                  refine ⟨28763837065925178323447501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19175891377283452215631667 28763837065925178323447501)
                  ·
                    refine ⟨10786438899721941871292813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28763837065925178323447501 10786438899721941871292813)
                    ·
                      refine ⟨4044914587395728201734805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10786438899721941871292813 4044914587395728201734805)
                      ·
                        rfl

theorem cell23_7877443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_7877443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877443 prefixEnd_7877443 := by exact prefixLift 7877443
  have htrace : WordTrace (prefixWord ++ tailWord_7877443) baseStart_7877443 baseEnd_7877443 := by
    simpa [prefixWord, tailWord_7877443, baseEnd_7877443] using wordTrace_append hprefix tailTrace_7877443
  have hstable : (prefixWord ++ tailWord_7877443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877443).length < 2 ^ (prefixWord ++ tailWord_7877443).sum := by decide
  have hdescent : baseEnd_7877443 < baseStart_7877443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877483 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 3, 4, 2]
def baseStart_7877483 : Nat := 118140960795 + 7877483 * 2 ^ 59
def prefixEnd_7877483 : Nat := 4983230072969 + 3 ^ 40 * 7877483 * 2
def baseEnd_7877483 : Nat := 4044935126621908045234621

theorem tailTrace_7877483 : CollatzResearch.WordTrace tailWord_7877483 prefixEnd_7877483 4044935126621908045234621 := by
  unfold tailWord_7877483
  simp only [CollatzResearch.WordTrace]
  refine ⟨287315408920231932831373103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191543605946821288554248735 287315408920231932831373103)
  ·
    refine ⟨430973113380347899247059655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287315408920231932831373103 430973113380347899247059655)
    ·
      refine ⟨646459670070521848870589483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430973113380347899247059655 646459670070521848870589483)
      ·
        refine ⟨969689505105782773305884225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646459670070521848870589483 969689505105782773305884225)
        ·
          refine ⟨727267128829337079979413169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969689505105782773305884225 727267128829337079979413169)
          ·
            refine ⟨545450346622002809984559877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727267128829337079979413169 545450346622002809984559877)
            ·
              refine ⟨102271939991625526872104977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545450346622002809984559877 102271939991625526872104977)
              ·
                refine ⟨76703954993719145154078733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102271939991625526872104977 76703954993719145154078733)
                ·
                  refine ⟨28763983122644679432779525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76703954993719145154078733 28763983122644679432779525)
                  ·
                    refine ⟨5393246835495877393646161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28763983122644679432779525 5393246835495877393646161)
                    ·
                      refine ⟨4044935126621908045234621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393246835495877393646161 4044935126621908045234621)
                      ·
                        rfl

theorem cell23_7877483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4, 2].length) (baseStart_7877483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877483 prefixEnd_7877483 := by exact prefixLift 7877483
  have htrace : WordTrace (prefixWord ++ tailWord_7877483) baseStart_7877483 baseEnd_7877483 := by
    simpa [prefixWord, tailWord_7877483, baseEnd_7877483] using wordTrace_append hprefix tailTrace_7877483
  have hstable : (prefixWord ++ tailWord_7877483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877483).length < 2 ^ (prefixWord ++ tailWord_7877483).sum := by decide
  have hdescent : baseEnd_7877483 < baseStart_7877483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877493 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7877493 : Nat := 118140960795 + 7877493 * 2 ^ 59
def prefixEnd_7877493 : Nat := 4983230072969 + 3 ^ 40 * 7877493 * 2
def baseEnd_7877493 : Nat := 1348313420476151002036525

theorem tailTrace_7877493 : CollatzResearch.WordTrace tailWord_7877493 prefixEnd_7877493 1348313420476151002036525 := by
  unfold tailWord_7877493
  simp only [CollatzResearch.WordTrace]
  refine ⟨287315773650195704539237133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191543849100130469692824755 287315773650195704539237133)
  ·
    refine ⟨107743415118823389202213925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287315773650195704539237133 107743415118823389202213925)
    ·
      refine ⟨20201890334779385475415111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107743415118823389202213925 20201890334779385475415111)
      ·
        refine ⟨30302835502169078213122667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20201890334779385475415111 30302835502169078213122667)
        ·
          refine ⟨45454253253253617319684001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30302835502169078213122667 45454253253253617319684001)
          ·
            refine ⟨34090689939940212989763001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45454253253253617319684001 34090689939940212989763001)
            ·
              refine ⟨25568017454955159742322251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34090689939940212989763001 25568017454955159742322251)
              ·
                refine ⟨38352026182432739613483377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25568017454955159742322251 38352026182432739613483377)
                ·
                  refine ⟨28764019636824554710112533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38352026182432739613483377 28764019636824554710112533)
                  ·
                    refine ⟨1348313420476151002036525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28764019636824554710112533 1348313420476151002036525)
                    ·
                      rfl

theorem cell23_7877493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7877493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877493 prefixEnd_7877493 := by exact prefixLift 7877493
  have htrace : WordTrace (prefixWord ++ tailWord_7877493) baseStart_7877493 baseEnd_7877493 := by
    simpa [prefixWord, tailWord_7877493, baseEnd_7877493] using wordTrace_append hprefix tailTrace_7877493
  have hstable : (prefixWord ++ tailWord_7877493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877493).length < 2 ^ (prefixWord ++ tailWord_7877493).sum := by decide
  have hdescent : baseEnd_7877493 < baseStart_7877493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877496 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_7877496 : Nat := 118140960795 + 7877496 * 2 ^ 59
def prefixEnd_7877496 : Nat := 4983230072969 + 3 ^ 40 * 7877496 * 2
def baseEnd_7877496 : Nat := 4044941801870416494372061

theorem tailTrace_7877496 : CollatzResearch.WordTrace tailWord_7877496 prefixEnd_7877496 4044941801870416494372061 := by
  unfold tailWord_7877496
  simp only [CollatzResearch.WordTrace]
  refine ⟨143657941534592418025798171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191543922046123224034397561 143657941534592418025798171)
  ·
    refine ⟨215486912301888627038697257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143657941534592418025798171 215486912301888627038697257)
    ·
      refine ⟨161615184226416470279022943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215486912301888627038697257 161615184226416470279022943)
      ·
        refine ⟨242422776339624705418534415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161615184226416470279022943 242422776339624705418534415)
        ·
          refine ⟨363634164509437058127801623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242422776339624705418534415 363634164509437058127801623)
          ·
            refine ⟨545451246764155587191702435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363634164509437058127801623 545451246764155587191702435)
            ·
              refine ⟨818176870146233380787553653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545451246764155587191702435 818176870146233380787553653)
              ·
                refine ⟨76704081576209379448833155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 818176870146233380787553653 76704081576209379448833155)
                ·
                  refine ⟨115056122364314069173249733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76704081576209379448833155 115056122364314069173249733)
                  ·
                    refine ⟨21573022943308887969984325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115056122364314069173249733 21573022943308887969984325)
                    ·
                      refine ⟨4044941801870416494372061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21573022943308887969984325 4044941801870416494372061)
                      ·
                        rfl

theorem cell23_7877496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_7877496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877496 prefixEnd_7877496 := by exact prefixLift 7877496
  have htrace : WordTrace (prefixWord ++ tailWord_7877496) baseStart_7877496 baseEnd_7877496 := by
    simpa [prefixWord, tailWord_7877496, baseEnd_7877496] using wordTrace_append hprefix tailTrace_7877496
  have hstable : (prefixWord ++ tailWord_7877496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877496).length < 2 ^ (prefixWord ++ tailWord_7877496).sum := by decide
  have hdescent : baseEnd_7877496 < baseStart_7877496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877523 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 5]
def baseStart_7877523 : Nat := 118140960795 + 7877523 * 2 ^ 59
def prefixEnd_7877523 : Nat := 4983230072969 + 3 ^ 40 * 7877523 * 2
def baseEnd_7877523 : Nat := 449439518427565320970493

theorem tailTrace_7877523 : CollatzResearch.WordTrace tailWord_7877523 prefixEnd_7877523 449439518427565320970493 := by
  unfold tailWord_7877523
  simp only [CollatzResearch.WordTrace]
  refine ⟨287316867840087019662829223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191544578560058013108552815 287316867840087019662829223)
  ·
    refine ⟨430975301760130529494243835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287316867840087019662829223 430975301760130529494243835)
    ·
      refine ⟨646462952640195794241365753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430975301760130529494243835 646462952640195794241365753)
      ·
        refine ⟨484847214480146845681024315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646462952640195794241365753 484847214480146845681024315)
        ·
          refine ⟨727270821720220268521536473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484847214480146845681024315 727270821720220268521536473)
          ·
            refine ⟨545453116290165201391152355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727270821720220268521536473 545453116290165201391152355)
            ·
              refine ⟨818179674435247802086728533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545453116290165201391152355 818179674435247802086728533)
              ·
                refine ⟨4794021529894030090351925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 818179674435247802086728533 4794021529894030090351925)
                ·
                  refine ⟨449439518427565320970493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794021529894030090351925 449439518427565320970493)
                  ·
                    rfl

theorem cell23_7877523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 5].length) (baseStart_7877523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877523 prefixEnd_7877523 := by exact prefixLift 7877523
  have htrace : WordTrace (prefixWord ++ tailWord_7877523) baseStart_7877523 baseEnd_7877523 := by
    simpa [prefixWord, tailWord_7877523, baseEnd_7877523] using wordTrace_append hprefix tailTrace_7877523
  have hstable : (prefixWord ++ tailWord_7877523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877523).length < 2 ^ (prefixWord ++ tailWord_7877523).sum := by decide
  have hdescent : baseEnd_7877523 < baseStart_7877523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877607 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7877607 : Nat := 118140960795 + 7877607 * 2 ^ 59
def prefixEnd_7877607 : Nat := 4983230072969 + 3 ^ 40 * 7877607 * 2
def baseEnd_7877607 : Nat := 4044998798223065560084051

theorem tailTrace_7877607 : CollatzResearch.WordTrace tailWord_7877607 prefixEnd_7877607 4044998798223065560084051 := by
  unfold tailWord_7877607
  simp only [CollatzResearch.WordTrace]
  refine ⟨287319931571782702008887075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191546621047855134672591383 287319931571782702008887075)
  ·
    refine ⟨430979897357674053013330613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287319931571782702008887075 430979897357674053013330613)
    ·
      refine ⟨40404365377281942469999745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430979897357674053013330613 40404365377281942469999745)
      ·
        refine ⟨30303274032961456852499809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40404365377281942469999745 30303274032961456852499809)
        ·
          refine ⟨22727455524721092639374857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30303274032961456852499809 22727455524721092639374857)
          ·
            refine ⟨17045591643540819479531143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22727455524721092639374857 17045591643540819479531143)
            ·
              refine ⟨25568387465311229219296715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17045591643540819479531143 25568387465311229219296715)
              ·
                refine ⟨38352581197966843828945073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25568387465311229219296715 38352581197966843828945073)
                ·
                  refine ⟨28764435898475132871708805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38352581197966843828945073 28764435898475132871708805)
                  ·
                    refine ⟨5393331730964087413445401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28764435898475132871708805 5393331730964087413445401)
                    ·
                      refine ⟨4044998798223065560084051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393331730964087413445401 4044998798223065560084051)
                      ·
                        rfl

theorem cell23_7877607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7877607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877607 prefixEnd_7877607 := by exact prefixLift 7877607
  have htrace : WordTrace (prefixWord ++ tailWord_7877607) baseStart_7877607 baseEnd_7877607 := by
    simpa [prefixWord, tailWord_7877607, baseEnd_7877607] using wordTrace_append hprefix tailTrace_7877607
  have hstable : (prefixWord ++ tailWord_7877607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877607).length < 2 ^ (prefixWord ++ tailWord_7877607).sum := by decide
  have hdescent : baseEnd_7877607 < baseStart_7877607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877621 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7877621 : Nat := 118140960795 + 7877621 * 2 ^ 59
def prefixEnd_7877621 : Nat := 4983230072969 + 3 ^ 40 * 7877621 * 2
def baseEnd_7877621 : Nat := 1348335328984076168436329

theorem tailTrace_7877621 : CollatzResearch.WordTrace tailWord_7877621 prefixEnd_7877621 1348335328984076168436329 := by
  unfold tailWord_7877621
  simp only [CollatzResearch.WordTrace]
  refine ⟨287320442193731982399896717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191546961462487988266597811 287320442193731982399896717)
  ·
    refine ⟨107745165822649493399961269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287320442193731982399896717 107745165822649493399961269)
    ·
      refine ⟨10101109295873390006246369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107745165822649493399961269 10101109295873390006246369)
      ·
        refine ⟨7575831971905042504684777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10101109295873390006246369 7575831971905042504684777)
        ·
          refine ⟨5681873978928781878513583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7575831971905042504684777 5681873978928781878513583)
          ·
            refine ⟨8522810968393172817770375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681873978928781878513583 8522810968393172817770375)
            ·
              refine ⟨12784216452589759226655563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522810968393172817770375 12784216452589759226655563)
              ·
                refine ⟨19176324678884638839983345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784216452589759226655563 19176324678884638839983345)
                ·
                  refine ⟨14382243509163479129987509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19176324678884638839983345 14382243509163479129987509)
                  ·
                    refine ⟨1348335328984076168436329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14382243509163479129987509 1348335328984076168436329)
                    ·
                      rfl

theorem cell23_7877621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7877621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877621 prefixEnd_7877621 := by exact prefixLift 7877621
  have htrace : WordTrace (prefixWord ++ tailWord_7877621) baseStart_7877621 baseEnd_7877621 := by
    simpa [prefixWord, tailWord_7877621, baseEnd_7877621] using wordTrace_append hprefix tailTrace_7877621
  have hstable : (prefixWord ++ tailWord_7877621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877621).length < 2 ^ (prefixWord ++ tailWord_7877621).sum := by decide
  have hdescent : baseEnd_7877621 < baseStart_7877621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877664 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 6]
def baseStart_7877664 : Nat := 118140960795 + 7877664 * 2 ^ 59
def prefixEnd_7877664 : Nat := 4983230072969 + 3 ^ 40 * 7877664 * 2
def baseEnd_7877664 : Nat := 449447562957819093007921

theorem tailTrace_7877664 : CollatzResearch.WordTrace tailWord_7877664 prefixEnd_7877664 449447562957819093007921 := by
  unfold tailWord_7877664
  simp only [CollatzResearch.WordTrace]
  refine ⟨143661005266288100371856023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191548007021717467162474697 143661005266288100371856023)
  ·
    refine ⟨215491507899432150557784035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143661005266288100371856023 215491507899432150557784035)
    ·
      refine ⟨323237261849148225836676053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215491507899432150557784035 323237261849148225836676053)
      ·
        refine ⟨7575873324589411543047095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 323237261849148225836676053 7575873324589411543047095)
        ·
          refine ⟨11363809986884117314570643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575873324589411543047095 11363809986884117314570643)
          ·
            refine ⟨17045714980326175971855965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363809986884117314570643 17045714980326175971855965)
            ·
              refine ⟨6392143117622315989445987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17045714980326175971855965 6392143117622315989445987)
              ·
                refine ⟨9588214676433473984168981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392143117622315989445987 9588214676433473984168981)
                ·
                  refine ⟨449447562957819093007921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9588214676433473984168981 449447562957819093007921)
                  ·
                    rfl

theorem cell23_7877664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 6].length) (baseStart_7877664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877664 prefixEnd_7877664 := by exact prefixLift 7877664
  have htrace : WordTrace (prefixWord ++ tailWord_7877664) baseStart_7877664 baseEnd_7877664 := by
    simpa [prefixWord, tailWord_7877664, baseEnd_7877664] using wordTrace_append hprefix tailTrace_7877664
  have hstable : (prefixWord ++ tailWord_7877664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877664).length < 2 ^ (prefixWord ++ tailWord_7877664).sum := by decide
  have hdescent : baseEnd_7877664 < baseStart_7877664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877680 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 6, 2]
def baseStart_7877680 : Nat := 118140960795 + 7877680 * 2 ^ 59
def prefixEnd_7877680 : Nat := 4983230072969 + 3 ^ 40 * 7877680 * 2
def baseEnd_7877680 : Nat := 4045036282310843774471215

theorem tailTrace_7877680 : CollatzResearch.WordTrace tailWord_7877680 prefixEnd_7877680 4045036282310843774471215 := by
  unfold tailWord_7877680
  simp only [CollatzResearch.WordTrace]
  refine ⟨143661297050259117738147247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191548396067012156984196329 143661297050259117738147247)
  ·
    refine ⟨215491945575388676607220871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143661297050259117738147247 215491945575388676607220871)
    ·
      refine ⟨323237918363083014910831307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215491945575388676607220871 323237918363083014910831307)
      ·
        refine ⟨484856877544624522366246961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323237918363083014910831307 484856877544624522366246961)
        ·
          refine ⟨363642658158468391774685221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484856877544624522366246961 363642658158468391774685221)
          ·
            refine ⟨68182998404712823457753479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363642658158468391774685221 68182998404712823457753479)
            ·
              refine ⟨102274497607069235186630219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68182998404712823457753479 102274497607069235186630219)
              ·
                refine ⟨153411746410603852779945329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102274497607069235186630219 153411746410603852779945329)
                ·
                  refine ⟨115058809807952889584958997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153411746410603852779945329 115058809807952889584958997)
                  ·
                    refine ⟨5393381709747791699294953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115058809807952889584958997 5393381709747791699294953)
                    ·
                      refine ⟨4045036282310843774471215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393381709747791699294953 4045036282310843774471215)
                      ·
                        rfl

theorem cell23_7877680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 6, 2].length) (baseStart_7877680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877680 prefixEnd_7877680 := by exact prefixLift 7877680
  have htrace : WordTrace (prefixWord ++ tailWord_7877680) baseStart_7877680 baseEnd_7877680 := by
    simpa [prefixWord, tailWord_7877680, baseEnd_7877680] using wordTrace_append hprefix tailTrace_7877680
  have hstable : (prefixWord ++ tailWord_7877680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877680).length < 2 ^ (prefixWord ++ tailWord_7877680).sum := by decide
  have hdescent : baseEnd_7877680 < baseStart_7877680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877683 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5]
def baseStart_7877683 : Nat := 118140960795 + 7877683 * 2 ^ 59
def prefixEnd_7877683 : Nat := 4983230072969 + 3 ^ 40 * 7877683 * 2
def baseEnd_7877683 : Nat := 4045037822752807262733701

theorem tailTrace_7877683 : CollatzResearch.WordTrace tailWord_7877683 prefixEnd_7877683 4045037822752807262733701 := by
  unfold tailWord_7877683
  simp only [CollatzResearch.WordTrace]
  refine ⟨287322703519507366988653703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191548469013004911325769135 287322703519507366988653703)
  ·
    refine ⟨430984055279261050482980555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287322703519507366988653703 430984055279261050482980555)
    ·
      refine ⟨646476082918891575724470833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430984055279261050482980555 646476082918891575724470833)
      ·
        refine ⟨484857062189168681793353125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646476082918891575724470833 484857062189168681793353125)
        ·
          refine ⟨90910699160469127836253711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484857062189168681793353125 90910699160469127836253711)
          ·
            refine ⟨136366048740703691754380567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90910699160469127836253711 136366048740703691754380567)
            ·
              refine ⟨204549073111055537631570851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136366048740703691754380567 204549073111055537631570851)
              ·
                refine ⟨306823609666583306447356277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204549073111055537631570851 306823609666583306447356277)
                ·
                  refine ⟨28764713406242184979439651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306823609666583306447356277 28764713406242184979439651)
                  ·
                    refine ⟨43147070109363277469159477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28764713406242184979439651 43147070109363277469159477)
                    ·
                      refine ⟨4045037822752807262733701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43147070109363277469159477 4045037822752807262733701)
                      ·
                        rfl

theorem cell23_7877683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_7877683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877683 prefixEnd_7877683 := by exact prefixLift 7877683
  have htrace : WordTrace (prefixWord ++ tailWord_7877683) baseStart_7877683 baseEnd_7877683 := by
    simpa [prefixWord, tailWord_7877683, baseEnd_7877683] using wordTrace_append hprefix tailTrace_7877683
  have hstable : (prefixWord ++ tailWord_7877683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877683).length < 2 ^ (prefixWord ++ tailWord_7877683).sum := by decide
  have hdescent : baseEnd_7877683 < baseStart_7877683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877684 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7877684 : Nat := 118140960795 + 7877684 * 2 ^ 59
def prefixEnd_7877684 : Nat := 4983230072969 + 3 ^ 40 * 7877684 * 2
def baseEnd_7877684 : Nat := 4045038336233461758821197

theorem tailTrace_7877684 : CollatzResearch.WordTrace tailWord_7877684 prefixEnd_7877684 4045038336233461758821197 := by
  unfold tailWord_7877684
  simp only [CollatzResearch.WordTrace]
  refine ⟨143661369996251872079720053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191548493328335829439626737 143661369996251872079720053)
  ·
    refine ⟨13468253437148613007473755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143661369996251872079720053 13468253437148613007473755)
    ·
      refine ⟨20202380155722919511210633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468253437148613007473755 20202380155722919511210633)
      ·
        refine ⟨15151785116792189633407975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20202380155722919511210633 15151785116792189633407975)
        ·
          refine ⟨22727677675188284450111963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151785116792189633407975 22727677675188284450111963)
          ·
            refine ⟨34091516512782426675167945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22727677675188284450111963 34091516512782426675167945)
            ·
              refine ⟨25568637384586820006375959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34091516512782426675167945 25568637384586820006375959)
              ·
                refine ⟨38352956076880230009563939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25568637384586820006375959 38352956076880230009563939)
                ·
                  refine ⟨57529434115320345014345909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38352956076880230009563939 57529434115320345014345909)
                  ·
                    refine ⟨5393384448311282345094929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57529434115320345014345909 5393384448311282345094929)
                    ·
                      refine ⟨4045038336233461758821197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393384448311282345094929 4045038336233461758821197)
                      ·
                        rfl

theorem cell23_7877684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7877684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877684 prefixEnd_7877684 := by exact prefixLift 7877684
  have htrace : WordTrace (prefixWord ++ tailWord_7877684) baseStart_7877684 baseEnd_7877684 := by
    simpa [prefixWord, tailWord_7877684, baseEnd_7877684] using wordTrace_append hprefix tailTrace_7877684
  have hstable : (prefixWord ++ tailWord_7877684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877684).length < 2 ^ (prefixWord ++ tailWord_7877684).sum := by decide
  have hdescent : baseEnd_7877684 < baseStart_7877684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877690 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_7877690 : Nat := 118140960795 + 7877690 * 2 ^ 59
def prefixEnd_7877690 : Nat := 4983230072969 + 3 ^ 40 * 7877690 * 2
def baseEnd_7877690 : Nat := 1348347139039129578448723

theorem tailTrace_7877690 : CollatzResearch.WordTrace tailWord_7877690 prefixEnd_7877690 1348347139039129578448723 := by
  unfold tailWord_7877690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71830739707620501796039631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191548639220321338122772349 71830739707620501796039631)
  ·
    refine ⟨107746109561430752694059447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71830739707620501796039631 107746109561430752694059447)
    ·
      refine ⟨161619164342146129041089171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107746109561430752694059447 161619164342146129041089171)
      ·
        refine ⟨242428746513219193561633757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161619164342146129041089171 242428746513219193561633757)
        ·
          refine ⟨90910779942457197585612659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242428746513219193561633757 90910779942457197585612659)
          ·
            refine ⟨136366169913685796378418989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90910779942457197585612659 136366169913685796378418989)
            ·
              refine ⟨51137313717632173641907121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136366169913685796378418989 51137313717632173641907121)
              ·
                refine ⟨38352985288224130231430341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51137313717632173641907121 38352985288224130231430341)
                ·
                  refine ⟨7191184741542024418393189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38352985288224130231430341 7191184741542024418393189)
                  ·
                    refine ⟨1348347139039129578448723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191184741542024418393189 1348347139039129578448723)
                    ·
                      rfl

theorem cell23_7877690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_7877690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877690 prefixEnd_7877690 := by exact prefixLift 7877690
  have htrace : WordTrace (prefixWord ++ tailWord_7877690) baseStart_7877690 baseEnd_7877690 := by
    simpa [prefixWord, tailWord_7877690, baseEnd_7877690] using wordTrace_append hprefix tailTrace_7877690
  have hstable : (prefixWord ++ tailWord_7877690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877690).length < 2 ^ (prefixWord ++ tailWord_7877690).sum := by decide
  have hdescent : baseEnd_7877690 < baseStart_7877690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877703 : List Nat := [1, 1, 4, 1, 3, 2, 11]
def baseStart_7877703 : Nat := 118140960795 + 7877703 * 2 ^ 59
def prefixEnd_7877703 : Nat := 4983230072969 + 3 ^ 40 * 7877703 * 2
def baseEnd_7877703 : Nat := 49938865337850582524489

theorem tailTrace_7877703 : CollatzResearch.WordTrace tailWord_7877703 prefixEnd_7877703 49938865337850582524489 := by
  unfold tailWord_7877703
  simp only [CollatzResearch.WordTrace]
  refine ⟨287323432979434910404381763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191548955319623273602921175 287323432979434910404381763)
  ·
    refine ⟨430985149469152365606572645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287323432979434910404381763 430985149469152365606572645)
    ·
      refine ⟨80809715525466068551232371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430985149469152365606572645 80809715525466068551232371)
      ·
        refine ⟨121214573288199102826848557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80809715525466068551232371 121214573288199102826848557)
        ·
          refine ⟨45455464983074663560068209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121214573288199102826848557 45455464983074663560068209)
          ·
            refine ⟨34091598737305997670051157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45455464983074663560068209 34091598737305997670051157)
            ·
              refine ⟨49938865337850582524489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34091598737305997670051157 49938865337850582524489)
              ·
                rfl

theorem cell23_7877703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 11].length) (baseStart_7877703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877703 prefixEnd_7877703 := by exact prefixLift 7877703
  have htrace : WordTrace (prefixWord ++ tailWord_7877703) baseStart_7877703 baseEnd_7877703 := by
    simpa [prefixWord, tailWord_7877703, baseEnd_7877703] using wordTrace_append hprefix tailTrace_7877703
  have hstable : (prefixWord ++ tailWord_7877703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877703).length < 2 ^ (prefixWord ++ tailWord_7877703).sum := by decide
  have hdescent : baseEnd_7877703 < baseStart_7877703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877764 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_7877764 : Nat := 118140960795 + 7877764 * 2 ^ 59
def prefixEnd_7877764 : Nat := 4983230072969 + 3 ^ 40 * 7877764 * 2
def baseEnd_7877764 : Nat := 4045079414685821445820829

theorem tailTrace_7877764 : CollatzResearch.WordTrace tailWord_7877764 prefixEnd_7877764 4045079414685821445820829 := by
  unfold tailWord_7877764
  simp only [CollatzResearch.WordTrace]
  refine ⟨143662828916106958911176173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191550438554809278548234897 143662828916106958911176173)
  ·
    refine ⟨53873560843540109591691065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143662828916106958911176173 53873560843540109591691065)
    ·
      refine ⟨40405170632655082193768299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53873560843540109591691065 40405170632655082193768299)
      ·
        refine ⟨60607755948982623290652449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40405170632655082193768299 60607755948982623290652449)
        ·
          refine ⟨45455816961736967467989337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60607755948982623290652449 45455816961736967467989337)
          ·
            refine ⟨34091862721302725600992003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45455816961736967467989337 34091862721302725600992003)
            ·
              refine ⟨51137794081954088401488005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34091862721302725600992003 51137794081954088401488005)
              ·
                refine ⟨9588336390366391575279001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51137794081954088401488005 9588336390366391575279001)
                ·
                  refine ⟨7191252292774793681459251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9588336390366391575279001 7191252292774793681459251)
                  ·
                    refine ⟨10786878439162190522188877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7191252292774793681459251 10786878439162190522188877)
                    ·
                      refine ⟨4045079414685821445820829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10786878439162190522188877 4045079414685821445820829)
                      ·
                        rfl

theorem cell23_7877764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_7877764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877764 prefixEnd_7877764 := by exact prefixLift 7877764
  have htrace : WordTrace (prefixWord ++ tailWord_7877764) baseStart_7877764 baseEnd_7877764 := by
    simpa [prefixWord, tailWord_7877764, baseEnd_7877764] using wordTrace_append hprefix tailTrace_7877764
  have hstable : (prefixWord ++ tailWord_7877764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877764).length < 2 ^ (prefixWord ++ tailWord_7877764).sum := by decide
  have hdescent : baseEnd_7877764 < baseStart_7877764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7877765 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 1, 2, 2]
def baseStart_7877765 : Nat := 118140960795 + 7877765 * 2 ^ 59
def prefixEnd_7877765 : Nat := 4983230072969 + 3 ^ 40 * 7877765 * 2
def baseEnd_7877765 : Nat := 4045079928166475941908325

theorem tailTrace_7877765 : CollatzResearch.WordTrace tailWord_7877765 prefixEnd_7877765 4045079928166475941908325 := by
  unfold tailWord_7877765
  simp only [CollatzResearch.WordTrace]
  refine ⟨287325694305210294993138749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191550462870140196662092499 287325694305210294993138749)
  ·
    refine ⟨107747135364453860622427031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287325694305210294993138749 107747135364453860622427031)
    ·
      refine ⟨161620703046680790933640547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107747135364453860622427031 161620703046680790933640547)
      ·
        refine ⟨242431054570021186400460821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161620703046680790933640547 242431054570021186400460821)
        ·
          refine ⟨11363955682969743112521601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242431054570021186400460821 11363955682969743112521601)
          ·
            refine ⟨8522966762227307334391201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11363955682969743112521601 8522966762227307334391201)
            ·
              refine ⟨6392225071670480500793401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8522966762227307334391201 6392225071670480500793401)
              ·
                refine ⟨4794168803752860375595051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392225071670480500793401 4794168803752860375595051)
                ·
                  refine ⟨7191253205629290563392577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794168803752860375595051 7191253205629290563392577)
                  ·
                    refine ⟨5393439904221967922544433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191253205629290563392577 5393439904221967922544433)
                    ·
                      refine ⟨4045079928166475941908325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5393439904221967922544433 4045079928166475941908325)
                      ·
                        rfl

theorem cell23_7877765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_7877765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7877765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7877765 prefixEnd_7877765 := by exact prefixLift 7877765
  have htrace : WordTrace (prefixWord ++ tailWord_7877765) baseStart_7877765 baseEnd_7877765 := by
    simpa [prefixWord, tailWord_7877765, baseEnd_7877765] using wordTrace_append hprefix tailTrace_7877765
  have hstable : (prefixWord ++ tailWord_7877765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7877765).length < 2 ^ (prefixWord ++ tailWord_7877765).sum := by decide
  have hdescent : baseEnd_7877765 < baseStart_7877765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7877765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
